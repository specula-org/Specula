package buga_test

import (
	"fmt"
	"sort"
	"strings"
	"testing"

	raft "go.etcd.io/etcd/raft"
	pb "go.etcd.io/etcd/raft/raftpb"
)

const noLimit = ^uint64(0)

type testNode struct {
	id      uint64
	rn      *raft.RawNode
	storage *raft.MemoryStorage
}

type cluster struct {
	t     *testing.T
	nodes map[uint64]*testNode
}

func newCluster(t *testing.T) *cluster {
	t.Helper()
	c := &cluster{t: t, nodes: map[uint64]*testNode{}}
	peers := []raft.Peer{{ID: 1}, {ID: 2}, {ID: 3}}
	for _, id := range []uint64{1, 2, 3} {
		st := raft.NewMemoryStorage()
		rn, err := raft.NewRawNode(&raft.Config{
			ID:                        id,
			ElectionTick:              10,
			HeartbeatTick:             1,
			Storage:                   st,
			MaxSizePerMsg:             noLimit,
			MaxCommittedSizePerReady:  1,
			MaxInflightMsgs:           256,
			MaxUncommittedEntriesSize: noLimit,
			PreVote:                   false,
		})
		if err != nil {
			t.Fatalf("NewRawNode(%d): %v", id, err)
		}
		if err := rn.Bootstrap(peers); err != nil {
			t.Fatalf("Bootstrap(%d): %v", id, err)
		}
		c.nodes[id] = &testNode{id: id, rn: rn, storage: st}
	}
	for _, id := range []uint64{1, 2, 3} {
		c.drain(id, true)
	}
	return c
}

func (c *cluster) node(id uint64) *testNode {
	n := c.nodes[id]
	if n == nil {
		c.t.Fatalf("missing node %d", id)
	}
	return n
}

func (c *cluster) beginReady(id uint64) raft.Ready {
	n := c.node(id)
	if !n.rn.HasReady() {
		c.t.Fatalf("node %d has no Ready", id)
	}
	rd := n.rn.Ready()
	if !raft.IsEmptySnap(rd.Snapshot) {
		if err := n.storage.ApplySnapshot(rd.Snapshot); err != nil {
			c.t.Fatalf("node %d ApplySnapshot: %v", id, err)
		}
	}
	if len(rd.Entries) > 0 {
		if err := n.storage.Append(rd.Entries); err != nil {
			c.t.Fatalf("node %d Append: %v", id, err)
		}
	}
	if !raft.IsEmptyHardState(rd.HardState) {
		if err := n.storage.SetHardState(rd.HardState); err != nil {
			c.t.Fatalf("node %d SetHardState: %v", id, err)
		}
	}
	return rd
}

func (c *cluster) finishReady(id uint64, rd raft.Ready, applyConf bool) {
	n := c.node(id)
	if applyConf {
		for _, ent := range rd.CommittedEntries {
			c.applyEntry(id, ent)
		}
	}
	n.rn.Advance(rd)
}

func (c *cluster) drain(id uint64, applyConf bool) []pb.Message {
	var out []pb.Message
	for c.node(id).rn.HasReady() {
		rd := c.beginReady(id)
		out = append(out, rd.Messages...)
		c.finishReady(id, rd, applyConf)
	}
	return out
}

func (c *cluster) applyEntry(id uint64, ent pb.Entry) {
	switch ent.Type {
	case pb.EntryConfChange:
		var cc pb.ConfChange
		if err := cc.Unmarshal(ent.Data); err != nil {
			c.t.Fatalf("node %d unmarshal ConfChange at %d: %v", id, ent.Index, err)
		}
		c.node(id).rn.ApplyConfChange(cc)
	case pb.EntryConfChangeV2:
		var cc pb.ConfChangeV2
		if err := cc.Unmarshal(ent.Data); err != nil {
			c.t.Fatalf("node %d unmarshal ConfChangeV2 at %d: %v", id, ent.Index, err)
		}
		c.node(id).rn.ApplyConfChange(cc)
	}
}

func (c *cluster) step(m pb.Message) {
	n := c.nodes[m.To]
	if n == nil {
		return
	}
	if err := n.rn.Step(m); err != nil {
		c.t.Fatalf("Step %s: %v", msgString(m), err)
	}
}

func (c *cluster) electNode1AndCommitNoopToNode2() {
	if err := c.node(1).rn.Campaign(); err != nil {
		c.t.Fatalf("campaign node 1: %v", err)
	}
	for _, m := range c.drain(1, true) {
		if m.Type == pb.MsgVote {
			c.step(m)
			for _, resp := range c.drain(m.To, true) {
				if resp.To == 1 {
					c.step(resp)
				}
			}
		}
	}

	var appendResponses []pb.Message
	for _, m := range c.drain(1, true) {
		if m.Type == pb.MsgApp && (m.To == 2 || m.To == 3) {
			c.step(m)
			appendResponses = append(appendResponses, c.drain(m.To, true)...)
		}
	}
	for _, m := range appendResponses {
		if m.To == 1 {
			c.step(m)
		}
	}

	var commitMsgs []pb.Message
	for _, m := range c.drain(1, true) {
		if m.Type == pb.MsgApp && (m.To == 2 || m.To == 3) {
			commitMsgs = append(commitMsgs, m)
		}
	}
	for _, m := range commitMsgs {
		c.step(m)
		c.drain(m.To, true)
	}

	leader := c.node(1).rn.Status()
	follower := c.node(2).rn.Status()
	if leader.RaftState != raft.StateLeader || leader.Term != 2 || leader.Commit < 4 {
		c.t.Fatalf("node 1 not established leader at term 2 with commit >=4: %s", statusString(leader))
	}
	if follower.RaftState != raft.StateFollower || follower.Term != 2 || follower.Commit != 4 || follower.Applied != 4 {
		c.t.Fatalf("node 2 not at expected pre-conf state: %s", statusString(follower))
	}
}

func (c *cluster) commitV2EntryToNode2ButDoNotApply() []pb.ConfChangeI {
	cc := pb.ConfChangeV2{
		Transition: pb.ConfChangeTransitionAuto,
		Changes: []pb.ConfChangeSingle{
			{Type: pb.ConfChangeRemoveNode, NodeID: 3},
			{Type: pb.ConfChangeAddNode, NodeID: 4},
		},
	}
	if err := c.node(1).rn.ProposeConfChange(cc); err != nil {
		c.t.Fatalf("propose V2 conf change: %v", err)
	}
	var toNode2 []pb.Message
	for _, m := range c.drain(1, true) {
		if m.Type == pb.MsgApp && m.To == 2 {
			toNode2 = append(toNode2, m)
		}
	}
	if len(toNode2) == 0 {
		c.t.Fatalf("leader emitted no append carrying V2 entry to node 2")
	}
	c.step(toNode2[0])
	var responses []pb.Message
	for _, m := range c.drain(2, true) {
		if m.To == 1 {
			responses = append(responses, m)
		}
	}
	for _, m := range responses {
		c.step(m)
	}

	rd := c.beginReady(1)
	var delayed []pb.ConfChangeI
	var commitTo2 []pb.Message
	for _, ent := range rd.CommittedEntries {
		if ent.Type == pb.EntryConfChangeV2 {
			var cc pb.ConfChangeV2
			if err := cc.Unmarshal(ent.Data); err != nil {
				c.t.Fatalf("leader unmarshal committed V2: %v", err)
			}
			delayed = append(delayed, cc)
		}
	}
	for _, m := range rd.Messages {
		if m.Type == pb.MsgApp && m.To == 2 {
			commitTo2 = append(commitTo2, m)
		}
	}
	c.finishReady(1, rd, false)
	if len(commitTo2) == 0 {
		c.t.Fatalf("leader emitted no commit update for V2 entry to node 2")
	}
	c.step(commitTo2[0])
	return delayed
}

func (c *cluster) commitLegacyEntryToNode2ButDoNotApply() {
	cc := pb.ConfChange{Type: pb.ConfChangeAddNode, NodeID: 4}
	if err := c.node(1).rn.ProposeConfChange(cc); err != nil {
		c.t.Fatalf("propose legacy conf change: %v", err)
	}
	var toNode2 []pb.Message
	for _, m := range c.drain(1, true) {
		if m.Type == pb.MsgApp && m.To == 2 {
			toNode2 = append(toNode2, m)
		}
	}
	if len(toNode2) == 0 {
		c.t.Fatalf("leader emitted no append carrying legacy entry to node 2")
	}
	c.step(toNode2[0])
	var responses []pb.Message
	for _, m := range c.drain(2, true) {
		if m.To == 1 {
			responses = append(responses, m)
		}
	}
	for _, m := range responses {
		c.step(m)
	}

	rd := c.beginReady(1)
	var commitTo2 []pb.Message
	for _, m := range rd.Messages {
		if m.Type == pb.MsgApp && m.To == 2 {
			commitTo2 = append(commitTo2, m)
		}
	}
	c.finishReady(1, rd, true)
	if len(commitTo2) == 0 {
		c.t.Fatalf("leader emitted no commit update for legacy entry to node 2")
	}
	c.step(commitTo2[0])
}

func TestBugA_V2PendingCampaignDisruptsLeader(t *testing.T) {
	c := newCluster(t)
	c.electNode1AndCommitNoopToNode2()
	delayedLeaderConf := c.commitV2EntryToNode2ButDoNotApply()

	before := c.node(2).rn.Status()
	if before.RaftState != raft.StateFollower || before.Term != 2 || before.Commit != 5 || before.Applied != 4 {
		t.Fatalf("node 2 branch precondition mismatch: %s", statusString(before))
	}
	if !c.node(2).rn.HasReady() {
		t.Fatalf("node 2 should have a pending, not-yet-active Ready for committed V2 entry")
	}
	fmt.Printf("BRANCH before campaign node2=%s hasReady=%v activeReady=false pendingEntry=EntryConfChangeV2@5\n",
		statusString(before), c.node(2).rn.HasReady())

	leaderBefore := c.node(1).rn.Status()
	if err := c.node(2).rn.Campaign(); err != nil {
		t.Fatalf("campaign node 2: %v", err)
	}
	afterCampaign := c.node(2).rn.Status()
	rd2 := c.beginReady(2)
	votes := filterMessages(rd2.Messages, pb.MsgVote)
	fmt.Printf("CAMPAIGN after node2=%s emittedVotes=%s allMessages=%s\n",
		statusString(afterCampaign), msgList(votes), msgList(rd2.Messages))
	if afterCampaign.RaftState != raft.StateCandidate || afterCampaign.Term != 3 {
		t.Fatalf("node 2 did not campaign over pending V2 entry: %s", statusString(afterCampaign))
	}
	if len(votes) != 2 || !hasVoteTo(votes, 1) || !hasVoteTo(votes, 3) {
		t.Fatalf("expected MsgVote requests to old voters 1 and 3, got %s", msgList(votes))
	}

	c.step(firstVoteTo(votes, 1))
	leaderAfterVote := c.node(1).rn.Status()
	fmt.Printf("CONSEQUENCE leaderBefore=%s leaderAfterVote=%s\n",
		statusString(leaderBefore), statusString(leaderAfterVote))
	if leaderBefore.RaftState != raft.StateLeader || leaderBefore.Term != 2 {
		t.Fatalf("node 1 was not a live leader before vote: %s", statusString(leaderBefore))
	}
	if leaderAfterVote.RaftState == raft.StateLeader || leaderAfterVote.Term != 3 {
		t.Fatalf("leader was not disrupted by higher-term vote: %s", statusString(leaderAfterVote))
	}

	rd1 := c.beginReady(1)
	voteResponses := filterMessages(rd1.Messages, pb.MsgVoteResp)
	c.finishReady(1, rd1, true)
	for _, ent := range rd2.CommittedEntries {
		c.applyEntry(2, ent)
	}
	c.finishReady(2, rd2, false)
	if len(voteResponses) > 0 {
		c.step(voteResponses[0])
		c.drain(2, true)
	}
	for _, cc := range delayedLeaderConf {
		c.node(1).rn.ApplyConfChange(cc)
	}
	fmt.Printf("RESULT reproduced=true finalNode1=%s finalNode2=%s voteResponses=%s\n",
		statusString(c.node(1).rn.Status()), statusString(c.node(2).rn.Status()), msgList(voteResponses))
}

func TestControl_LegacyPendingConfBlocksCampaign(t *testing.T) {
	c := newCluster(t)
	c.electNode1AndCommitNoopToNode2()
	c.commitLegacyEntryToNode2ButDoNotApply()

	before := c.node(2).rn.Status()
	if before.RaftState != raft.StateFollower || before.Term != 2 || before.Commit != 5 || before.Applied != 4 {
		t.Fatalf("node 2 legacy-control precondition mismatch: %s", statusString(before))
	}
	if err := c.node(2).rn.Campaign(); err != nil {
		t.Fatalf("legacy-control campaign node 2: %v", err)
	}
	afterCampaign := c.node(2).rn.Status()
	rd2 := c.beginReady(2)
	votes := filterMessages(rd2.Messages, pb.MsgVote)
	fmt.Printf("CONTROL legacy before=%s afterCampaign=%s emittedVotes=%s allMessages=%s\n",
		statusString(before), statusString(afterCampaign), msgList(votes), msgList(rd2.Messages))
	if afterCampaign.RaftState != raft.StateFollower || afterCampaign.Term != 2 {
		t.Fatalf("legacy pending conf did not block campaign: %s", statusString(afterCampaign))
	}
	if len(votes) != 0 {
		t.Fatalf("legacy pending conf emitted votes: %s", msgList(votes))
	}
	leader := c.node(1).rn.Status()
	if leader.RaftState != raft.StateLeader || leader.Term != 2 {
		t.Fatalf("legacy control leader unexpectedly disrupted: %s", statusString(leader))
	}
	c.finishReady(2, rd2, true)
	fmt.Printf("CONTROL_RESULT legacyBlocked=true leader=%s node2=%s\n",
		statusString(c.node(1).rn.Status()), statusString(c.node(2).rn.Status()))
}

func filterMessages(msgs []pb.Message, typ pb.MessageType) []pb.Message {
	var out []pb.Message
	for _, m := range msgs {
		if m.Type == typ {
			out = append(out, m)
		}
	}
	return out
}

func hasVoteTo(msgs []pb.Message, to uint64) bool {
	for _, m := range msgs {
		if m.To == to {
			return true
		}
	}
	return false
}

func firstVoteTo(msgs []pb.Message, to uint64) pb.Message {
	for _, m := range msgs {
		if m.To == to {
			return m
		}
	}
	panic(fmt.Sprintf("missing vote to %d", to))
}

func statusString(st raft.Status) string {
	return fmt.Sprintf("{id:%d state:%s term:%d vote:%d commit:%d applied:%d lead:%d}",
		st.ID, st.RaftState, st.Term, st.Vote, st.Commit, st.Applied, st.Lead)
}

func msgList(msgs []pb.Message) string {
	if len(msgs) == 0 {
		return "[]"
	}
	parts := make([]string, 0, len(msgs))
	for _, m := range msgs {
		parts = append(parts, msgString(m))
	}
	sort.Strings(parts)
	return "[" + strings.Join(parts, ", ") + "]"
}

func msgString(m pb.Message) string {
	return fmt.Sprintf("%d->%d %s term=%d index=%d logTerm=%d commit=%d entries=%d reject=%v",
		m.From, m.To, m.Type, m.Term, m.Index, m.LogTerm, m.Commit, len(m.Entries), m.Reject)
}
