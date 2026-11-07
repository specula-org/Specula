package raft

// Generated adapter: setup, real calls, observation only.
import (
	"context"
	"encoding/json"
	"fmt"
	"go.etcd.io/etcd/raft/quorum"
	pb "go.etcd.io/etcd/raft/raftpb"
	"go.etcd.io/etcd/raft/tracker"
	"os"
	"reflect"
	"sort"
	"strconv"
	"strings"
	"testing"
	"time"
)

type avConfig struct {
	Voters, Outgoing, Learners, LearnersNext []uint64
	AutoLeave                                bool
}
type avChange struct {
	Kind   string
	Target uint64
}
type avEntry struct {
	Kind, Transition                     string
	Target, Weight, Encoded, Term, Index uint64
	Changes                              []avChange
}
type avProgress struct {
	ID, Match, Next, Pending uint64
	Mode                     string
	Probe, Active            bool
	Inflight                 []uint64
}
type avRead struct {
	ID, Index, FromID uint64
	Acks              []uint64
}
type avMessage struct {
	Type                                                    string
	FromID, To, Term, Index, LogTerm, Commit, Hint, Context uint64
	Reject, Forced                                          bool
	Entries                                                 []avEntry
}
type avSnap struct {
	Index, Term uint64
	Config      avConfig
}
type avSoft struct {
	Role string
	Lead uint64
}
type avVote struct {
	ID  uint64
	Yes bool
}
type avPre struct {
	Usnap                                                             avSnap
	Votes                                                             []avVote
	Config                                                            avConfig
	Role                                                              string
	Term, Vote, Lead, Commit, Applied, Pending, Quota, Transfer, Uoff uint64
	Cut                                                               uint64
	StoreSnapshot                                                     avSnap
	Log                                                               []avEntry
	Prs                                                               []avProgress
	Messages                                                          []avMessage
	Reads, ReadQueue                                                  []avRead
	PreVote, CheckQuorum                                              bool
	Elapsed, Heartbeat                                                int
	PrevHS                                                            pb.HardState
	PrevSS                                                            avSoft
}
type avInput struct {
	Entries         []avEntry
	Entry           avEntry
	Snapshot        avSnap
	FromID, Context uint64
	Message         avMessage
	Between         []avMessage
}
type avCase struct {
	Protocol, ID, Action string
	Pre                  avPre
	Input                avInput
	Meta                 map[string]interface{}
}

func avSet(xs []uint64) map[uint64]struct{} {
	if len(xs) == 0 {
		return nil
	}
	m := map[uint64]struct{}{}
	for _, x := range xs {
		m[x] = struct{}{}
	}
	return m
}
func avIDs(m map[uint64]struct{}) []uint64 {
	a := []uint64{}
	for x := range m {
		a = append(a, x)
	}
	sort.Slice(a, func(i, j int) bool { return a[i] < a[j] })
	return a
}
func avCfg(c tracker.Config) interface{} {
	return map[string]interface{}{"voters": avIDs(c.Voters[0]), "outgoing": avIDs(c.Voters[1]), "learners": avIDs(c.Learners), "learnersNext": avIDs(c.LearnersNext), "autoLeave": c.AutoLeave}
}
func avCS(c avConfig) pb.ConfState {
	return pb.ConfState{Voters: c.Voters, VotersOutgoing: c.Outgoing, Learners: c.Learners, LearnersNext: c.LearnersNext, AutoLeave: c.AutoLeave}
}
func avCfgCS(c pb.ConfState) interface{} {
	return avCfg(tracker.Config{Voters: quorum.JointConfig{avSet(c.Voters), avSet(c.VotersOutgoing)}, Learners: avSet(c.Learners), LearnersNext: avSet(c.LearnersNext), AutoLeave: c.AutoLeave})
}
func avKind(s string) pb.ConfChangeType {
	switch s {
	case "AddVoter":
		return pb.ConfChangeAddNode
	case "AddLearner":
		return pb.ConfChangeAddLearnerNode
	case "Remove":
		return pb.ConfChangeRemoveNode
	case "Update":
		return pb.ConfChangeUpdateNode
	}
	panic("unsupported change " + s)
}
func avKindName(t pb.ConfChangeType) string {
	switch t {
	case pb.ConfChangeAddNode:
		return "AddVoter"
	case pb.ConfChangeAddLearnerNode:
		return "AddLearner"
	case pb.ConfChangeRemoveNode:
		return "Remove"
	case pb.ConfChangeUpdateNode:
		return "Update"
	}
	panic("unknown change")
}
func avCC(e avEntry) pb.ConfChangeI {
	if e.Kind != "V2" {
		return pb.ConfChange{Type: avKind(e.Kind), NodeID: e.Target}
	}
	c := pb.ConfChangeV2{}
	switch e.Transition {
	case "JointImplicit":
		c.Transition = pb.ConfChangeTransitionJointImplicit
	case "JointExplicit":
		c.Transition = pb.ConfChangeTransitionJointExplicit
	}
	for _, x := range e.Changes {
		c.Changes = append(c.Changes, pb.ConfChangeSingle{Type: avKind(x.Kind), NodeID: x.Target})
	}
	return c
}
func avEnt(e avEntry) pb.Entry {
	p := pb.Entry{Term: e.Term, Index: e.Index}
	if e.Kind == "Normal" {
		p.Data = make([]byte, e.Weight)
	} else {
		var err error
		p.Type, p.Data, err = pb.MarshalConfChange(avCC(e))
		if err != nil {
			panic(err)
		}
	}
	// Encoded=6 denotes nil Data, including the new automatic leave entry.
	if e.Weight == 0 && e.Encoded == 6 {
		p.Data = nil
	}
	return p
}
func avEnts(es []avEntry) []pb.Entry {
	r := []pb.Entry{}
	for _, e := range es {
		r = append(r, avEnt(e))
	}
	return r
}
func avObsEnt(e pb.Entry) interface{} {
	kind := "Normal"
	transition := "Legacy"
	target := uint64(0)
	changes := []interface{}{}
	if e.Type == pb.EntryConfChange {
		var c pb.ConfChange
		if err := c.Unmarshal(e.Data); err != nil {
			panic(err)
		}
		kind = avKindName(c.Type)
		target = c.NodeID
		changes = append(changes, map[string]interface{}{"kind": kind, "target": target})
	} else if e.Type == pb.EntryConfChangeV2 {
		kind = "V2"
		var c pb.ConfChangeV2
		if err := c.Unmarshal(e.Data); err != nil {
			panic(err)
		}
		transition = []string{"Auto", "JointImplicit", "JointExplicit"}[int(c.Transition)]
		for _, x := range c.Changes {
			changes = append(changes, map[string]interface{}{"kind": avKindName(x.Type), "target": x.NodeID})
		}
	}
	return map[string]interface{}{"kind": kind, "transition": transition, "target": target, "changes": changes, "weight": len(e.Data), "encoded": e.Size(), "term": e.Term, "index": e.Index}
}
func avObsEnts(es []pb.Entry) []interface{} {
	a := []interface{}{}
	for _, e := range es {
		a = append(a, avObsEnt(e))
	}
	return a
}
func avCtx(n uint64) []byte {
	if n == 0 {
		return nil
	}
	return []byte(strconv.FormatUint(n, 10))
}
func avCtxID(b []byte) uint64 {
	if len(b) == 0 {
		return 0
	}
	i, e := strconv.ParseUint(string(b), 10, 64)
	if e != nil {
		panic(e)
	}
	return i
}
func avMsg(m avMessage) pb.Message {
	ctx := avCtx(m.Context)
	if m.Forced {
		ctx = []byte(campaignTransfer)
	}
	return pb.Message{Type: pb.MessageType(pb.MessageType_value[m.Type]), From: m.FromID, To: m.To, Term: m.Term, Index: m.Index, LogTerm: m.LogTerm, Commit: m.Commit, Reject: m.Reject, RejectHint: m.Hint, Context: ctx, Entries: avEnts(m.Entries)}
}
func avContextID(b []byte) uint64 {
	if string(b) == string(campaignTransfer) {
		return 0
	}
	return avCtxID(b)
}
func avObsMessages(ms []avMessage) []interface{} {
	out := []pb.Message{}
	for _, m := range ms {
		out = append(out, avMsg(m))
	}
	return avObsMsgs(out)
}
func avObsMsgs(ms []pb.Message) []interface{} {
	a := []interface{}{}
	for _, m := range ms {
		a = append(a, map[string]interface{}{"type": m.Type.String(), "fromId": m.From, "to": m.To, "term": m.Term, "index": m.Index, "logTerm": m.LogTerm, "commit": m.Commit, "reject": m.Reject, "hint": m.RejectHint, "context": avContextID(m.Context), "forced": string(m.Context) == string(campaignTransfer), "entries": avObsEnts(m.Entries), "snapshot": avObsSnap(m.Snapshot)})
	}
	return a
}
func avSnapPB(s avSnap) pb.Snapshot {
	return pb.Snapshot{Metadata: pb.SnapshotMetadata{Index: s.Index, Term: s.Term, ConfState: avCS(s.Config)}}
}
func avObsSnap(s pb.Snapshot) interface{} {
	return map[string]interface{}{"index": s.Metadata.Index, "term": s.Metadata.Term, "config": avCfgCS(s.Metadata.ConfState)}
}
func avHS(h pb.HardState) interface{} {
	return map[string]interface{}{"term": h.Term, "vote": h.Vote, "commit": h.Commit}
}
func avSS(s *SoftState) interface{} {
	return map[string]interface{}{"role": strings.TrimPrefix(s.RaftState.String(), "State"), "lead": s.Lead}
}
func avState(s string) StateType {
	switch s {
	case "Follower":
		return StateFollower
	case "Leader":
		return StateLeader
	case "Candidate":
		return StateCandidate
	case "PreCandidate":
		return StatePreCandidate
	}
	panic(s)
}
func avReads(rs []ReadState) []interface{} {
	a := []interface{}{}
	for _, r := range rs {
		a = append(a, map[string]interface{}{"id": avCtxID(r.RequestCtx), "index": r.Index})
	}
	return a
}
func avVotes(v map[uint64]bool) []interface{} {
	a := []interface{}{}
	for n, b := range v {
		a = append(a, map[string]interface{}{"id": n, "yes": b})
	}
	return a
}
func avObs(rn *RawNode) interface{} {
	r := rn.raft
	l := r.raftLog
	prs := []interface{}{}
	r.prs.Visit(func(id uint64, p *tracker.Progress) {
		v := reflect.ValueOf(p.Inflights).Elem()
		buf := v.FieldByName("buffer")
		start := int(v.FieldByName("start").Int())
		cnt := int(v.FieldByName("count").Int())
		in := []uint64{}
		for i := 0; i < cnt; i++ {
			in = append(in, buf.Index((start+i)%buf.Len()).Uint())
		}
		prs = append(prs, map[string]interface{}{"id": id, "match": p.Match, "next": p.Next, "mode": strings.TrimPrefix(p.State.String(), "State"), "probe": p.ProbeSent, "pending": p.PendingSnapshot, "active": p.RecentActive, "inflight": in, "learner": p.IsLearner})
	})
	q := []interface{}{}
	for _, k := range r.readOnly.readIndexQueue {
		s := r.readOnly.pendingReadIndex[k]
		acks := []uint64{}
		for n, b := range s.acks {
			if b {
				acks = append(acks, n)
			}
		}
		q = append(q, map[string]interface{}{"id": avCtxID([]byte(k)), "index": s.index, "fromId": s.req.From, "acks": acks})
	}
	es, err := l.slice(l.firstIndex(), l.lastIndex()+1, noLimit)
	if err != nil {
		panic(err)
	}
	snap := pb.Snapshot{}
	if l.unstable.snapshot != nil {
		snap = *l.unstable.snapshot
	}
	st := l.storage.(*MemoryStorage)
	return map[string]interface{}{"config": avCfg(r.prs.Config), "role": strings.TrimPrefix(r.state.String(), "State"), "term": r.Term, "vote": r.Vote, "lead": r.lead, "commit": l.committed, "applied": l.applied, "pending": r.pendingConfIndex, "quota": r.uncommittedSize, "transfer": r.leadTransferee, "log": avObsEnts(es), "last": l.lastIndex(), "first": l.firstIndex(), "unstable": avObsEnts(l.unstable.entries), "uoff": l.unstable.offset, "snapshot": avObsSnap(snap), "prs": prs, "messages": avObsMsgs(r.msgs), "reads": avReads(r.readStates), "readQueue": q, "prevHS": avHS(rn.prevHardSt), "prevSS": avSS(rn.prevSoftSt), "elapsed": r.electionElapsed, "heartbeat": r.heartbeatElapsed, "preVote": r.preVote, "checkQuorum": r.checkQuorum, "isLearner": r.isLearner, "votes": avVotes(r.prs.Votes), "storage": map[string]interface{}{"log": avObsEnts(st.ents[1:]), "snapshot": avObsSnap(st.snapshot), "hs": avHS(st.hardState), "cut": st.ents[0].Index}}
}
func avRD(rd Ready) interface{} {
	ss := interface{}(nil)
	if rd.SoftState != nil {
		ss = avSS(rd.SoftState)
	}
	return map[string]interface{}{"hs": avHS(rd.HardState), "ss": ss, "entries": avObsEnts(rd.Entries), "committed": avObsEnts(rd.CommittedEntries), "messages": avObsMsgs(rd.Messages), "reads": avReads(rd.ReadStates), "snapshot": avObsSnap(rd.Snapshot), "mustSync": rd.MustSync, "cursor": rd.appliedCursor()}
}
func avSetup(c avCase) *RawNode {
	p := c.Pre
	st := NewMemoryStorage()
	if err := st.Append(avEnts(p.Log)); err != nil {
		panic(err)
	}
	if p.Cut > 0 {
		if err := st.Compact(p.Cut); err != nil {
			panic(err)
		}
	}
	st.snapshot = avSnapPB(p.StoreSnapshot)
	rn, err := NewRawNode(&Config{ID: 1, ElectionTick: 10, HeartbeatTick: 1, Storage: st, MaxSizePerMsg: 1024, MaxCommittedSizePerReady: 1024, MaxUncommittedEntriesSize: 16, MaxInflightMsgs: 2})
	if err != nil {
		panic(err)
	}
	r := rn.raft
	r.Term = p.Term
	r.Vote = p.Vote
	r.lead = p.Lead
	r.state = avState(p.Role)
	switch r.state {
	case StateLeader:
		r.step = stepLeader
		r.tick = r.tickHeartbeat
	case StateFollower:
		r.step = stepFollower
		r.tick = r.tickElection
	case StateCandidate, StatePreCandidate:
		r.step = stepCandidate
		r.tick = r.tickElection
	}
	r.prs = tracker.MakeProgressTracker(2)
	for _, v := range p.Votes {
		r.prs.RecordVote(v.ID, v.Yes)
	}
	r.prs.Config = tracker.Config{Voters: quorum.JointConfig{avSet(p.Config.Voters), avSet(p.Config.Outgoing)}, Learners: avSet(p.Config.Learners), LearnersNext: avSet(p.Config.LearnersNext), AutoLeave: p.Config.AutoLeave}
	for _, q := range p.Prs {
		pr := &tracker.Progress{Match: q.Match, Next: q.Next, ProbeSent: q.Probe, PendingSnapshot: q.Pending, RecentActive: q.Active, Inflights: tracker.NewInflights(2)}
		if q.Mode == "Replicate" {
			pr.State = tracker.StateReplicate
		}
		if q.Mode == "Snapshot" {
			pr.State = tracker.StateSnapshot
		}
		_, pr.IsLearner = r.prs.Learners[q.ID]
		for _, i := range q.Inflight {
			pr.Inflights.Add(i)
		}
		r.prs.Progress[q.ID] = pr
	}
	_, r.isLearner = r.prs.Learners[1]
	r.raftLog.committed = p.Commit
	r.raftLog.applied = p.Applied
	r.raftLog.unstable.offset = p.Uoff
	r.raftLog.unstable.entries = avEnts(p.Log[p.Uoff-1:])
	if p.Usnap.Index > 0 {
		snap := avSnapPB(p.Usnap)
		r.raftLog.unstable.snapshot = &snap
	}
	r.pendingConfIndex = p.Pending
	r.uncommittedSize = p.Quota
	r.leadTransferee = p.Transfer
	r.preVote = p.PreVote
	r.checkQuorum = p.CheckQuorum
	r.electionElapsed = p.Elapsed
	r.heartbeatElapsed = p.Heartbeat
	r.randomizedElectionTimeout = 10
	r.msgs = nil
	for _, m := range p.Messages {
		r.msgs = append(r.msgs, avMsg(m))
	}
	for _, s := range p.Reads {
		r.readStates = append(r.readStates, ReadState{Index: s.Index, RequestCtx: avCtx(s.ID)})
	}
	for _, s := range p.ReadQueue {
		msg := pb.Message{From: s.FromID, Entries: []pb.Entry{{Data: avCtx(s.ID)}}}
		r.readOnly.addRequest(s.Index, msg)
		for _, a := range s.Acks {
			r.readOnly.recvAck(a, avCtx(s.ID))
		}
	}
	rn.prevHardSt = p.PrevHS
	rn.prevSoftSt = &SoftState{Lead: p.PrevSS.Lead, RaftState: avState(p.PrevSS.Role)}
	return rn
}
func avNodeReady(n *node) Ready {
	select {
	case rd := <-n.Ready():
		return rd
	case <-time.After(2 * time.Second):
		panic("Node Ready timeout")
	}
}
func avRun(c avCase) (result map[string]interface{}) {
	result = map[string]interface{}{"protocol": "action-validation/v1", "id": c.ID, "engine": "go", "adapter_status": "ok"}
	var rn *RawNode
	phase := "setup"
	status := "ok"
	var ret interface{} = nil
	defer func() {
		if x := recover(); x != nil {
			result["raw_panic"] = fmt.Sprint(x)
			if phase == "execute" {
				status = "panic"
			} else {
				result["adapter_status"] = "error"
			}
		}
		if rn != nil {
			result["observation"] = map[string]interface{}{"state": avObs(rn), "status": status, "return": ret}
		}
	}()
	rn = avSetup(c)
	if strings.HasPrefix(c.Action, "bootstrap") {
		var err error
		rn, err = NewRawNode(&Config{ID: 1, ElectionTick: 10, HeartbeatTick: 1, Storage: NewMemoryStorage(), MaxSizePerMsg: 1024, MaxCommittedSizePerReady: 1024, MaxUncommittedEntriesSize: 16, MaxInflightMsgs: 2})
		if err != nil {
			panic(err)
		}
	}
	r := rn.raft
	var rd Ready
	var nd *node
	nodeDisabled := (c.Action == "ready_node" || c.Action == "advance_node") && !rn.HasReady()
	if strings.HasSuffix(c.Action, "_node") {
		n := newNode(rn)
		nd = &n
		go nd.run()
		defer nd.Stop()
	}
	if strings.HasPrefix(c.Action, "advance") && !nodeDisabled {
		if c.Action == "advance_node" {
			rd = avNodeReady(nd)
			nd.Status()
		} else {
			rd = rn.Ready()
		}
		if !IsEmptySnap(rd.Snapshot) {
			if err := r.raftLog.storage.(*MemoryStorage).ApplySnapshot(rd.Snapshot); err != nil {
				panic(err)
			}
		}
		if err := r.raftLog.storage.(*MemoryStorage).Append(rd.Entries); err != nil {
			panic(err)
		}
		if !IsEmptyHardState(rd.HardState) {
			if err := r.raftLog.storage.(*MemoryStorage).SetHardState(rd.HardState); err != nil {
				panic(err)
			}
		}
		result["captured_ready"] = avRD(rd)
		for _, m := range c.Input.Between {
			var e error
			if nd != nil {
				ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
				e = nd.step(ctx, avMsg(m))
				cancel()
				nd.Status()
			} else {
				e = r.Step(avMsg(m))
			}
			if e != nil && e != ErrProposalDropped {
				panic(e)
			}
			if e != nil {
				result["between_error"] = e.Error()
			}
		}
	}
	result["pre_observation"] = avObs(rn)
	var restartStorage *MemoryStorage
	var restartConfig *Config
	if c.Action == "restart" || c.Action == "construct" {
		restartStorage = NewMemoryStorage()
		if c.Action == "restart" {
			if e := restartStorage.ApplySnapshot(avSnapPB(c.Input.Snapshot)); e != nil {
				panic(e)
			}
		} else {
			restartStorage.snapshot = avSnapPB(c.Input.Snapshot)
			if e := restartStorage.Append(avEnts(c.Input.Entries)); e != nil {
				panic(e)
			}
		}
		if c.Action == "restart" {
			if e := restartStorage.SetHardState(pb.HardState{Term: 3, Commit: c.Input.Snapshot.Index}); e != nil {
				panic(e)
			}
		}
		restartConfig = &Config{ID: 1, ElectionTick: 10, HeartbeatTick: 1, Storage: restartStorage, MaxSizePerMsg: 1024, MaxCommittedSizePerReady: 1024, MaxUncommittedEntriesSize: 16, MaxInflightMsgs: 2}
		st := restartStorage
		opt := restartConfig
		result["pre_observation"] = map[string]interface{}{
			"storage":     map[string]interface{}{"log": avObsEnts(st.ents[1:]), "snapshot": avObsSnap(st.snapshot), "hs": avHS(st.hardState), "cut": st.ents[0].Index},
			"constructor": map[string]interface{}{"id": opt.ID, "applied": opt.Applied, "electionTick": opt.ElectionTick, "heartbeatTick": opt.HeartbeatTick, "maxSizePerMsg": opt.MaxSizePerMsg, "maxCommittedSizePerReady": opt.MaxCommittedSizePerReady, "maxUncommittedEntriesSize": opt.MaxUncommittedEntriesSize, "maxInflightMsgs": opt.MaxInflightMsgs},
		}
	}
	result["input_observation"] = map[string]interface{}{"entries": avObsEnts(avEnts(c.Input.Entries)), "entry": avObsEnt(avEnt(c.Input.Entry)), "snapshot": avObsSnap(avSnapPB(c.Input.Snapshot)), "fromId": c.Input.FromID, "context": c.Input.Context, "message": avObsMsgs([]pb.Message{avMsg(c.Input.Message)})[0], "between": avObsMessages(c.Input.Between)}
	if strings.HasPrefix(c.Action, "advance") && !nodeDisabled {
		result["input_observation"].(map[string]interface{})["batch"] = avRD(rd)
	}
	phase = "execute"
	if nodeDisabled {
		// Observe the real channel loop; HasReady is the explicit delivery prerequisite.
		nd.Status()
		select {
		case <-nd.Ready():
			panic("unexpected empty Node Ready delivery")
		case <-time.After(30 * time.Millisecond):
		}
		status = "disabled"
		result["disabled_phase"] = "Node HasReady delivery prerequisite"
		if strings.HasPrefix(c.Action, "advance") {
			result["input_observation"].(map[string]interface{})["batch"] = avRD(rn.readyWithoutAccept())
		}
		return result
	}
	var err error
	switch c.Action {
	case "vote", "receive":
		err = rn.Step(avMsg(c.Input.Message))
	case "proposal", "propose_then_apply":
		err = r.Step(pb.Message{Type: pb.MsgProp, From: 1, Entries: avEnts(c.Input.Entries)})
		if err == nil && c.Action == "propose_then_apply" {
			es, e := r.raftLog.slice(r.raftLog.lastIndex(), r.raftLog.lastIndex()+1, noLimit)
			if e != nil {
				panic(e)
			}
			ent := es[0]
			switch ent.Type {
			case pb.EntryConfChangeV2:
				var cc pb.ConfChangeV2
				if e := cc.Unmarshal(ent.Data); e != nil {
					panic(e)
				}
				rn.ApplyConfChange(cc)
			case pb.EntryConfChange:
				var cc pb.ConfChange
				if e := cc.Unmarshal(ent.Data); e != nil {
					panic(e)
				}
				rn.ApplyConfChange(cc)
			}
		}
	case "callback_node":
		ret = avCfgCS(*nd.ApplyConfChange(avCC(c.Input.Entry)))
		nd.Status()
		ctx, cancel := context.WithTimeout(context.Background(), 30*time.Millisecond)
		err = nd.Propose(ctx, nil)
		cancel()
		nd.Status()
		if err == context.DeadlineExceeded {
			status = "disabled"
			result["disabled_phase"] = "proposal channel after ApplyConfChange"
			err = nil
		}
	case "apply", "apply_then_step":
		ret = avCfgCS(*rn.ApplyConfChange(avCC(c.Input.Entry)))
		if c.Action == "apply_then_step" {
			ret = nil
			err = r.Step(avMsg(c.Input.Message))
		}
	case "bootstrap", "bootstrap_hup", "bootstrap_ready":
		peers := []Peer{}
		for _, id := range c.Input.Snapshot.Config.Voters {
			peers = append(peers, Peer{ID: id})
		}
		err = rn.Bootstrap(peers)
		if err == nil && c.Action == "bootstrap_hup" {
			err = rn.Campaign()
		}
		if err == nil && c.Action == "bootstrap_ready" {
			ret = avRD(rn.Ready())
		}
	case "hup":
		err = rn.Campaign()
	case "read":
		err = r.Step(pb.Message{Type: pb.MsgReadIndex, From: 1, Entries: []pb.Entry{{Data: avCtx(c.Input.Context)}}})
	case "readack":
		err = r.Step(pb.Message{Type: pb.MsgHeartbeatResp, From: c.Input.FromID, Context: avCtx(c.Input.Context)})
	case "checkquorum":
		err = r.Step(pb.Message{Type: pb.MsgCheckQuorum})
	case "restore":
		ret = map[string]interface{}{"restored": r.restore(avSnapPB(c.Input.Snapshot))}
	case "restart", "construct":
		result["restart_storage"] = avObsSnap(restartStorage.snapshot)
		rn, err = NewRawNode(restartConfig)
	case "ready_raw":
		ret = avRD(rn.Ready())
	case "ready_node":
		rd = avNodeReady(nd)
		nd.Status()
		ret = avRD(rd)
	case "advance_raw":
		rn.Advance(rd)
		ret = map[string]interface{}{"batchAfter": avRD(rd)}
	case "advance_node":
		nd.Advance()
		nd.Status()
		ret = map[string]interface{}{"batchAfter": avRD(rd)}
	default:
		phase = "dispatch"
		panic("unsupported action " + c.Action)
	}
	if err != nil {
		result["raw_error"] = err.Error()
		if err == ErrProposalDropped {
			status = "dropped"
		} else {
			status = "error"
		}
	}
	result["raw_messages"] = rn.raft.msgs
	return result
}
func TestActionValidation(t *testing.T) {
	in := os.Getenv("AV_INPUT")
	if in == "" {
		t.Skip("adapter requires AV_INPUT")
	}
	b, err := os.ReadFile(in)
	if err != nil {
		t.Fatal(err)
	}
	var cs []avCase
	if err = json.Unmarshal(b, &cs); err != nil {
		t.Fatal(err)
	}
	out, err := os.Create(os.Getenv("AV_OUTPUT"))
	if err != nil {
		t.Fatal(err)
	}
	defer out.Close()
	enc := json.NewEncoder(out)
	for _, c := range cs {
		t.Run(c.ID, func(t *testing.T) {
			if err = enc.Encode(avRun(c)); err != nil {
				t.Fatal(err)
			}
		})
	}
}
