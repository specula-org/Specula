package main

import (
	"encoding/json"
	"fmt"
	"math/rand"
	"os"
	"time"
)

// Message types matching etcd's raft implementation
const (
	MsgHup           = "MsgHup"
	MsgBeat          = "MsgBeat"
	MsgProp          = "MsgProp"
	MsgApp           = "MsgApp"
	MsgAppResp       = "MsgAppResp"
	MsgVote          = "MsgVote"
	MsgVoteResp      = "MsgVoteResp"
	MsgPreVote       = "MsgPreVote"
	MsgPreVoteResp   = "MsgPreVoteResp"
	MsgHeartbeat     = "MsgHeartbeat"
	MsgHeartbeatResp = "MsgHeartbeatResp"
)

// Node states matching etcd's StateType
const (
	StateFollower     = "Follower"
	StateCandidate    = "Candidate"
	StateLeader       = "Leader"
	StatePreCandidate = "PreCandidate"
)

// Entry represents a log entry
type Entry struct {
	Term  uint64 `json:"term"`
	Index uint64 `json:"index"`
	Type  string `json:"type"`
	Data  string `json:"data"`
}

// Message represents a raft message
type Message struct {
	Type       string  `json:"type"`
	To         uint64  `json:"to"`
	From       uint64  `json:"from"`
	Term       uint64  `json:"term,omitempty"`
	LogTerm    uint64  `json:"log_term,omitempty"`
	Index      uint64  `json:"index,omitempty"`
	Entries    []Entry `json:"entries,omitempty"`
	Commit     uint64  `json:"commit,omitempty"`
	Reject     bool    `json:"reject,omitempty"`
	RejectHint uint64  `json:"reject_hint,omitempty"`
	Context    string  `json:"context,omitempty"`
}

// RaftNode represents a single raft node following etcd's design
type RaftNode struct {
	ID    uint64 `json:"id"`
	Term  uint64 `json:"term"`
	Vote  uint64 `json:"vote"`
	State string `json:"state"`
	Lead  uint64 `json:"lead"`

	// Log state
	Log         []Entry `json:"log"`
	CommitIndex uint64  `json:"commit_index"`

	// Election state
	VotesGranted    map[uint64]bool `json:"votes_granted"`
	VotesRejected   map[uint64]bool `json:"votes_rejected"`
	ElectionElapsed int             `json:"election_elapsed"`

	// Leader state
	NextIndex        map[uint64]uint64 `json:"next_index,omitempty"`
	MatchIndex       map[uint64]uint64 `json:"match_index,omitempty"`
	HeartbeatElapsed int               `json:"heartbeat_elapsed"`

	// Timing
	ElectionTimeout           int `json:"election_timeout"`
	HeartbeatTimeout          int `json:"heartbeat_timeout"`
	RandomizedElectionTimeout int `json:"randomized_election_timeout"`
	CanBecomeCandidate        bool
}

// RaftCluster manages the entire 3-node cluster
type RaftCluster struct {
	Nodes        map[uint64]*RaftNode `json:"nodes"`
	Messages     []Message            `json:"messages"`
	Step         int                  `json:"step"`
	PreviousStep int                  `json:"previous_step"`
}

func NewRaftCluster() *RaftCluster {
	nodes := make(map[uint64]*RaftNode)
	for i := uint64(1); i <= 3; i++ {
		node := &RaftNode{
			ID:                 i,
			Term:               0,
			Vote:               0,
			State:              StateFollower,
			Lead:               0,
			Log:                []Entry{},
			CommitIndex:        0,
			VotesGranted:       make(map[uint64]bool),
			VotesRejected:      make(map[uint64]bool),
			ElectionElapsed:    0,
			NextIndex:          make(map[uint64]uint64),
			MatchIndex:         make(map[uint64]uint64),
			HeartbeatElapsed:   0,
			ElectionTimeout:    10,
			HeartbeatTimeout:   1,
			CanBecomeCandidate: (i == 1), // Only node 1 can become a candidate
		}
		// Initialize tracking data for other nodes
		for j := uint64(1); j <= 3; j++ {
			if j != i {
				node.NextIndex[j] = 1
				node.MatchIndex[j] = 0
			}
		}
		nodes[i] = node
	}
	return &RaftCluster{
		Nodes:        nodes,
		Messages:     []Message{},
		Step:         0,
		PreviousStep: -1,
	}
}

// TraceState outputs the state before an action occurs - capturing the pre-event state
func (c *RaftCluster) TraceState(action string, nodeID uint64, details map[string]interface{}) {
	// Map action to one of the four standard actions
	standardAction := action

	// All message handling operations should be mapped to "Step"
	if action == "receiveMessage" ||
		action == "sendVote" || action == "voteResponse" || action == "countVotes" ||
		action == "heartbeatResponse" || action == "receiveHeartbeatResp" ||
		action == "appendEntriesResponse" || action == "receiveAppendResp" ||
		action == "becomeFollower" || action == "becomeCandidate" || action == "becomeLeader" ||
		action == "ignoreOldTerm" || action == "commitAdvanced" {
		standardAction = "Step"
	}

	// Map proposal actions to "SendClientRequest"
	if action == "proposeEntry" || action == "proposeNoLeader" {
		standardAction = "SendClientRequest"
	}

	// Skip if not one of the four standard actions
	if standardAction != "tickElection" &&
		standardAction != "tickHeartbeat" &&
		standardAction != "Step" &&
		standardAction != "SendClientRequest" {
		return
	}

	node := c.Nodes[nodeID]

	// Create a snapshot of the current state BEFORE any changes are made
	// This represents the system state when the event is about to happen
	traceData := map[string]interface{}{
		"action":    standardAction, // Use the mapped standard action
		"step":      c.Step,
		"timestamp": time.Now().UnixNano(),
		"node_id":   nodeID,
		"term":      node.Term,
		"state":     node.State,
		"lead":      node.Lead,
		"vote":      node.Vote,
		"commit":    node.CommitIndex,
		"log_len":   len(node.Log),
		"details":   details,
	}

	// Add state for all nodes for context - snapshot of the state before action
	// This shows what the entire cluster looked like when this event was triggered
	allNodes := make(map[string]interface{})
	for id, n := range c.Nodes {
		allNodes[fmt.Sprintf("node_%d", id)] = map[string]interface{}{
			"term":  n.Term,
			"state": n.State,
			"lead":  n.Lead,
		}
	}
	traceData["cluster_state"] = allNodes

	// Record the trace data - this is the pre-event state
	if traceFile := os.Getenv("RAFT_TRACE_OUTPUT"); traceFile != "" {
		if file, err := os.OpenFile(traceFile, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644); err == nil {
			defer file.Close()
			jsonData, _ := json.Marshal(traceData)
			fmt.Fprintf(file, "%s\n", jsonData)
		}
	}
}

// Tick advances time for all nodes
func (c *RaftCluster) Tick() {
	c.PreviousStep = c.Step
	c.Step++

	for nodeID, node := range c.Nodes {
		if node.State == StateLeader {
			c.tickHeartbeat(nodeID)
		} else {
			c.tickElection(nodeID)
		}
	}

	// Process pending messages
	c.processMessages()
}

func (c *RaftCluster) tickElection(nodeID uint64) {
	node := c.Nodes[nodeID]

	// Only record trace when election timer is getting close to timeout or when significant events happen
	shouldTrace := false

	// Always trace if we're about to timeout and can become candidate (only for Followers)
	if node.CanBecomeCandidate && node.State == StateFollower && node.ElectionElapsed >= node.ElectionTimeout-1 {
		shouldTrace = true
	}

	// Trace occasionally during the election process (every 3 ticks) to avoid too much noise
	if node.ElectionElapsed%3 == 0 && node.ElectionElapsed > 0 {
		shouldTrace = true
	}

	// Always trace the first few ticks to show initial state
	if node.ElectionElapsed < 2 {
		shouldTrace = true
	}

	if shouldTrace {
		c.TraceState("tickElection", nodeID, map[string]interface{}{
			"election_elapsed": node.ElectionElapsed,
			"election_timeout": node.ElectionTimeout,
			"can_timeout":      node.CanBecomeCandidate && node.State == StateFollower && node.ElectionElapsed >= node.ElectionTimeout-1,
			"current_state":    node.State,
		})
	}

	// All nodes increment their election timer
	node.ElectionElapsed++

	// Only Follower nodes that can become candidates can timeout and start an election
	// Candidates should not start new elections - they're already in one
	if node.CanBecomeCandidate && node.State == StateFollower && node.ElectionElapsed >= node.ElectionTimeout {
		node.ElectionElapsed = 0
		c.startElection(nodeID)
	}
}

// tickHeartbeat handles heartbeat timeout for leaders
func (c *RaftCluster) tickHeartbeat(nodeID uint64) {
	node := c.Nodes[nodeID]

	// Record state BEFORE making any changes
	c.TraceState("tickHeartbeat", nodeID, map[string]interface{}{
		"heartbeat_elapsed":   node.HeartbeatElapsed,
		"heartbeat_timeout":   node.HeartbeatTimeout,
		"will_send_heartbeat": node.HeartbeatElapsed >= node.HeartbeatTimeout-1,
	})

	node.HeartbeatElapsed++
	node.ElectionElapsed++

	if node.HeartbeatElapsed >= node.HeartbeatTimeout {
		node.HeartbeatElapsed = 0
		c.sendHeartbeat(nodeID)
	}
}

// startElection begins an election process
func (c *RaftCluster) startElection(nodeID uint64) {
	node := c.Nodes[nodeID]

	// Record state BEFORE becoming candidate
	c.TraceState("becomeCandidate", nodeID, map[string]interface{}{
		"current_term":  node.Term,
		"current_state": node.State,
	})

	// Become candidate and increment term
	node.State = StateCandidate
	node.Term++
	node.Vote = nodeID
	node.Lead = 0
	node.VotesGranted = map[uint64]bool{nodeID: true} // Vote for self
	node.VotesRejected = make(map[uint64]bool)
	node.RandomizedElectionTimeout = node.ElectionTimeout + rand.Intn(node.ElectionTimeout)

	// Send vote requests to other nodes
	lastLogIndex := uint64(len(node.Log))
	lastLogTerm := uint64(0)
	if lastLogIndex > 0 {
		lastLogTerm = node.Log[lastLogIndex-1].Term
	}

	for otherID := range c.Nodes {
		if otherID != nodeID {
			// Record state BEFORE sending vote request
			c.TraceState("sendVote", nodeID, map[string]interface{}{
				"to":            otherID,
				"term":          node.Term,
				"last_log_idx":  lastLogIndex,
				"last_log_term": lastLogTerm,
			})

			msg := Message{
				Type:    MsgVote,
				To:      otherID,
				From:    nodeID,
				Term:    node.Term,
				Index:   lastLogIndex,
				LogTerm: lastLogTerm,
			}
			c.Messages = append(c.Messages, msg)
		}
	}
}

// sendHeartbeat sends heartbeat to all followers
func (c *RaftCluster) sendHeartbeat(nodeID uint64) {
	node := c.Nodes[nodeID]

	for otherID := range c.Nodes {
		if otherID != nodeID {
			// Record state BEFORE sending heartbeat
			c.TraceState("sendHeartbeat", nodeID, map[string]interface{}{
				"to":     otherID,
				"term":   node.Term,
				"commit": node.CommitIndex,
			})

			msg := Message{
				Type:   MsgHeartbeat,
				To:     otherID,
				From:   nodeID,
				Term:   node.Term,
				Commit: node.CommitIndex,
			}
			c.Messages = append(c.Messages, msg)
		}
	}
}

// processMessages handles all pending messages
func (c *RaftCluster) processMessages() {
	messages := c.Messages
	c.Messages = []Message{}

	for _, msg := range messages {
		c.handleMessage(msg)
	}
}

// handleMessage processes a single message
func (c *RaftCluster) handleMessage(msg Message) {
	toNode := c.Nodes[msg.To]

	// Record state BEFORE processing the message
	c.TraceState("receiveMessage", msg.To, map[string]interface{}{
		"msg_type": msg.Type,
		"from":     msg.From,
		"msg_term": msg.Term,
	})

	// Handle term comparison first
	if msg.Term > toNode.Term {
		if msg.Type == MsgVote || msg.Type == MsgPreVote {
			// Check if we should grant the vote
			c.handleVoteRequest(msg)
		} else {
			// Step down to follower
			c.becomeFollower(msg.To, msg.Term, msg.From)
		}
		return
	} else if msg.Term < toNode.Term {
		// Record state BEFORE ignoring old term message
		c.TraceState("ignoreOldTerm", msg.To, map[string]interface{}{
			"msg_type":  msg.Type,
			"msg_term":  msg.Term,
			"node_term": toNode.Term,
		})
		return
	}

	// Handle messages by type
	switch msg.Type {
	case MsgVote:
		c.handleVoteRequest(msg)
	case MsgVoteResp:
		c.handleVoteResponse(msg)
	case MsgHeartbeat:
		c.handleHeartbeat(msg)
	case MsgHeartbeatResp:
		c.handleHeartbeatResponse(msg)
	case MsgApp:
		c.handleAppendEntries(msg)
	case MsgAppResp:
		c.handleAppendEntriesResponse(msg)
	}
}

// becomeFollower transitions node to follower state
func (c *RaftCluster) becomeFollower(nodeID uint64, term uint64, lead uint64) {
	node := c.Nodes[nodeID]

	// Record state BEFORE becoming follower
	c.TraceState("becomeFollower", nodeID, map[string]interface{}{
		"current_term":  node.Term,
		"current_state": node.State,
		"current_lead":  node.Lead,
		"new_term":      term,
		"new_leader":    lead,
	})

	node.State = StateFollower
	node.Term = term
	node.Vote = 0
	node.Lead = lead
	node.ElectionElapsed = 0
	node.HeartbeatElapsed = 0
	node.RandomizedElectionTimeout = node.ElectionTimeout + rand.Intn(node.ElectionTimeout)
}

// becomeLeader transitions node to leader state
func (c *RaftCluster) becomeLeader(nodeID uint64) {
	node := c.Nodes[nodeID]

	// Record state BEFORE becoming leader
	c.TraceState("becomeLeader", nodeID, map[string]interface{}{
		"current_state": node.State,
		"term":          node.Term,
		"votes_granted": len(node.VotesGranted),
	})

	node.State = StateLeader
	node.Lead = nodeID
	node.HeartbeatElapsed = 0

	// Initialize progress tracking
	for otherID := range c.Nodes {
		if otherID != nodeID {
			node.NextIndex[otherID] = uint64(len(node.Log)) + 1
			node.MatchIndex[otherID] = 0
		}
	}

	// Send immediate heartbeat to establish leadership
	c.sendHeartbeat(nodeID)
}

// handleVoteRequest processes vote requests
func (c *RaftCluster) handleVoteRequest(msg Message) {
	node := c.Nodes[msg.To]

	// Update term if higher
	if msg.Term > node.Term {
		node.Term = msg.Term
		node.Vote = 0
		node.State = StateFollower
		node.Lead = 0
	}

	// Check if we can vote for this candidate
	canVote := (node.Vote == 0 || node.Vote == msg.From) &&
		c.isLogUpToDate(msg.To, msg.Index, msg.LogTerm)

	granted := canVote

	// Record state BEFORE responding to vote
	c.TraceState("voteResponse", msg.To, map[string]interface{}{
		"for":          msg.From,
		"granted":      granted,
		"term":         node.Term,
		"can_vote":     canVote,
		"current_vote": node.Vote,
	})

	if granted {
		node.Vote = msg.From
		node.ElectionElapsed = 0
	}

	// Send vote response
	response := Message{
		Type:   MsgVoteResp,
		To:     msg.From,
		From:   msg.To,
		Term:   node.Term,
		Reject: !granted,
	}
	c.Messages = append(c.Messages, response)
}

// handleVoteResponse processes vote responses
func (c *RaftCluster) handleVoteResponse(msg Message) {
	node := c.Nodes[msg.To]

	if node.State != StateCandidate {
		return
	}

	// Record state BEFORE counting votes
	c.TraceState("countVotes", msg.To, map[string]interface{}{
		"from":             msg.From,
		"granted":          !msg.Reject,
		"current_granted":  len(node.VotesGranted),
		"current_rejected": len(node.VotesRejected),
		"total":            len(c.Nodes),
		"majority":         len(c.Nodes)/2 + 1,
	})

	if !msg.Reject {
		node.VotesGranted[msg.From] = true
	} else {
		node.VotesRejected[msg.From] = true
	}

	granted := len(node.VotesGranted)
	rejected := len(node.VotesRejected)
	total := len(c.Nodes)

	// Check if won election
	if granted > total/2 {
		c.becomeLeader(msg.To)
	} else if rejected > total/2 {
		c.becomeFollower(msg.To, node.Term, 0)
	}
}

// handleHeartbeat processes heartbeat messages
func (c *RaftCluster) handleHeartbeat(msg Message) {
	node := c.Nodes[msg.To]

	// Record state BEFORE processing heartbeat
	c.TraceState("heartbeatResponse", msg.To, map[string]interface{}{
		"from":           msg.From,
		"msg_commit":     msg.Commit,
		"current_commit": node.CommitIndex,
		"current_lead":   node.Lead,
	})

	node.ElectionElapsed = 0
	node.Lead = msg.From

	if msg.Commit > node.CommitIndex {
		node.CommitIndex = msg.Commit
	}

	// Send heartbeat response
	response := Message{
		Type: MsgHeartbeatResp,
		To:   msg.From,
		From: msg.To,
		Term: node.Term,
	}
	c.Messages = append(c.Messages, response)
}

// handleHeartbeatResponse processes heartbeat responses
func (c *RaftCluster) handleHeartbeatResponse(msg Message) {
	// Record state BEFORE processing heartbeat response
	c.TraceState("receiveHeartbeatResp", msg.To, map[string]interface{}{
		"from": msg.From,
	})
}

// handleAppendEntries processes append entries messages
func (c *RaftCluster) handleAppendEntries(msg Message) {
	node := c.Nodes[msg.To]

	// Record state BEFORE processing append entries
	c.TraceState("appendEntriesResponse", msg.To, map[string]interface{}{
		"from":            msg.From,
		"msg_index":       msg.Index,
		"msg_commit":      msg.Commit,
		"entries_count":   len(msg.Entries),
		"current_log_len": len(node.Log),
		"current_commit":  node.CommitIndex,
	})

	node.ElectionElapsed = 0
	node.Lead = msg.From

	// Simple append entries handling - just accept for now
	success := true

	// Append entries to log
	if len(msg.Entries) > 0 {
		for _, entry := range msg.Entries {
			node.Log = append(node.Log, entry)
		}
	}

	// Update commit index
	if msg.Commit > node.CommitIndex {
		node.CommitIndex = msg.Commit
	}

	response := Message{
		Type:   MsgAppResp,
		To:     msg.From,
		From:   msg.To,
		Term:   node.Term,
		Index:  msg.Index + uint64(len(msg.Entries)),
		Reject: !success,
	}
	c.Messages = append(c.Messages, response)
}

// handleAppendEntriesResponse processes append entries responses
func (c *RaftCluster) handleAppendEntriesResponse(msg Message) {
	node := c.Nodes[msg.To]

	if node.State != StateLeader {
		return
	}

	// Record state BEFORE processing append entries response
	c.TraceState("receiveAppendResp", msg.To, map[string]interface{}{
		"from":              msg.From,
		"reject":            msg.Reject,
		"index":             msg.Index,
		"current_match_idx": node.MatchIndex[msg.From],
		"current_next_idx":  node.NextIndex[msg.From],
	})

	if !msg.Reject {
		// Update match and next index for follower
		node.MatchIndex[msg.From] = msg.Index
		node.NextIndex[msg.From] = msg.Index + 1

		// Try to advance commit index
		c.maybeCommit(msg.To)
	}
}

// maybeCommit attempts to advance commit index
func (c *RaftCluster) maybeCommit(leaderID uint64) {
	leader := c.Nodes[leaderID]

	if len(leader.Log) == 0 {
		return
	}

	// Find the highest index that is replicated on majority
	for i := len(leader.Log) - 1; i >= 0; i-- {
		index := uint64(i + 1)
		if index <= leader.CommitIndex {
			break
		}

		// Count how many nodes have this entry
		count := 1 // Leader has it
		for otherID := range c.Nodes {
			if otherID != leaderID && leader.MatchIndex[otherID] >= index {
				count++
			}
		}

		// If majority has it and it's from current term, commit it
		if count > len(c.Nodes)/2 && leader.Log[i].Term == leader.Term {
			// Record state BEFORE advancing commit
			c.TraceState("commitAdvanced", leaderID, map[string]interface{}{
				"old_commit":       leader.CommitIndex,
				"new_commit":       index,
				"replicated_count": count,
				"majority_needed":  len(c.Nodes)/2 + 1,
			})

			leader.CommitIndex = index
			break
		}
	}
}

// isLogUpToDate checks if candidate's log is up-to-date
func (c *RaftCluster) isLogUpToDate(nodeID uint64, lastIndex uint64, lastTerm uint64) bool {
	node := c.Nodes[nodeID]

	if len(node.Log) == 0 {
		return true
	}

	ourLastIndex := uint64(len(node.Log))
	ourLastTerm := node.Log[ourLastIndex-1].Term

	// Candidate's log is up-to-date if:
	// 1. Last term is higher, or
	// 2. Last term is same and last index is >= ours
	return lastTerm > ourLastTerm || (lastTerm == ourLastTerm && lastIndex >= ourLastIndex)
}

// proposeEntry simulates a client proposal
func (c *RaftCluster) proposeEntry(data string) {
	// Find leader
	var leaderID uint64 = 0
	for id, node := range c.Nodes {
		if node.State == StateLeader {
			leaderID = id
			break
		}
	}

	if leaderID == 0 {
		// Record state BEFORE handling proposal with no leader
		c.TraceState("proposeNoLeader", 0, map[string]interface{}{
			"data": data,
		})
		return
	}

	leader := c.Nodes[leaderID]

	// Record state BEFORE proposing entry
	c.TraceState("proposeEntry", leaderID, map[string]interface{}{
		"data":            data,
		"current_log_len": len(leader.Log),
		"term":            leader.Term,
	})

	entry := Entry{
		Term:  leader.Term,
		Index: uint64(len(leader.Log)) + 1,
		Type:  "Normal",
		Data:  data,
	}
	leader.Log = append(leader.Log, entry)

	// Send to followers
	for otherID := range c.Nodes {
		if otherID != leaderID {
			prevIndex := entry.Index - 1
			prevTerm := uint64(0)
			if prevIndex > 0 && len(leader.Log) > int(prevIndex-1) {
				prevTerm = leader.Log[prevIndex-1].Term
			}

			msg := Message{
				Type:    MsgApp,
				To:      otherID,
				From:    leaderID,
				Term:    leader.Term,
				Index:   prevIndex,
				LogTerm: prevTerm,
				Entries: []Entry{entry},
				Commit:  leader.CommitIndex,
			}
			c.Messages = append(c.Messages, msg)
		}
	}
}

// main function runs the simulation
func main() {
	// Set trace output file
	os.Setenv("RAFT_TRACE_OUTPUT", "trace.ndjson")

	fmt.Println("Starting etcd-style 3-node Raft cluster simulation...")

	cluster := NewRaftCluster()

	// Run simulation
	for step := 0; step < 10; step++ {
		fmt.Printf("=== Simulation Step %d ===\n", step+1)

		// Tick all nodes
		cluster.Tick()

		// Occasionally propose entries if we have a leader
		if step > 15 && step%5 == 0 {
			cluster.proposeEntry(fmt.Sprintf("data_%d", step))
		}

		// Print current state
		var leaders []uint64
		for id, node := range cluster.Nodes {
			if node.State == StateLeader {
				leaders = append(leaders, id)
			}
		}

		fmt.Printf("Step %d: Leaders=%v, Messages=%d\n",
			step+1, leaders, len(cluster.Messages))

		time.Sleep(100 * time.Millisecond)
	}

	// Final state
	fmt.Println("\n=== Final Cluster State ===")
	for id, node := range cluster.Nodes {
		fmt.Printf("Node %d: Term=%d, State=%s, Lead=%d, LogLen=%d, Commit=%d\n",
			id, node.Term, node.State, node.Lead, len(node.Log), node.CommitIndex)
	}

	fmt.Println("\nSimulation completed! Check raft_trace.ndjson for detailed traces.")
}
