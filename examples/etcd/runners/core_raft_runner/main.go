package main

import (
	"crypto/rand"
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"sync"
	"time"
)

// === 从原始插桩后的 raft 代码中提取的核心类型和常量 ===

const (
	None uint64 = 0
)

// StateType represents the role of a node in a cluster.
type StateType uint64

const (
	StateFollower StateType = iota
	StateCandidate
	StateLeader
	StatePreCandidate
	numStates
)

var stmap = [...]string{
	"StateFollower",
	"StateCandidate",
	"StateLeader",
	"StatePreCandidate",
}

func (st StateType) String() string {
	return stmap[st]
}

// CampaignType represents the type of campaigning
type CampaignType string

const (
	campaignPreElection CampaignType = "CampaignPreElection"
	campaignElection    CampaignType = "CampaignElection"
	campaignTransfer    CampaignType = "CampaignTransfer"
)

// Message types (simplified from raftpb)
type MessageType int32

const (
	MsgHup           MessageType = 0
	MsgBeat          MessageType = 1
	MsgProp          MessageType = 2
	MsgApp           MessageType = 3
	MsgAppResp       MessageType = 4
	MsgVote          MessageType = 5
	MsgVoteResp      MessageType = 6
	MsgHeartbeat     MessageType = 8
	MsgHeartbeatResp MessageType = 9
	MsgCheckQuorum   MessageType = 12
)

func (t MessageType) String() string {
	switch t {
	case MsgHup:
		return "MsgHup"
	case MsgBeat:
		return "MsgBeat"
	case MsgProp:
		return "MsgProp"
	case MsgApp:
		return "MsgApp"
	case MsgAppResp:
		return "MsgAppResp"
	case MsgVote:
		return "MsgVote"
	case MsgVoteResp:
		return "MsgVoteResp"
	case MsgHeartbeat:
		return "MsgHeartbeat"
	case MsgHeartbeatResp:
		return "MsgHeartbeatResp"
	case MsgCheckQuorum:
		return "MsgCheckQuorum"
	default:
		return fmt.Sprintf("Unknown(%d)", int(t))
	}
}

// Message represents a message in raft protocol
type Message struct {
	Type    MessageType
	To      uint64
	From    uint64
	Term    uint64
	LogTerm uint64
	Index   uint64
	Reject  bool
}

// TraceLogger interface
type TraceLogger interface {
	LogTrace(action string, data map[string]interface{})
}

// Entry represents a log entry
type Entry struct {
	Index uint64
	Term  uint64
	Data  []byte
}

// === 从原始插桩后的 raft 代码中提取的 raft 结构体（简化版） ===

// lockedRand - 直接从原始代码复制
type lockedRand struct {
	mu sync.Mutex
}

func (r *lockedRand) Intn(n int) int {
	r.mu.Lock()
	v, _ := rand.Int(rand.Reader, big.NewInt(int64(n)))
	r.mu.Unlock()
	return int(v.Int64())
}

var globalRand = &lockedRand{}

// raft struct - 提取核心字段
type raft struct {
	id uint64

	Term uint64
	Vote uint64

	state StateType

	// the leader id
	lead uint64

	// election and heartbeat timing
	electionElapsed           int
	heartbeatElapsed          int
	electionTimeout           int
	heartbeatTimeout          int
	randomizedElectionTimeout int

	checkQuorum bool
	preVote     bool

	tick func()
	step stepFunc

	traceLogger TraceLogger

	// peers in the cluster
	peers map[uint64]bool
}

type stepFunc func(r *raft, m Message) error

// Config contains the parameters to start a raft
type Config struct {
	ID            uint64
	ElectionTick  int
	HeartbeatTick int
	CheckQuorum   bool
	PreVote       bool
	TraceLogger   TraceLogger
	Peers         []uint64 // Added for simplicity
}

// === Trace 函数实现 ===

// Global trace logger
var globalTraceLogger TraceLogger

// FileTraceLogger implements TraceLogger by writing to a file
type FileTraceLogger struct {
	file *os.File
}

func NewFileTraceLogger(filename string) (*FileTraceLogger, error) {
	file, err := os.OpenFile(filename, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		return nil, err
	}
	return &FileTraceLogger{file: file}, nil
}

func (f *FileTraceLogger) LogTrace(action string, data map[string]interface{}) {
	entry := map[string]interface{}{
		"timestamp": time.Now().UnixNano(),
		"action":    action,
		"data":      data,
	}

	jsonData, err := json.Marshal(entry)
	if err != nil {
		fmt.Printf("Error marshaling trace data: %v\n", err)
		return
	}

	f.file.Write(jsonData)
	f.file.Write([]byte("\n"))
	f.file.Sync()
}

func (f *FileTraceLogger) Close() error {
	return f.file.Close()
}

// === 从插桩后的代码中复制的 trace 函数 ===

func traceAction(action string, params map[string]interface{}) {
	if globalTraceLogger != nil {
		globalTraceLogger.LogTrace(action, params)
	}
}

func traceInitState(r *raft) {
	data := map[string]interface{}{
		"event":   "init_state",
		"node_id": r.id,
		"term":    r.Term,
		"state":   r.state.String(),
	}

	if globalTraceLogger != nil {
		globalTraceLogger.LogTrace("init_state", data)
	}
}

func traceSendMessage(r *raft, m *Message) {
	data := map[string]interface{}{
		"event":    "send_message",
		"node_id":  r.id,
		"msg_type": m.Type.String(),
		"from":     m.From,
		"to":       m.To,
		"term":     m.Term,
		"index":    m.Index,
	}

	if globalTraceLogger != nil {
		globalTraceLogger.LogTrace("send_message", data)
	}
}

func traceReceiveMessage(r *raft, m *Message) {
	data := map[string]interface{}{
		"event":    "receive_message",
		"node_id":  r.id,
		"msg_type": m.Type.String(),
		"from":     m.From,
		"to":       m.To,
		"term":     m.Term,
		"index":    m.Index,
	}

	if globalTraceLogger != nil {
		globalTraceLogger.LogTrace("receive_message", data)
	}
}

func traceBecomeFollower(r *raft) {
	data := map[string]interface{}{
		"event":   "become_follower",
		"node_id": r.id,
		"term":    r.Term,
	}

	if globalTraceLogger != nil {
		globalTraceLogger.LogTrace("become_follower", data)
	}
}

func traceBecomeCandidate(r *raft) {
	data := map[string]interface{}{
		"event":   "become_candidate",
		"node_id": r.id,
		"term":    r.Term,
	}

	if globalTraceLogger != nil {
		globalTraceLogger.LogTrace("become_candidate", data)
	}
}

func traceBecomeLeader(r *raft) {
	data := map[string]interface{}{
		"event":   "become_leader",
		"node_id": r.id,
		"term":    r.Term,
	}

	if globalTraceLogger != nil {
		globalTraceLogger.LogTrace("become_leader", data)
	}
}

func traceCommit(r *raft) {
	data := map[string]interface{}{
		"event":   "commit",
		"node_id": r.id,
		"term":    r.Term,
	}

	if globalTraceLogger != nil {
		globalTraceLogger.LogTrace("commit", data)
	}
}

func traceReplicate(r *raft, entries ...Entry) {
	data := map[string]interface{}{
		"event":       "replicate",
		"node_id":     r.id,
		"term":        r.Term,
		"entry_count": len(entries),
	}

	if len(entries) > 0 {
		data["first_index"] = entries[0].Index
		data["last_index"] = entries[len(entries)-1].Index
	}

	if globalTraceLogger != nil {
		globalTraceLogger.LogTrace("replicate", data)
	}
}

// === 从插桩后的 raft 代码中提取的核心函数 ===

// newRaft - 基于原始实现简化
func newRaft(c *Config) *raft {
	if c.ID == None {
		panic("cannot use none as id")
	}

	if c.HeartbeatTick <= 0 {
		panic("heartbeat tick must be greater than 0")
	}

	if c.ElectionTick <= c.HeartbeatTick {
		panic("election tick must be greater than heartbeat tick")
	}

	r := &raft{
		id:               c.ID,
		lead:             None,
		electionTimeout:  c.ElectionTick,
		heartbeatTimeout: c.HeartbeatTick,
		checkQuorum:      c.CheckQuorum,
		preVote:          c.PreVote,
		traceLogger:      c.TraceLogger,
		peers:            make(map[uint64]bool),
	}

	// Add peers
	for _, peer := range c.Peers {
		r.peers[peer] = true
	}

	traceInitState(r)
	r.becomeFollower(r.Term, None)

	return r
}

// tickElection - 从原始代码复制并插桩
func (r *raft) tickElection() {
	traceAction("tickElection", map[string]interface{}{
		"node_id": r.id,
		"term":    r.Term,
		"state":   r.state.String(),
	})
	r.electionElapsed++

	if r.promotable() && r.pastElectionTimeout() {
		r.electionElapsed = 0
		if err := r.Step(Message{From: r.id, Type: MsgHup}); err != nil {
			fmt.Printf("error occurred during election: %v\n", err)
		}
	}
}

// tickHeartbeat - 从原始代码复制并插桩
func (r *raft) tickHeartbeat() {
	traceAction("tickHeartbeat", map[string]interface{}{
		"node_id": r.id,
		"term":    r.Term,
		"state":   r.state.String(),
	})
	r.heartbeatElapsed++
	r.electionElapsed++

	if r.electionElapsed >= r.electionTimeout {
		r.electionElapsed = 0
		if r.checkQuorum {
			if err := r.Step(Message{From: r.id, Type: MsgCheckQuorum}); err != nil {
				fmt.Printf("error occurred during checking sending heartbeat: %v\n", err)
			}
		}
	}

	if r.state != StateLeader {
		return
	}

	if r.heartbeatElapsed >= r.heartbeatTimeout {
		r.heartbeatElapsed = 0
		if err := r.Step(Message{From: r.id, Type: MsgBeat}); err != nil {
			fmt.Printf("error occurred during checking sending heartbeat: %v\n", err)
		}
	}
}

// 状态转换函数 - 从原始代码复制并添加插桩

func (r *raft) becomeFollower(term uint64, lead uint64) {
	r.step = stepFollower
	r.reset(term)
	r.tick = r.tickElection
	r.lead = lead
	r.state = StateFollower
	fmt.Printf("%x became follower at term %d\n", r.id, r.Term)

	traceBecomeFollower(r)
}

func (r *raft) becomeCandidate() {
	if r.state == StateLeader {
		panic("invalid transition [leader -> candidate]")
	}
	r.step = stepCandidate
	r.reset(r.Term + 1)
	r.tick = r.tickElection
	r.Vote = r.id
	r.state = StateCandidate
	fmt.Printf("%x became candidate at term %d\n", r.id, r.Term)

	traceBecomeCandidate(r)
}

func (r *raft) becomePreCandidate() {
	if r.state == StateLeader {
		panic("invalid transition [leader -> pre-candidate]")
	}
	r.step = stepCandidate
	r.tick = r.tickElection
	r.lead = None
	r.state = StatePreCandidate
	fmt.Printf("%x became pre-candidate at term %d\n", r.id, r.Term)
}

func (r *raft) becomeLeader() {
	if r.state == StateFollower {
		panic("invalid transition [follower -> leader]")
	}
	r.step = stepLeader
	r.reset(r.Term)
	r.tick = r.tickHeartbeat
	r.lead = r.id
	r.state = StateLeader

	traceBecomeLeader(r)
	fmt.Printf("%x became leader at term %d\n", r.id, r.Term)
}

func (r *raft) reset(term uint64) {
	if r.Term != term {
		r.Term = term
		r.Vote = None
	}
	r.lead = None
	r.electionElapsed = 0
	r.heartbeatElapsed = 0
	r.resetRandomizedElectionTimeout()
}

func (r *raft) resetRandomizedElectionTimeout() {
	r.randomizedElectionTimeout = r.electionTimeout + globalRand.Intn(r.electionTimeout)
}

func (r *raft) pastElectionTimeout() bool {
	return r.electionElapsed >= r.randomizedElectionTimeout
}

func (r *raft) promotable() bool {
	return r.peers[r.id] // simplified
}

// Step - 从原始代码简化并插桩
func (r *raft) Step(m Message) error {
	traceAction("Step", map[string]interface{}{
		"node_id": r.id,
		"term":    r.Term,
		"state":   r.state.String(),
	})
	traceReceiveMessage(r, &m)

	// Handle the message term
	switch {
	case m.Term == 0:
		// local message
	case m.Term > r.Term:
		fmt.Printf("%x [term: %d] received a %s message with higher term from %x [term: %d]\n",
			r.id, r.Term, m.Type, m.From, m.Term)
		if m.Type == MsgApp || m.Type == MsgHeartbeat {
			r.becomeFollower(m.Term, m.From)
		} else {
			r.becomeFollower(m.Term, None)
		}
	case m.Term < r.Term:
		fmt.Printf("%x [term: %d] ignored a %s message with lower term from %x [term: %d]\n",
			r.id, r.Term, m.Type, m.From, m.Term)
		return nil
	}

	switch m.Type {
	case MsgHup:
		if r.preVote {
			r.hup(campaignPreElection)
		} else {
			r.hup(campaignElection)
		}
	default:
		err := r.step(r, m)
		if err != nil {
			return err
		}
	}
	return nil
}

func (r *raft) hup(t CampaignType) {
	if r.state == StateLeader {
		fmt.Printf("%x ignoring MsgHup because already leader\n", r.id)
		return
	}

	if !r.promotable() {
		fmt.Printf("%x is unpromotable and can not campaign\n", r.id)
		return
	}

	fmt.Printf("%x is starting a new election at term %d\n", r.id, r.Term)
	r.campaign(t)
}

func (r *raft) campaign(t CampaignType) {
	if !r.promotable() {
		fmt.Printf("%x is unpromotable; campaign() should have been called\n", r.id)
	}
	if t == campaignPreElection {
		r.becomePreCandidate()
	} else {
		r.becomeCandidate()
	}

	// Simplified: become leader after some votes (for demo)
	if r.state == StateCandidate && len(r.peers) <= 3 {
		r.becomeLeader()
	}
}

// Step functions
func stepLeader(r *raft, m Message) error {
	switch m.Type {
	case MsgBeat:
		fmt.Printf("%x broadcasting heartbeat\n", r.id)
		// Send heartbeat to all peers
		for peerID := range r.peers {
			if peerID != r.id {
				heartbeat := Message{
					Type: MsgHeartbeat,
					From: r.id,
					To:   peerID,
					Term: r.Term,
				}
				traceSendMessage(r, &heartbeat)
			}
		}
		return nil
	case MsgCheckQuorum:
		fmt.Printf("%x checking quorum\n", r.id)
		return nil
	case MsgProp:
		fmt.Printf("%x handling proposal\n", r.id)
		traceReplicate(r, Entry{Index: 1, Term: r.Term, Data: []byte("test")})
		return nil
	default:
		return nil
	}
}

func stepCandidate(r *raft, m Message) error {
	switch m.Type {
	case MsgVoteResp:
		// Handle vote response
		if !m.Reject {
			fmt.Printf("%x received vote from %x\n", r.id, m.From)
		}
		return nil
	default:
		return nil
	}
}

func stepFollower(r *raft, m Message) error {
	switch m.Type {
	case MsgProp:
		if r.lead == None {
			fmt.Printf("%x no leader at term %d; dropping proposal\n", r.id, r.Term)
			return fmt.Errorf("no leader")
		}
		fmt.Printf("%x forwarding proposal to leader %x\n", r.id, r.lead)
		return nil
	case MsgApp:
		r.electionElapsed = 0
		r.lead = m.From
		fmt.Printf("%x handling append entries from %x\n", r.id, m.From)
		return nil
	case MsgHeartbeat:
		r.electionElapsed = 0
		r.lead = m.From
		fmt.Printf("%x handling heartbeat from %x\n", r.id, m.From)
		return nil
	case MsgVote:
		fmt.Printf("%x received vote request from %x at term %d\n", r.id, m.From, m.Term)
		// Send vote response
		voteResp := Message{
			Type: MsgVoteResp,
			From: r.id,
			To:   m.From,
			Term: r.Term,
		}
		traceSendMessage(r, &voteResp)
		return nil
	default:
		return nil
	}
}

// Tick function
func (r *raft) Tick() {
	r.tick()
}

// === Main 函数 ===

func main() {
	// Initialize trace logger
	traceFile := "core_raft_trace.ndjson"
	logger, err := NewFileTraceLogger(traceFile)
	if err != nil {
		fmt.Printf("Failed to initialize trace logger: %v\n", err)
		return
	}
	defer logger.Close()

	globalTraceLogger = logger

	fmt.Println("Starting Core Raft Algorithm Simulation...")
	fmt.Printf("Trace output will be written to: %s\n", traceFile)

	// Create a 3-node raft cluster
	nodeConfigs := []*Config{
		{
			ID:            1,
			ElectionTick:  10,
			HeartbeatTick: 1,
			CheckQuorum:   true,
			PreVote:       true,
			TraceLogger:   globalTraceLogger,
			Peers:         []uint64{1, 2, 3},
		},
		{
			ID:            2,
			ElectionTick:  10,
			HeartbeatTick: 1,
			CheckQuorum:   true,
			PreVote:       true,
			TraceLogger:   globalTraceLogger,
			Peers:         []uint64{1, 2, 3},
		},
		{
			ID:            3,
			ElectionTick:  10,
			HeartbeatTick: 1,
			CheckQuorum:   true,
			PreVote:       true,
			TraceLogger:   globalTraceLogger,
			Peers:         []uint64{1, 2, 3},
		},
	}

	nodes := make([]*raft, 3)
	for i, config := range nodeConfigs {
		nodes[i] = newRaft(config)
		fmt.Printf("Created node %d\n", config.ID)
	}

	fmt.Println("\n=== Starting Raft Core Algorithm Simulation ===")

	// Run simulation
	for round := 0; round < 15; round++ {
		fmt.Printf("\n--- Round %d ---\n", round+1)

		// Tick all nodes
		for _, node := range nodes {
			node.Tick()
		}

		// Simulate some inter-node messages
		if round > 5 && round%3 == 0 {
			// Simulate vote requests
			fromNode := nodes[0]
			if fromNode.state == StateCandidate {
				for _, toNode := range nodes[1:] {
					voteMsg := Message{
						Type: MsgVote,
						From: fromNode.id,
						To:   toNode.id,
						Term: fromNode.Term,
					}
					fmt.Printf("Sending vote request from %d to %d\n", fromNode.id, toNode.id)
					toNode.Step(voteMsg)
				}
			}
		}

		// Print current state
		fmt.Printf("Node states: ")
		for _, node := range nodes {
			fmt.Printf("Node%d:%s(T%d) ",
				node.id, node.state.String(), node.Term)
		}
		fmt.Println()

		time.Sleep(300 * time.Millisecond)
	}

	// Final state
	fmt.Println("\n=== Final State ===")
	for _, node := range nodes {
		fmt.Printf("Node %d: State=%s, Term=%d, Leader=%d\n",
			node.id, node.state.String(), node.Term, node.lead)
	}

	fmt.Printf("\nCore Raft simulation completed! Check %s for detailed traces.\n", traceFile)

	// Show trace statistics
	showTraceStatistics(traceFile)
}

func showTraceStatistics(filename string) {
	file, err := os.Open(filename)
	if err != nil {
		fmt.Printf("Could not open trace file: %v\n", err)
		return
	}
	defer file.Close()

	fmt.Println("\n=== Trace Statistics ===")

	actionCounts := make(map[string]int)
	var totalEvents int

	// Read and count trace entries
	decoder := json.NewDecoder(file)
	for decoder.More() {
		var entry map[string]interface{}
		if err := decoder.Decode(&entry); err != nil {
			break
		}

		if action, ok := entry["action"].(string); ok {
			actionCounts[action]++
			totalEvents++
		}
	}

	fmt.Printf("Total trace events: %d\n", totalEvents)
	fmt.Println("Event breakdown:")
	for action, count := range actionCounts {
		fmt.Printf("  %s: %d\n", action, count)
	}
}
