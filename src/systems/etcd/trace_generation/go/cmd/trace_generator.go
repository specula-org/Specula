//go:build with_tla

package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"math/rand"
	"os"
	"path/filepath"
	"sync"
	"time"

	"go.etcd.io/raft/v3"
	"go.etcd.io/raft/v3/raftpb"
)

// TraceConfig captures runtime options for trace generation.
type TraceConfig struct {
	NodeCount   int     `json:"node_count"`
	DurationSec int     `json:"duration_seconds"`
	ClientQPS   float64 `json:"client_qps"`
	FaultRate   float64 `json:"fault_rate"`
	OutputFile  string  `json:"output_file"`
	RandomSeed  int64   `json:"random_seed"`
	FilterType  string  `json:"filter_type"` // "coarse", "fine", "election", "logsync"
}

// FileTraceLogger implements raft.TraceLogger to write events to NDJSON.
type FileTraceLogger struct {
	file  *os.File
	mutex sync.Mutex
}

func NewFileTraceLogger(filepath string) (*FileTraceLogger, error) {
	file, err := os.Create(filepath)
	if err != nil {
		return nil, fmt.Errorf("failed to create trace file: %v", err)
	}
	return &FileTraceLogger{file: file}, nil
}

func (f *FileTraceLogger) TraceEvent(event *raft.TracingEvent) {
	f.mutex.Lock()
	defer f.mutex.Unlock()

	eventJSON := map[string]interface{}{
		"name": event.Name,
		"nid":  event.NodeID,
		"state": map[string]interface{}{
			"term":   event.State.Term,
			"vote":   event.State.Vote,
			"commit": event.State.Commit,
		},
		"role": event.Role,
		"log":  event.LogSize,
		"conf": event.Conf,
	}

	if event.Message != nil {
		eventJSON["msg"] = map[string]interface{}{
			"type":    event.Message.Type,
			"from":    event.Message.From,
			"to":      event.Message.To,
			"term":    event.Message.Term,
			"entries": event.Message.EntryLength,
			"logTerm": event.Message.LogTerm,
			"index":   event.Message.Index,
			"commit":  event.Message.Commit,
			"vote":    event.Message.Vote,
			"reject":  event.Message.Reject,
		}
	}

	if event.ConfChange != nil {
		eventJSON["cc"] = event.ConfChange
	}

	if len(event.Properties) > 0 {
		eventJSON["prop"] = event.Properties
	}

	jsonBytes, err := json.Marshal(eventJSON)
	if err != nil {
		log.Printf("Error marshaling trace event: %v", err)
		return
	}
	f.file.Write(jsonBytes)
	f.file.Write([]byte("\n"))
}

func (f *FileTraceLogger) Close() error {
	f.mutex.Lock()
	defer f.mutex.Unlock()
	if f.file != nil {
		return f.file.Close()
	}
	return nil
}

// SimpleRaftNode represents a single raft node.
type SimpleRaftNode struct {
	id       uint64
	node     raft.Node
	storage  *raft.MemoryStorage
	done     chan struct{}
	propChan chan []byte
	msgChan  chan raftpb.Message

	peers    map[uint64]*SimpleRaftNode
	isolated bool
	mutex    sync.RWMutex
}

func NewSimpleRaftNode(id uint64, peers []raft.Peer, traceLogger raft.TraceLogger) *SimpleRaftNode {
	storage := raft.NewMemoryStorage()
	config := &raft.Config{
		ID:              id,
		ElectionTick:    10,
		HeartbeatTick:   1,
		Storage:         storage,
		MaxSizePerMsg:   4096,
		MaxInflightMsgs: 256,
		CheckQuorum:     true,
		PreVote:         true,
		TraceLogger:     traceLogger,
	}

	node := raft.StartNode(config, peers)

	rn := &SimpleRaftNode{
		id:       id,
		node:     node,
		storage:  storage,
		done:     make(chan struct{}),
		propChan: make(chan []byte, 10),
		msgChan:  make(chan raftpb.Message, 100),
		peers:    make(map[uint64]*SimpleRaftNode),
	}

	go rn.run()
	return rn
}

func (rn *SimpleRaftNode) run() {
	ticker := time.NewTicker(100 * time.Millisecond)
	defer ticker.Stop()

	for {
		select {
		case <-ticker.C:
			rn.node.Tick()
		case prop := <-rn.propChan:
			if err := rn.node.Propose(context.Background(), prop); err != nil {
				log.Printf("Node %d: Propose failed: %v", rn.id, err)
			}
		case msg := <-rn.msgChan:
			if err := rn.node.Step(context.Background(), msg); err != nil {
				log.Printf("Node %d: Step failed: %v", rn.id, err)
			}
		case rd := <-rn.node.Ready():
			if !raft.IsEmptyHardState(rd.HardState) {
				rn.storage.SetHardState(rd.HardState)
			}
			if len(rd.Entries) > 0 {
				rn.storage.Append(rd.Entries)
			}
			if !raft.IsEmptySnap(rd.Snapshot) {
				rn.storage.ApplySnapshot(rd.Snapshot)
			}
			rn.sendMessages(rd.Messages)
			for _, entry := range rd.CommittedEntries {
				if entry.Type == raftpb.EntryConfChange {
					var cc raftpb.ConfChange
					if err := cc.Unmarshal(entry.Data); err != nil {
						log.Printf("Node %d: Failed to unmarshal conf change: %v", rn.id, err)
						continue
					}
					rn.node.ApplyConfChange(cc)
				}
			}
			rn.node.Advance()
		case <-rn.done:
			return
		}
	}
}

func (rn *SimpleRaftNode) sendMessages(msgs []raftpb.Message) {
	rn.mutex.RLock()
	isolated := rn.isolated
	rn.mutex.RUnlock()
	if isolated {
		return
	}
	for _, msg := range msgs {
		if peer, ok := rn.peers[msg.To]; ok {
			select {
			case peer.msgChan <- msg:
			default:
			}
		}
	}
}

func (rn *SimpleRaftNode) Propose(data []byte) {
	select {
	case rn.propChan <- data:
	default:
	}
}

func (rn *SimpleRaftNode) SetIsolated(isolated bool) {
	rn.mutex.Lock()
	defer rn.mutex.Unlock()
	rn.isolated = isolated
}

func (rn *SimpleRaftNode) Stop() {
	close(rn.done)
	rn.node.Stop()
}

// SimpleRaftCluster manages a cluster of simple raft nodes.
type SimpleRaftCluster struct {
	nodes       map[uint64]*SimpleRaftNode
	traceLogger *FileTraceLogger
	rand        *rand.Rand
}

func NewSimpleRaftCluster(nodeCount int, traceLogger *FileTraceLogger, seed int64) *SimpleRaftCluster {
	peers := make([]raft.Peer, nodeCount)
	for i := 0; i < nodeCount; i++ {
		peers[i] = raft.Peer{ID: uint64(i + 1)}
	}

	nodes := make(map[uint64]*SimpleRaftNode)
	for i := 0; i < nodeCount; i++ {
		id := uint64(i + 1)
		node := NewSimpleRaftNode(id, peers, traceLogger)
		nodes[id] = node
	}

	for _, node := range nodes {
		for _, peer := range nodes {
			if peer.id != node.id {
				node.peers[peer.id] = peer
			}
		}
	}

	rng := rand.New(rand.NewSource(seed))
	return &SimpleRaftCluster{
		nodes:       nodes,
		traceLogger: traceLogger,
		rand:        rng,
	}
}

func (sc *SimpleRaftCluster) ProposeRandom() {
	nodeID := uint64(sc.rand.Intn(len(sc.nodes)) + 1)
	if node, ok := sc.nodes[nodeID]; ok {
		data := fmt.Sprintf("proposal_%d_%d", time.Now().UnixNano(), sc.rand.Intn(10000))
		node.Propose([]byte(data))
	}
}

func (sc *SimpleRaftCluster) InjectRandomFault() {
	nodeID := uint64(sc.rand.Intn(len(sc.nodes)) + 1)
	if node, ok := sc.nodes[nodeID]; ok {
		log.Printf("Isolating node %d temporarily", nodeID)
		node.SetIsolated(true)
		go func() {
			time.Sleep(time.Duration(1+sc.rand.Intn(3)) * time.Second)
			node.SetIsolated(false)
			log.Printf("Node %d recovered from isolation", nodeID)
		}()
	}
}

func (sc *SimpleRaftCluster) Stop() {
	for _, node := range sc.nodes {
		node.Stop()
	}
}

// TraceGenerator generates realistic traces using simple raft nodes.
type TraceGenerator struct {
	config      TraceConfig
	cluster     *SimpleRaftCluster
	traceLogger *FileTraceLogger
	rand        *rand.Rand
}

func NewTraceGenerator(config TraceConfig) (*TraceGenerator, error) {
	var traceLogger raft.TraceLogger

	if config.FilterType != "" && config.FilterType != "fine" {
		filter := GetFilter(config.FilterType)
		filteredLogger, err := NewFilteredTraceLogger(config.OutputFile, filter)
		if err != nil {
			return nil, fmt.Errorf("failed to create filtered trace logger: %v", err)
		}
		traceLogger = filteredLogger
		log.Printf("Using %s trace filter", filter.Name())
	} else {
		baseLogger, err := NewFileTraceLogger(config.OutputFile)
		if err != nil {
			return nil, fmt.Errorf("failed to create trace logger: %v", err)
		}
		traceLogger = baseLogger
		log.Printf("Using fine-grained trace logging")
	}

	var seed int64
	if config.RandomSeed > 0 {
		seed = config.RandomSeed
	} else {
		seed = time.Now().UnixNano()
	}
	rng := rand.New(rand.NewSource(seed))

	var fileLogger *FileTraceLogger
	if fl, ok := traceLogger.(*FileTraceLogger); ok {
		fileLogger = fl
	} else if filteredLogger, ok := traceLogger.(*FilteredTraceLogger); ok {
		fileLogger = filteredLogger.baseLogger
	} else {
		return nil, fmt.Errorf("unsupported trace logger type")
	}
	cluster := NewSimpleRaftCluster(config.NodeCount, fileLogger, seed)

	return &TraceGenerator{
		config:      config,
		cluster:     cluster,
		traceLogger: nil,
		rand:        rng,
	}, nil
}

func (tg *TraceGenerator) Generate() error {
	log.Printf("Starting simple trace generation with %d nodes for %d seconds...",
		tg.config.NodeCount, tg.config.DurationSec)

	time.Sleep(3 * time.Second)

	startTime := time.Now()
	endTime := startTime.Add(time.Duration(tg.config.DurationSec) * time.Second)

	clientInterval := time.Duration(float64(time.Second) / tg.config.ClientQPS)
	nextClientOp := time.Now()
	nextFaultOp := time.Now().Add(time.Duration(tg.rand.Float64()*10) * time.Second)

	operationCount := 0
	faultCount := 0

	for time.Now().Before(endTime) {
		now := time.Now()

		if now.After(nextClientOp) {
			tg.cluster.ProposeRandom()
			operationCount++
			jitter := time.Duration(tg.rand.Float64() * float64(clientInterval))
			nextClientOp = now.Add(clientInterval + jitter)
		}

		if tg.config.FaultRate > 0 && now.After(nextFaultOp) {
			if tg.rand.Float64() < tg.config.FaultRate {
				tg.cluster.InjectRandomFault()
				faultCount++
			}
			nextFaultOp = now.Add(time.Duration(5+tg.rand.Intn(10)) * time.Second)
		}

		time.Sleep(50 * time.Millisecond)
	}

	log.Printf("Simple trace generation completed: %d operations, %d faults injected",
		operationCount, faultCount)
	return nil
}

func (tg *TraceGenerator) Close() error {
	if tg.cluster != nil {
		tg.cluster.Stop()
	}
	return nil
}

func main() {
	var (
		configFile = flag.String("config", "", "Configuration file (JSON)")
		nodeCount  = flag.Int("nodes", 3, "Number of nodes in cluster")
		duration   = flag.Int("duration", 60, "Duration in seconds")
		clientQPS  = flag.Float64("qps", 10.0, "Client operations per second")
		faultRate  = flag.Float64("fault-rate", 0.1, "Fault injection rate")
		outputFile = flag.String("output", "", "Output trace file (required)")
		seed       = flag.Int64("seed", 0, "Random seed (0 for current time)")
		filterType = flag.String("filter", "coarse", "Trace filter type (coarse, fine, election, logsync)")
	)
	flag.Parse()

	if *outputFile == "" {
		log.Fatal("Output file is required (-output)")
	}

	if err := os.MkdirAll(filepath.Dir(*outputFile), 0755); err != nil {
		log.Fatalf("Failed to create output directory: %v", err)
	}

	var config TraceConfig

	if *configFile != "" {
		data, err := os.ReadFile(*configFile)
		if err != nil {
			log.Fatalf("Failed to read config file: %v", err)
		}
		if err := json.Unmarshal(data, &config); err != nil {
			log.Fatalf("Failed to parse config file: %v", err)
		}
	} else {
		config = TraceConfig{
			NodeCount:   *nodeCount,
			DurationSec: *duration,
			ClientQPS:   *clientQPS,
			FaultRate:   *faultRate,
			OutputFile:  *outputFile,
			RandomSeed:  *seed,
			FilterType:  *filterType,
		}
	}

	if *outputFile != "" {
		config.OutputFile = *outputFile
	}

	log.Printf("Starting simple trace generation with config: %+v", config)

	generator, err := NewTraceGenerator(config)
	if err != nil {
		log.Fatalf("Failed to create trace generator: %v", err)
	}
	defer generator.Close()

	if err := generator.Generate(); err != nil {
		log.Fatalf("Simple trace generation failed: %v", err)
	}

	log.Printf("Simple trace generation completed successfully. Output: %s", config.OutputFile)
}
