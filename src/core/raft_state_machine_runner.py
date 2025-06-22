#!/usr/bin/env python3
"""
Lightweight Raft State Machine Random Runner
"""

import os
import json
import random
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
import logging

logger = logging.getLogger(__name__)

class RaftStateMachineRunner:
    """Lightweight Raft state machine random runner"""
    
    def __init__(self, instrumented_raft_path: str, trace_output_dir: str):
        self.instrumented_raft_path = Path(instrumented_raft_path)
        self.trace_output_dir = Path(trace_output_dir)
        self.trace_output_dir.mkdir(parents=True, exist_ok=True)
        
        # Check if instrumented raft code exists
        if not self.instrumented_raft_path.exists():
            raise FileNotFoundError(f"Instrumented raft code not found: {instrumented_raft_path}")
    
    def create_minimal_test_program(self) -> str:
        """Create minimal Go test program"""
        test_program = '''package main

import (
    "context"
    "encoding/json"
    "fmt"
    "math/rand"
    "os"
    "time"
    
    "go.etcd.io/raft/v3"
    "go.etcd.io/raft/v3/raftpb"
)

type TestNetwork struct {
    nodes map[uint64]*raft.RawNode
    messages []raftpb.Message
    rand *rand.Rand
}

func NewTestNetwork(seed int64) *TestNetwork {
    return &TestNetwork{
        nodes: make(map[uint64]*raft.RawNode),
        messages: make([]raftpb.Message, 0),
        rand: rand.New(rand.NewSource(seed)),
    }
}

func (tn *TestNetwork) CreateNode(id uint64) {
    storage := raft.NewMemoryStorage()
    cfg := &raft.Config{
        ID:              id,
        ElectionTick:    10,
        HeartbeatTick:   1,
        Storage:         storage,
        MaxSizePerMsg:   4096,
        MaxInflightMsgs: 256,
        Logger:          raft.DiscardLogger,
    }
    
    peers := []raft.Peer{{ID: 1}, {ID: 2}, {ID: 3}}
    rn, err := raft.NewRawNode(cfg, peers)
    if err != nil {
        panic(err)
    }
    
    tn.nodes[id] = rn
}

func (tn *TestNetwork) Step(nodeID uint64, msg raftpb.Message) {
    if node, ok := tn.nodes[nodeID]; ok {
        node.Step(msg)
    }
}

func (tn *TestNetwork) Tick(nodeID uint64) {
    if node, ok := tn.nodes[nodeID]; ok {
        node.Tick()
    }
}

func (tn *TestNetwork) ProcessReady(nodeID uint64) {
    node, ok := tn.nodes[nodeID]
    if !ok {
        return
    }
    
    if !node.HasReady() {
        return
    }
    
    rd := node.Ready()
    
    // Process Messages
    for _, msg := range rd.Messages {
        tn.messages = append(tn.messages, msg)
    }
    
    // Record state changes
    if !raft.IsEmptyHardState(rd.HardState) {
        fmt.Printf("Node %d: HardState changed - Term: %d, Vote: %d, Commit: %d\\n",
            nodeID, rd.HardState.Term, rd.HardState.Vote, rd.HardState.Commit)
    }
    
    if len(rd.Entries) > 0 {
        fmt.Printf("Node %d: %d new entries\\n", nodeID, len(rd.Entries))
    }
    
    if len(rd.CommittedEntries) > 0 {
        fmt.Printf("Node %d: %d committed entries\\n", nodeID, len(rd.CommittedEntries))
    }
    
    node.Advance(rd)
}

func (tn *TestNetwork) DeliverRandomMessage() bool {
    if len(tn.messages) == 0 {
        return false
    }
    
    // Randomly select a message to deliver
    idx := tn.rand.Intn(len(tn.messages))
    msg := tn.messages[idx]
    tn.messages = append(tn.messages[:idx], tn.messages[idx+1:]...)
    
    fmt.Printf("Delivering message: %s from %d to %d\\n", msg.Type, msg.From, msg.To)
    tn.Step(msg.To, msg)
    
    return true
}

func (tn *TestNetwork) RandomTick() {
    nodeIDs := []uint64{1, 2, 3}
    nodeID := nodeIDs[tn.rand.Intn(len(nodeIDs))]
    fmt.Printf("Tick node %d\\n", nodeID)
    tn.Tick(nodeID)
}

func main() {
    if len(os.Args) < 2 {
        fmt.Println("Usage: go run test_raft.go <seed>")
        os.Exit(1)
    }
    
    var seed int64 = time.Now().UnixNano()
    if len(os.Args) >= 2 {
        fmt.Sscanf(os.Args[1], "%d", &seed)
    }
    
    fmt.Printf("Running with seed: %d\\n", seed)
    
    network := NewTestNetwork(seed)
    
    // Create 3 nodes
    for i := uint64(1); i <= 3; i++ {
        network.CreateNode(i)
        fmt.Printf("Created node %d\\n", i)
    }
    
    // Randomly execute operations
    for step := 0; step < 100; step++ {
        fmt.Printf("\\n=== Step %d ===\\n", step)
        
        // Randomly select operation type
        switch network.rand.Intn(3) {
        case 0:
            // Random tick
            network.RandomTick()
        case 1:
            // Process Ready state
            nodeID := uint64(network.rand.Intn(3) + 1)
            fmt.Printf("Processing ready for node %d\\n", nodeID)
            network.ProcessReady(nodeID)
        case 2:
            // Deliver message
            if !network.DeliverRandomMessage() {
                fmt.Println("No messages to deliver")
            }
        }
        
        // Process Ready state for all nodes
        for i := uint64(1); i <= 3; i++ {
            network.ProcessReady(i)
        }
        
        time.Sleep(10 * time.Millisecond)
    }
}
'''
        return test_program
    
    def run_random_test(self, num_runs: int = 10, steps_per_run: int = 100) -> List[Dict[str, Any]]:
        """Run random tests"""
        results = []
        
        for run_id in range(num_runs):
            logger.info(f"Running test {run_id + 1}/{num_runs}")
            
            # Generate different random seed for each run
            seed = random.randint(1, 1000000)
            
            # Create temporary test program
            with tempfile.NamedTemporaryFile(mode='w', suffix='.go', delete=False) as f:
                f.write(self.create_minimal_test_program())
                test_file = f.name
            
            try:
                # Run test
                result = self._run_single_test(test_file, seed, steps_per_run, run_id)
                results.append(result)
                
            finally:
                os.unlink(test_file)
        
        return results
    
    def _run_single_test(self, test_file: str, seed: int, steps: int, run_id: int) -> Dict[str, Any]:
        """Run single test"""
        start_time = time.time()
        
        # Set environment variables to enable trace output
        env = os.environ.copy()
        env['RAFT_TRACE_OUTPUT'] = str(self.trace_output_dir / f"trace_run_{run_id}.ndjson")
        
        try:
            # Run test in instrumented code directory
            result = subprocess.run(
                ['go', 'run', test_file, str(seed)],
                cwd=self.instrumented_raft_path.parent,
                capture_output=True,
                text=True,
                timeout=30,
                env=env
            )
            
            execution_time = time.time() - start_time
            
            return {
                'run_id': run_id,
                'seed': seed,
                'steps': steps,
                'execution_time': execution_time,
                'success': result.returncode == 0,
                'stdout': result.stdout,
                'stderr': result.stderr,
                'trace_file': env.get('RAFT_TRACE_OUTPUT')
            }
            
        except subprocess.TimeoutExpired:
            return {
                'run_id': run_id,
                'seed': seed,
                'steps': steps,
                'execution_time': 30,
                'success': False,
                'stdout': '',
                'stderr': 'Test timed out',
                'trace_file': None
            }
        except Exception as e:
            return {
                'run_id': run_id,
                'seed': seed,
                'steps': steps,
                'execution_time': time.time() - start_time,
                'success': False,
                'stdout': '',
                'stderr': f'Exception: {str(e)}',
                'trace_file': None
            }
    
    def generate_report(self, results: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Generate test report"""
        successful_runs = [r for r in results if r['success']]
        failed_runs = [r for r in results if not r['success']]
        
        total_execution_time = sum(r['execution_time'] for r in results)
        avg_execution_time = total_execution_time / len(results) if results else 0
        
        report = {
            'summary': {
                'total_runs': len(results),
                'successful_runs': len(successful_runs),
                'failed_runs': len(failed_runs),
                'success_rate': len(successful_runs) / len(results) if results else 0,
                'total_execution_time': total_execution_time,
                'average_execution_time': avg_execution_time
            },
            'successful_runs': successful_runs,
            'failed_runs': failed_runs,
            'trace_files': [r['trace_file'] for r in successful_runs if r['trace_file']]
        }
        
        return report


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description="Raft State Machine Random Runner")
    parser.add_argument('instrumented_raft_path', help="Path to instrumented raft.go file")
    parser.add_argument('--trace-dir', default='./traces', help="Directory for trace output")
    parser.add_argument('--runs', type=int, default=10, help="Number of test runs")
    parser.add_argument('--steps', type=int, default=100, help="Steps per run")
    parser.add_argument('--output', help="Output report file (JSON)")
    
    args = parser.parse_args()
    
    logging.basicConfig(level=logging.INFO, format='[%(levelname)s] %(message)s')
    
    runner = RaftStateMachineRunner(args.instrumented_raft_path, args.trace_dir)
    
    logger.info(f"Starting {args.runs} random test runs...")
    results = runner.run_random_test(args.runs, args.steps)
    
    report = runner.generate_report(results)
    
    logger.info(f"Test completed: {report['summary']['successful_runs']}/{report['summary']['total_runs']} successful")
    logger.info(f"Average execution time: {report['summary']['average_execution_time']:.2f}s")
    
    if args.output:
        with open(args.output, 'w') as f:
            json.dump(report, f, indent=2)
        logger.info(f"Report saved to {args.output}")
    else:
        print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main() 