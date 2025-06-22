package main

import (
	"fmt"
	"math/rand"
	"os"
	"time"
)

// Simplified raft test program
func main() {
	// Set trace output file
	os.Setenv("RAFT_TRACE_OUTPUT", "raft_trace.ndjson")

	fmt.Println("Starting Raft state machine random testing...")

	// Simulate simplified version of raft state machine
	type RaftState struct {
		id    uint64
		term  uint64
		state string
	}

	raft := &RaftState{
		id:    1,
		term:  1,
		state: "Follower",
	}

	fmt.Printf("Initial state: ID=%d, Term=%d, State=%s\n", raft.id, raft.term, raft.state)

	// Run random state transitions
	for i := 0; i < 20; i++ {
		fmt.Printf("\n=== Step %d ===\n", i+1)

		// Randomly select operation
		operation := rand.Intn(3)

		switch operation {
		case 0:
			// Simulate tickElection
			fmt.Println("Executing tickElection")
			simulateTraceAction("tickElection", map[string]interface{}{
				"node_id": raft.id,
				"term":    raft.term,
				"state":   raft.state,
			})

			// Random state transition
			if raft.state == "Follower" && rand.Intn(3) == 0 {
				raft.state = "Candidate"
				raft.term++
				fmt.Printf("State transition: %s -> Term=%d\n", raft.state, raft.term)
			}

		case 1:
			// Simulate tickHeartbeat
			fmt.Println("Executing tickHeartbeat")
			simulateTraceAction("tickHeartbeat", map[string]interface{}{
				"node_id": raft.id,
				"term":    raft.term,
				"state":   raft.state,
			})

			if raft.state == "Leader" {
				fmt.Println("Sending heartbeat...")
			}

		case 2:
			// Simulate Step
			fmt.Println("Executing Step")
			simulateTraceAction("Step", map[string]interface{}{
				"node_id":  raft.id,
				"term":     raft.term,
				"state":    raft.state,
				"msg_type": "MsgVote",
				"msg_from": uint64(2),
			})

			// Random state transition
			if raft.state == "Candidate" && rand.Intn(2) == 0 {
				raft.state = "Leader"
				fmt.Printf("State transition: %s\n", raft.state)
			}
		}

		time.Sleep(200 * time.Millisecond)
	}

	fmt.Println("\nRandom testing completed!")
	fmt.Printf("Final state: ID=%d, Term=%d, State=%s\n", raft.id, raft.term, raft.state)
}

// Simulate traceAction function
func simulateTraceAction(actionName string, params map[string]interface{}) {
	timestamp := time.Now().UnixNano()

	if traceFile := os.Getenv("RAFT_TRACE_OUTPUT"); traceFile != "" {
		if file, err := os.OpenFile(traceFile, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644); err == nil {
			defer file.Close()
			// Simplified JSON output
			fmt.Fprintf(file, `{"action":"%s","timestamp":%d,"params":%v}`+"\n",
				actionName, timestamp, params)
		}
	}

	fmt.Printf("  -> Recording trace: %s\n", actionName)
}
