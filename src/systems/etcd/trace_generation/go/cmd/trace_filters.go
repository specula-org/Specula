//go:build with_tla

package main

import (
	"go.etcd.io/raft/v3"
)

// TraceFilter defines the interface for pluggable trace filtering.
type TraceFilter interface {
	// ShouldInclude returns true if the event should be included in the trace.
	ShouldInclude(event *raft.TracingEvent) bool

	// TransformEvent allows modification of the event before writing.
	// Returns the transformed event, or nil to skip the event.
	TransformEvent(event *raft.TracingEvent) *raft.TracingEvent

	// Name returns the name of this filter.
	Name() string
}

// CoarseGrainedFilter keeps only high-level election and log sync events.
type CoarseGrainedFilter struct{}

func NewCoarseGrainedFilter() *CoarseGrainedFilter {
	return &CoarseGrainedFilter{}
}

func (f *CoarseGrainedFilter) Name() string {
	return "CoarseGrained"
}

func (f *CoarseGrainedFilter) ShouldInclude(event *raft.TracingEvent) bool {
	// Include only key events for election and log synchronization.
	switch event.Name {
	case "BecomeCandidate", "BecomeLeader", "BecomeFollower":
		return true
	case "RequestVote", "ReceiveVote":
		return true
	case "AppendEntries", "ReceiveAppendEntries":
		return true
	case "CommitEntries", "ApplyEntries":
		return true
	case "StateChange", "TermChange":
		return true
	case "MessageStep":
		if event.Message != nil {
			switch event.Message.Type {
			case "MsgVote", "MsgVoteResp":
				return true
			case "MsgApp", "MsgAppResp":
				return true
			case "MsgHeartbeat", "MsgHeartbeatResp":
				return false // Filter out heartbeats for coarse-grained traces.
			}
		}
		return false
	default:
		return false
	}
}

func (f *CoarseGrainedFilter) TransformEvent(event *raft.TracingEvent) *raft.TracingEvent {
	// Create a simplified copy of the event.
	transformed := &raft.TracingEvent{
		Name:   event.Name,
		NodeID: event.NodeID,
		Role:   event.Role,
		State: raft.TracingState{
			Term:   event.State.Term,
			Vote:   event.State.Vote,
			Commit: event.State.Commit,
		},
		LogSize: event.LogSize,
	}

	// Simplify message information if present.
	if event.Message != nil {
		transformed.Message = &raft.TracingMessage{
			Type:        event.Message.Type,
			From:        event.Message.From,
			To:          event.Message.To,
			Term:        event.Message.Term,
			Index:       event.Message.Index,
			LogTerm:     event.Message.LogTerm,
			Commit:      event.Message.Commit,
			Vote:        event.Message.Vote,
			Reject:      event.Message.Reject,
			EntryLength: event.Message.EntryLength,
		}
	}

	if len(event.Properties) > 0 {
		transformed.Properties = make(map[string]interface{})
		for key, value := range event.Properties {
			switch key {
			case "term", "vote", "commit", "leader", "state":
				transformed.Properties[key] = value
			}
		}
	}

	return transformed
}

// FineGrainedFilter includes all events (pass-through).
type FineGrainedFilter struct{}

func NewFineGrainedFilter() *FineGrainedFilter {
	return &FineGrainedFilter{}
}

func (f *FineGrainedFilter) Name() string {
	return "FineGrained"
}

func (f *FineGrainedFilter) ShouldInclude(event *raft.TracingEvent) bool {
	return true
}

func (f *FineGrainedFilter) TransformEvent(event *raft.TracingEvent) *raft.TracingEvent {
	return event
}

// ElectionOnlyFilter keeps only election-related events.
type ElectionOnlyFilter struct{}

func NewElectionOnlyFilter() *ElectionOnlyFilter {
	return &ElectionOnlyFilter{}
}

func (f *ElectionOnlyFilter) Name() string {
	return "ElectionOnly"
}

func (f *ElectionOnlyFilter) ShouldInclude(event *raft.TracingEvent) bool {
	switch event.Name {
	case "BecomeCandidate", "BecomeLeader", "BecomeFollower":
		return true
	case "RequestVote", "ReceiveVote":
		return true
	case "StateChange":
		return true
	case "MessageStep":
		if event.Message != nil {
			msgType := event.Message.Type
			return msgType == "MsgVote" || msgType == "MsgVoteResp"
		}
		return false
	default:
		return false
	}
}

func (f *ElectionOnlyFilter) TransformEvent(event *raft.TracingEvent) *raft.TracingEvent {
	return NewCoarseGrainedFilter().TransformEvent(event)
}

// LogSyncOnlyFilter keeps only log synchronization events.
type LogSyncOnlyFilter struct{}

func NewLogSyncOnlyFilter() *LogSyncOnlyFilter {
	return &LogSyncOnlyFilter{}
}

func (f *LogSyncOnlyFilter) Name() string {
	return "LogSyncOnly"
}

func (f *LogSyncOnlyFilter) ShouldInclude(event *raft.TracingEvent) bool {
	switch event.Name {
	case "AppendEntries", "ReceiveAppendEntries":
		return true
	case "CommitEntries", "ApplyEntries":
		return true
	case "MessageStep":
		if event.Message != nil {
			msgType := event.Message.Type
			return msgType == "MsgApp" || msgType == "MsgAppResp"
		}
		return false
	default:
		return false
	}
}

func (f *LogSyncOnlyFilter) TransformEvent(event *raft.TracingEvent) *raft.TracingEvent {
	return NewCoarseGrainedFilter().TransformEvent(event)
}

// FilteredTraceLogger wraps FileTraceLogger with pluggable filtering.
type FilteredTraceLogger struct {
	baseLogger *FileTraceLogger
	filter     TraceFilter
}

func NewFilteredTraceLogger(filepath string, filter TraceFilter) (*FilteredTraceLogger, error) {
	baseLogger, err := NewFileTraceLogger(filepath)
	if err != nil {
		return nil, err
	}

	return &FilteredTraceLogger{
		baseLogger: baseLogger,
		filter:     filter,
	}, nil
}

func (f *FilteredTraceLogger) TraceEvent(event *raft.TracingEvent) {
	if !f.filter.ShouldInclude(event) {
		return
	}

	transformedEvent := f.filter.TransformEvent(event)
	if transformedEvent == nil {
		return
	}

	f.baseLogger.TraceEvent(transformedEvent)
}

func (f *FilteredTraceLogger) Close() error {
	return f.baseLogger.Close()
}

// GetFilter returns a filter by name.
func GetFilter(filterName string) TraceFilter {
	switch filterName {
	case "coarse":
		return NewCoarseGrainedFilter()
	case "fine":
		return NewFineGrainedFilter()
	case "election":
		return NewElectionOnlyFilter()
	case "logsync":
		return NewLogSyncOnlyFilter()
	default:
		return NewCoarseGrainedFilter()
	}
}
