package raft

import (
    "encoding/json"
    "os"
    "strings"
    "testing"
    pb "go.etcd.io/etcd/raft/raftpb"
)

type avInput struct {
    Kind string `json:"kind"`
    Applied uint64 `json:"applied"`
    PreVote bool `json:"pre_vote"`
    Learner bool `json:"learner"`
}

func TestActionValidationCampaign(t *testing.T) {
    data, err := os.ReadFile(os.Getenv("AV_CASES"))
    if err != nil { t.Fatal(err) }
    var cases []avInput
    if err = json.Unmarshal(data, &cases); err != nil { t.Fatal(err) }
    f, err := os.Create(os.Getenv("AV_OUTPUT"))
    if err != nil { t.Fatal(err) }
    defer f.Close()
    for _, c := range cases {
        func() {
            defer func() { if p := recover(); p != nil { t.Fatalf("input=%+v panic=%v", c, p) } }()
            voters := []uint64{1,2,3}
            var learners []uint64
            if c.Learner { voters=[]uint64{2,3}; learners=[]uint64{1} }
            storage := NewMemoryStorage()
            if err := storage.ApplySnapshot(pb.Snapshot{Metadata:pb.SnapshotMetadata{
                Index:3, Term:1, ConfState:pb.ConfState{Voters:voters, Learners:learners},
            }}); err != nil { t.Fatal(err) }
            kind := pb.EntryNormal
            if c.Kind == "AddVoter" { kind=pb.EntryConfChange }
            if c.Kind == "V2" { kind=pb.EntryConfChangeV2 }
            if err := storage.Append([]pb.Entry{{Index:4, Term:1, Type:kind}}); err != nil { t.Fatal(err) }
            if err := storage.SetHardState(pb.HardState{Term:1, Commit:4}); err != nil { t.Fatal(err) }
            r := newRaft(&Config{ID:1, Applied:c.Applied, ElectionTick:3, HeartbeatTick:1,
                Storage:storage, MaxSizePerMsg:1024, MaxInflightMsgs:2, PreVote:c.PreVote, Logger:discardLogger})
            if err := r.Step(pb.Message{Type:pb.MsgHup, From:1, To:1}); err != nil { t.Fatal(err) }
            messages := make([]map[string]interface{},0,len(r.msgs))
            for _, m := range r.msgs {
                messages=append(messages,map[string]interface{}{"type":m.Type.String(),"from":m.From,
                    "to":m.To,"term":m.Term,"index":m.Index,"logTerm":m.LogTerm})
            }
            result:=map[string]interface{}{"action":"StepHup","input":c,"output":map[string]interface{}{
                "role":strings.TrimPrefix(r.state.String(),"State"),"term":r.Term,"vote":r.Vote,
                "lead":r.lead,"applied":r.raftLog.applied,"commit":r.raftLog.committed,
                "last":r.raftLog.lastIndex(),"messages":messages}}
            if err := json.NewEncoder(f).Encode(result); err != nil { t.Fatal(err) }
        }()
    }
}
