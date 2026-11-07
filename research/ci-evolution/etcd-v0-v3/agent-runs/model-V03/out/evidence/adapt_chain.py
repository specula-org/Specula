from pathlib import Path
p=Path('out/framework/adapters/go/action_validation_test.go');s=p.read_text().replace('case "proposal":\n', 'case "proposal", "propose_then_apply":\n')
s=s.replace('err = r.Step(pb.Message{Type: pb.MsgProp, From: 1, Entries: avEnts(c.Input.Entries)})','''err = r.Step(pb.Message{Type: pb.MsgProp, From: 1, Entries: avEnts(c.Input.Entries)})
  if err == nil && c.Action == "propose_then_apply" {
   es,e := r.raftLog.slice(r.raftLog.lastIndex(),r.raftLog.lastIndex()+1,noLimit)
   if e != nil {panic(e)}
   ent:=es[0]
   switch ent.Type {
   case pb.EntryConfChangeV2:
    var cc pb.ConfChangeV2; if e:=cc.Unmarshal(ent.Data); e!=nil {panic(e)}; rn.ApplyConfChange(cc)
   case pb.EntryConfChange:
    var cc pb.ConfChange; if e:=cc.Unmarshal(ent.Data); e!=nil {panic(e)}; rn.ApplyConfChange(cc)
   }
  }''');p.write_text(s)
p=Path('out/framework/adapters/tla/LocalActions.tla');s=p.read_text();s=s.replace(' [] c.action="apply" ->', ''' [] c.action="propose_then_apply" ->
      LET a==Step(r,[Message("MsgProp",1,1,0) EXCEPT !.entries=Ents(c.input.entries)],10)
          e==Hist(a)[Last(a)]
      IN IF a.fatal#"" \\/ a.decision#"Accepted" \\/ e.kind\\notin ConfKinds THEN a ELSE ApplyConfCore(a,e,10)
 [] c.action="apply" ->''')
s=s.replace('{"proposal","apply_then_step","callback_node"}', '{"proposal","apply_then_step","callback_node","propose_then_apply"}')
s=s.replace('raw_fatal |-> raft[1].fatal]', '''raw_fatal |-> raft[1].fatal,
 model_witnesses |-> [coreDecision |-> raft[1].decision,autoLeaveChecks |-> history.autoLeaveChecks,
 proposal |-> IF selected.action\\in {"proposal","propose_then_apply"} THEN
     ProposalObservation(Built(selected),Ents(selected.input.entries),raft[1],requests) ELSE "__null__"]]''')
p.write_text(s)
