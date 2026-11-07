from pathlib import Path
p=Path('out/framework/adapters/go/action_validation_test.go');s=p.read_text()
s=s.replace('Log                                                               []avEntry','Cut uint64\n StoreSnapshot avSnap\n Log                                                               []avEntry')
s=s.replace('return p\n}\nfunc avEnts', '''// Encoded=6 denotes nil Data, including the new automatic leave entry.
 if e.Weight == 0 && e.Encoded == 6 { p.Data = nil }
 return p
}
func avEnts''')
s=s.replace('rn, err := NewRawNode(&Config{ID: 1, ElectionTick: 10, HeartbeatTick: 1, Storage: st,', '''if p.Cut > 0 { if err := st.Compact(p.Cut); err != nil { panic(err) } }
 st.snapshot = avSnapPB(p.StoreSnapshot)
 rn, err := NewRawNode(&Config{ID: 1, ElectionTick: 10, HeartbeatTick: 1, Storage: st,''')
# Constructor cannot load zero HS below a compacted snapshot? newRaft default committed cut supports it.
s=s.replace('rn = avSetup(c)\n\tr := rn.raft', '''rn = avSetup(c)
 if strings.HasPrefix(c.Action, "bootstrap") {
  var err error
  rn, err = NewRawNode(&Config{ID:1, ElectionTick:10, HeartbeatTick:1, Storage:NewMemoryStorage(), MaxSizePerMsg:1024, MaxCommittedSizePerReady:1024, MaxUncommittedEntriesSize:16, MaxInflightMsgs:2})
  if err != nil { panic(err) }
 }
 r := rn.raft''')
s=s.replace('var nd *node\n', 'var nd *node\n nodeDisabled := strings.HasSuffix(c.Action,"_node") && !rn.HasReady()\n')
s=s.replace('if strings.HasPrefix(c.Action, "advance") {','if strings.HasPrefix(c.Action, "advance") && !nodeDisabled {')
s=s.replace('if c.Action == "restart" {','if c.Action == "restart" || c.Action == "construct" {')
s=s.replace('if e := restartStorage.ApplySnapshot(avSnapPB(c.Input.Snapshot)); e != nil {\n\t\t\tpanic(e)\n\t\t}', '''if c.Action == "restart" {
   if e := restartStorage.ApplySnapshot(avSnapPB(c.Input.Snapshot)); e != nil { panic(e) }
  } else {
   restartStorage.snapshot = avSnapPB(c.Input.Snapshot)
   if e := restartStorage.Append(avEnts(c.Input.Entries)); e != nil { panic(e) }
  }''')
s=s.replace('if e := restartStorage.SetHardState(pb.HardState{Term: 3, Commit: c.Input.Snapshot.Index}); e != nil {\n\t\t\tpanic(e)\n\t\t}', '''if c.Action == "restart" {
   if e := restartStorage.SetHardState(pb.HardState{Term:3, Commit:c.Input.Snapshot.Index}); e != nil { panic(e) }
  }''')
s=s.replace('phase = "execute"\n\tvar err error', '''phase = "execute"
 if nodeDisabled {
  // Observe the real channel loop; HasReady is the explicit delivery prerequisite.
  nd.Status()
  select {
  case <-nd.Ready(): panic("unexpected empty Node Ready delivery")
  case <-time.After(30*time.Millisecond):
  }
  status = "disabled"
  result["disabled_phase"] = "Node HasReady delivery prerequisite"
  if strings.HasPrefix(c.Action,"advance") { result["input_observation"].(map[string]interface{})["batch"] = avRD(rn.readyWithoutAccept()) }
  return result
 }
 var err error''')
s=s.replace('case "apply":\n\t\tret = avCfgCS(*rn.ApplyConfChange(avCC(c.Input.Entry)))', '''case "apply", "apply_then_step":
  ret = avCfgCS(*rn.ApplyConfChange(avCC(c.Input.Entry)))
  if c.Action == "apply_then_step" { ret = nil; err = r.Step(avMsg(c.Input.Message)) }
 case "bootstrap", "bootstrap_hup", "bootstrap_ready":
  peers := []Peer{}
  for _, id := range c.Input.Snapshot.Config.Voters { peers=append(peers,Peer{ID:id}) }
  err=rn.Bootstrap(peers)
  if err==nil && c.Action=="bootstrap_hup" { err=rn.Campaign() }
  if err==nil && c.Action=="bootstrap_ready" { ret=avRD(rn.Ready()) }''')
s=s.replace('case "restart":\n', 'case "restart", "construct":\n')
p.write_text(s)
p=Path('out/framework/adapters/tla/LocalActions.tla');s=p.read_text()
s=s.replace('LocalEmptyEncoded == 6','''LocalEmptyEncoded == 6
LocalBootstrapPayload == 6
LocalBootstrapEncoded == 14
BootState(c) ==
 LET peers==c.input.snapshot.config.voters
     joining==Server \\ SeqSet(peers)
     B==INSTANCE base WITH BootPeers <- peers, Joining <- joining
 IN B!InitialRaft(1,10)
StorageSnap(p) == IF "storeSnapshot" \\in DOMAIN p THEN Snap(p.storeSnapshot) ELSE EmptySnapshot
StorageCut(p) == IF "cut" \\in DOMAIN p THEN p.cut ELSE 0
IsBoot(c) == c.action \\in {"bootstrap","bootstrap_hup","bootstrap_ready"}
IsConstruct(c) == c.action \\in {"restart","construct"}''')
s=s.replace('!.store=Store(h,EmptySnapshot,0,EmptyHS)','!.store=Store(h,StorageSnap(p),StorageCut(p),EmptyHS)')
s=s.replace('RestartBefore(c) == [storage |-> [log |-> <<>>,snapshot', 'RestartBefore(c) == [storage |-> [log |-> IF c.action="construct" THEN PEnts(Ents(c.input.entries)) ELSE <<>>,snapshot')
s=s.replace('hs |-> [term |-> 3,vote |-> 0,commit |-> c.input.snapshot.index],cut', 'hs |-> IF c.action="construct" THEN EmptyHS ELSE [term |-> 3,vote |-> 0,commit |-> c.input.snapshot.index],cut')
s=s.replace('THEN Built(selected) ELSE InitialRaft', 'THEN (IF IsBoot(selected) THEN InitialRaft(1,10) ELSE Built(selected)) ELSE InitialRaft')
s=s.replace('IF selected.action="restart" THEN RestartBefore(selected) ELSE PState(Built(selected))', 'IF IsConstruct(selected) THEN RestartBefore(selected) ELSE PState(IF IsBoot(selected) THEN InitialRaft(1,10) ELSE Built(selected))')
s=s.replace('n=1 /\\ selected.action="restart"', 'n=1 /\\ IsConstruct(selected)')
s=s.replace('!.hs=[term |-> 3,vote |-> 0,commit |-> selected.input.snapshot.index]', '''!.log=IF selected.action="construct" THEN [e \\in SeqSet(Ents(selected.input.entries)) |-> e] ELSE EmptyFunction,
        !.hs=IF selected.action="construct" THEN EmptyHS ELSE [term |-> 3,vote |-> 0,commit |-> selected.input.snapshot.index]''')
# Disk log map must have index keys.
s=s.replace('[e \\in SeqSet(Ents(selected.input.entries)) |-> e]', '[k \\in DOMAIN selected.input.entries |-> Ent(selected.input.entries[k])]')
s=s.replace('[] c.action="restart" -> RestartCore(1,10)', '''[] IsConstruct(c) -> RestartCore(1,10)
 [] c.action="bootstrap" -> BootState(c)
 [] c.action="bootstrap_hup" -> Step(BootState(c),Message("MsgHup",1,1,0),10)
 [] c.action="apply_then_step" -> LET a==ApplyConfCore(r,Ent(c.input.entry),10) IN
      IF a.fatal#"" THEN a ELSE Step(a,Msg(c.input.message),10)''')
# bootstrap_ready uses original ProtocolReady with boot state substitution, no copied Ready semantics.
s=s.replace('[] IsAdvance(selected) -> ProtocolAdvance(1)', '''[] IsAdvance(selected) -> ProtocolAdvance(1)
    [] selected.action="bootstrap_ready" ->
       LET rs==[raft EXCEPT ![1]=BootState(selected)]
           B==INSTANCE base WITH raft <- rs
       IN B!ProtocolReady(1)''')
# Instance primed expression substitutions would bind rs' not raft; remove bootstrap_ready here; support via prep phase instead.
s=s.replace('/\\ phase=(IF IsAdvance(selected) THEN -2 ELSE 0)', '/\\ phase=(IF IsAdvance(selected) THEN -2 ELSE IF selected.action="bootstrap_ready" THEN -3 ELSE 0)')
a=s.index('    [] selected.action="bootstrap_ready" ->');b=s.index('    [] OTHER ->',a)
s=s[:a]+s[b:]
s=s.replace('selected.action\\in {"ready_raw","ready_node"}', 'selected.action\\in {"ready_raw","ready_node","bootstrap_ready"}')
s=s.replace('LocalNext == PrepareReady', '''PrepareBoot == /\\ phase=-3 /\\ phase'=0
 /\\ raft'=[raft EXCEPT ![1]=BootState(selected)]
 /\\ UNCHANGED <<selected,before,captured,quality,disk,ready,application,requests,wire,history>>
LocalNext == PrepareBoot \\/ PrepareReady''')
s=s.replace('c.action="proposal" /\\', 'c.action\\in {"proposal","apply_then_step"} /\\')
s=s.replace('c.action\\in {"ready_raw","ready_node"} -> PReady', 'c.action\\in {"ready_raw","ready_node","bootstrap_ready"} -> PReady')
s=s.replace('phase\\in {-2,0}', 'phase\\in {-3,-2,0}')
p.write_text(s)
p=Path('out/framework/adapters/tla/constants.cfg');s=p.read_text();s+='\n BootstrapPayload <- LocalBootstrapPayload\n BootstrapEncoded <- LocalBootstrapEncoded\n';p.write_text(s)
# Finite V03 generation domains take precedence over older family defaults.
p=Path('out/framework/adapters/tla/ModelDomains.tla');s=p.read_text().replace('Domain(c) == CASE ','''Domain(c) == CASE c.id="v03-advance-raw-cross-17" \\/ c.id="v03-advance-node-equal-old-17" ->
 {[c EXCEPT !.id="tlc-" \\o c.id \\o "-" \\o ToString(p),!.pre.pending=p]:p\\in {0,1,2,3}}
 [] c.id="v03-quota-17-two-empty" ->
 {[c EXCEPT !.id="tlc-" \\o c.id \\o "-" \\o ToString(q),!.pre=QuotaPre(c.pre,q)]:q\\in {0,16,17}}
 [] ''');p.write_text(s)
