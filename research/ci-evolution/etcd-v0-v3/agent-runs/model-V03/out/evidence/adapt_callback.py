from pathlib import Path
p=Path('out/framework/adapters/go/action_validation_test.go');s=p.read_text()
s=s.replace('nodeDisabled := strings.HasSuffix(c.Action, "_node") && !rn.HasReady()', 'nodeDisabled := (c.Action == "ready_node" || c.Action == "advance_node") && !rn.HasReady()')
s=s.replace('case "apply", "apply_then_step":', '''case "callback_node":
  ret = avCfgCS(*nd.ApplyConfChange(avCC(c.Input.Entry)))
  nd.Status()
  ctx,cancel := context.WithTimeout(context.Background(),30*time.Millisecond)
  err = nd.Propose(ctx,nil)
  cancel()
  nd.Status()
  if err == context.DeadlineExceeded { status="disabled"; result["disabled_phase"]="proposal channel after ApplyConfChange"; err=nil }
 case "apply", "apply_then_step":''')
p.write_text(s)
p=Path('out/framework/adapters/tla/LocalActions.tla');s=p.read_text()
s=s.replace('!.prevHS=p.prevHS,!.prevSS=p.prevSS]', '!.prevHS=p.prevHS,!.prevSS=p.prevSS,!.nodeLead=p.lead,!.propcEnabled=p.lead#0]')
s=s.replace('/\\ application=[n\\in Server |-> EmptyApp]', '''/\\ application=[n\\in Server |-> IF n=1 /\\ selected.action="callback_node" THEN
      [EmptyApp EXCEPT !.hist=Prefix(Ents(selected.pre.log),1),
       !.jobs= <<[batch |-> 1,snapshot |-> EmptySnapshot,entries |-> <<Ent(selected.input.entry)>>]>>] ELSE EmptyApp]''')
s=s.replace('/\\ requests=[id\\in RequestId |-> EmptyRequest]', '''/\\ requests=[id\\in RequestId |-> IF selected.action="callback_node" THEN
      [EmptyRequest EXCEPT !.status="Invoked",!.node=1,!.weight=0,!.encoded=6] ELSE EmptyRequest]''')
s=s.replace("Execute == /\\ phase=0 /\\ phase'=1", "Execute == /\\ phase=0 /\\ phase'=(IF selected.action=\"callback_node\" THEN 2 ELSE 1)")
s=s.replace('[] IsAdvance(c) -> ProtocolAdvance(1)', '[] IsAdvance(c) -> ProtocolAdvance(1)\n      [] c.action="callback_node" -> ProtocolApplyEntry(1,10)')
s=s.replace('LocalNext == PrepareBoot \\/ PrepareReady \\/ PrepareAdvance \\/ Execute', '''CallbackPropose == /\\ phase=2 /\\ phase'=1
 /\\ IF raft[1].propcEnabled THEN ProtocolPropose(1,7,10) ELSE UNCHANGED protocolVars
 /\\ UNCHANGED <<selected,before,captured,quality>>
LocalNext == PrepareBoot \\/ PrepareReady \\/ PrepareAdvance \\/ Execute \\/ CallbackPropose''')
s=s.replace('status |-> IF r.fatal#"" THEN "panic" ELSE IF c.action\\in {"proposal","apply_then_step"}', 'status |-> IF r.fatal#"" THEN "panic" ELSE IF c.action="callback_node" /\\ ~r.propcEnabled THEN "disabled" ELSE IF c.action\\in {"proposal","apply_then_step","callback_node"}')
s=s.replace('CASE c.action="apply" -> PCfg(r.config)', 'CASE c.action\\in {"apply","callback_node"} -> PCfg(r.config)')
p.write_text(s)
