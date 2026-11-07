import json,pathlib,sys
name=sys.argv[1];module=sys.argv[2];node=sys.argv[3]=='node'
p=pathlib.Path('out/runs')/name
cx=json.load(open(p/'counterexample.json'))['counterexample']
acts=cx['action'];loops=[a for a in acts if a[2][0]<=a[0][0]]
loop=loops[-1][2][0] if loops else None
replay=acts+([a for a in acts if a[0][0]>=loop] if loop else [])
def q(s):return json.dumps(s)
rows=[];events=[]
for a in replay:
 src,dst=a[0][1],a[2][1]
 if src['l']<=153:
  rows.append('[name |-> "Prefix", line |-> '+str(src['l'])+']');events.append(dict(name='Prefix',line=src['l']));continue
 ev=dst['lastEvent']; n=ev['node']; k=ev['action'];fields={'name':q(k),'node':str(n)}
 if k in ['Tick','ApplyEntry','TransferLeader','Receive']:fields['timeout']=str(src['raft'][n-1]['timeout'])
 if k in ['Receive','Publish']:
  old=src['wire'] or {};new=dst['wire'] or {}
  if k=='Receive':ms=[m for m,v in old.items() if v>new.get(m,0)]
  else:ms=[m for m,v in new.items() if v>old.get(m,0)]
  assert len(ms)==1 or (k=='Publish' and not ms),(a[0][0],k,len(ms))
  if ms:fields['message']=ms[0]
  fields['hasMessage']='TRUE' if ms else 'FALSE'
 rows.append('['+', '.join(k+' |-> '+v for k,v in fields.items())+']')
 events.append(dict(source_state=a[0][0],target_state=a[2][0],action=k,node=n,parameters_tla=fields))
script='''------------------------------ MODULE MODULE ------------------------------
EXTENDS Trace
VARIABLE pc
rvars == <<traceVars,pc>>
Events == <<
ROWS
>>
Call(e) ==
    CASE e.name="Prefix" -> MatchEvent(TraceLog[e.line])
      [] e.name="Ready" -> Ready(e.node)
      [] e.name="StartPersist" -> StartPersist(e.node,"All")
      [] e.name="CompletePersist" -> CompletePersist(e.node,"All")
      [] e.name="StorageApplySnapshot" -> StorageApplySnapshot(e.node)
      [] e.name="StorageAppend" -> StorageAppend(e.node)
      [] e.name="StorageSetHardState" -> StorageSetHardState(e.node)
      [] e.name="Publish" -> /\\ Publish(e.node)
           /\\ IF e.hasMessage THEN wire'=AddBag(wire,e.message) ELSE TRUE
      [] e.name="QueueApplication" -> QueueApplication(e.node)
      [] e.name="ApplyEntry" -> ApplyEntry(e.node,e.timeout)
      [] e.name="FinishApplication" -> FinishApplication(e.node)
      [] e.name="Advance" -> Advance(e.node)
      [] e.name="ReturnAPI" -> ReturnAPI(1)
      [] e.name="Receive" -> Receive(e.message,e.timeout)
      [] e.name="Tick" -> Tick(e.node,e.timeout)
      [] e.name="TransferLeader" -> TransferLeader(e.node,2,e.timeout)
      [] e.name="DeferApplication" -> UNCHANGED vars
      [] OTHER -> FALSE
ReplayInit == Init /\\ l=2 /\\ pc=1
ReplayStep ==
    /\\ pc<=Len(Events) /\\ Call(Events[pc])
    /\\ l'=IF Events[pc].name="Prefix" THEN l+1 ELSE l
    /\\ pc'=pc+1
ReplaySpec == ReplayInit /\\ [][ReplayStep]_rvars /\\ WF_rvars(ReplayStep)
Applicable == pc>Len(Events) \\/ ENABLED Call(Events[pc])
ReachedEnd == <>(pc>Len(Events))
NoFatal == \\A n\\in Server:raft[n].fatal=""
EndStillJoint == pc>Len(Events) => \\E n\\in Server:
    /\\ raft[n].role="Leader" /\\ raft[n].config.outgoing#{} /\\ raft[n].config.autoLeave
    /\\ raft[n].applied>=5
    /\\ ~\\E e\\in SeqSet(Hist(raft[n])):e.index>5 /\\ IsLeave(e)
=============================================================================
'''.replace('MODULE MODULE','MODULE '+module).replace('ROWS',',\n'.join(rows))
pathlib.Path('out/drivers',module+'.tla').write_text(script)
cfg=pathlib.Path('versions/V03/spec/Trace.cfg').read_text().split('INVARIANTS')[0].replace('SPECIFICATION TraceSpec','SPECIFICATION ReplaySpec')
if node:cfg=cfg.replace('RawNodes <- TraceRawNodes','RawNodes = {}')
cfg+='\nINVARIANTS Applicable NoFatal EndStillJoint\nPROPERTY ReachedEnd\nCHECK_DEADLOCK FALSE\n'
pathlib.Path('out/drivers',module+'.cfg').write_text(cfg)
json.dump(dict(source=name,loop_start=loop,actions=events,extra_loop_repetitions=1 if loop else 0),open(p/'reference-actions.json','w'),indent=2)
print(module,len(rows),'actions loop',loop)
