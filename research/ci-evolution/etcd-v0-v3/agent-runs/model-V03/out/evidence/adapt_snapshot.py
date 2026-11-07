from pathlib import Path
p=Path('out/framework/adapters/go/action_validation_test.go');s=p.read_text();s=s.replace('StoreSnapshot                                                     avSnap','StoreSnapshot                                                     avSnap')
# Find the declaration independent of gofmt alignment.
s=s.replace('type avPre struct {','type avPre struct {\n Usnap avSnap')
s=s.replace('r.pendingConfIndex = p.Pending','if p.Usnap.Index > 0 { snap:=avSnapPB(p.Usnap); r.raftLog.unstable.snapshot=&snap }\n r.pendingConfIndex = p.Pending')
s=s.replace('if !IsEmptyHardState(rd.HardState) {\n', '''if !IsEmptySnap(rd.Snapshot) {
   if err:=r.raftLog.storage.(*MemoryStorage).ApplySnapshot(rd.Snapshot); err!=nil {panic(err)}
  }
  if err:=r.raftLog.storage.(*MemoryStorage).Append(rd.Entries); err!=nil {panic(err)}
  if !IsEmptyHardState(rd.HardState) {
''')
p.write_text(s)
p=Path('out/framework/adapters/tla/LocalActions.tla');s=p.read_text()
s=s.replace('!.unstable=Suffix(h,p.uoff),!.uoff=p.uoff', '!.usnap=IF "usnap" \\in DOMAIN p THEN Snap(p.usnap) ELSE EmptySnapshot,\n !.unstable=Suffix(h,p.uoff),!.uoff=p.uoff')
s=s.replace('''a==Between([r EXCEPT !.store.hs=IF b.hasHS THEN b.hs ELSE @],selected.input.between)''','''st==IF b.snapshot.index>0 THEN Store(b.snapshot.hist,b.snapshot,b.snapshot.index,r.store.hs) ELSE r.store
         persisted==StoreAppend(st,b.entries)
         a==Between([r EXCEPT !.store=[persisted EXCEPT !.hs=IF b.hasHS THEN b.hs ELSE @]],selected.input.between)''')
p.write_text(s)
