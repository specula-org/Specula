-------------------------- MODULE ModelDomains --------------------------
EXTENDS Naturals, Sequences, TLC, Json
CONSTANT InputFile
\* Target-specific finite domains, not an oracle. TLC chooses these combinations
\* and LocalActions invokes original base transitions before exporting a case.
Seeds == JsonDeserialize(InputFile)
\* Locally valid quota states: held payload bytes must exist after applied.
\* This only constructs input records; it does not compute action outputs.
QuotaPre(p,q) ==
 LET h==IF q=0 THEN p.log ELSE IF p.applied<Len(p.log) THEN
         [p.log EXCEPT ![Len(p.log)].weight=q,![Len(p.log)].encoded=8+q]
        ELSE Append(p.log,[p.log[1] EXCEPT !.index=Len(p.log)+1,!.weight=q,!.encoded=8+q])
 IN [p EXCEPT !.quota=q,!.log=h,
     !.prs=[k\in DOMAIN p.prs |-> [p.prs[k] EXCEPT
         !.match=IF p.prs[k].id=1 THEN Len(h) ELSE @,!.next=Len(h)+1]]]

Domain(c) == CASE c.id\in {"v03-advance-after-drop-raw-14","v03-advance-after-drop-node-17"} ->
 {[c EXCEPT !.id="tlc-" \o c.id]}
 [] c.id="v03-snapshot-advance-raw-cross" ->
 {[c EXCEPT !.id="tlc-" \o c.id \o "-" \o ToString(p),!.pre.pending=p]:p\in {0,2,3,4}}
 [] c.id="v03-advance-raw-cross-17" \/ c.id="v03-advance-node-equal-old-17" ->
 {[c EXCEPT !.id="tlc-" \o c.id \o "-" \o ToString(p),!.pre.pending=p]:p\in {0,1,2,3}}
 [] c.id="v03-quota-17-two-empty" ->
 {[c EXCEPT !.id="tlc-" \o c.id \o "-" \o ToString(q),!.pre=QuotaPre(c.pre,q)]:q\in {0,16,17}}
 [] c.id="advance-v02-raw-empty" -> {[c EXCEPT !.id="tlc-" \o c.id]}
 [] c.action="vote" ->
 {[c EXCEPT !.id="tlc-" \o c.id \o "-" \o ToString(t) \o "-" \o ToString(l) \o "-" \o ToString(v),
   !.input.message.term=t,!.input.message.logTerm=l,!.pre.vote=v]:
   t\in {1,2,3},l\in {1,2},v\in {0,3}}
 [] c.action="apply" /\ c.input.entry.kind#"V2" -> {[c EXCEPT !.id="tlc-" \o c.id]}
 [] c.action="apply" ->
 {[c EXCEPT !.id="tlc-" \o c.id \o "-" \o tr \o "-" \o ToString(k),
   !.input.entry.transition=tr,!.input.entry.changes=IF k=0 THEN <<>> ELSE @,
   !.input.entry.weight=IF k=0 THEN 2 ELSE @,
   !.input.entry.encoded=IF k=0 THEN 10 ELSE @]:
   tr\in {"Auto","JointImplicit","JointExplicit"},k\in {0,1}}
 [] c.action="proposal" ->
 {[c EXCEPT !.id="tlc-" \o c.id \o "-" \o ToString(p) \o "-" \o ToString(q),
   !.pre=QuotaPre([c.pre EXCEPT !.pending=p],q)]:p\in {0,2},q\in {0,15,16}}
 [] c.action="hup" ->
 {[c EXCEPT !.id="tlc-" \o c.id \o "-" \o ToString(a) \o "-" \o ToString(p),
   !.pre.applied=a,!.pre.preVote=p]:a\in {1,2},p\in BOOLEAN}
 [] c.action\in {"advance_raw","advance_node"} ->
 {[c EXCEPT !.id="tlc-" \o c.id \o "-" \o ToString(a) \o "-" \o ToString(q),
   !.pre=QuotaPre([c.pre EXCEPT !.applied=a,!.pending=0],q)]:a\in {0,2},q\in {0,16}}
 [] c.action="checkquorum" ->
 {[c EXCEPT !.id="tlc-" \o c.id \o "-" \o ToString(n),
   !.pre.prs=[k\in DOMAIN @ |-> [@[k] EXCEPT !.active=c.pre.prs[k].id\in {1,n}]]]:n\in {2,3,4}}
 [] c.action="read" ->
 {[c EXCEPT !.id="tlc-" \o c.id \o "-" \o ToString(t),
   !.pre.log=[k\in DOMAIN c.pre.log |-> [c.pre.log[k] EXCEPT !.term=t]]]:t\in {1,2}}
 [] c.action="restore" ->
 {[c EXCEPT !.id="tlc-" \o c.id \o "-" \o ToString(t),
   !.input.snapshot.term=t]:t\in {2,3}}
 [] OTHER -> {[c EXCEPT !.id="tlc-" \o c.id]}
ModelCases == UNION {Domain(Seeds[k]):k\in DOMAIN Seeds}
=============================================================================
