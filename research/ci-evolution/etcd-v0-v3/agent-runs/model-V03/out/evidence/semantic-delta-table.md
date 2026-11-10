| Boundary / case | V02 Go / inherited model | V03 Go / evolved model |
|---|---|---|
| Phase: empty in simple (`v03-prop-simple-0-empty-auto`) | tail=V2; pending=3 (both) | tail=Normal; pending=0 (both) |
| Phase: nonempty in joint (`v03-prop-joint-0-v2`) | tail=V2; pending=3 (both) | tail=Normal; pending=0 (both) |
| Joint explicit empty, then apply (`v03-propose-apply-joint-JointExplicit`) | panic (both) | panic (both) |
| Zero payload over quota (`v03-quota-17-two-empty`) | dropped; last=3; quota=17 (both) | ok; last=5; quota=17 (both) |
| Nonempty V2 over quota (`v03-quota-17-v2-payload`) | dropped; pending=4 (both) | dropped; pending=4 (both) |
| Auto-leave crossing, quota 17 (`v03-advance-raw-cross-17`) | last=2; pending=2; quota=0 (both) | last=3; pending=3; quota=0 (both) |
| Auto-leave oldApplied=pending (`v03-advance-raw-equal-old-0`) | last=3; pending=1 (both) | last=2; pending=1 (both) |
| New peer (`v03-apply-new-voter-Leader`) | p4=next 3, probe False, active True; messages=0 (both) | p4=next 2, probe True, active True; messages=1 (both) |
| Probe existing self (`v03-probe-existing-self-probe`) | messages=0 (both) | messages=1 (both) |
| Demote transferee (`v03-apply-demote-Leader`) | transfer=3 (both) | transfer=0 (both) |
| Bootstrap 3 peers (`v03-bootstrap-123`) | self=match 0/next 4 (both) | self=match 0/next 3 (both) |
| Constructor resets progress (`v03-construct-joint-2`) | self=match 2/next 3 (both) | self=match 2/next 3 (both) |
| Live snapshot restore (`restore-simple`) | self=match 3/next 4 (both) | self=match 2/next 3 (both) |
| Learner remove/re-add (`v03-apply-remove-readd-learner-Follower`) | p4=next 3, probe False, active True / model: p4=next 3, probe False, active False | p4=next 2, probe False, active True (both) |
| Node V2 self-removal (`v03-callback-v2-leave-remove-self`) | disabled / model: dropped | disabled (both) |
| Empty-log add then propose (`v03-empty-log-Leader-apply_then_step`) | ok (both) | panic (both) |
| Advance after proposal drop (`v03-advance-after-drop-raw-14`) | pending=2; quota=2; ok / model: pending=3; quota=2; ok | pending=3; quota=0; ok (both) |
| Panic precedes cancellation (`v03-config-broadcast-panic-before-transfer`) | transfer=4; panic / model: transfer=0; panic | transfer=4; panic (both) |
