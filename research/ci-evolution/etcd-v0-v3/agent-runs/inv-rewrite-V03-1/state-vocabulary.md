The existing abstract vocabulary describes Raft nodes, messages, Ready batches, caller storage/application and API requests. No existing predicates or maintenance conclusions are supplied.

Per node: id, role, term, vote, leader, committed/applied indices, log (term/index/kind/payload/encoded size), pendingConf index, uncommitted quota, configuration (incoming voters, outgoing voters, active learners, staged learners, AutoLeave), per-peer Progress (Match, Next, mode, inflights, active/paused state), outgoing message multiset, read requests/results, accepted prior SoftState/HardState, liveness/fatal status.

Ready: captured entries, committed entries, snapshot, messages, reads, HardState/SoftState, applied cursor, persistence/publication/application/acknowledgement status. Application of committed configuration entries is an explicit caller action; Advance is a separate action. The environment permits both RawNode calls and asynchronous Node channels.

Network messages can be delivered, delayed, lost or duplicated. Source interfaces include constructor/bootstrap, Campaign/Tick, Propose/ProposeConfChange, ApplyConfChange, Ready/Advance, Step, TransferLeader, snapshot/restart. Observable properties may use actual pre/input/post observations or explicitly justified history monitors. State names are vocabulary, not specification requirements.
