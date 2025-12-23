---------- MODULE MCetcdraft_progress ----------
\* Model Checking Spec for etcdraft_progress
\* Mirrors MCetcdraft.tla but extends etcdraft_progress

EXTENDS etcdraft_progress

CONSTANT ReconfigurationLimit
ASSUME ReconfigurationLimit \in Nat

CONSTANT MaxTermLimit
ASSUME MaxTermLimit \in Nat

\* Limit on client requests
CONSTANT RequestLimit
ASSUME RequestLimit \in Nat

\* NEW: Limits on fault injection events to reduce state space
CONSTANT RestartLimit
ASSUME RestartLimit \in Nat

CONSTANT DropLimit
ASSUME DropLimit \in Nat

CONSTANT DuplicateLimit
ASSUME DuplicateLimit \in Nat

CONSTANT StepDownLimit
ASSUME StepDownLimit \in Nat

CONSTANT HeartbeatLimit
ASSUME HeartbeatLimit \in Nat

\* NEW: Counters for fault injection events (aggregated in a record for easier View definition)
VARIABLE constraintCounters

faultVars == <<constraintCounters>>

etcd == INSTANCE etcdraft_progress

\* Application uses Node (instead of RawNode) will have multiple ConfigEntry entries appended to log in bootstrapping.
BootstrapLog ==
    LET prevConf(y) == IF Len(y) = 0 THEN {} ELSE y[Len(y)].value.newconf
    IN FoldSeq(LAMBDA x, y: Append(y, [ term  |-> 1, type |-> ConfigEntry, value |-> [ newconf |-> prevConf(y) \union {x}, learners |-> {} ] ]), <<>>, SetToSeq(InitServer))

\* etcd is bootstrapped in two ways.
\* 1. bootstrap a cluster for the first time: server vars are initialized with term 1 and pre-inserted log entries for initial configuration.
\* 2. adding a new member: server vars are initialized with all state 0
\* 3. restarting an existing member: all states are loaded from durable storage
etcdInitServerVars  == /\ currentTerm = [i \in Server |-> IF i \in InitServer THEN 1 ELSE 0]
                       /\ state       = [i \in Server |-> Follower]
                       /\ votedFor    = [i \in Server |-> Nil]
etcdInitLogVars     == /\ log          = [i \in Server |-> IF i \in InitServer THEN BootstrapLog ELSE <<>>]
                       /\ commitIndex  = [i \in Server |-> IF i \in InitServer THEN Cardinality(InitServer) ELSE 0]
etcdInitConfigVars  == /\ config = [i \in Server |-> [ jointConfig |-> IF i \in InitServer THEN <<InitServer, {}>> ELSE <<{}, {}>>, learners |-> {}]]
                       /\ reconfigCount = 0 \* the bootstrap configurations are not counted

\* This file controls the constants as seen below.
\* In addition to basic settings of how many nodes are to be model checked,
\* the model allows to place additional limitations on the state space of the program.

\* Limit the # of reconfigurations to ReconfigurationLimit
MCAddNewServer(i, j) ==
    /\ reconfigCount < ReconfigurationLimit
    /\ etcd!AddNewServer(i, j)
MCDeleteServer(i, j) ==
    /\ reconfigCount < ReconfigurationLimit
    /\ etcd!DeleteServer(i, j)
MCAddLearner(i, j) ==
    /\ reconfigCount < ReconfigurationLimit
    /\ etcd!AddLearner(i, j)

\* Limit the terms that can be reached. Needs to be set to at least 3 to
\* evaluate all relevant states. If set to only 2, the candidate_quorum
\* constraint below is too restrictive.
MCTimeout(i) ==
    \* Limit the term of each server to reduce state space
    /\ currentTerm[i] < MaxTermLimit
    \* Limit max number of simultaneous candidates
    /\ Cardinality({ s \in GetConfig(i) : state[s] = Candidate}) < 1
    /\ etcd!Timeout(i)

\* Limit number of requests (new entries) that can be made
MCClientRequest(i, v) ==
    \* Allocation-free variant of Len(SelectSeq(log[i], LAMBDA e: e.contentType = TypeEntry)) < RequestLimit
    /\ FoldSeq(LAMBDA e, count: IF e.type = ValueEntry THEN count + 1 ELSE count, 0, log[i]) < RequestLimit
    /\ etcd!ClientRequest(i, v)

\* NEW: Limit node restarts/crashes to reduce state space explosion
MCRestart(i) ==
    /\ constraintCounters.restart < RestartLimit
    /\ etcd!Restart(i)
    /\ constraintCounters' = [constraintCounters EXCEPT !.restart = @ + 1]

\* NEW: Limit message drops to reduce state space explosion
MCDropMessage(m) ==
    /\ constraintCounters.drop < DropLimit
    /\ etcd!DropMessage(m)
    /\ constraintCounters' = [constraintCounters EXCEPT !.drop = @ + 1]

\* NEW: Limit message duplicates to reduce state space explosion
MCDuplicateMessage(m) ==
    /\ constraintCounters.duplicate < DuplicateLimit
    /\ etcd!DuplicateMessage(m)
    /\ constraintCounters' = [constraintCounters EXCEPT !.duplicate = @ + 1]

\* NEW: Limit heartbeats
MCHeartbeat(i, j) ==
    /\ constraintCounters.heartbeat < HeartbeatLimit
    /\ etcd!Heartbeat(i, j)
    /\ constraintCounters' = [constraintCounters EXCEPT !.heartbeat = @ + 1]

\* NEW: Limit step downs
MCStepDown(i) ==
    /\ constraintCounters.stepDown < StepDownLimit
    /\ etcd!StepDownToFollower(i)
    /\ constraintCounters' = [constraintCounters EXCEPT !.stepDown = @ + 1]

\* Limit how many identical append entries messages each node can send to another
\* Limit number of duplicate messages sent to the same server
MCSend(msg) ==
    \* One AppendEntriesRequest per node-pair at a time:
    \* a) No AppendEntries request from i to j.
    /\ ~ \E n \in DOMAIN messages \union DOMAIN pendingMessages:
        /\ n.mdest = msg.mdest
        /\ n.msource = msg.msource
        /\ n.mterm = msg.mterm
        /\ n.mtype = AppendEntriesRequest
        /\ msg.mtype = AppendEntriesRequest
    \* b) No (corresponding) AppendEntries response from j to i.
    /\ ~ \E n \in DOMAIN messages \union DOMAIN pendingMessages:
        /\ n.mdest = msg.msource
        /\ n.msource = msg.mdest
        /\ n.mterm = msg.mterm
        /\ n.mtype = AppendEntriesResponse
        /\ msg.mtype = AppendEntriesRequest
    /\ etcd!Send(msg)

\* NEW: Initialize fault injection counters
MCInit ==
    /\ etcd!Init
    /\ constraintCounters = [restart |-> 0, drop |-> 0, duplicate |-> 0, stepDown |-> 0, heartbeat |-> 0]

\* NEW: Next state formula with limited fault injection
MCNextAsync ==
    \/ /\ \E i,j \in Server : etcd!RequestVote(i, j)
       /\ UNCHANGED faultVars
    \/ /\ \E i \in Server : etcd!BecomeLeader(i)
       /\ UNCHANGED faultVars
    \/ /\ \E i \in Server: MCClientRequest(i, 0)
       /\ UNCHANGED faultVars
    \/ /\ \E i \in Server: etcd!ClientRequestAndSend(i, 0)
       /\ UNCHANGED faultVars
    \/ /\ \E i \in Server : etcd!AdvanceCommitIndex(i)
       /\ UNCHANGED faultVars
    \/ /\ \E i,j \in Server : \E b,e \in matchIndex[i][j]+1..Len(log[i])+1 : etcd!AppendEntries(i, j, <<b,e>>)
       /\ UNCHANGED faultVars
    \/ /\ \E i \in Server : etcd!AppendEntriesToSelf(i)
       /\ UNCHANGED faultVars
    \/ /\ \E i,j \in Server : MCHeartbeat(i, j)
    \/ /\ \E i,j \in Server : \E index \in 1..commitIndex[i] : etcd!SendSnapshot(i, j, index)
       /\ UNCHANGED faultVars
    \/ /\ \E m \in DOMAIN messages : etcd!Receive(m)
       /\ UNCHANGED faultVars
    \/ /\ \E i \in Server : MCTimeout(i)
       /\ UNCHANGED faultVars
    \/ /\ \E i \in Server : etcd!Ready(i)
       /\ UNCHANGED faultVars
    \/ /\ \E i \in Server : MCStepDown(i)

MCNextCrash == \E i \in Server : MCRestart(i)

MCNextUnreliable ==
    \* Only duplicate once
    \/ \E m \in DOMAIN messages :
        /\ messages[m] = 1
        /\ MCDuplicateMessage(m)
    \* Only drop if it makes a difference
    \/ \E m \in DOMAIN messages :
        /\ messages[m] = 1
        /\ MCDropMessage(m)

MCNext ==
    \/ MCNextAsync
    \/ MCNextCrash
    \/ MCNextUnreliable

MCNextDynamic ==
    \/ MCNext
    \/ /\ \E i, j \in Server : MCAddNewServer(i, j)
       /\ UNCHANGED faultVars
    \/ /\ \E i, j \in Server : MCAddLearner(i, j)
       /\ UNCHANGED faultVars
    \/ /\ \E i, j \in Server : MCDeleteServer(i, j)
       /\ UNCHANGED faultVars
    \/ /\ \E i \in Server : etcd!ChangeConf(i)
       /\ UNCHANGED faultVars
    \/ /\ \E i \in Server : etcd!ChangeConfAndSend(i)
       /\ UNCHANGED faultVars
    \/ /\ \E i \in Server : etcd!ApplySimpleConfChange(i)
       /\ UNCHANGED faultVars

mc_vars == <<vars, faultVars>>

mc_etcdSpec ==
    /\ MCInit
    /\ [][MCNextDynamic]_mc_vars

\* Symmetry set over possible servers. May dangerous and is only enabled
\* via the Symmetry option in cfg file.
Symmetry == Permutations(Server)

\* View used for state space reduction. 
\* It excludes 'constraintCounters' so that states differing only in counters are considered identical.
ModelView == << vars >>

=============================================================================