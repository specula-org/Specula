---- MODULE etcdraft ----
EXTENDS TLC, Sequences, Naturals, FiniteSets, Bags

CONSTANTS NodeSet, electionTimeout, heartbeatTimeout

VARIABLES nodes, net

vars == <<nodes, net>>

NodeState == [state: {"Follower", "Candidate", "PreCandidate", "Leader"},
              currentTerm: Nat,
              votedFor: NodeSet \union {0},
              log: Seq([term: Nat, cmd: {}]),
              commitIndex: Nat,
              leaderId: NodeSet \union {0},
              electionElapsed: Nat,
              heartbeatElapsed: Nat,
              randomizedElectionTimeout: Nat]

Init == 
    /\ nodes = [n \in NodeSet |-> 
                [state |-> "Follower",
                 currentTerm |-> 0,
                 votedFor |-> 0,
                 log |-> <<>>,
                 commitIndex |-> 0,
                 leaderId |-> 0,
                 electionElapsed |-> 0,
                 heartbeatElapsed |-> 0,
                 randomizedElectionTimeout |-> electionTimeout + CHOOSE r \in 0..electionTimeout-1 : TRUE]]
    /\ net = EmptyBag

Send(m) == net' = net \union {[type |-> m.type, from |-> m.from, to |-> m.to, term |-> m.term, 
                              logTerm |-> m.logTerm, index |-> m.index, entries |-> m.entries, 
                              commit |-> m.commit, reject |-> m.reject]}

HandleMsg(n, m) ==
    LET node == nodes[n]
    IN CASE m.type = "MsgHup" ->
            IF node.state \in {"Follower", "Candidate"} THEN
                /\ ( \/ ( /\ node.state = "Follower"
                          /\ nodes' = [nodes EXCEPT ![n] = [@ EXCEPT !.state = "PreCandidate"]]
                        )
                     \/ ( /\ node.state = "Candidate"
                          /\ nodes' = [nodes EXCEPT ![n] = [@ EXCEPT !.currentTerm = @ + 1,
                                                             !.votedFor = n]]
                        )
                  )
                /\ LET newTerm == IF node.state = "Follower" THEN node.currentTerm ELSE node.currentTerm + 1
                   IN \A dst \in NodeSet: 
                          Send([type |-> "MsgVote", from |-> n, to |-> dst, term |-> newTerm,
                                logTerm |-> LastTerm(node.log), index |-> Len(node.log)])
            ELSE TRUE

    [] m.type = "MsgVote" ->
        IF m.term > node.currentTerm THEN
            /\ nodes' = [nodes EXCEPT ![n] = [@ EXCEPT !.currentTerm = m.term, !.votedFor = 0]]
            /\ HandleMsg(n, m)
        ELSE IF m.term = node.currentTerm /\ (node.votedFor = 0 \/ node.votedFor = m.from) THEN
            /\ nodes' = [nodes EXCEPT ![n] = [@ EXCEPT !.votedFor = m.from]]
            /\ Send([type |-> "MsgVoteResp", from |-> n, to |-> m.from, term |-> m.term, reject |-> FALSE])
        ELSE
            /\ Send([type |-> "MsgVoteResp", from |-> n, to |-> m.from, term |-> node.currentTerm, reject |-> TRUE])

    [] m.type = "MsgVoteResp" ->
        IF m.term = node.currentTerm /\ node.state = "Candidate" THEN
            LET votes == {p \in NodeSet: \E msg \in BagToSet(net): msg.from = p /\ msg.to = n /\ msg.type = "MsgVoteResp" /\ ~msg.reject}
            IN IF Cardinality(votes) >= QuorumSize() THEN
                /\ nodes' = [nodes EXCEPT ![n] = [@ EXCEPT !.state = "Leader", !.leaderId = n]]
                /\ \A dst \in NodeSet: 
                       Send([type |-> "MsgApp", from |-> n, to |-> dst, term |-> node.currentTerm,
                             logTerm |-> LastTerm(node.log), index |-> Len(node.log), entries |-> <<>>, commit |-> node.commitIndex])
            ELSE TRUE
        ELSE TRUE

    [] m.type = "MsgApp" ->
        IF m.term >= node.currentTerm THEN
            /\ nodes' = [nodes EXCEPT ![n] = [@ EXCEPT !.currentTerm = m.term, !.state = "Follower", !.leaderId = m.from]]
            /\ IF m.index <= Len(node.log) /\ (m.index = 0 \/ m.logTerm = node.log[m.index].term) THEN
                /\ nodes' = [nodes EXCEPT ![n] = [@ EXCEPT !.log = AppendEntries(node.log, m.index, m.entries),
                                                   !.commitIndex = MAX(node.commitIndex, m.commit)]]
                /\ Send([type |-> "MsgAppResp", from |-> n, to |-> m.from, term |-> m.term, index |-> Len(node.log), reject |-> FALSE])
            ELSE
                /\ Send([type |-> "MsgAppResp", from |-> n, to |-> m.from, term |-> node.currentTerm, index |-> Len(node.log), reject |-> TRUE])
        ELSE
            /\ Send([type |-> "MsgAppResp", from |-> n, to |-> m.from, term |-> node.currentTerm, index |-> Len(node.log), reject |-> TRUE])

    [] m.type = "MsgAppResp" ->
        IF m.term = node.currentTerm /\ node.state = "Leader" THEN
            IF ~m.reject THEN
                /\ nodes' = [nodes EXCEPT ![n] = [@ EXCEPT !.commitIndex = 
                    IF Cardinality({p \in NodeSet: \E msg \in BagToSet(net): msg.from = p /\ msg.type = "MsgAppResp" /\ msg.index >= m.index}) >= QuorumSize()
                    THEN m.index ELSE node.commitIndex]]
            ELSE TRUE
        ELSE TRUE

    [] m.type = "MsgHeartbeat" ->
        IF m.term >= node.currentTerm THEN
            /\ nodes' = [nodes EXCEPT ![n] = [@ EXCEPT !.currentTerm = m.term, !.state = "Follower", !.leaderId = m.from]]
            /\ nodes' = [nodes EXCEPT ![n] = [@ EXCEPT !.commitIndex = MAX(node.commitIndex, m.commit)]]
            /\ Send([type |-> "MsgHeartbeatResp", from |-> n, to |-> m.from, term |-> m.term])
        ELSE TRUE

Tick(n) ==
    LET node == nodes[n]
    IN /\ IF node.state = "Leader" 
           THEN nodes' = [nodes EXCEPT ![n] = [@ EXCEPT !.heartbeatElapsed = (@ + 1) % heartbeatTimeout]]
           ELSE nodes' = [nodes EXCEPT ![n] = [@ EXCEPT !.electionElapsed = @ + 1]]
        /\ IF node.state \in {"Follower", "Candidate"} /\ node.electionElapsed >= node.randomizedElectionTimeout THEN
               Send([type |-> "MsgHup", from |-> n, to |-> n, term |-> node.currentTerm])
           ELSE IF node.state = "Leader" /\ node.heartbeatElapsed = 0 THEN
               \A dst \in NodeSet: 
                   Send([type |-> "MsgHeartbeat", from |-> n, to |-> dst, term |-> node.currentTerm, commit |-> node.commitIndex])
           ELSE TRUE

Next == 
    \/ \E n \in NodeSet: Tick(n)
    \/ \E m \in net: \E n \in NodeSet: m.to = n /\ HandleMsg(n, m)

QuorumSize() == Cardinality(NodeSet) \div 2 + 1

LastTerm(log) == IF Len(log) > 0 THEN log[Len(log)].term ELSE 0

AppendEntries(log, index, entries) ==
    IF index + Len(entries) <= Len(log) THEN log
    ELSE SubSeq(log, 1, index) \o entries

====