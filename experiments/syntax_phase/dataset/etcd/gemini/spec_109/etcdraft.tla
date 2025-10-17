---- MODULE etcdraft ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    Servers,
    Data,
    DefaultVoteValue,
    ElectionTimeout,
    HeartbeatTimeout,
    PreVoteEnabled

VARIABLES
    nodes,
    network

vars == <<nodes, network>>

LastLogIndex(log) == Len(log)
LastLogTerm(log) == IF LastLogIndex(log) = 0 THEN 0 ELSE log[LastLogIndex(log)].term
Quorum == (Cardinality(Servers) \div 2) + 1
isUpToDate(candidateLastLogTerm, candidateLastLogIndex, voterLog) ==
    LET voterLastLogTerm = LastLogTerm(voterLog)
    IN (candidateLastLogTerm > voterLastLogTerm) \/
       (candidateLastLogTerm = voterLastLogTerm /\ candidateLastLogIndex >= LastLogIndex(voterLog))

BecomeFollower(n, term, lead) ==
    [ n EXCEPT !.state = "Follower",
               !.currentTerm = term,
               !.votedFor = DefaultVoteValue,
               !.leader = lead,
               !.votesGranted = {},
               !.electionTimer = 0 ]

BecomePreCandidate(n) ==
    [ n EXCEPT !.state = "PreCandidate",
               !.leader = DefaultVoteValue,
               !.votesGranted = {n.id},
               !.electionTimer = 0 ]

BecomeCandidate(n) ==
    [ n EXCEPT !.state = "Candidate",
               !.currentTerm = n.currentTerm + 1,
               !.votedFor = n.id,
               !.leader = DefaultVoteValue,
               !.votesGranted = {n.id},
               !.electionTimer = 0 ]

BecomeLeader(n) ==
    [ n EXCEPT !.state = "Leader",
               !.leader = n.id,
               !.nextIndex = [s \in Servers |-> LastLogIndex(n.log) + 1],
               !.matchIndex = [s \in Servers |-> 0] WITH [n.id] = LastLogIndex(n.log),
               !.heartbeatTimer = 0 ]

Msg(from, to, type, term, payload) == [ from |-> from, to |-> to, type |-> type, term |-> term, payload |-> payload ]

Init ==
    /\ nodes = [s \in Servers |->
        [ id |-> s,
          state |-> "Follower",
          currentTerm |-> 0,
          votedFor |-> DefaultVoteValue,
          log |-> << >>,
          commitIndex |-> 0,
          leader |-> DefaultVoteValue,
          votesGranted |-> {},
          nextIndex |-> [s \in Servers |-> 1],
          matchIndex |-> [s \in Servers |-> 0],
          electionTimer |-> 0,
          heartbeatTimer |-> 0
        ]
      ]
    /\ network = EmptyBag

Tick(s) ==
    /\ nodes' = [nodes EXCEPT ![s].electionTimer = @ + 1,
                                ![s].heartbeatTimer = @ + 1]
    /\ UNCHANGED network

Timeout(s) ==
    LET n == nodes[s]
    IN
    \/ /\ n.state \in {"Follower", "PreCandidate", "Candidate"}
       /\ n.electionTimer >= ElectionTimeout
       /\ \/ /\ PreVoteEnabled
             /\ LET new_node == BecomePreCandidate(n)
                    new_messages == { Msg(s, peer, "MsgPreVote", n.currentTerm + 1,
                                          [ lastLogIndex |-> LastLogIndex(n.log),
                                            lastLogTerm |-> LastLogTerm(n.log) ])
                                      : peer \in Servers \ {s} }
                IN /\ nodes' = [nodes EXCEPT ![s] = new_node]
                   /\ network' = network (+) Bag(new_messages)
          \/ /\ \lnot PreVoteEnabled
             /\ LET new_node == BecomeCandidate(n)
                    new_messages == { Msg(s, peer, "MsgVote", new_node.currentTerm,
                                          [ lastLogIndex |-> LastLogIndex(new_node.log),
                                            lastLogTerm |-> LastLogTerm(new_node.log) ])
                                      : peer \in Servers \ {s} }
                IN /\ nodes' = [nodes EXCEPT ![s] = new_node]
                   /\ network' = network (+) Bag(new_messages)

    \/ /\ n.state = "Leader"
       /\ n.heartbeatTimer >= HeartbeatTimeout
       /\ LET new_messages == {
                LET prevLogIndex == n.nextIndex[peer] - 1
                    prevLogTerm == IF prevLogIndex > 0 THEN n.log[prevLogIndex].term ELSE 0
                IN Msg(s, peer, "MsgApp", n.currentTerm,
                       [ prevLogIndex |-> prevLogIndex,
                         prevLogTerm |-> prevLogTerm,
                         entries |-> SubSeq(n.log, n.nextIndex[peer], LastLogIndex(n.log)),
                         leaderCommit |-> n.commitIndex ])
                : peer \in Servers \ {s} }
       IN /\ nodes' = [nodes EXCEPT ![s].heartbeatTimer = 0]
          /\ network' = network (+) Bag(new_messages)

HandleClientRequest(s) ==
    LET n == nodes[s]
    IN
    /\ n.state = "Leader"
    /\ \E d \in Data:
        LET newEntry == [ term |-> n.currentTerm, data |-> d ]
            newLog == Append(n.log, newEntry)
            new_node == [n EXCEPT !.log = newLog,
                                  !.matchIndex[s] = LastLogIndex(newLog),
                                  !.nextIndex[s] = LastLogIndex(newLog) + 1]
            new_messages == {
                LET prevLogIndex == new_node.nextIndex[peer] - 1
                    prevLogTerm == IF prevLogIndex > 0 THEN new_node.log[prevLogIndex].term ELSE 0
                IN Msg(s, peer, "MsgApp", new_node.currentTerm,
                       [ prevLogIndex |-> prevLogIndex,
                         prevLogTerm |-> prevLogTerm,
                         entries |-> SubSeq(new_node.log, new_node.nextIndex[peer], LastLogIndex(new_node.log)),
                         leaderCommit |-> new_node.commitIndex ])
                : peer \in Servers \ {s} }
        IN /\ nodes' = [nodes EXCEPT ![s] = new_node]
           /\ network' = network (+) Bag(new_messages)

Receive(m) ==
    LET receiver == nodes[m.to]
        sender == m.from
        new_network == network (-) Bag({m})
    IN
    \/ /\ m.term > receiver.currentTerm
       /\ LET new_receiver == BecomeFollower(receiver, m.term, DefaultVoteValue)
       /\ LET new_nodes == [nodes EXCEPT ![m.to] = new_receiver]
       /\ Receive([m EXCEPT !.from = sender, !.to = m.to, !.type = m.type, !.term = m.term, !.payload = m.payload,
                          nodes |-> new_nodes, network |-> new_network])
    \/ /\ m.term = receiver.currentTerm
       /\ \/ /\ m.type = "MsgApp"
             /\ LET p == m.payload
             /\ LET logOk == \/ /\ p.prevLogIndex = 0
                             \/ /\ p.prevLogIndex > 0
                                /\ p.prevLogIndex <= LastLogIndex(receiver.log)
                                /\ receiver.log[p.prevLogIndex].term = p.prevLogTerm
             /\ \/ /\ logOk
                   /\ LET newLog == IF Len(p.entries) > 0
                                   THEN SubSeq(receiver.log, 1, p.prevLogIndex) \o p.entries
                                   ELSE receiver.log
                      newCommitIndex == max(receiver.commitIndex, p.leaderCommit)
                      new_receiver == [ receiver EXCEPT
                                         !.log = newLog,
                                         !.commitIndex = newCommitIndex,
                                         !.leader = sender,
                                         !.electionTimer = 0,
                                         !.state = "Follower" ]
                      new_message == Msg(m.to, sender, "MsgAppResp", receiver.currentTerm,
                                         [ success |-> TRUE,
                                           matchIndex |-> LastLogIndex(new_receiver.log) ])
                   IN /\ nodes' = [nodes EXCEPT ![m.to] = new_receiver]
                      /\ network' = new_network (+) Bag({new_message})
                \/ /\ \lnot logOk
                   /\ LET new_message == Msg(m.to, sender, "MsgAppResp", receiver.currentTerm,
                                            [ success |-> FALSE,
                                              matchIndex |-> 0 ])
                   IN /\ nodes' = [nodes EXCEPT ![m.to].electionTimer = 0, ![m.to].leader = sender]
                      /\ network' = new_network (+) Bag({new_message})

          \/ /\ m.type = "MsgAppResp"
             /\ receiver.state = "Leader"
             /\ LET p == m.payload
             /\ \/ /\ p.success
                   /\ LET new_next == [receiver.nextIndex EXCEPT ![sender] = p.matchIndex + 1]
                      new_match == [receiver.matchIndex EXCEPT ![sender] = p.matchIndex]
                      new_commit_index ==
                         LET
                             CanCommit(idx) ==
                                 /\ idx > receiver.commitIndex
                                 /\ idx <= LastLogIndex(receiver.log)
                                 /\ receiver.log[idx].term = receiver.currentTerm
                                 /\ Cardinality({srv \in Servers |-> new_match[srv] >= idx}) >= Quorum
                         IN
                             IF \E idx \in (receiver.commitIndex+1)..LastLogIndex(receiver.log) : CanCommit(idx)
                             THEN CHOOSE idx \in (receiver.commitIndex+1)..LastLogIndex(receiver.log) : CanCommit(idx) /\ \A j \in (idx+1)..LastLogIndex(receiver.log) : ~CanCommit(j)
                             ELSE receiver.commitIndex
                   IN /\ nodes' = [nodes EXCEPT ![m.to].nextIndex = new_next,
                                              ![m.to].matchIndex = new_match,
                                              ![m.to].commitIndex = new_commit_index]
                      /\ network' = new_network
                \/ /\ \lnot p.success
                   /\ nodes' = [nodes EXCEPT ![m.to].nextIndex[sender] = max(1, @ - 1)]
                   /\ network' = new_network

          \/ /\ m.type \in {"MsgPreVote", "MsgVote"}
             /\ LET p == m.payload
             /\ LET voteGranted ==
                     /\ isUpToDate(p.lastLogTerm, p.lastLogIndex, receiver.log)
                     /\ \/ m.type = "MsgPreVote"
                        \/ /\ m.type = "MsgVote"
                           /\ (receiver.votedFor = DefaultVoteValue \/ receiver.votedFor = sender)
             /\ \/ /\ voteGranted
                   /\ LET new_receiver == IF m.type = "MsgVote"
                                         THEN [receiver EXCEPT !.votedFor = sender, !.electionTimer = 0]
                                         ELSE receiver
                      resp_type == IF m.type = "MsgPreVote" THEN "MsgPreVoteResp" ELSE "MsgVoteResp"
                      new_message == Msg(m.to, sender, resp_type, receiver.currentTerm, [granted |-> TRUE])
                   IN /\ nodes' = [nodes EXCEPT ![m.to] = new_receiver]
                      /\ network' = new_network (+) Bag({new_message})
                \/ /\ \lnot voteGranted
                   /\ LET resp_type == IF m.type = "MsgPreVote" THEN "MsgPreVoteResp" ELSE "MsgVoteResp"
                      new_message == Msg(m.to, sender, resp_type, receiver.currentTerm, [granted |-> FALSE])
                   IN /\ nodes' = nodes
                      /\ network' = new_network (+) Bag({new_message})

          \/ /\ m.type \in {"MsgPreVoteResp", "MsgVoteResp"}
             /\ receiver.state = IF m.type = "MsgPreVoteResp" THEN "PreCandidate" ELSE "Candidate"
             /\ LET p == m.payload
             /\ \/ /\ p.granted
                   /\ LET new_votes = receiver.votesGranted \cup {sender}
                   /\ \/ /\ Cardinality(new_votes) >= Quorum
                         /\ \/ /\ receiver.state = "PreCandidate"
                               /\ LET new_node == BecomeCandidate(receiver)
                                  new_messages == { Msg(m.to, peer, "MsgVote", new_node.currentTerm,
                                                        [ lastLogIndex |-> LastLogIndex(new_node.log),
                                                          lastLogTerm |-> LastLogTerm(new_node.log) ])
                                                    : peer \in Servers \ {m.to} }
                               IN /\ nodes' = [nodes EXCEPT ![m.to] = new_node]
                                  /\ network' = new_network (+) Bag(new_messages)
                            \/ /\ receiver.state = "Candidate"
                               /\ LET new_node == BecomeLeader(receiver)
                                  new_messages == {
                                     LET prevLogIndex == new_node.nextIndex[peer] - 1
                                         prevLogTerm == IF prevLogIndex > 0 THEN new_node.log[prevLogIndex].term ELSE 0
                                     IN Msg(m.to, peer, "MsgApp", new_node.currentTerm,
                                            [ prevLogIndex |-> prevLogIndex,
                                              prevLogTerm |-> prevLogTerm,
                                              entries |-> << >>,
                                              leaderCommit |-> new_node.commitIndex ])
                                     : peer \in Servers \ {m.to} }
                               IN /\ nodes' = [nodes EXCEPT ![m.to] = new_node]
                                  /\ network' = new_network (+) Bag(new_messages)
                      \/ /\ Cardinality(new_votes) < Quorum
                         /\ nodes' = [nodes EXCEPT ![m.to].votesGranted = new_votes]
                         /\ network' = new_network
                \/ /\ \lnot p.granted
                   /\ nodes' = nodes
                   /\ network' = new_network

    \/ /\ m.term < receiver.currentTerm
       /\ LET resp_type == CASE m.type = "MsgApp" -> "MsgAppResp"
                            [] m.type = "MsgVote" -> "MsgVoteResp"
                            [] m.type = "MsgPreVote" -> "MsgPreVoteResp"
                            [] OTHER -> "Error"
          new_message == Msg(m.to, sender, resp_type, receiver.currentTerm, [success |-> FALSE, granted |-> FALSE])
       IN /\ nodes' = nodes
          /\ network' = new_network (+) Bag({new_message})

Drop(m) ==
    /\ network' = network (-) Bag({m})
    /\ UNCHANGED nodes

Next ==
    \/ \E s \in Servers:
        \/ Tick(s)
        \/ Timeout(s)
        \/ HandleClientRequest(s)
    \/ \E m \in BagToSet(network):
        \/ Receive(m)
        \/ Drop(m)

Spec == Init /\ [][Next]_vars

====
