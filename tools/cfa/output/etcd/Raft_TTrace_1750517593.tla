---- MODULE Raft_TTrace_1750517593 ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, Raft, Raft_TEConstants

_expression ==
    LET Raft_TEExpression == INSTANCE Raft_TEExpression
    IN Raft_TEExpression!expression
----

_trace ==
    LET Raft_TETrace == INSTANCE Raft_TETrace
    IN Raft_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        stack = (<<[info |-> [args |-> <<>>, temp |-> <<>>], args |-> <<>>, backsite |-> Nil]>>)
        /\
        leadTransferee = ((s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil))
        /\
        randomizedElectionTimeout = ((s1 :> 10 @@ s2 :> 10 @@ s3 :> 10))
        /\
        log = ((s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>>))
        /\
        nextIndex = ((s1 :> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1) @@ s2 :> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1) @@ s3 :> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1)))
        /\
        leaderId = ((s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil))
        /\
        readStates = ((s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>>))
        /\
        currentTerm = ((s1 :> 0 @@ s2 :> 0 @@ s3 :> 0))
        /\
        votesGranted = ((s1 :> {} @@ s2 :> {} @@ s3 :> {}))
        /\
        state = ((s1 :> "Follower" @@ s2 :> "Follower" @@ s3 :> "Follower"))
        /\
        readOnlyOption = ((s1 :> "Safe" @@ s2 :> "Safe" @@ s3 :> "Safe"))
        /\
        info = ([args |-> <<s1>>, temp |-> <<>>])
        /\
        isLearner = ((s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE))
        /\
        votedFor = ((s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil))
        /\
        pendingReadIndexMessages = ((s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>>))
        /\
        pc = ("tickElection_1")
        /\
        heartbeatElapsed = ((s1 :> 0 @@ s2 :> 0 @@ s3 :> 0))
        /\
        messages = ({})
        /\
        matchIndex = ((s1 :> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0) @@ s2 :> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0) @@ s3 :> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0)))
        /\
        electionElapsed = ((s1 :> 1 @@ s2 :> 0 @@ s3 :> 0))
        /\
        pendingConfIndex = ((s1 :> 0 @@ s2 :> 0 @@ s3 :> 0))
        /\
        config = ((s1 :> {} @@ s2 :> {} @@ s3 :> {}))
        /\
        uncommittedSize = ((s1 :> 0 @@ s2 :> 0 @@ s3 :> 0))
        /\
        votesRejected = ((s1 :> {} @@ s2 :> {} @@ s3 :> {}))
        /\
        commitIndex = ((s1 :> 0 @@ s2 :> 0 @@ s3 :> 0))
    )
----

_init ==
    /\ pendingConfIndex = _TETrace[1].pendingConfIndex
    /\ messages = _TETrace[1].messages
    /\ leadTransferee = _TETrace[1].leadTransferee
    /\ uncommittedSize = _TETrace[1].uncommittedSize
    /\ matchIndex = _TETrace[1].matchIndex
    /\ log = _TETrace[1].log
    /\ leaderId = _TETrace[1].leaderId
    /\ pc = _TETrace[1].pc
    /\ state = _TETrace[1].state
    /\ readOnlyOption = _TETrace[1].readOnlyOption
    /\ votesRejected = _TETrace[1].votesRejected
    /\ randomizedElectionTimeout = _TETrace[1].randomizedElectionTimeout
    /\ pendingReadIndexMessages = _TETrace[1].pendingReadIndexMessages
    /\ commitIndex = _TETrace[1].commitIndex
    /\ readStates = _TETrace[1].readStates
    /\ config = _TETrace[1].config
    /\ electionElapsed = _TETrace[1].electionElapsed
    /\ currentTerm = _TETrace[1].currentTerm
    /\ heartbeatElapsed = _TETrace[1].heartbeatElapsed
    /\ nextIndex = _TETrace[1].nextIndex
    /\ votesGranted = _TETrace[1].votesGranted
    /\ info = _TETrace[1].info
    /\ votedFor = _TETrace[1].votedFor
    /\ stack = _TETrace[1].stack
    /\ isLearner = _TETrace[1].isLearner
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ pendingConfIndex  = _TETrace[i].pendingConfIndex
        /\ pendingConfIndex' = _TETrace[j].pendingConfIndex
        /\ messages  = _TETrace[i].messages
        /\ messages' = _TETrace[j].messages
        /\ leadTransferee  = _TETrace[i].leadTransferee
        /\ leadTransferee' = _TETrace[j].leadTransferee
        /\ uncommittedSize  = _TETrace[i].uncommittedSize
        /\ uncommittedSize' = _TETrace[j].uncommittedSize
        /\ matchIndex  = _TETrace[i].matchIndex
        /\ matchIndex' = _TETrace[j].matchIndex
        /\ log  = _TETrace[i].log
        /\ log' = _TETrace[j].log
        /\ leaderId  = _TETrace[i].leaderId
        /\ leaderId' = _TETrace[j].leaderId
        /\ pc  = _TETrace[i].pc
        /\ pc' = _TETrace[j].pc
        /\ state  = _TETrace[i].state
        /\ state' = _TETrace[j].state
        /\ readOnlyOption  = _TETrace[i].readOnlyOption
        /\ readOnlyOption' = _TETrace[j].readOnlyOption
        /\ votesRejected  = _TETrace[i].votesRejected
        /\ votesRejected' = _TETrace[j].votesRejected
        /\ randomizedElectionTimeout  = _TETrace[i].randomizedElectionTimeout
        /\ randomizedElectionTimeout' = _TETrace[j].randomizedElectionTimeout
        /\ pendingReadIndexMessages  = _TETrace[i].pendingReadIndexMessages
        /\ pendingReadIndexMessages' = _TETrace[j].pendingReadIndexMessages
        /\ commitIndex  = _TETrace[i].commitIndex
        /\ commitIndex' = _TETrace[j].commitIndex
        /\ readStates  = _TETrace[i].readStates
        /\ readStates' = _TETrace[j].readStates
        /\ config  = _TETrace[i].config
        /\ config' = _TETrace[j].config
        /\ electionElapsed  = _TETrace[i].electionElapsed
        /\ electionElapsed' = _TETrace[j].electionElapsed
        /\ currentTerm  = _TETrace[i].currentTerm
        /\ currentTerm' = _TETrace[j].currentTerm
        /\ heartbeatElapsed  = _TETrace[i].heartbeatElapsed
        /\ heartbeatElapsed' = _TETrace[j].heartbeatElapsed
        /\ nextIndex  = _TETrace[i].nextIndex
        /\ nextIndex' = _TETrace[j].nextIndex
        /\ votesGranted  = _TETrace[i].votesGranted
        /\ votesGranted' = _TETrace[j].votesGranted
        /\ info  = _TETrace[i].info
        /\ info' = _TETrace[j].info
        /\ votedFor  = _TETrace[i].votedFor
        /\ votedFor' = _TETrace[j].votedFor
        /\ stack  = _TETrace[i].stack
        /\ stack' = _TETrace[j].stack
        /\ isLearner  = _TETrace[i].isLearner
        /\ isLearner' = _TETrace[j].isLearner

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("Raft_TTrace_1750517593.json", _TETrace)

=============================================================================

 Note that you can extract this module `Raft_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `Raft_TEExpression.tla` file takes precedence 
  over the module `Raft_TEExpression` below).

---- MODULE Raft_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Naturals, TLC, Raft, Raft_TEConstants

expression == 
    [
        \* To hide variables of the `Raft` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        pendingConfIndex |-> pendingConfIndex
        ,messages |-> messages
        ,leadTransferee |-> leadTransferee
        ,uncommittedSize |-> uncommittedSize
        ,matchIndex |-> matchIndex
        ,log |-> log
        ,leaderId |-> leaderId
        ,pc |-> pc
        ,state |-> state
        ,readOnlyOption |-> readOnlyOption
        ,votesRejected |-> votesRejected
        ,randomizedElectionTimeout |-> randomizedElectionTimeout
        ,pendingReadIndexMessages |-> pendingReadIndexMessages
        ,commitIndex |-> commitIndex
        ,readStates |-> readStates
        ,config |-> config
        ,electionElapsed |-> electionElapsed
        ,currentTerm |-> currentTerm
        ,heartbeatElapsed |-> heartbeatElapsed
        ,nextIndex |-> nextIndex
        ,votesGranted |-> votesGranted
        ,info |-> info
        ,votedFor |-> votedFor
        ,stack |-> stack
        ,isLearner |-> isLearner
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_pendingConfIndexUnchanged |-> pendingConfIndex = pendingConfIndex'
        
        \* Format the `pendingConfIndex` variable as Json value.
        \* ,_pendingConfIndexJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(pendingConfIndex)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_pendingConfIndexModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].pendingConfIndex # _TETrace[s-1].pendingConfIndex
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE Raft_TETrace ----
\*EXTENDS IOUtils, TLC, Raft, Raft_TEConstants
\*
\*trace == IODeserialize("Raft_TTrace_1750517593.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE Raft_TETrace ----
EXTENDS TLC, Raft, Raft_TEConstants

trace == 
    <<
    ([stack |-> <<[info |-> [args |-> <<>>, temp |-> <<>>], args |-> <<>>, backsite |-> Nil]>>,leadTransferee |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil),randomizedElectionTimeout |-> (s1 :> 10 @@ s2 :> 10 @@ s3 :> 10),log |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>>),nextIndex |-> (s1 :> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1) @@ s2 :> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1) @@ s3 :> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1)),leaderId |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil),readStates |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>>),currentTerm |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),votesGranted |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {}),state |-> (s1 :> "Follower" @@ s2 :> "Follower" @@ s3 :> "Follower"),readOnlyOption |-> (s1 :> "Safe" @@ s2 :> "Safe" @@ s3 :> "Safe"),info |-> [args |-> <<>>, temp |-> <<>>],isLearner |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE),votedFor |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil),pendingReadIndexMessages |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>>),pc |-> Nil,heartbeatElapsed |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),messages |-> {},matchIndex |-> (s1 :> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0) @@ s2 :> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0) @@ s3 :> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0)),electionElapsed |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),pendingConfIndex |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),config |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {}),uncommittedSize |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),votesRejected |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {}),commitIndex |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0)]),
    ([stack |-> <<[info |-> [args |-> <<>>, temp |-> <<>>], args |-> <<>>, backsite |-> Nil]>>,leadTransferee |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil),randomizedElectionTimeout |-> (s1 :> 10 @@ s2 :> 10 @@ s3 :> 10),log |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>>),nextIndex |-> (s1 :> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1) @@ s2 :> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1) @@ s3 :> (s1 :> 1 @@ s2 :> 1 @@ s3 :> 1)),leaderId |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil),readStates |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>>),currentTerm |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),votesGranted |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {}),state |-> (s1 :> "Follower" @@ s2 :> "Follower" @@ s3 :> "Follower"),readOnlyOption |-> (s1 :> "Safe" @@ s2 :> "Safe" @@ s3 :> "Safe"),info |-> [args |-> <<s1>>, temp |-> <<>>],isLearner |-> (s1 :> FALSE @@ s2 :> FALSE @@ s3 :> FALSE),votedFor |-> (s1 :> Nil @@ s2 :> Nil @@ s3 :> Nil),pendingReadIndexMessages |-> (s1 :> <<>> @@ s2 :> <<>> @@ s3 :> <<>>),pc |-> "tickElection_1",heartbeatElapsed |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),messages |-> {},matchIndex |-> (s1 :> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0) @@ s2 :> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0) @@ s3 :> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0)),electionElapsed |-> (s1 :> 1 @@ s2 :> 0 @@ s3 :> 0),pendingConfIndex |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),config |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {}),uncommittedSize |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0),votesRejected |-> (s1 :> {} @@ s2 :> {} @@ s3 :> {}),commitIndex |-> (s1 :> 0 @@ s2 :> 0 @@ s3 :> 0)])
    >>
----


=============================================================================

---- MODULE Raft_TEConstants ----
EXTENDS Raft

CONSTANTS s1, s2, s3, v1, v2

=============================================================================

---- CONFIG Raft_TTrace_1750517593 ----
CONSTANTS
    Server = { s1 , s2 , s3 }
    Value = { v1 , v2 }
    Nil = Nil
    NoLimit = 5
    s2 = s2
    v2 = v2
    v1 = v1
    s3 = s3
    Nil = Nil
    s1 = s1

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Sat Jun 21 22:53:14 CST 2025