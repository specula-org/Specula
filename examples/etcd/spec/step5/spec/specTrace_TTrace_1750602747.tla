---- MODULE specTrace_TTrace_1750602747 ----
EXTENDS specTrace, Sequences, TLCExt, Toolbox, Naturals, TLC

_expression ==
    LET specTrace_TEExpression == INSTANCE specTrace_TEExpression
    IN specTrace_TEExpression!expression
----

_trace ==
    LET specTrace_TETrace == INSTANCE specTrace_TETrace
    IN specTrace_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        stack = (<<[info |-> [args |-> <<>>, temp |-> <<>>], args |-> <<>>, backsite |-> "null"]>>)
        /\
        randomizedElectionTimeout = ([n1 |-> 10, n2 |-> 10, n3 |-> 10])
        /\
        leadTransferee = ([n1 |-> "null", n2 |-> "null", n3 |-> "null"])
        /\
        log = ([n1 |-> <<>>, n2 |-> <<>>, n3 |-> <<>>])
        /\
        nextIndex = ([n1 |-> [n1 |-> 1, n2 |-> 1, n3 |-> 1], n2 |-> [n1 |-> 1, n2 |-> 1, n3 |-> 1], n3 |-> [n1 |-> 1, n2 |-> 1, n3 |-> 1]])
        /\
        leaderId = ([n1 |-> "null", n2 |-> "null", n3 |-> "null"])
        /\
        readStates = ([n1 |-> <<>>, n2 |-> <<>>, n3 |-> <<>>])
        /\
        currentTerm = ([n1 |-> 0, n2 |-> 0, n3 |-> 0])
        /\
        votesGranted = ([n1 |-> {}, n2 |-> {}, n3 |-> {}])
        /\
        state = ([n1 |-> "Follower", n2 |-> "Follower", n3 |-> "Follower"])
        /\
        readOnlyOption = ([n1 |-> "Safe", n2 |-> "Safe", n3 |-> "Safe"])
        /\
        info = ([args |-> <<"s1">>, temp |-> <<>>])
        /\
        isLearner = ([n1 |-> FALSE, n2 |-> FALSE, n3 |-> FALSE])
        /\
        votedFor = ([n1 |-> "null", n2 |-> "null", n3 |-> "null"])
        /\
        l = (2)
        /\
        pendingReadIndexMessages = ([n1 |-> <<>>, n2 |-> <<>>, n3 |-> <<>>])
        /\
        pc = ("tickHeartbeat_1")
        /\
        heartbeatElapsed = ([n1 |-> 0, n2 |-> 0, n3 |-> 0])
        /\
        matchIndex = ([n1 |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0], n2 |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0], n3 |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0]])
        /\
        messages = ({})
        /\
        electionElapsed = ([n1 |-> 0, n2 |-> 0, n3 |-> 0])
        /\
        config = ([n1 |-> {}, n2 |-> {}, n3 |-> {}])
        /\
        pendingConfIndex = ([n1 |-> 0, n2 |-> 0, n3 |-> 0])
        /\
        votesRejected = ([n1 |-> {}, n2 |-> {}, n3 |-> {}])
        /\
        commitIndex = ([n1 |-> 0, n2 |-> 0, n3 |-> 0])
        /\
        uncommittedSize = ([n1 |-> 0, n2 |-> 0, n3 |-> 0])
    )
----

_init ==
    /\ config = _TETrace[1].config
    /\ l = _TETrace[1].l
    /\ stack = _TETrace[1].stack
    /\ readStates = _TETrace[1].readStates
    /\ info = _TETrace[1].info
    /\ nextIndex = _TETrace[1].nextIndex
    /\ currentTerm = _TETrace[1].currentTerm
    /\ electionElapsed = _TETrace[1].electionElapsed
    /\ votedFor = _TETrace[1].votedFor
    /\ pendingReadIndexMessages = _TETrace[1].pendingReadIndexMessages
    /\ pc = _TETrace[1].pc
    /\ leaderId = _TETrace[1].leaderId
    /\ isLearner = _TETrace[1].isLearner
    /\ randomizedElectionTimeout = _TETrace[1].randomizedElectionTimeout
    /\ matchIndex = _TETrace[1].matchIndex
    /\ votesRejected = _TETrace[1].votesRejected
    /\ commitIndex = _TETrace[1].commitIndex
    /\ leadTransferee = _TETrace[1].leadTransferee
    /\ state = _TETrace[1].state
    /\ heartbeatElapsed = _TETrace[1].heartbeatElapsed
    /\ readOnlyOption = _TETrace[1].readOnlyOption
    /\ uncommittedSize = _TETrace[1].uncommittedSize
    /\ messages = _TETrace[1].messages
    /\ log = _TETrace[1].log
    /\ votesGranted = _TETrace[1].votesGranted
    /\ pendingConfIndex = _TETrace[1].pendingConfIndex
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ config  = _TETrace[i].config
        /\ config' = _TETrace[j].config
        /\ l  = _TETrace[i].l
        /\ l' = _TETrace[j].l
        /\ stack  = _TETrace[i].stack
        /\ stack' = _TETrace[j].stack
        /\ readStates  = _TETrace[i].readStates
        /\ readStates' = _TETrace[j].readStates
        /\ info  = _TETrace[i].info
        /\ info' = _TETrace[j].info
        /\ nextIndex  = _TETrace[i].nextIndex
        /\ nextIndex' = _TETrace[j].nextIndex
        /\ currentTerm  = _TETrace[i].currentTerm
        /\ currentTerm' = _TETrace[j].currentTerm
        /\ electionElapsed  = _TETrace[i].electionElapsed
        /\ electionElapsed' = _TETrace[j].electionElapsed
        /\ votedFor  = _TETrace[i].votedFor
        /\ votedFor' = _TETrace[j].votedFor
        /\ pendingReadIndexMessages  = _TETrace[i].pendingReadIndexMessages
        /\ pendingReadIndexMessages' = _TETrace[j].pendingReadIndexMessages
        /\ pc  = _TETrace[i].pc
        /\ pc' = _TETrace[j].pc
        /\ leaderId  = _TETrace[i].leaderId
        /\ leaderId' = _TETrace[j].leaderId
        /\ isLearner  = _TETrace[i].isLearner
        /\ isLearner' = _TETrace[j].isLearner
        /\ randomizedElectionTimeout  = _TETrace[i].randomizedElectionTimeout
        /\ randomizedElectionTimeout' = _TETrace[j].randomizedElectionTimeout
        /\ matchIndex  = _TETrace[i].matchIndex
        /\ matchIndex' = _TETrace[j].matchIndex
        /\ votesRejected  = _TETrace[i].votesRejected
        /\ votesRejected' = _TETrace[j].votesRejected
        /\ commitIndex  = _TETrace[i].commitIndex
        /\ commitIndex' = _TETrace[j].commitIndex
        /\ leadTransferee  = _TETrace[i].leadTransferee
        /\ leadTransferee' = _TETrace[j].leadTransferee
        /\ state  = _TETrace[i].state
        /\ state' = _TETrace[j].state
        /\ heartbeatElapsed  = _TETrace[i].heartbeatElapsed
        /\ heartbeatElapsed' = _TETrace[j].heartbeatElapsed
        /\ readOnlyOption  = _TETrace[i].readOnlyOption
        /\ readOnlyOption' = _TETrace[j].readOnlyOption
        /\ uncommittedSize  = _TETrace[i].uncommittedSize
        /\ uncommittedSize' = _TETrace[j].uncommittedSize
        /\ messages  = _TETrace[i].messages
        /\ messages' = _TETrace[j].messages
        /\ log  = _TETrace[i].log
        /\ log' = _TETrace[j].log
        /\ votesGranted  = _TETrace[i].votesGranted
        /\ votesGranted' = _TETrace[j].votesGranted
        /\ pendingConfIndex  = _TETrace[i].pendingConfIndex
        /\ pendingConfIndex' = _TETrace[j].pendingConfIndex

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("specTrace_TTrace_1750602747.json", _TETrace)

=============================================================================

 Note that you can extract this module `specTrace_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `specTrace_TEExpression.tla` file takes precedence 
  over the module `specTrace_TEExpression` below).

---- MODULE specTrace_TEExpression ----
EXTENDS specTrace, Sequences, TLCExt, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `specTrace` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        config |-> config
        ,l |-> l
        ,stack |-> stack
        ,readStates |-> readStates
        ,info |-> info
        ,nextIndex |-> nextIndex
        ,currentTerm |-> currentTerm
        ,electionElapsed |-> electionElapsed
        ,votedFor |-> votedFor
        ,pendingReadIndexMessages |-> pendingReadIndexMessages
        ,pc |-> pc
        ,leaderId |-> leaderId
        ,isLearner |-> isLearner
        ,randomizedElectionTimeout |-> randomizedElectionTimeout
        ,matchIndex |-> matchIndex
        ,votesRejected |-> votesRejected
        ,commitIndex |-> commitIndex
        ,leadTransferee |-> leadTransferee
        ,state |-> state
        ,heartbeatElapsed |-> heartbeatElapsed
        ,readOnlyOption |-> readOnlyOption
        ,uncommittedSize |-> uncommittedSize
        ,messages |-> messages
        ,log |-> log
        ,votesGranted |-> votesGranted
        ,pendingConfIndex |-> pendingConfIndex
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_configUnchanged |-> config = config'
        
        \* Format the `config` variable as Json value.
        \* ,_configJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(config)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_configModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].config # _TETrace[s-1].config
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE specTrace_TETrace ----
\*EXTENDS specTrace, IOUtils, TLC
\*
\*trace == IODeserialize("specTrace_TTrace_1750602747.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE specTrace_TETrace ----
EXTENDS specTrace, TLC

trace == 
    <<
    ([stack |-> <<[info |-> [args |-> <<>>, temp |-> <<>>], args |-> <<>>, backsite |-> "null"]>>,randomizedElectionTimeout |-> [n1 |-> 10, n2 |-> 10, n3 |-> 10],leadTransferee |-> [n1 |-> "null", n2 |-> "null", n3 |-> "null"],log |-> [n1 |-> <<>>, n2 |-> <<>>, n3 |-> <<>>],nextIndex |-> [n1 |-> [n1 |-> 1, n2 |-> 1, n3 |-> 1], n2 |-> [n1 |-> 1, n2 |-> 1, n3 |-> 1], n3 |-> [n1 |-> 1, n2 |-> 1, n3 |-> 1]],leaderId |-> [n1 |-> "null", n2 |-> "null", n3 |-> "null"],readStates |-> [n1 |-> <<>>, n2 |-> <<>>, n3 |-> <<>>],currentTerm |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0],votesGranted |-> [n1 |-> {}, n2 |-> {}, n3 |-> {}],state |-> [n1 |-> "Follower", n2 |-> "Follower", n3 |-> "Follower"],readOnlyOption |-> [n1 |-> "Safe", n2 |-> "Safe", n3 |-> "Safe"],info |-> [args |-> <<>>, temp |-> <<>>],isLearner |-> [n1 |-> FALSE, n2 |-> FALSE, n3 |-> FALSE],votedFor |-> [n1 |-> "null", n2 |-> "null", n3 |-> "null"],l |-> 1,pendingReadIndexMessages |-> [n1 |-> <<>>, n2 |-> <<>>, n3 |-> <<>>],pc |-> "null",heartbeatElapsed |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0],matchIndex |-> [n1 |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0], n2 |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0], n3 |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0]],messages |-> {},electionElapsed |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0],config |-> [n1 |-> {}, n2 |-> {}, n3 |-> {}],pendingConfIndex |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0],votesRejected |-> [n1 |-> {}, n2 |-> {}, n3 |-> {}],commitIndex |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0],uncommittedSize |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0]]),
    ([stack |-> <<[info |-> [args |-> <<>>, temp |-> <<>>], args |-> <<>>, backsite |-> "null"]>>,randomizedElectionTimeout |-> [n1 |-> 10, n2 |-> 10, n3 |-> 10],leadTransferee |-> [n1 |-> "null", n2 |-> "null", n3 |-> "null"],log |-> [n1 |-> <<>>, n2 |-> <<>>, n3 |-> <<>>],nextIndex |-> [n1 |-> [n1 |-> 1, n2 |-> 1, n3 |-> 1], n2 |-> [n1 |-> 1, n2 |-> 1, n3 |-> 1], n3 |-> [n1 |-> 1, n2 |-> 1, n3 |-> 1]],leaderId |-> [n1 |-> "null", n2 |-> "null", n3 |-> "null"],readStates |-> [n1 |-> <<>>, n2 |-> <<>>, n3 |-> <<>>],currentTerm |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0],votesGranted |-> [n1 |-> {}, n2 |-> {}, n3 |-> {}],state |-> [n1 |-> "Follower", n2 |-> "Follower", n3 |-> "Follower"],readOnlyOption |-> [n1 |-> "Safe", n2 |-> "Safe", n3 |-> "Safe"],info |-> [args |-> <<"s1">>, temp |-> <<>>],isLearner |-> [n1 |-> FALSE, n2 |-> FALSE, n3 |-> FALSE],votedFor |-> [n1 |-> "null", n2 |-> "null", n3 |-> "null"],l |-> 2,pendingReadIndexMessages |-> [n1 |-> <<>>, n2 |-> <<>>, n3 |-> <<>>],pc |-> "tickHeartbeat_1",heartbeatElapsed |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0],matchIndex |-> [n1 |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0], n2 |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0], n3 |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0]],messages |-> {},electionElapsed |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0],config |-> [n1 |-> {}, n2 |-> {}, n3 |-> {}],pendingConfIndex |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0],votesRejected |-> [n1 |-> {}, n2 |-> {}, n3 |-> {}],commitIndex |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0],uncommittedSize |-> [n1 |-> 0, n2 |-> 0, n3 |-> 0]])
    >>
----


=============================================================================

---- CONFIG specTrace_TTrace_1750602747 ----
CONSTANTS
    Server = { "n1" , "n2" , "n3" }
    Value = { "v1" , "v2" , "v3" }
    Nil = "Nil"
    NoLimit = 3
    Nil <- TraceNil
    Vars <- vars
    Default <- DefaultImpl
    BaseInit <- Init
    UpdateVariables <- UpdateVariablesImpl
    TraceNext <- TraceNextImpl

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
\* Generated on Sun Jun 22 22:32:28 CST 2025