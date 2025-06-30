(* Generic module that aims to handle trace specifications *)
(* Just need to import it, and override some operators in order to have a trace spec that works *)
---- MODULE TraceSpec ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, TVOperators

ASSUME TLCGet("config").mode = "bfs"

VARIABLES l

(* Operators to override *)
Vars == Print(<<"Trace spec isn't valid, you should override 'Vars'.">>, <<>>)
BaseInit == Print(<<"Trace spec isn't valid, you should override 'BaseInit'.">>, Nil)
TraceNext == Print(<<"Trace spec isn't valid, you should override 'TraceNext'.">>, Nil)
UpdateVariables(logline) == Print(<<"Trace spec isn't valid, you should override 'UpdateVariables'.">>, Nil)
\*ASSUME Vars /= <<>>
\*ASSUME TraceNext # Nil

(* Read trace *)
Trace ==
    IF "TRACE_PATH" \in DOMAIN IOEnv THEN
        ndJsonDeserialize(IOEnv.TRACE_PATH)
    ELSE
        Print(<<"TRACE_PATH environnement variable not found, use default trace file.">>, ndJsonDeserialize("trace.ndjson"))

(* Read config *)
Config ==
    IF "CONFIG_PATH" \in DOMAIN IOEnv THEN
        ndJsonDeserialize(IOEnv.CONFIG_PATH)
    ELSE
        Print(<<"CONFIG_PATH environnement variable not found, use default config file.">>, ndJsonDeserialize("conf.ndjson"))

(* Manage exceptions: assume that trace is free of any exception *)
ASSUME \A t \in ToSet(Trace) : "event" \notin DOMAIN t \/ ("event" \in DOMAIN t /\ t.event /= "__exception")

logline ==
    Trace[l]
    
IsEvent(e) ==
    \* Equals FALSE if we get past the end of the log, causing model checking to stop.
    /\ l \in 1..Len(Trace)
    /\ IF "event" \in DOMAIN logline THEN logline.event = e ELSE TRUE
    /\ l' = l + 1
    /\ UpdateVariables(logline)
    /\ l' >= TLCGet(0) => TLCSet(0, l')

TraceInit ==
    /\ l = 1
    /\ BaseInit
    /\ TLCSet(0, 0)

IsStuttering ==
    /\ IsEvent("Stuttering")
    /\ UNCHANGED Vars

TraceSpec ==
    \* Because of  [A]_v <=> A \/ v=v'  , the following formula is logically
     \* equivalent to the (canonical) Spec formula Init /\ [][Next]_vars.
     \* However, TLC's breadth-first algorithm does not explore successor
     \* states of a *seen* state.  Since one or more states may appear one or
     \* more times in the the trace, the  UNCHANGED vars  combined with the
     \*  TraceView  that includes  TLCGet("level")  is our workaround.
    TraceInit /\ [][TraceNext \/ IsStuttering]_<<l, Vars>>

TraceAccepted ==
    LET d == TLCGet(0) IN
    IF d - 1 = Len(Trace) THEN TRUE
    ELSE Print(<<"Failed matching the trace to (a prefix of) a behavior:", Trace[d],
                    "TLA+ debugger breakpoint hit count " \o ToString(d+1)>>, FALSE)

TraceView ==
    \* A high-level state  s  can appear multiple times in a system trace.  Including the
     \* current level in TLC's view ensures that TLC will not stop model checking when  s
     \* appears the second time in the trace.  Put differently,  TraceView  causes TLC to
     \* consider  s_i  and s_j  , where  i  and  j  are the positions of  s  in the trace,
     \* to be different states.
    <<Vars, TLCGet("level")>>

Termination ==
    \* -Dtlc2.tool.queue.IStateQueue=StateDeque
    l = Len(Trace) + 1  => TLCSet("exit", TRUE)

====