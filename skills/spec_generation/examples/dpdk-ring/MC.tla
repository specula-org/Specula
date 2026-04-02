---- MODULE MC ----
(***************************************************************************)
(* Model checking wrapper for DPDK rte_ring specification.                 *)
(* Counter-bounds fault-injection actions (Stall, StaleRead, CaptureHead). *)
(* Reactive actions (Reserve, WriteData, PublishTail, PeekStart/Finish)    *)
(* are NOT bounded — they react to existing state.                         *)
(***************************************************************************)

EXTENDS base

\* ========================================================================
\* Constants (counter limits and state space bounds)
\* ========================================================================

CONSTANTS
    StallLimit,     \* Max number of thread stalls
    StaleLimit,     \* Max number of stale-read events
    StaleHeadLimit, \* Max number of stale head captures (RTS update_tail)
    EnqueueBound    \* Max total enqueued elements (state constraint)

\* ========================================================================
\* Counter-bounded fault injection
\* ========================================================================

VARIABLES
    stallCount,     \* Number of Stall actions fired so far
    staleCount,     \* Number of StaleRead actions fired so far
    staleHeadCount  \* Number of RTSCaptureHead actions fired so far

mcVars == <<stallCount, staleCount, staleHeadCount>>

\* --- Bounded Stall (Family 1) ---
MCStall(t) ==
    /\ stallCount < StallLimit
    /\ Stall(t)
    /\ stallCount' = stallCount + 1
    /\ UNCHANGED <<staleCount, staleHeadCount>>

\* --- Bounded StaleRead (Family 2) ---
MCStaleRead(t) ==
    /\ staleCount < StaleLimit
    /\ StaleRead(t)
    /\ staleCount' = staleCount + 1
    /\ UNCHANGED <<stallCount, staleHeadCount>>

\* --- Bounded RTSCaptureHead (Family 4: stale RELAXED head in update_tail) ---
MCRTSCaptureHead(t) ==
    /\ staleHeadCount < StaleHeadLimit
    /\ RTSCaptureHead(t)
    /\ staleHeadCount' = staleHeadCount + 1
    /\ UNCHANGED <<stallCount, staleCount>>

\* ========================================================================
\* Unconstrained reactive actions (pass-through with UNCHANGED mcVars)
\* ========================================================================

MCReserveProd(t) == ReserveProd(t) /\ UNCHANGED mcVars
MCReserveCons(t) == ReserveCons(t) /\ UNCHANGED mcVars
MCWriteData(t) == WriteData(t) /\ UNCHANGED mcVars
MCPublishTail(t) == PublishTail(t) /\ UNCHANGED mcVars
MCPeekStart(t) == PeekStart(t) /\ UNCHANGED mcVars
MCPeekFinish(t) == PeekFinishAction(t) /\ UNCHANGED mcVars

\* ========================================================================
\* Init and Next
\* ========================================================================

MCInit ==
    /\ Init
    /\ stallCount = 0
    /\ staleCount = 0
    /\ staleHeadCount = 0

MCNext ==
    \E t \in Thread :
        \/ MCReserveProd(t)
        \/ MCReserveCons(t)
        \/ MCWriteData(t)
        \/ MCPublishTail(t)
        \/ MCStall(t)
        \/ MCStaleRead(t)
        \/ MCPeekStart(t)
        \/ MCPeekFinish(t)
        \/ MCRTSCaptureHead(t)

MCSpec == MCInit /\ [][MCNext]_<<allVars, mcVars>>

\* ========================================================================
\* State constraint (prune state space)
\* ========================================================================

StateConstraint ==
    /\ Len(enqueued) <= EnqueueBound
    /\ Len(dequeued) <= EnqueueBound

\* ========================================================================
\* Structural Invariants (always checked)
\* ========================================================================

MCHeadTailOrder == HeadTailOrder
MCValidPhases == ValidPhases

\* ========================================================================
\* Safety Invariants
\* ========================================================================

MCRingSafety == RingSafety
MCCapacityBound == CapacityBound
MCCounterConsistency == CounterConsistency
MCNoABA == NoABA
MCNoGarbageEnqueued == NoGarbageEnqueued

\* ========================================================================
\* Extension Invariants (bug-family specific, commented out in MC.cfg)
\* ========================================================================

MCHTSSingleInFlight == HTSSingleInFlight

====
