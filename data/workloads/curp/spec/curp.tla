---- MODULE curp ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Server,
    RoleSet,
    CmdSet,
    InitLeader,
    InitRole,
    InitTerm,
    InitSpecPool,
    InitUncommittedPool,
    InitCommittedCommands

VARIABLES
    leader,
    role,
    term,
    spec_pool,
    uncommitted_pool,
    committed_commands

vars == <<leader, role, term, spec_pool, uncommitted_pool, committed_commands>>

TypeOK ==
    /\ leader \in Server
    /\ role \in [Server -> RoleSet]
    /\ term \in Nat
    /\ spec_pool \in [Server -> Seq(CmdSet)]
    /\ uncommitted_pool \in Seq(CmdSet)
    /\ committed_commands \in Seq(CmdSet)

Init ==
    /\ leader = InitLeader
    /\ role = InitRole
    /\ term = InitTerm
    /\ spec_pool = InitSpecPool
    /\ uncommitted_pool = InitUncommittedPool
    /\ committed_commands = InitCommittedCommands

Next == UNCHANGED vars

Spec ==
    Init /\ [][Next]_vars

====
