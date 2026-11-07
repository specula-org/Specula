# Exact-old V0 validation repair

Repair an already generated exact-old prior using only old-version evidence.
This is a validation back-edge, not an incremental update or incident hunt.

Inputs:

- `/work/source/`: immutable pristine exact-old source;
- `/work/work-source/`: writable instrumented exact-old worktree;
- `/work/prior/.specula-output/`: writable prior copied from the preceding V0
  attempt;
- `/work/audit/`: immutable deterministic audit and replay failures;
- `/work/scope.md`, frozen skills, libraries, and tools.

Read and apply the validation, trace, checking, harness, and spec-generation
skills relevant to the reported failures. Do not search the internet, history,
issues, pull requests, papers, release notes, benchmark labels, or paths outside
`/work`. Network is reserved for ordinary build dependencies.

Close every audit blocker without deleting valid traces, weakening properties,
or narrowing the frozen scope merely to obtain green output. In particular:

1. Put required semantic artifacts at their standard paths under `spec/` while
   preserving any compatible legacy copy.
2. Make `Trace.tla` and `Trace.cfg` consume and validate every retained fresh
   trace, including event-specific state fields. A scenario-name filter that
   silently ignores another trace is invalid.
3. Run real trace validation for every trace before canonical base/MC checking.
4. Require naturally completed bounded BFS with zero states left on queue for
   canonical base and MC; preserve broader timeout/open-frontier runs only as
   limited evidence.
5. Preserve commands, exit codes, logs, trace digests, coverage, instrumentation
   patch provenance, and a machine-readable suite manifest.

Use bounded outer timeouts and remove TLC state directories and background
processes. Do not inspect any new or fixed revision. Your final response must be
only the JSON object required by `/work/final-schema.json`.
