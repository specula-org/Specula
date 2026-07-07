# findings.json Format

Machine-readable companion to `spec/bug-report.md`, emitted at the end of Bug
Hunting. `bug-report.md` stays the human-facing narrative; `findings.json` is a
structured mirror of the same findings so a downstream orchestrator can enumerate
them deterministically (one work item per finding) instead of regex-splitting
prose.

Path: `spec/findings.json` (relative to `.specula-output/`).

## Scope

`findings.json` produced by this skill (Phase 3) covers **model-checking
findings only** — the same set written to `bug-report.md`. Code-review findings
live in `modeling-brief.md` (Phase 1) and are **not** in this skill's scope. The
full Phase-4 candidate set is `findings.json` (MC) **plus** the code-review
findings; consolidating the two is the consumer's job (the bug-confirmation
dispatcher, or the splitter for historical runs). Keeping each producer honest
about what it knows avoids a P3 agent inventing code-review entries it never saw.

## Schema

```json
{
  "schema_version": "1",
  "system": "<system name>",
  "generated_by": "validation-workflow",
  "findings": [
    {
      "id": "MC-1",
      "title": "<one-line title, matches the bug-report heading>",
      "source": "model-checking",
      "family": "<bug family name/number>",
      "severity": "Critical | High | Medium",
      "invariant": "<invariant violated>",
      "config": "MC_hunt_xxx.cfg",
      "counterexample": "spec/output/MC_hunt_xxx_violation.out",
      "affected_code": ["src/foo.go:812", "src/bar.go:44"],
      "summary": "3-5 sentences: the mechanism, mirroring the bug-report Root Cause."
    }
  ]
}
```

## Field rules

- **id** — stable within a run. Model-checking findings use `MC-<n>`; the
  splitter uses `CR-<n>` for code-review findings it pulls from the brief. The
  id is what the dispatcher names each per-finding work item, so it must be
  filesystem-safe (`[A-Za-z0-9._-]`) and unique.
- **source** — always `"model-checking"` for entries this skill emits.
- **invariant / config / counterexample** — required for model-checking
  findings; the `counterexample` path is relative to `.specula-output/` and must
  point at a real file saved under `spec/output/`.
- **affected_code** — list of `file:line` strings, same references cited in the
  bug-report Affected Code section. May be empty if hunting produced no code
  mapping yet, but prefer at least one anchor.
- **summary** — self-contained enough that a fresh agent with no other context
  can start investigating; do not assume the reader has `bug-report.md` open.

## Consistency with bug-report.md

Every `## Bug N` heading in `bug-report.md` MUST have exactly one entry in
`findings.json` with the matching title, and vice versa. The `Not Reproduced`
table is **not** included — those are non-findings by definition. If a run finds
zero bugs, emit `"findings": []` (a valid, present file), not a missing file.

## Why a present-but-empty file over a missing one

Consumers treat a missing `findings.json` as "this run predates the contract"
and fall back to the splitter. An empty `findings.json` means "P3 ran under the
contract and genuinely found nothing" — a different, cheaper signal. Always
write the file.
