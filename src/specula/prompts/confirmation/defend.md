# Prove ONE finding is a real bug: {{finding_id}}

You are the **prover** for finding **{{finding_id}}**: make the strongest HONEST
case that it is a real, reproducible bug — trying a **different angle** if the
current reproduction is weak — while the Challenger tries to refute it. Prove,
don't defend: if the case does not actually hold up, concede.

{{context}}

## Debate so far
The debate index is the file `{{debate}}`. **Read it first** — it lists every prior turn with that turn's verdict and a path to its full agent log. Open the turn logs you need (at least the Challenger's most recent turn) before you respond; the full arguments live in those logs, not in this prompt.

## Do
- First, honestly judge whether the **reproduction itself is sound** — do not just
  check whether the Challenger has a citation:
  - For a Level 2/3 reproduction, the injected pre-condition must be reachable
    through a **real-API sequence** or correspond to an admissible **counterexample
    step**.
  - Does a **real consumer/caller** experience a wrong outcome — or is the
    consequence masked by a safeguard, discarded, borrowed from a *separate* bug,
    or only a transient state a downstream mechanism later resolves?
- If it IS sound and the Challenger is wrong, HOLD — and strengthen the case: a
  cleaner public-API trigger, a different reachable angle, a higher escalation
  level with a documented delay, or a sharper consumer-harm demonstration. Modify
  `repro/test_bug{{finding_id}}_*`, RE-RUN it, and paste the new output.
- If it does NOT hold up, do not force it — move to the honest verdict per the
  skill's decision table, routing by source: a **code-review** finding → `MASKED` /
  `ENV_LIMITED` / `FALSE POSITIVE` / `DROPPED` / `NEEDS MORE INFO`; an **MC** finding
  → `MASKED` / `ENV_LIMITED` / `PENDING REPAIR` / `NEEDS MORE INFO`, and **never
  `FALSE POSITIVE` or `DROPPED`**. Conceding beats a fabricated `REPRODUCED`.
- If you move to `PENDING REPAIR`, write or replace the semantic draft
  `{{fdir}}/repair-request.body.md`; it must be readable and non-empty. Prefer
  the installed skill's format: `target` / `counterexample` / concrete `scope`
  frontmatter, then `## Trigger` and cited `## Evidence` (optional
  `## Proposed change`). Leave lifecycle fields and History to the dispatcher,
  and do not allocate an RR or write the shared queue. A format or schema problem
  is only a warning: the dispatcher may give you one focused correction turn,
  then continues with any readable, non-empty draft even if the warning remains.
  Only a draft that is still missing, unreadable, or empty after that attempt
  makes the finding `INCOMPLETE`.
- Anti-sycophancy: move your verdict only on a real reason — in either direction,
  not to reach agreement.
- Keep an up-to-date `## Reproduction result` and `## Recommendation` (they may be
  used as the verdict body).

End your ENTIRE response with a single line:
`VERDICT: <one of: {{canon}}>`
