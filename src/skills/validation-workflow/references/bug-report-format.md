# Bug Report Format

Template for `spec/bug-report.md`, produced after spec convergence during bug hunting.

See `case-studies/cometbft/bug-report.md` for a complete real-world example.

## Template

```markdown
# Bug Report — <System Name>

## Summary

- Bug families tested: N
- Bugs found: N
- Configs run: MC_hunt_xxx.cfg, MC_family_xxx.cfg, ...

## Bug N: <Title>

- **Bug Family**: <family name/number>
- **Severity**: Critical / High / Medium
- **Invariant violated**: <name>
- **Config**: <cfg file>
- **Counterexample**: <N states, output file in spec/output/>

### Trace Summary

<Step-by-step description of the counterexample — what happens at each key state>

### Root Cause

<Why this happens in the implementation, with code references (file:line)>

### Affected Code

- `file:line`: <brief description>

### Recommendation

<Suggested fix>

---

## Not Reproduced

| Bug Family | Config | States Explored | Result |
|------------|--------|-----------------|--------|
| ... | ... | ... | No violation / Not testable (reason) |
```

## Guidelines

- **Every bug**: trace summary + root cause + affected code. Without these it's just a TLC output, not a bug report.
- **Not reproduced**: always include. "Not testable" with a reason is valid (e.g., spec doesn't model that mechanism).
- **No bugs found**: still write the report with Summary showing 0 bugs and the full Not Reproduced table.
- **Spec fixes during hunting**: if the spec was adjusted during bug hunting (Case A/B), document them briefly at the end.
