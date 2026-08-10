# Target-Specific Modeling Guidance

Complete the Required sections and remove unused Optional sections. Describe
WHAT should be verified, not HOW to model it. Priority questions are a coverage
floor: Specula should verify each one against the code and may also explore
adjacent code-derived risks. Expected behavior is a contract to test, not an
implementation fact to assume.

## Required

### Goal

- [What decision or confidence should this run support?]

### Scope

- In scope: [Subsystems, operations, or interfaces.]
- Boundaries/exclusions: [Explicit trust boundaries or exclusions, if any; otherwise `None`.]

### Priority Questions

List genuine priorities in order (typically 3–5). Never invent questions only
to reach that range.

1. When [event or condition], can [observable undesired outcome]?
   Expected behavior: [The intended user-visible or system contract.]
2. When [event or condition], can [observable undesired outcome]?
   Expected behavior: [The intended contract.]

### Must-cover Interactions

- [Module/component A] ↔ [Module/component B]:
  [Operation, lifecycle, or state transition that must be followed.]
- Consider: [Relevant failure, recovery, concurrency, or ordering conditions.]

### Assumptions

- [Only non-obvious caller, environment, or fault assumptions; write `None` if none.]

## Optional

### Known Incidents and References

- [Issue, incident, paper, or design document]: [Why it matters.]

### Suggested Starting Points

- `[path/to/file:line or symbol]`: [Why it may be relevant.]

### Additional Exploration

- [Adjacent risks worth exploring after the priority questions; omit to leave exploration open.]
