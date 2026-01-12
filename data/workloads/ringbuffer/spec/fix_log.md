## 2026-01-11 - Trace parsing failed on comment headers

**Trace:** `../harness/traces/trace_rand_01.jsonl`
**Error Type:** Inconsistency Error

**Issue:**
Trace validation failed during JSON deserialization before any matching, because trace files contain `#` header lines.

**Root Cause:**
`ndJsonDeserialize` rejects non-JSON lines; the harness emits comment headers.

**Fix:**
Sanitize the trace input by stripping `#` lines into `trace_sanitized.jsonl` before deserialization.

**Files Modified:**
- `Traceringbuffer.tla`: added IOExec-based sanitization and read from sanitized file.

## 2026-01-11 - Create failed to add new ringbuffer entry

**Trace:** `../harness/traces/trace_rand_01.jsonl`
**Error Type:** Inconsistency Error

**Issue:**
Validation failed at `l=2` (Split) because the ringbuffer ID was missing after `Create`.

**Root Cause:**
`EXCEPT` does not extend function domains; and `@@ [rb |-> ...]` created a record with field `"rb"` rather than a function entry for the value of `rb`.

**Fix:**
Extend `rbs` with `@@ [i \in {rb} |-> ...]` so the new ID is inserted correctly.

**Files Modified:**
- `ringbuffer.tla`: fixed `Create` update to extend the map domain.

## 2026-01-11 - Non-enumerable quantifier in IsPowerOfTwo

**Trace:** `../harness/traces/trace_rand_01.jsonl`
**Error Type:** Inconsistency Error

**Issue:**
TLC failed in the initial state due to an infinite quantifier.

**Root Cause:**
`IsPowerOfTwo` used `\E k \in Nat`, which TLC cannot enumerate.

**Fix:**
Bound the quantifier to `0..n` to keep it finite.

**Files Modified:**
- `ringbuffer.tla`: bounded `IsPowerOfTwo` quantifier.

## 2026-01-11 - Disjunction scoping in Next caused symbol conflicts

**Trace:** `../harness/traces/trace_rand_01.jsonl`
**Error Type:** Inconsistency Error

**Issue:**
TLC reported multiply-defined symbol errors for `rb` in `Next`.

**Root Cause:**
The disjunction mixed multiple `\E rb` binders without explicit grouping, causing name conflicts.

**Fix:**
Restructured `Next` to use explicit `\/` branches and parenthesized sub-disjunctions.

**Files Modified:**
- `ringbuffer.tla`: rewrote `Next` disjunction for proper scoping.
