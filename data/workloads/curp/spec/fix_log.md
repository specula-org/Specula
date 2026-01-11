## 2026-01-11 - Trace helpers missing required operators

**Trace:** `../harness/traces/trace-1.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
TLC failed semantic analysis with unknown operators (`FoldSeq`, `Max`, `Range`, `Cardinality`) and `logline` referenced before declaration.

**Root Cause:**
The trace wrapper did not extend the required modules or define `Range`, and `l/logline` were declared after they were used.

**Fix:**
Extended `SequencesExt` and `FiniteSets`, defined `Range`, replaced `Max` with a conditional stride, and moved `l/logline` to the top.

**Files Modified:**
- `Tracecurp.tla`

## 2026-01-11 - Helper parameter shadowed trace index variable

**Trace:** `../harness/traces/trace-1.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
TLC reported multiply-defined symbol `l` during semantic analysis.

**Root Cause:**
Helper operators used the parameter name `l`, conflicting with the trace index variable `l`.

**Fix:**
Renamed helper parameters to `line`.

**Files Modified:**
- `Tracecurp.tla`

## 2026-01-11 - NormalizeCmd applied DOMAIN to string values

**Trace:** `../harness/traces/trace-1.ndjson`
**Error Type:** Inconsistency Error

**Issue:**
TLC errored while computing `TraceCmdSet` because `NormalizeCmd` called `DOMAIN` on string command values.

**Root Cause:**
Older traces store commands as strings; `NormalizeCmd` assumed commands were records/functions.

**Fix:**
Removed normalization and used raw command values directly for trace-derived state and command sets.

**Files Modified:**
- `Tracecurp.tla`
