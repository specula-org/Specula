# libgomp Bug Report

## Summary

- **Target**: GCC's libgomp OpenMP runtime (bugs affect stock GCC, not specific to any patch)
- **Bugs found**: 2
  - Bug #28: BAR_CANCELLED overwrite in `gomp_barrier_handle_tasks` (NVIDIA flat barrier patch)
  - Bug #29: Missing BAR_TASK_PENDING in `omp_fulfill_event` unshackled thread path (stock GCC, all versions since GCC 11)
- **Legitimate reproduction**: Yes (standard OpenMP 5.0 API only, zero invasiveness)

### Model Checking Coverage

| Config | Mode | States | Result |
|--------|------|--------|--------|
| MC.cfg | BFS | 434K | All 5 invariants hold |
| MC_hunt_cross_cancel_task.cfg | BFS | ~22K | **BarrierSafety violated** |
| MC_stress.cfg | BFS | 434K | All hold |
| MC_hunt_family1.cfg | BFS | ~15K | All hold |
| MC_hunt_family2.cfg | BFS | ~18K | All hold |
| MC_hunt_family3.cfg | BFS | ~12K | All hold |
| MC_hunt_family4.cfg | BFS | ~20K | All hold |
| MC_hunt_detach_deadlock.cfg | BFS | 492 | **DetachFulfillNoDeadlock violated** |

---

## Bug #28: BAR_CANCELLED Overwrite in gomp_barrier_handle_tasks

- **Severity**: Medium (code defect; checking builds: assertion failure at bar.c:521; production builds: no observable impact due to `team_cancelled` fallback)
- **Status**: Not yet reported upstream
- **Root cause**: `gomp_increment_gen` unconditionally strips all flag bits including BAR_CANCELLED

### Root Cause

In `config/linux/bar.h`, `gomp_increment_gen` computes the new barrier generation:

```c
static unsigned gomp_increment_gen(gomp_barrier_state_t gen, unsigned increment)
{
    unsigned gens = (gen & BAR_BOTH_GENS_MASK);  // strips ALL flags (bits 0-5)
    switch (increment) {
    case BAR_CANCEL_INCR:
        return BAR_INCREMENT_CANCEL(gens);
    case BAR_HOLDING_SECONDARIES:
        return gens | BAR_HOLDING_SECONDARIES;   // BAR_CANCELLED lost!
    // ...
    }
}
```

`BAR_BOTH_GENS_MASK` covers bits 6+ (generation counters). Bits 0-5 are flags:
- Bit 0: BAR_WAS_LAST
- Bit 1: BAR_WAITING_FOR_TASK
- Bit 2: **BAR_CANCELLED**
- Bit 3: BAR_TASK_PENDING
- Bit 5: BAR_HOLDING_SECONDARIES

`gomp_increment_gen` strips ALL of them, then only restores the increment-specific flag. BAR_CANCELLED is never preserved.

`gomp_team_barrier_done` calls `gomp_increment_gen` and performs an `__atomic_store_n` on `bar->generation`, unconditionally overwriting any BAR_CANCELLED that was set by `gomp_team_barrier_cancel`.

There are two call sites in `gomp_barrier_handle_tasks` (task.c) that trigger this:

1. **Line 1612-1614**: Primary enters handle_tasks, task_count is already 0
2. **Line 1648-1667**: All tasks finished/cancelled during the while(1) loop

Neither site checks BAR_CANCELLED before calling `gomp_team_barrier_done`.

### Trigger Path: Final Barrier (Legitimate OpenMP)

**File**: `repro/final_barrier_cancel_task.c`

This path uses only standard OpenMP constructs:

```
1. Thread 0 creates 500 deferred tasks (#pragma omp task)
2. Threads 0,2,3 reach implicit barrier at end of parallel region
3. Primary enters handle_tasks(BAR_HOLDING_SECONDARIES), starts executing tasks
4. Thread 1 issues #pragma omp cancel parallel (after 5ms delay)
   → gomp_team_barrier_cancel sets BAR_CANCELLED on bar->generation
5. Subsequent gomp_task_run_pre calls see BAR_CANCELLED → cancel remaining tasks
6. task_count drops to 0
7. gomp_team_barrier_done(state, BAR_HOLDING_SECONDARIES)
   → gomp_increment_gen strips BAR_CANCELLED
   → atomic_store overwrites bar->generation → BAR_CANCELLED LOST
```

**Consequences** (final barrier path):
- Checking builds (`_LIBGOMP_CHECKING_=1`): Assertion at bar.c:521 fires → abort
- Non-checking builds: BAR_CANCELLED inconsistency in bar->generation, but `team_cancelled` (independent field) handles cleanup correctly. Limited observable impact.

### Why NVIDIA's Tests Miss This

NVIDIA has three cancel-parallel tests in the testsuite:

| Test | Has cancel? | Has tasks? | Has final barrier + tasks? |
|------|-------------|------------|---------------------------|
| cancel-parallel-1.c | Yes | No | No |
| cancel-parallel-2.c | Yes | Yes | Tasks pending at explicit barrier, but `gomp_team_barrier_wait_cancel` returns early (line 860-861) before entering handle_tasks |
| cancel-parallel-3.c | Yes | No | Cancel during final barrier, but no tasks → handle_tasks not called |

The bug requires **cancel + pending tasks + handle_tasks at a barrier** — a combination none of their tests exercise.

NVIDIA's own comment at bar.c:526-533 acknowledges that BAR_CANCELLED can be set during the final barrier (the cancel-parallel-3.c scenario), but the interaction with handle_tasks was not tested.

### Suggested Fix

Option A — Preserve BAR_CANCELLED in `gomp_increment_gen`:
```c
case BAR_HOLDING_SECONDARIES:
    return gens | BAR_HOLDING_SECONDARIES | (gen & BAR_CANCELLED);
```

Option B — Check BAR_CANCELLED before calling `gomp_team_barrier_done` in handle_tasks:
```c
if (team->task_count == 0
    && gomp_team_barrier_waiting_for_tasks (&team->barrier))
{
    if (gomp_team_barrier_cancelled (&team->barrier))
        /* handle cancellation instead of overwriting */;
    gomp_team_barrier_done (&team->barrier, state, increment);
    ...
}
```

Option A is simpler and fixes the root cause for all barrier types at once.

### TLA+ Model

The bug was discovered through TLA+ model checking of the flat barrier protocol. The specification models:
- 4 threads, 4 barriers, 2 tasks, 3 cancellations
- Barrier lifecycle: arrival → ensure_last → handle_tasks → barrier_done
- Cancel semantics: BAR_CANCELLED flag set via atomic fetch_or
- Task scheduling: dequeue, execute, cancel interactions

Key invariant violated: `BarrierSafety` — asserts that no secondary thread proceeds past the barrier before all secondaries have arrived (`threadGen` ordering). The violation is indirect: `PrimaryHandleTaskLast` completes the barrier (increments generation) without checking BAR_CANCELLED, causing a split-brain where one secondary sees the cancel (undoes its arrival) while another sees the generation increment (passes normally). This creates inconsistent `threadGen` values among secondaries at "done".

Note: The model found this violation on the cancel barrier path (`BAR_CANCEL_INCR`). Investigation of the real code shows this path is blocked in practice by an early return at bar.c:860-861. However, the same root cause (`gomp_increment_gen` stripping BAR_CANCELLED) is reachable via the final barrier path (`BAR_HOLDING_SECONDARIES`), where it triggers the checking assertion at bar.c:521-534.

---

## Bug #29: Missing BAR_TASK_PENDING in omp_fulfill_event (Deadlock)

- **Severity**: Critical (deterministic deadlock in production builds)
- **Affects**: All GCC versions since 11 (commit d656bfda, Feb 2021). Unfixed in GCC trunk as of March 2026.
- **Affects all barrier implementations**: centralized (Linux), flat (NVIDIA patch), POSIX — all use identical BAR_TASK_PENDING gating
- **Status**: Reported upstream — https://gcc.gnu.org/bugzilla/show_bug.cgi?id=124620
- **Root cause**: `omp_fulfill_event` from unshackled thread wakes a barrier thread without setting BAR_TASK_PENDING

### Root Cause

In `libgomp/task.c`, the `omp_fulfill_event` function has two wake paths:

**Path 1 — dependent tasks exist (`new_tasks > 0`)**: Correctly sets BAR_TASK_PENDING before waking (fixed in [commit ba886d0c](https://github.com/gcc-mirror/gcc/commit/ba886d0c488ebea2eb2df95c2069a3e207704dac), May 2021):
```c
if (new_tasks > 0)
  {
    gomp_team_barrier_set_task_pending (&team->barrier);  // ← correct
    do_wake = team->nthreads - team->task_running_count;
  }
```

**Path 2 — no dependent tasks, unshackled thread (`!shackled_thread_p`)**: Only wakes, does NOT set BAR_TASK_PENDING (introduced in [commit d656bfda](https://github.com/gcc-mirror/gcc/commit/d656bfda2d8316627d0bbb18b10954e6aaf3c88c), Feb 2021):
```c
if (!shackled_thread_p
    && !do_wake
    && team->task_detach_count == 0
    && gomp_team_barrier_waiting_for_tasks (&team->barrier))
  do_wake = 1;  // ← BUG: no gomp_team_barrier_set_task_pending
```

### Why This Causes Deadlock

The barrier wait loop (same pattern in all 3 barrier implementations) uses BAR_TASK_PENDING as the **sole gate** for entering `gomp_barrier_handle_tasks`:

```c
// config/linux/bar.c (centralized barrier, lines 113-125):
do {
    do_wait ((int *) &bar->generation, generation);
    gen = __atomic_load_n (&bar->generation, MEMMODEL_ACQUIRE);
    if (__builtin_expect (gen & BAR_TASK_PENDING, 0))  // ← gate
        gomp_barrier_handle_tasks (state);
    generation |= gen & BAR_WAITING_FOR_TASK;
} while (!gomp_barrier_state_is_incremented (gen, state));
```

`gomp_barrier_handle_tasks` is not just "run tasks" — it is also responsible for calling `gomp_team_barrier_done` when `task_count == 0`, which is the **only** path to complete a barrier when tasks are involved.

The deadlock sequence:
1. Detached task body completes → task becomes `GOMP_TASK_DETACHED`, `task_count > 0`
2. All team threads enter barrier wait loop, see no tasks to run, enter `futex_wait`
3. External thread calls `omp_fulfill_event` → `task_count` drops to 0
4. `gomp_team_barrier_wake` wakes one thread via `futex_wake`
5. **BUG**: BAR_TASK_PENDING is NOT set, so `bar->generation` is unchanged
6. Woken thread loads `bar->generation`, sees no change, loops back to `futex_wait`
7. **DEADLOCK** — no thread ever calls `gomp_team_barrier_done`

Key insight: `futex_wake` only wakes threads from `futex_wait`; it does **not** change `bar->generation`. Without BAR_TASK_PENDING modifying `bar->generation`, the wake is a no-op from the woken thread's perspective.

### Reproduction

**File**: `repro/detach_fulfill_deadlock.c`

The reproduction is **100% non-invasive** — uses only standard OpenMP 5.0 `detach` clause and POSIX `pthread_create`. Its structure is nearly identical to GCC's own test case `task-detach-13.c` ([commit ba886d0c](https://github.com/gcc-mirror/gcc/commit/ba886d0c488ebea2eb2df95c2069a3e207704dac)), except without `depend` clauses (to trigger the `new_tasks == 0` path).

```bash
gcc -fopenmp -O2 -lpthread -o detach_repro detach_fulfill_deadlock.c

# Deadlocks with any GCC (system or NVIDIA-patched):
timeout 5 ./detach_repro
echo $?  # 124 = deadlock

# Succeeds with patched libgomp:
timeout 5 LD_LIBRARY_PATH=/path/to/patched/.libs ./detach_repro
echo $?  # 0 = success
```

**Tested**: 5/5 deadlock (unpatched) vs 5/5 success (patched), using identical source/compiler/flags builds differing only by the one-line fix.

### Suggested Fix

Add `gomp_team_barrier_set_task_pending` before `do_wake = 1` in the unshackled thread path:

```c
if (!shackled_thread_p
    && !do_wake
    && team->task_detach_count == 0
    && gomp_team_barrier_waiting_for_tasks (&team->barrier))
  {
    gomp_team_barrier_set_task_pending (&team->barrier);
    do_wake = 1;
  }
```

This is the same pattern used in:
- The `new_tasks > 0` path (task.c, same function, 3 lines above)
- `gomp_target_task_completion` (task.c:835)

### Patch

See `repro/patches/bug29-fulfill-event-set-task-pending.patch`

### TLA+ Model

The bug was discovered through TLA+ model checking. The specification extends the flat barrier model with detached task lifecycle:
- `ScheduleDetachTask`: models `#pragma omp task detach(ev)` — task enters the queue
- `DetachTaskBodyComplete`: task body finishes, task becomes `GOMP_TASK_DETACHED` (`taskDetachCount++`, `taskPending` cleared)
- `FulfillEvent`: external thread calls `omp_fulfill_event` — `taskCount--`, `taskDetachCount--`, but **`taskPending` stays unchanged** (the bug)
- `WaitingPrimaryCompleteBarrier`: primary re-enters `gomp_barrier_handle_tasks` from wait loop when `taskPending` is set

Key invariant violated: `DetachFulfillNoDeadlock` — asserts that the system never reaches a state where all threads are in the barrier wait loop (`pc[t] = "waiting"`), `taskCount = 0`, `waitingForTask = TRUE`, and `~taskPending`. This state is a deadlock because no thread will enter `gomp_barrier_handle_tasks` to call `gomp_team_barrier_done`.

The counterexample trace (13 states) shows the exact deadlock sequence:
1. Detach task scheduled → `taskCount=1`, `taskPending=TRUE`
2. All threads enter barrier, primary scans, all arrived
3. Primary enters `handle_tasks` (`waitingForTask=TRUE`)
4. Task body completes → `taskDetachCount=1`, `taskPending=FALSE` (queue empty)
5. Primary sees no runnable tasks, exits to wait loop (`pc[Primary]="waiting"`)
6. `FulfillEvent`: `taskCount→0`, but `taskPending` stays `FALSE`
7. **Deadlock**: all threads waiting, `taskCount=0`, `~taskPending` — invariant violated

Applying the fix (`taskPending' = TRUE` in `FulfillEvent`) eliminates the violation: TLC explores 662 states with no errors.

### Why This Bug Survived

1. **Test gap**: GCC's test `task-detach-13.c` uses `depend(out/in)` → triggers `new_tasks > 0` path (correctly fixed by ba886d0c). No test covers the `new_tasks == 0` + unshackled thread combination.
2. **Subtle mechanism**: The developer (Kwok Cheung Yeung) correctly identified the need for `do_wake = 1` but missed that `futex_wake` alone doesn't change `bar->generation`, making the wake invisible to the woken thread.
3. **Same-author oversight**: The `set_task_pending` fix (ba886d0c, May 2021) was applied 3 months after the original code (d656bfda, Feb 2021) but only to the `new_tasks > 0` path, not the symmetric `!shackled_thread_p` path.

---

## Reproduction Instructions

See `repro/README.md` for step-by-step reproduction instructions.
