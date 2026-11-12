# Prefix probe vs. ordinary model checking at the same budget (bug B, V03)

For #188 §3.3. The V0–V3 report says the prefix search found bug B where ordinary model checking did not, but the two were never run with the same budget and settings. The original runs differ in more than the starting point: the probe had 600 s and checked the C03 progress properties, while the ordinary runs had 60 s and 45 s and checked only safety invariants. This folder reruns them under identical conditions, then changes one thing at a time: first only the property, then only how much of the prefix is replayed.

Only bug B is covered. Every input of its probe is in this branch. Bug A's probe needs `joint-autoleave.ndjson` (sha256 `4ba1bd3f…`), which is not.

## Setup

- Specs: `agent-runs/inv-evidence/out/revised-spec/{V02,V03}`. Their files are byte-identical to the probe's recorded inputs (`agent-runs/progress-probe-V03/input-manifest.json`), and `run.py` refuses to run if they are not.
- Drivers: `agent-runs/progress-probe-V03/out/drivers/`, plus `drivers/clocked-leadership-safety.cfg`. That config is `clocked-leadership.cfg` with the progress properties replaced by the six safety invariants from `ordinary-v2.cfg`.
- Prefix inputs: `agent-runs/progress-probe-V03/out/joint-autoleave-prefix-inputs.ndjson` (153 events).
- `drivers/C03Free.tla` is the probe's driver with part of the prefix left to the search. Events up to `PrefixEnd` are replayed as before. The client inputs recorded after it (`Campaign` at event 41, `InvokeV2` at 152, `Propose` at 153) keep their recorded parameters but may each happen once, at any point and in any order, with no fairness. The recorded service events after `PrefixEnd` are dropped, and the probe's own fair pump does that work. Service scheduling, the optional leader transfer, the view and the properties are unchanged. `PrefixEnd = 1` starts at Init, and `PrefixEnd = 153` is the original probe.
- Every run uses the probe's original 600 s limit unless its name carries a longer one, one TLC worker, a 6 GiB heap and the same TLC jar (TLC 2026.11.03, OpenJDK 21, macOS arm64).

## Results

| Run | Version | Start | Checks | Budget | Outcome | Distinct states | Depth | Wall time |
|---|---|---|---|---:|---|---:|---:|---:|
| `probe-v03` | V03 | prefix | progress properties | 600 s | liveness violation | 3156 | 673 | 134.5 s |
| `probe-v02` | V02 | prefix | progress properties | 600 s | completed, no error | 3177 | 706 | 116.04 s |
| `probe-safety-v03` | V03 | prefix | safety invariants | 600 s | completed, no error | 3272 | 715 | 27.97 s |
| `free-153-v03` | V03 | prefix | progress properties | 600 s | liveness violation | 3272 | 715 | 135.74 s |
| `free-151-v03` | V03 | prefix to event 151 | progress properties | 600 s | budget exhausted, no error | 17007 | 314 | 600.02 s |
| `free-151-v03-3600s` | V03 | prefix to event 151 | progress properties | 3600 s | liveness violation | 80882 | 665 | 3274.68 s |
| `free-41-v03` | V03 | prefix to event 41 | progress properties | 600 s | budget exhausted, no error | 17878 | 218 | 600.02 s |
| `free-1-v03` | V03 | Init | progress properties | 600 s | budget exhausted, no error | 20445 | 217 | 600.02 s |
| `free-1-v03-3600s` | V03 | Init | progress properties | 3600 s | budget exhausted, no error | 103850 | 453 | 3600.03 s |
| `free-151-v02-5400s` | V02 | prefix to event 151 | progress properties | 5400 s | completed, no error | 90301 | 822 | 3199.73 s |
| `ordinary-v03` | V03 | Init | safety invariants | 600 s | budget exhausted, no error | 2788752 | 3 | 600.04 s |
| `ordinary-v2-v03` | V03 | Init | safety invariants | 600 s | budget exhausted, no error | 3031196 | 3 | 600.02 s |

Depth is the last BFS level TLC reported. Each run's `run.json` has the exact command, and `tlc.log` keeps TLC's statistics and the counterexample's action sequence, without the per-state dumps.

## What this shows

1. **The probe reproduces outside the original machine.** V03 violates `ProposalProgress` and `CompletionProgress` with a counterexample of the same shape as the original: 657 states (152 prefix replays, one leader transfer, then service and tick steps) looping back to state 466. The only difference is that the leader transfer comes one step earlier (state 178 instead of 179). V02 passes with exactly the original 3,177 distinct states. The V03 state count is lower than the original 3,236 because this TLC version found the violation at an earlier liveness check.
2. **The property is what catches B, not the prefix alone.** With the same prefix, schedule and budget but only the safety invariants, the search covers its whole space in 28 s and finds nothing.
3. **Ordinary search from Init does not reach the scenario.** With 10 times the original budget it explores about 3 million states but only to depth 3. The counterexample is 657 steps long.
4. **The prefix is what makes the progress check affordable.** `C03Free` with the full prefix behaves like the probe (`free-153-v03`). Freeing only the last two inputs, the configuration change and its proposal, finds nothing in 600 s. Given an hour it finds the same counterexample (657 states, back to state 466) after 3,275 s and 80,882 distinct states, about 24 times the probe's time and 26 times its states. On V02 the same search covers its whole space (90,301 states) with no error, so the driver does not raise a false alarm. Freeing the campaign as well, or starting at Init, finds nothing in 600 s, and the Init start finds nothing in an hour (depth 453).

So in the original comparison the property and the budget changed together with the starting point, and both matter: without the progress properties the prefix finds nothing, and without the prefix the progress properties do not get there within the budget.

## What this does not show

- **A fully open search with the progress properties.** `C03Free` frees when the three recorded inputs happen, not which inputs exist, and it keeps the probe's serialized network and fixed service order. The C03 properties are tied to this scenario (the joint configuration at index 5), so a wider input set would need different properties.
- **Other search strategies.** Everything here is TLC breadth-first search with one worker. Simulation or depth-first search from Init was not tried.
- **Bug A.** Its trace is not in the branch.
- **Generality.** This is one bug on one machine. States here are large, and TLC generates only about 2,000 distinct states a minute, so the times say little about other models.

## Running

```sh
python3 run.py                       # all runs, one after another
python3 run.py probe-v03 --jobs 2    # selected runs; each TLC run uses one worker
python3 run.py free-151-v03 --seconds 3600   # longer budget, saved as results/free-151-v03-3600s
python3 run.py --summarize           # rebuild results/summary.md from saved logs
```

`TLA2TOOLS` and `COMMUNITY_MODULES` point to the jars. They default to `lib/tla2tools.jar` and `lib/CommunityModules-deps.jar` in the Specula checkout. TLC works in a temporary directory, and only the trimmed log and `run.json` are kept under `results/`.
