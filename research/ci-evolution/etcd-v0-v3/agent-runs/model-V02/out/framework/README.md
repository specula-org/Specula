This reusable action-validation framework executes actual Go and original TLA+ actions. `runner.py`, `protocol.schema.json` and `test_runner.py` are unchanged from the supplied hardened framework. The runner compares actual mapped inputs and pre-states before outputs; unordered paths retain multiplicity. Failed commands contribute no results, and every invocation requires fresh output/work directories.

From the workspace root, rerun the complete V02 suite with unique directories:

```sh
python3 out/framework/targets/etcd/replay.py
```

The script prints its output root. It runs both directions against `new/spec` and `out/repaired-spec`, the 21-case old-version delta subset, and the separate six-case invalid-input domain. `targets/etcd/suite.json` is the portable suite manifest. `manifest.json` and `manifest-old.json` bind the generic runner to the source adapters. Paths are relative to the workspace; supplied Go/JAR locations and the local dependency overlay are prerequisites. The supplied go.mod files reference `/workspace/deps/legacy-pkg`; this task's supported root is `/workspace`.

A single comparison is also reusable:

```sh
python3 out/framework/runner.py --manifest out/framework/targets/etcd/manifest.json --cases out/cases/code-inputs.json --output out/cases/my-fresh-run --spec out/repaired-spec --route code-to-model
```

Use `--cases out/framework/targets/etcd/model-seeds.json --route model-to-code` for TLC-generated cases. Every case is exported, including an explicitly mapped disabled Ready prerequisite or tested action after a successful TLC run. Parsing/evaluation failures remain adapter errors; they never become disabled results.

The final recorded suite is `out/cases/v02-final-02`. `out/results.json` and `out/report.md` contain counts, evidence, source-backed repairs, timing and limitations. Preserve all baseline and diagnostic directories. `prior-*` inputs remain immutable reusable inputs. `domain_v02.py` enriches their descriptors and adds V02 cases; `ModelDomains.tla` builds finite symbolic inputs, never expected successors. `LocalActions.tla` invokes the original `Step`, `ApplyConfCore`, `Restore`, `RestartCore`, `ProtocolReady`, and `ProtocolAdvance` operators/actions. Advance preparation runs original Ready and intervening original Step calls before comparing the captured batch and actual pre-state.

`adapters/go/action_validation_test.go` contains package-local setup/call/projection glue. `run.py` installs it into the selected source tree; old-source spelling/API changes are explicit. Production source remains unchanged. Node ownership cases run the real `node.run` goroutine and channels, using `Status` as an execution barrier. Go uses a 90-second outer timeout, GOMAXPROCS=2, offline modules and workspace-local build/temp paths. Each local TLC invocation has one worker, 2 GB heap and a 175-second timeout. No safety invariants or global protocol search run here.

Additional verification:

```sh
python3 -m unittest discover -s out/framework -p test_runner.py -v
python3 out/framework/targets/etcd/audit_inputs.py out/cases/code-inputs.json out/cases/model-inputs.json
python3 out/framework/targets/etcd/summarize.py --run-root out/cases/v02-final-02
```

The deliberately invalid snapshot cases fail the structural audit and remain outside supported-domain conformance totals. See `targets/etcd/observations.md` for mapping and validity assumptions. Observer proposals are kept separately in `out/adaptation/observer-corrections.patch`, unapplied.
