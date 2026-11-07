# Local action-validation prototype

The generic JSON protocol and runner are in `out/framework`. The Go and TLC adapters bind exact implementation calls and original model actions. `versions/V01..V03` and per-version manifests provide the reproducible etcd experiment. All edits are experiment-only.

Run from this packet inside the recorded sandbox, replacing the output with a new path:

```sh
python3 out/framework/runner.py --manifest manifests/V03.json --cases code-inputs.json --output out/my-code-check --spec versions/V03/spec --route code-to-model
python3 out/framework/runner.py --manifest manifests/V03.json --cases model-seeds.json --output out/my-model-check --spec versions/V03/spec --route model-to-code
```

The outer runner is `../../control/run_agent.py:sandbox`; the complete non-AI setup and replay commands are in `../../control/final_action_framework_replay.py` and `../../control/complete_final_framework_replay.py`. Source dependencies are supplied in `deps`; Go and TLC caches/artifacts are isolated. The adapter-generation instruction is `out/framework/regenerate-adapters.md`. A different target/language supplies new adapters, input domains and mappings while retaining the generic protocol/runner. Only Go has been experimentally validated.

Read `out/final-results.json` for the accepted matrix and source hashes. Each version matched 479 code-derived and 174 model-derived instances. These are overlapping, locally constructed domains, not global reachability or a conformance proof. Native Node channel cases use controlled schedules. Terminal-panic internal message order has the explicit scope documented at `../../control/terminal-panic-observation.md`.

Both actual pre-state and actual input must agree before comparing post-state, return, messages and side effects. Enabled/disabled, unsupported setup, behavior mismatch, and invocation failure remain distinct evidence. Failed processes never provide successful observations; every output/work directory must be new.

TLC now writes all completed observations to an append-only invocation journal. A case with more than one distinct observation is reported unsupported, with alternatives retained; it is never accepted by overwriting one successor. This version requires a deterministic observable action under its chosen input/schedule. General nondeterministic relations need a relation-valued protocol or a more precise observation/schedule binding. Neither repeated sampling nor one selected successor proves bidirectional inclusion.

The runner is diagnostic: exit 0 is not a correctness verdict. Accept only a nonempty run with every declared case matching, no unsupported/mapping errors, no failed commands and no extra results. Before integration, a CI gate should enforce that report condition explicitly.
