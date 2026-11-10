Completed: [results.json](/workspace/out/results.json) and [report.md](/workspace/out/report.md).

- Repaired model: **239/239 code-derived and 103/103 model-derived matches**.
- Preserved 18 baseline mismatches; applied three behavior-only repairs.
- Generic runner, protocol and invariant predicates unchanged.
- Recorded old/new comparisons, invalid setups, observer proposals, footprint, timing and limits.

Rerun from `/workspace`:

```sh
python3 out/framework/targets/etcd/replay.py
```