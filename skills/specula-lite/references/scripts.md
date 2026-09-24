# Lite scripts

These helpers use Python 3.10+ and its standard library. Run them by their absolute installed paths; no working copy of Specula is needed.

## Preparation

`python3 scripts/prepare.py` prints JSON containing `java`, `jars`, `guides`, and `shared`. It reuses a working Java 21+ from `JAVA_HOME` or `PATH`, or prepares a pinned Temurin JRE in the user cache. TLA+ and CommunityModules JARs are pinned and checksum-verified. Downloads need network access only on first use. The downloaded JRE supports Linux (glibc), macOS, and Windows on x64/arm64; an existing compatible Java also works on other platforms.

`SPECULA_LITE_CACHE` overrides the cache directory. `SPECULA_LITE_JAVA` selects an existing Java executable. Neither helper edits shell profiles, agent settings, or the system Java installation. Preparation never starts a model check.

## Parsing and checking

```bash
python3 scripts/tlc.py parse base.tla --log output/parse.log
python3 scripts/tlc.py check MC.tla --config MC.cfg --log output/check.log
python3 scripts/tlc.py check MC.tla --config MC.cfg --log output/simulation.log -- -simulate num=10000 -depth 100
```

`--heap` defaults to `1g`; `--workers` defaults to `1`. Adjust these to the available machine. Arguments after `--` go directly to TLC (or SANY in parse mode). There is no automatic wall-clock deadline. Choose finite model bounds or finite simulation campaigns, and record them with the result.

The model's parent directory is the process working directory. Relative config paths resolve there; relative log paths resolve from the caller's working directory. Existing logs, receipts, and counterexample dumps are not overwritten. All process output goes to the log; its neighboring `.run.json` records the command, start/end times, and exit code. Model checks also save JSON counterexamples to `.trace.json` beside the log when a violation occurs; do not pass another `-dumptrace` option. The runner returns the underlying process exit status. An invariant violation is normally a nonzero exit and requires inspecting the log, not retrying blindly. Interrupting the runner terminates its child and records interruption.

## Reading results

`read_tlc.py` exposes the standard Specula TLC Output Reader CLI, with no MCP dependency:

```bash
python3 scripts/read_tlc.py output/check.log --summary --json
python3 scripts/read_tlc.py output/check.log --states 1:5
python3 scripts/read_tlc.py output/check.log --state last --var currentTerm.s1
python3 scripts/read_tlc.py output/check.log --diff -2 -1
python3 scripts/read_tlc.py output/check.log --track currentTerm
```

Supply a log containing a text counterexample or a `CounterExample written:` reference to a JSON dump. Logs without a counterexample are not accepted by this reader. This helper only unpacks local shared resources; it does not download Java or JARs. Consult the original log and process result for syntax errors, evaluation errors, interrupted exploration, and completion status.
