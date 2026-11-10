Validation scope: proposed edits only, using the supplied packet. No global protocol campaign, repository integration, independent generation score, or complete property coverage claim.

The generic runner/protocol are unchanged. `go-adapter` only renames its private avInput type to avoid the supplied campaign test's name. Each manifest specifies `--source versions/Vxx/source`. `adapter/LocalActions.tla` calls the original supplied behavior operators; its added observers use actual pre/input/post states. Failed invocations remain in their original directories and do not contribute passes.

Reproduce from /workspace (choose a new output tag):

    python3 out/validation/run_observed.py fresh-tag
    python3 out/validation/witnesses.py fresh-tag
    python3 out/validation/run_witnesses.py fresh-witness-tag
    python3 out/validation/native_quorum.py
    python3 -m unittest discover -s out/framework -p test_runner.py

Do not run `build.py` alone to replace the final case set: initial assembly is `build.py`, `add_cases.py`, then `add_config_cases.py`. These scripts assemble descriptors, not successors or property truth. The checked-in cases.json is the authoritative executed domain. `build_checks.py` generates the observation binding and Checks modules. The final executable witness files and their passed logs are preserved under ../revised-spec/Vxx.

TLC evaluates the original, candidate and control operators. Python only serializes type-mapped records, invokes engines, and combines their outputs. Witnesses.tla evaluates 97 explicitly expected truth pairs in three one-state finite tests. Real Go/TLA action results are separate from constructed negative observations. NativeQuorum additionally executes V00's original Step on its native flat type and V01 Step on the full joint type, exporting nonempty original commit-use records.

Property truth labels are operator-specific: replay `old` for Ack is HistoricalV00!AckPreservation, for Ready/Vote it is HistoricalV01, and for campaign/proposal it is the supplied current base definition (the unrevised oracle); `frozen` means supplied current base. The standalone tables also evaluate the new candidate directly on real old-version observations. For newly added transfer-callback coverage, old truth is explicitly not-observed, never a vacuous TRUE.

Original base.tla and all copied behavior modules are byte-identical to the version snapshots. Maintenance adds a ghost audit and wrappers around the original Next; no protocol guard reads audit. It preserves the global IsSingleton helper, including its read behavior. Maintenance.cfg and selected-invariants.json list the selected suite; historical base/MC/Update/Trace configs are retained. Only witness configs were model-checked. No temporal property was selected or validated.

Final replay roots are replay-V01-final-review, replay-V02-final-review, and replay-V03-final. Passed witness logs are V01/V02 witnesses-final-old-auto.log and V03 witnesses-03.log. The archived validation draft that overconstrained V01/V02 pending preservation is rejected; the final candidate permits a corrected index.
