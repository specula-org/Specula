"""Run the update coverage check on the etcd V01-V03 suites, as they are and with V2 added to the MC workloads.

The as-is suites are the final specs from `agent-runs/inv-evidence/out/revised-spec`. In the corrected copy,
every MC config with a non-empty `WorkloadKinds` also issues V2 requests, as `ordinary-v2.cfg` in the bug B
probe did for one config. Nothing else changes.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK = HERE.parent / "check.py"
SPECS = HERE.parents[1] / "etcd-v0-v3/agent-runs/inv-evidence/out/revised-spec"
VERSIONS = ("V01", "V02", "V03")
CANARIES = r"NotReached$|NotAppended$"
WORKLOAD = re.compile(r"^(\s*WorkloadKinds\s*=\s*\{)([^}]*)\}", re.M)


def add_v2(text: str) -> str:
    def patch(match: re.Match[str]) -> str:
        kinds = match.group(2).strip()
        if not kinds or '"V2"' in kinds:
            return match.group(0)
        return f'{match.group(1)}{kinds}, "V2"}}'

    return WORKLOAD.sub(patch, text)


def corrected_copy(spec: Path, destination: Path) -> Path:
    shutil.copytree(spec, destination)
    for cfg in destination.glob("MC*.cfg"):
        cfg.write_text(add_v2(cfg.read_text()))
    return destination


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("versions", nargs="*", default=list(VERSIONS), choices=VERSIONS)
    parser.add_argument("--variants", nargs="*", default=["as-is", "v2-workload"], choices=["as-is", "v2-workload"])
    parser.add_argument("--seconds", type=int, default=180)
    parser.add_argument("--jobs", type=int, default=5)
    parser.add_argument("--reports", type=Path, default=HERE / "reports")
    parser.add_argument("--rebuild", action="store_true", help="rebuild reports from saved results without TLC")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="update-coverage-etcd-") as scratch:
        for version in args.versions:
            for variant in args.variants:
                spec = SPECS / version
                if variant == "v2-workload" and not args.rebuild:
                    spec = corrected_copy(spec, Path(scratch) / version)
                out = args.reports / f"{version}-{variant}"
                command = [sys.executable, str(CHECK), "--out", str(out), "--ignore", CANARIES]
                if args.rebuild:
                    command += ["--rebuild"]
                else:
                    command += [str(spec), "--seconds", str(args.seconds), "--jobs", str(args.jobs)]
                print(f"== {version} {variant}", flush=True)
                subprocess.run(command, check=True, stdout=subprocess.DEVNULL)
                for name in ("report.md", "report.json"):
                    text = (out / name).read_text().replace(str(Path(scratch)), "$TMP")
                    (out / name).write_text(
                        re.sub(r"^# Update coverage: .*$", f"# {version}, {variant}", text, count=1, flags=re.M)
                    )


if __name__ == "__main__":
    main()
