#!/usr/bin/env python3
"""Bundle unchanged shared sources into the independently installable Lite skill."""

from __future__ import annotations

import argparse
import io
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DESTINATION = ROOT / "skills/specula-lite/assets/shared.zip"
SKILLS = ("code_analysis", "spec_generation", "tla-checking-workflow", "bug-confirmation", "bug-classification")
READER_FILES = (
    "__init__.py",
    "cli.py",
    "tlc_output_reader.py",
    "trace_reader.py",
    "utils/__init__.py",
    "utils/path_parser.py",
    "utils/preprocessing.py",
)


def bundle(root: Path = ROOT) -> bytes:
    sources = {"LICENSE": root / "LICENSE"}
    for name in SKILLS:
        for path in (root / "skills" / name).rglob("*"):
            if path.is_file() and path.suffix in {".md", ".tla", ".cfg"}:
                sources[path.relative_to(root).as_posix()] = path
    for name in READER_FILES:
        sources[f"reader/{name}"] = root / "tools/inv_checking_tool/src" / name
    output = io.BytesIO()
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for name, source in sorted(sources.items()):
            entry = zipfile.ZipInfo(name, date_time=(2020, 1, 1, 0, 0, 0))
            entry.compress_type = zipfile.ZIP_DEFLATED
            entry.external_attr = 0o100644 << 16
            archive.writestr(entry, source.read_bytes())
    return output.getvalue()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check", action="store_true", help="Fail if the checked-in bundle differs from shared sources"
    )
    args = parser.parse_args()
    data = bundle()
    if args.check:
        if not DESTINATION.is_file() or DESTINATION.read_bytes() != data:
            parser.exit(1, "Lite resources changed; run python3 scripts/infra/bundle_lite.py\n")
    else:
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        DESTINATION.write_bytes(data)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
