"""Pytest wrapper over the stdlib characterization oracle.

The real logic lives in `oracle.py` (stdlib-only, runnable without pytest while
the repo .venv is broken — see memory reference_broken_venv_pytest). This thin
wrapper lets step 2's CI discover the same cases via `pytest`.

Run:  pytest tests/characterization/          (once pytest works in the venv)
Regen golden:  python3 tests/characterization/oracle.py --update
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import oracle  # noqa: E402


@pytest.mark.parametrize("name", list(oracle.CASES))
def test_matches_golden(name: str) -> None:
    gp = oracle.golden_path(name)
    assert gp.exists(), f"missing golden for {name!r}; run: oracle.py --update"
    assert oracle.CASES[name]() == gp.read_text(), (
        f"{name} diverged from golden; inspect with: python3 tests/characterization/oracle.py --check -k {name}"
    )
