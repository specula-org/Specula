"""Specula was renamed to Specular.

Installs made before the rename run ``specula.cli:main`` with ``src/`` on
``sys.path``; importing this package tells them how to switch instead of
failing with an ImportError.
"""

import sys

sys.stderr.write(
    "Specula has been renamed to Specular. Switch once by running this in your checkout:\n"
    "\n"
    "    uv tool uninstall specula && uv tool install -e .\n"
    "\n"
    "Then use `specular` instead of `specula`. For the remaining steps, see\n"
    '"Switching from Specula" in docs/Usage.md.\n'
)
raise SystemExit(1)
