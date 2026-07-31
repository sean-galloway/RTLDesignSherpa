# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Path setup for the pumice sequence area.

The sequences live here; the drivers they call (`ddr2_char.DDR2CharDriver`,
`pumice_master.SimpleTest`) are build collateral and live in a build's `host/`.
This module is the ONE place that knows that, so no sequence carries a
`sys.path.insert` of its own.

Which build's drivers to use is a choice, not a constant: the LiteDRAM build
has its own host/ (same harness, no pumice-CSR config). `PUMICE_BUILD` selects
it, defaulting to the perf build.
"""

from __future__ import annotations

import os
import sys

# Sequence area -> repo root is five levels up
# (projects/fpga-systems/NexysA7/pumice/bin -> repo root).
_HERE = os.path.dirname(os.path.abspath(__file__))
_AREA = os.path.dirname(_HERE)
_FALLBACK_ROOT = os.path.abspath(os.path.join(_HERE, "..", "..", "..", "..", ".."))

FPGA_BIN_REL = "fpga/bin"
DEFAULT_BUILD = "perf"


def repo_root() -> str:
    env = os.environ.get("REPO_ROOT")
    if env and os.path.isdir(os.path.join(env, "fpga", "bin")):
        return env
    return _FALLBACK_ROOT


def flow_host_dir(build: str | None = None) -> str:
    """Where a build's host drivers live (sibling of this sequence area)."""
    build = build or os.environ.get("PUMICE_BUILD") or DEFAULT_BUILD
    return os.path.join(_AREA, f"build-{build}", "host")


def setup_paths() -> None:
    """Put the shared fpga/bin layer and the pumice flow host on sys.path.

    Idempotent, so every sequence module can call it at import time without
    caring who else already did.
    """
    for path in (os.path.join(repo_root(), FPGA_BIN_REL), flow_host_dir(), _HERE):
        if os.path.isdir(path) and path not in sys.path:
            sys.path.insert(0, path)


setup_paths()
