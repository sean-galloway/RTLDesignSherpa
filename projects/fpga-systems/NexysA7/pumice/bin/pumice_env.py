# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Path setup for the pumice sequence area.

The sequences live here; the pumice drivers they call
(`ddr2_char.DDR2CharDriver`, `pumice_master.SimpleTest`) still live with the
build flow at `projects/NexysA7/ddr2-characterization/flows-ours-uart/host/`.
This module is the ONE place that knows that, so no sequence carries a
`sys.path.insert` of its own.
"""

from __future__ import annotations

import os
import sys

# Sequence area -> repo root is five levels up
# (projects/fpga-systems/NexysA7/pumice/bin -> repo root).
_HERE = os.path.dirname(os.path.abspath(__file__))
_FALLBACK_ROOT = os.path.abspath(os.path.join(_HERE, "..", "..", "..", "..", ".."))

FLOW_HOST_REL = ("projects/NexysA7/ddr2-characterization/"
                 "flows-ours-uart/host")
FPGA_BIN_REL = "fpga/bin"


def repo_root() -> str:
    env = os.environ.get("REPO_ROOT")
    if env and os.path.isdir(os.path.join(env, "fpga", "bin")):
        return env
    return _FALLBACK_ROOT


def flow_host_dir() -> str:
    """Where the pumice host drivers live."""
    return os.path.join(repo_root(), FLOW_HOST_REL)


def setup_paths() -> None:
    """Put the shared fpga/bin layer and the pumice flow host on sys.path.

    Idempotent, so every sequence module can call it at import time without
    caring who else already did.
    """
    for path in (os.path.join(repo_root(), FPGA_BIN_REL), flow_host_dir(), _HERE):
        if os.path.isdir(path) and path not in sys.path:
            sys.path.insert(0, path)


setup_paths()
