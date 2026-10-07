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

_HERE = os.path.dirname(os.path.abspath(__file__))
_AREA = os.path.dirname(_HERE)

# The shared layer's location relative to the repo root, and the file that
# proves a candidate directory really is it.
FPGA_BIN_REL = os.path.join("projects", "fpga-systems", "bin")
FPGA_BIN_MARKER = "uart_link.py"
DEFAULT_BUILD = "perf"


def _is_shared_layer(path: str) -> bool:
    return os.path.isfile(os.path.join(path, FPGA_BIN_MARKER))


def fpga_bin() -> str:
    """Locate the shared board/UART layer.

    Found by searching UPWARD for the marker file rather than by counting
    directory levels. The previous version counted five levels to the repo
    root; when the shared layer moved from `fpga/bin` to
    `projects/fpga-systems/bin`, every such count in the tree broke at once.
    A search costs nothing and survives the next move.
    """
    env = os.environ.get("REPO_ROOT")
    if env:
        cand = os.path.join(env, FPGA_BIN_REL)
        if _is_shared_layer(cand):
            return cand
    here = _HERE
    for _ in range(12):
        cand = os.path.join(here, FPGA_BIN_REL)
        if _is_shared_layer(cand):
            return cand
        parent = os.path.dirname(here)
        if parent == here:          # reached filesystem root
            break
        here = parent
    raise FileNotFoundError(
        f"shared FPGA layer not found (looking for {FPGA_BIN_REL}/"
        f"{FPGA_BIN_MARKER}); set REPO_ROOT to the repository root"
    )


def repo_root() -> str:
    """The repository root, derived from wherever the shared layer was found."""
    env = os.environ.get("REPO_ROOT")
    if env and _is_shared_layer(os.path.join(env, FPGA_BIN_REL)):
        return env
    # fpga_bin() -> .../projects/fpga-systems/bin; the root is three up.
    layer = fpga_bin()
    return os.path.dirname(os.path.dirname(os.path.dirname(layer)))


def flow_host_dir(build: str | None = None) -> str:
    """Where a build's host drivers live (sibling of this sequence area)."""
    build = build or os.environ.get("PUMICE_BUILD") or DEFAULT_BUILD
    return os.path.join(_AREA, f"build-{build}", "host")


def setup_paths() -> None:
    """Put the flow-local layers on sys.path.

    Idempotent, so every sequence module can call it at import time without
    caring who else already did.

    Scope is deliberately narrow: the shared FPGA layer, this build's host
    drivers, and the sequence area itself. Repo-wide packages -- `TBClasses`
    and friends -- come from `env_python`, which owns PYTHONPATH. Adding them
    here would give the repo two path authorities that could disagree.
    """
    for path in (fpga_bin(), flow_host_dir(), _HERE):
        if os.path.isdir(path) and path not in sys.path:
            sys.path.insert(0, path)


setup_paths()
