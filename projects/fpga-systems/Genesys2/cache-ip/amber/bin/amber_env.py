# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Path setup for the amber Genesys2 area.

Mirrors the stream/pumice env pattern: one place that knows where the layers
are, so no host program or sequence carries a hand-counted `sys.path.insert`.

Layers (in host-program search order):
  * shared FPGA layer  -- uart_link, board, uart_axi_bridge
  * this area's bin/   -- sequences and area-wide libraries
  * this area's host/  -- board drivers and host programs
"""

from __future__ import annotations

import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_AREA = os.path.dirname(_HERE)

FPGA_BIN_REL = os.path.join("projects", "fpga-systems", "bin")
FPGA_BIN_MARKER = "uart_link.py"


def _is_shared_layer(path: str) -> bool:
    return os.path.isfile(os.path.join(path, FPGA_BIN_MARKER))


def fpga_bin() -> str:
    """Locate the shared board/UART layer by walking up from here."""
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
        if parent == here:
            break
        here = parent
    raise FileNotFoundError(
        f"shared FPGA layer not found (looking for {FPGA_BIN_REL}/"
        f"{FPGA_BIN_MARKER}); set REPO_ROOT to the repository root"
    )


def repo_root() -> str:
    """Repository root derived from the shared layer location."""
    env = os.environ.get("REPO_ROOT")
    if env and _is_shared_layer(os.path.join(env, FPGA_BIN_REL)):
        return env
    layer = fpga_bin()
    return os.path.dirname(os.path.dirname(os.path.dirname(layer)))


def setup_paths() -> None:
    """Put the shared FPGA layer, area bin/, and area host/ on sys.path."""
    host_dir = os.path.join(_AREA, "host")
    for path in (fpga_bin(), host_dir, _HERE):
        if os.path.isdir(path) and path not in sys.path:
            sys.path.insert(0, path)


setup_paths()
