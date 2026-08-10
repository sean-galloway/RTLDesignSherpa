# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Path setup for the stream area (Genesys 2).

This module is the ONE place that knows where the layers are, so no host
program or sequence carries a `sys.path.insert` of its own. Mirrors
`pumice/bin/pumice_env.py`.

Three layers, in the order a host program needs them:

  * the shared FPGA layer  -- `uart_link`, `board`, `uart_axi_bridge`
  * this area's `bin/`     -- the host libraries SHARED by every build here
                              (harness_addrs, stream_addrs, stream_device,
                              characterization, descriptor_builder,
                              harness_kick)
  * a build's `host/`      -- that build's own programs and drivers

Which build is a choice, not a constant: build-mon and build-perf have separate
host layers over the same shared libraries. `STREAM_BUILD` selects one,
defaulting to the monitor build.

NOTE the deliberate omission: `uart_axi_bridge` is NOT reached through
`projects/components/converters/bin`. That path still holds a compatibility
shim whose own docstring says new code must not import through it -- the real
module lives in the shared FPGA layer, which `fpga_bin()` finds.
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
DEFAULT_BUILD = "mon"


def _is_shared_layer(path: str) -> bool:
    return os.path.isfile(os.path.join(path, FPGA_BIN_MARKER))


def fpga_bin() -> str:
    """Locate the shared board/UART layer.

    Found by searching UPWARD for the marker file rather than by counting
    directory levels -- see [[flow-layout]] "Anchor paths, never count
    directory levels". The stream host programs used to hand-count their way
    to a sibling flow (`../../flows-stream-bridge/host`), which the move to
    `projects/fpga-systems` would have broken silently.
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
    layer = fpga_bin()   # .../projects/fpga-systems/bin -> root is three up
    return os.path.dirname(os.path.dirname(os.path.dirname(layer)))


def build_host_dir(build: str | None = None) -> str:
    """Where a build's host programs live (sibling of this shared bin/)."""
    build = build or os.environ.get("STREAM_BUILD") or DEFAULT_BUILD
    return os.path.join(_AREA, f"build-{build}", "host")


def setup_paths() -> None:
    """Put the flow-local layers on sys.path.

    Idempotent, so every module can call it at import time without caring who
    else already did.

    Scope is deliberately narrow: the shared FPGA layer, this area's shared
    libraries, and the selected build's host layer. Repo-wide packages --
    `TBClasses` and friends -- come from `env_python`, which owns PYTHONPATH.
    Adding them here would give the repo two path authorities that could
    disagree.
    """
    for path in (fpga_bin(), build_host_dir(), _HERE):
        if os.path.isdir(path) and path not in sys.path:
            sys.path.insert(0, path)


setup_paths()
