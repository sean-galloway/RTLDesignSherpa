"""Python view of ``rtl/stream_cfg_pkg.sv`` -- read, never copied.

The SystemVerilog package ``stream_char_cfg_pkg`` is the one source for the
STREAM characterization geometry: the board top and every cosim elaborate from
it.  The cocotb layer needs a few of those values too (``NUM_CHANNELS`` decides
how many channels a testbench drives), and the obvious shortcut -- retyping the
number in Python -- is what this module exists to prevent.

That shortcut had already bitten: ``test_stream_mon.py`` passed
``NUM_CHANNELS`` to the testbench as ``rtl_parameters.get('NUM_CHANNELS', 4)``
while never putting ``NUM_CHANNELS`` into ``rtl_parameters`` at all, so the
literal ``4`` won every time -- against RTL that elaborated 8.  Half the built
channels were never driven, and nothing reported a mismatch.

So this parses the package instead.  If a value moves in the ``.sv``, it moves
here on the next run, and a typo raises instead of silently returning a stale
default.
"""

from __future__ import annotations

import os
import re
from functools import lru_cache

# rtl/stream_cfg_pkg.sv, relative to this file (dv/ and rtl/ are siblings).
_PKG_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), os.pardir, "rtl", "stream_cfg_pkg.sv"
)

# `parameter int CFG_NAME = 123;` / `parameter bit CFG_NAME = 1'b0;`
_PARAM_RE = re.compile(
    r"^\s*parameter\s+(?:int|bit|logic)\s+(CFG_\w+)\s*=\s*"
    r"(?:\d+'[bdh])?([0-9_]+)\s*;",
    re.MULTILINE,
)


@lru_cache(maxsize=1)
def cfg() -> dict[str, int]:
    """Every ``CFG_*`` parameter in the package, as ints."""
    with open(_PKG_PATH, encoding="utf-8") as fh:
        text = fh.read()

    values = {m.group(1): int(m.group(2).replace("_", ""), 0) for m in _PARAM_RE.finditer(text)}
    if not values:
        raise RuntimeError(
            f"parsed no CFG_* parameters from {_PKG_PATH} -- the package format "
            "changed and this parser did not. Fix the parser; do not hardcode "
            "the values at the call site."
        )
    return values


def cfg_int(name: str) -> int:
    """One ``CFG_*`` value. Raises if absent -- never falls back to a literal."""
    try:
        return cfg()[name]
    except KeyError:
        raise KeyError(
            f"{name} is not in stream_char_cfg_pkg ({_PKG_PATH}). "
            f"Available: {sorted(cfg())}"
        ) from None


def verilator_unroll_args() -> list[str]:
    """Verilator unroll budget for elaborating the harness with monitors ON.

    The monitor per-slot loops do delayed array assignment, so Verilator must
    unroll them or it emits BLKLOOPINIT and refuses to build. The budget has to
    cover the DEEPEST loop in the design, and that depth is derived, not fixed:
    stream_core sizes its monitor CAMs as
        MAX(16, NUM_CHANNELS * Ax_MAX_OUTSTANDING + MON_TRANS_MARGIN)
    which at 8 channels x 8 outstanding + 8 is 72 slots.

    4096/20000 was sized when AR/AW was 2 (a 24-slot table). At the package's
    8 it leaves 6 BLKLOOPINIT errors in axi_monitor_timeout; 16384/200000
    elaborates clean. Measured 2026-08-25/26, monitors ON.

    This lives here because the number was copy-pasted into SEVEN run() calls
    across three test files, and raising it in two of them while monitors
    became default-on in the package is exactly how build-perf's four ext_*
    tests started failing to compile. One source, one place to raise it.

    NOTE this is a TOOL limit, not a design one -- it says nothing about
    whether the RTL closes timing. Do not let it acquire a design rationale.
    """
    return ["--unroll-count", "16384", "--unroll-stmts", "200000"]


def num_channels() -> int:
    """Channels the harness elaborates, unless a test overrides SIM_NUM_CHANNELS.

    Both the RTL parameter and the value handed to the testbench must come from
    here, or they drift apart the way they already did once.
    """
    return int(os.environ.get("SIM_NUM_CHANNELS", cfg_int("CFG_NUM_CHANNELS")))
