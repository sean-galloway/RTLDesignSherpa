# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Single source of truth for STREAM APB register addresses.

Every STREAM register address is resolved BY NAME from the generated
`stream_regmap.py` (PeakRDL output). NEVER hardcode addresses in the TB or host
tools: when the RDL / address map changes (e.g. the monitor block relocating to
0x1000+), only the regmap regenerates and every consumer follows automatically.
This module is the shim that turns a register name into its absolute address.

    from stream_addrs import A
    bridge.write(A("SCHED_CONFIG"), 0x0F)
    perf = bridge.read(A("RDMON_PERF_PROD_CYCLES"))
"""

from __future__ import annotations

import contextlib
import io
import logging
import os
from functools import lru_cache
from typing import Optional

from TBClasses.apb.register_map import RegisterMap

STREAM_APB_BASE = 0x0000_0000   # STREAM APB window base in the char harness map


def _default_regmap() -> str:
    env = os.environ.get("STREAM_REGMAP")
    if env:
        return env
    d = os.path.dirname(os.path.abspath(__file__))
    for _ in range(12):
        cand = os.path.join(d, "projects/components/dmas/stream/rtl/stream_regmap.py")
        if os.path.isfile(cand):
            return cand
        d = os.path.dirname(d)
    raise FileNotFoundError("stream_regmap.py not found; set STREAM_REGMAP")


@lru_cache(maxsize=1)
def _regmap(path: Optional[str] = None) -> RegisterMap:
    log = logging.getLogger("stream_addrs")
    log.addHandler(logging.NullHandler())
    with contextlib.redirect_stdout(io.StringIO()):
        return RegisterMap(path or _default_regmap(), 32, 32, 0, log)


def A(name: str, base: int = STREAM_APB_BASE) -> int:
    """Absolute address of a STREAM register, by name (base + regmap offset)."""
    regs = _regmap().registers
    if name not in regs:
        raise KeyError(f"unknown STREAM register {name!r}")
    return (base + int(regs[name]["address"], 16)) & 0xFFFF_FFFF


def has(name: str) -> bool:
    return name in _regmap().registers


def compose(name: str, **fields: int) -> int:
    """Compose a register word by setting named FIELDS from the regmap.

    The mandated pattern for all testing: set register fields individually by
    name (each placed at its regmap offset/width) rather than hand-assembling a
    bitmask -- a hardcoded mask silently drifts when the RDL changes (e.g. a new
    field shifting RSVD). Unspecified fields keep the register's reset default.

        bridge.write(A("SCHED_CONFIG"),
                     compose("SCHED_CONFIG", SCHED_EN=1, RD_PREFETCH_EN=1))
    """
    info = _regmap().registers.get(name)
    if info is None:
        raise KeyError(f"unknown STREAM register {name!r}")
    word = int(info.get("default", "0x0"), 16)
    for fname, val in fields.items():
        fld = info.get(fname)
        if not isinstance(fld, dict) or "offset" not in fld:
            raise KeyError(f"unknown field {name}.{fname}")
        off = fld["offset"]
        if ":" in off:
            hi, lo = (int(x) for x in off.split(":"))
        else:
            hi = lo = int(off)
        mask = ((1 << (hi - lo + 1)) - 1) << lo
        word = (word & ~mask) | ((int(val) << lo) & mask)
    return word & 0xFFFF_FFFF


def write_reg(bridge, name: str, **fields: int) -> int:
    """Set fields by name (see compose) then write the register to hardware.
    Returns the word written."""
    word = compose(name, **fields)
    bridge.write(A(name), word)
    return word
