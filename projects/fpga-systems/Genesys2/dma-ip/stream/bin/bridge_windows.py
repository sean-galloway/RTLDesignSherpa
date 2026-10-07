# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Single source of truth for the char-harness BRIDGE SLAVE WINDOWS.

The bridge analog of stream_addrs.A() and harness_addrs.H(): a bridge slave's
base/limit is resolved BY NAME from the same TOML the bridge generator reads,
so RTL and host can never disagree about where a window lives.

    from bridge_windows import W
    base, limit = W("comp_sram")
    bridge.write(A("MON_GROUP_BASE_ADDR"),  base)
    bridge.write(A("MON_GROUP_LIMIT_ADDR"), limit)

NEVER hardcode a window address in a host tool. Retyped copies are how the perf
counters read back zero for a week: the monitor block moved to 0x1000 and about
seven pasted copies of the old base stayed behind, each of them individually
plausible. There is one config; read it.

`limit` is INCLUSIVE (base + addr_range - 1), which is what the monbus group's
cfg_limit_addr expects -- it compares `addr <= limit`.
"""

from __future__ import annotations

import tomllib
from functools import lru_cache
from pathlib import Path
from typing import Tuple

_CONFIG_DIR = Path(__file__).resolve().parents[1] / "rtl" / "bridges" / "configs"

# The two build flavours ride different bridges. "mon" is the monitor build
# (tallies + comp_sram); "char" is the perf build (debug_sram, no monitors).
_CONFIGS = {
    "mon":  _CONFIG_DIR / "bridge_stream_mon_axil.toml",
    "char": _CONFIG_DIR / "bridge_stream_char_axil.toml",
}

# Where STREAM's in-core monbus group dumps its bulk-trace records.
#
# BOTH Genesys 2 builds -- build-perf and build-mon -- instantiate the SAME
# harness and the SAME bridge (stream_harness.sv line ~487 instantiates
# bridge_stream_mon_axil unconditionally; both Makefiles regen only that one).
# So there is ONE address map here and the capture memory is always comp_sram.
# USE_AXI_MONITORS changes what is BUILT INSIDE the harness, not which bridge
# wraps it -- do not switch address maps on it.
#
# bridge_stream_char_axil is generated in this tree but instantiated by nothing
# in it; only the older NexysA7 stream_char harness used it.
_CAPTURE_SLAVE = "comp_sram"


@lru_cache(maxsize=None)
def _slaves(bridge: str = "mon") -> dict:
    if bridge not in _CONFIGS:
        raise KeyError(f"unknown bridge {bridge!r}; have: {', '.join(sorted(_CONFIGS))}")
    cfgpath = _CONFIGS[bridge]
    if not cfgpath.is_file():
        raise FileNotFoundError(f"bridge config not found: {cfgpath}")
    with cfgpath.open("rb") as fh:
        cfg = tomllib.load(fh)
    out = {}
    for s in cfg.get("bridge", {}).get("slaves", []):
        name = s.get("name")
        if name is None or "base_addr" not in s:
            continue
        base = int(str(s["base_addr"]), 0)
        rng = int(str(s.get("addr_range", "0")), 0)
        out[name] = (base, rng)
    if not out:
        raise ValueError(f"no addressed slaves parsed from {cfgpath}")
    return out


def W(name: str, bridge: str = "mon") -> Tuple[int, int]:
    """Return (base, inclusive_limit) for bridge slave `name`."""
    slaves = _slaves(bridge)
    if name not in slaves:
        raise KeyError(f"no bridge slave {name!r} on {bridge!r} bridge; "
                       f"have: {', '.join(sorted(slaves))}")
    base_, rng = slaves[name]
    if rng <= 0:
        raise ValueError(f"bridge slave {name!r} has no addr_range")
    return base_, base_ + rng - 1


def base(name: str, bridge: str = "mon") -> int:
    return W(name, bridge)[0]


def monbus_capture_window() -> Tuple[int, int]:
    """(base, inclusive_limit) for STREAM's in-core monbus capture memory.

    Always comp_sram: one harness, one bridge, one map. It was hardcoded
    0x40000 for years, which is the TALLY in this bridge -- and the tally's
    write side is SLVERR-terminated now that the observers feed it directly, so
    the old constant aims records at a slave that rejects them.
    """
    return W(_CAPTURE_SLAVE, bridge="mon")


if __name__ == "__main__":
    for flavour in sorted(_CONFIGS):
        print(f"--- {flavour} bridge ---")
        for n, (b, r) in sorted(_slaves(flavour).items(), key=lambda kv: kv[1][0]):
            tag = ("  <-- monbus capture" if (flavour == "mon" and n == _CAPTURE_SLAVE)
                   else "")
            print(f"  {n:20s} 0x{b:08X} .. 0x{b + r - 1:08X}  ({r // 1024:>4} KB){tag}")
