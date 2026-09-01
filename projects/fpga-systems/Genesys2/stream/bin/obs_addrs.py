# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""By-name addresses for the axi4_intf_master_observer's own regblock (obs_regs).

The observer owns its configuration since it grew an APB slave, so it needs the
same by-name accessor every other block has. Without one, callers hardcode
`0x0019_0000 + offset`, which is the split-proof this repo has already been
bitten by twice (the monitor block moving to 0x1000 broke the perf path; a
12-bit APB window silently aliased MON addresses onto GLOBAL_CTRL).

Mirrors stream_addrs.A / harness_addrs.H:

    from obs_addrs import O
    bridge.write(O("AXI_PKT_MASK"), 0)

The base is the obs_apb slave in the stream bridge map
(rtl/bridges/configs/bridge_stream_mon_axil.toml). It lives HERE, once.
"""
from __future__ import annotations

import importlib.util
import os

OBS_APB_BASE = 0x0019_0000     # obs_apb slave, bridge_stream_mon_axil.toml

# The harness has TWO observers, each with its own obs_regs_top instance behind
# its own APB window: the MASTER-role observer on STREAM's own port (above), and
# the SLAVE-role observer on the DMA slaves' port (below). Same register map,
# different base -- so both are addressed with O(name, base=...).
#
# This base used to live in slvmon_device, which describes the RETIRED
# dma_slave_monitors regblock. host_reg_walk was its last consumer, so the base
# lived in a module nobody could delete without breaking the walk. It belongs
# here, with the block it actually addresses. (STREAM TASK-073.)
SLAVE_OBS_APB_BASE = 0x0018_0000   # slvmon_apb slave -> u_slave_observer

_REGS = None


def _regmap_path() -> str:
    here = os.path.dirname(os.path.abspath(__file__))
    root = os.environ.get("REPO_ROOT") or os.path.abspath(
        os.path.join(here, *([".."] * 5)))
    return os.path.join(
        root, "projects/components/misc/rtl/regs/generated/obs_regs_top_regmap.py")


def registers() -> dict:
    global _REGS
    if _REGS is None:
        path = _regmap_path()
        spec = importlib.util.spec_from_file_location("obs_regs_regmap", path)
        m = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(m)
        for attr in dir(m):
            if attr.startswith("_"):
                continue
            cand = getattr(m, attr)
            if isinstance(cand, dict) and cand:
                first = next(iter(cand.values()))
                if isinstance(first, dict) and ("address" in first or "offset" in first):
                    _REGS = cand
                    break
        if _REGS is None:
            raise KeyError(f"no register dict in {path}")
    return _REGS


def O(name: str, base: int = OBS_APB_BASE) -> int:
    """Absolute address of an observer register, by name."""
    regs = registers()
    if name not in regs:
        raise KeyError(f"unknown OBS register {name!r} "
                       f"(have {len(regs)}: {sorted(regs)[:6]}...)")
    r = regs[name]
    return (base + int(str(r.get("address", r.get("offset"))), 0)) & 0xFFFF_FFFF


def has(name: str) -> bool:
    return name in registers()
