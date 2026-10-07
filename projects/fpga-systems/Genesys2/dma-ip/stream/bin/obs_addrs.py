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
        root, "projects/components/utility-ip/misc/rtl/regs/generated/obs_regs_top_regmap.py")


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


# ---------------------------------------------------------------------------
# OBS_CAPS0 (0x0D0) -- the observer's self-description, and the contract every
# host campaign derives its expected classes from. Packed, not fielded; see
# the CAPS PACKING note in obs_regs.rdl. [4] PERF_CONE and [5] DEBUG_CONE read
# 0 on the lite taps REGARDLESS of TAP_ENABLE_* (78cddb5e2): the lite builds
# neither cone, and reporting the parameter would send every caps-derived
# consumer waiting for packets that can never come.
# ---------------------------------------------------------------------------
CAPS_ERROR_CONE, CAPS_TIMEOUT_CONE, CAPS_COMPL_CONE = 0x01, 0x02, 0x04
CAPS_THRESHOLD_CONE, CAPS_PERF_CONE, CAPS_DEBUG_CONE = 0x08, 0x10, 0x20
CAPS_MON_TAPS = 0x40
CAPS_N_ADDR_RANGES_SHIFT = 12

# packet type -> the OBS_CAPS0 state its emit path needs. AddrMatch rides the
# address-range checker, so it keys on N_ADDR_RANGES rather than a cone bit.
_TYPE_REQ = {
    0x0: (CAPS_ERROR_CONE, "ERROR_CONE"),
    0x1: (CAPS_COMPL_CONE, "COMPL_CONE"),
    0x2: (CAPS_THRESHOLD_CONE, "THRESHOLD_CONE"),
    0x3: (CAPS_TIMEOUT_CONE, "TIMEOUT_CONE"),
    0x4: (CAPS_PERF_CONE, "PERF_CONE"),
    0x8: ("ranges", "N_ADDR_RANGES"),
    0xF: (CAPS_DEBUG_CONE, "DEBUG_CONE"),
}

# MON_CTRL (obs_regs.rdl) runtime cone enables, bit-for-bit the arm word the
# obs campaigns write. Deriving the word from the legal set keeps "arm what
# you key" structural instead of a comment that drifts (BUG-019: an arm word
# that enabled THRESHOLD while no threshold tuple was keyed sent ~89% of live
# traffic to UNEXPECTED once the perf packets that used to dwarf it retired).
MON_CTRL_BITS = {0x0: 0,    # ERROR_EN
                 0x3: 1,    # TIMEOUT_EN
                 0x1: 2,    # COMPL_EN
                 0x2: 3,    # THRESHOLD_EN
                 0x4: 4,    # PERF_EN
                 0xF: 5}    # DEBUG_EN
MON_CTRL_ADDR_CHECK_EN = 6
MON_CTRL_MONITOR_EN = 7


def read_caps0(bridge, base: int = OBS_APB_BASE) -> int:
    """OBS_CAPS0 from the observer behind `base` (master or slave window)."""
    return bridge.read(O("OBS_CAPS0", base)) or 0


def n_addr_ranges(caps0: int) -> int:
    return (caps0 >> CAPS_N_ADDR_RANGES_SHIFT) & 0xF


def filter_legal_by_caps(legal, caps0: int):
    """Split a monbus legal set against ONE observer's OBS_CAPS0.

    Returns (kept, retired): kept is the sublist whose emit path exists in
    this build; retired is [(entry, reason)] for entries whose cone (or range
    checker) is not built. A class the hardware cannot emit is a class the
    board campaign can never cover -- the campaign must treat it as "not
    applicable", never "not seen".
    """
    kept, retired = [], []
    for t in legal:
        req = _TYPE_REQ.get(t[2])
        if req is None:
            kept.append(t)
            continue
        want, name = req
        have = n_addr_ranges(caps0) > 0 if want == "ranges" else bool(caps0 & want)
        if have:
            kept.append(t)
        else:
            retired.append((t, f"{name} not built (OBS_CAPS0=0x{caps0:08X})"))
    return kept, retired


def mon_ctrl_arm(ptypes, monitor_en: bool = True) -> int:
    """MON_CTRL arm word enabling exactly the cones behind `ptypes`.

    AddrMatch (0x8) has no cone enable -- it rides the address-range checker,
    programmed per row by the obs matrix (ADDR_CHECK_EN is deliberately NOT
    set here).
    """
    arm = 0
    for t in ptypes:
        b = MON_CTRL_BITS.get(t)
        if b is not None:
            arm |= 1 << b
    if monitor_en:
        arm |= 1 << MON_CTRL_MONITOR_EN
    return arm
