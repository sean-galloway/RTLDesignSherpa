# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Named host API for the DMA slave-side monitors.

One `SlaveMon` object == the pair of slave-side AXI monitors inside
`dma_slave_monitors` (read = agent 0x0001, write = agent 0x0002), programmed
entirely BY REGISTER NAME through the generated `slvmon_regs_top_regmap.py`.

WHY THIS EXISTS: until the block grew its own APB regblock these monitors had
no configuration path at all -- their enables were tied to 1'b1 by the harness
and the latency threshold, the nine event-code masks and the address-range
checker were tied off *inside* the module. On silicon they could therefore only
ever emit COMPLETION: nothing could exceed a threshold pinned at max, and with
the address checker held off there was no AddrMatch and no ADDR_RANGE error.
The whole AXI *slave* side of the monitor-validation environment was
structurally uncoverable, which is what this closes.

    slv = SlaveMon(bridge)
    slv.arm_threshold("rd", cycles=20)        # provoke THRESHOLD
    slv.arm_timeout("wr", cycles=50)          # provoke TIMEOUT
    slv.arm_addr_range("rd", 0x0, 0xFFFF_FFFF)  # provoke AddrMatch
    slv.classes("rd", compl=False, perf=False)  # quieten the monbus

Registers are never touched by offset -- see [[registers-by-name]]. Composition
is by field name, so a field that moves in the RDL moves here with it.
"""

from __future__ import annotations

import logging
import os
from typing import Optional

from TBClasses.harness.device import Device

# Bridge slave window for dma_slave_monitors' config APB.
SLVMON_APB_BASE = 0x0018_0000

# Enable-register field names, in the order the RDL declares them.
_CLASS_FIELDS = ("MON_EN", "ERR_EN", "COMPL_EN", "TIMEOUT_EN",
                 "PERF_EN", "DEBUG_EN", "THRESH_EN")


def _default_regmap() -> str:
    """Locate the generated slave-monitor regmap by anchoring, never counting."""
    env = os.environ.get("SLVMON_REGMAP")
    if env:
        return env
    here = os.path.dirname(os.path.abspath(__file__))
    # Component-level: the slave monitors are part of the shared harness, so
    # their regmap is shared too -- it was under build-mon/ when the harness
    # still lived there.
    # In projects/components/misc/ -- the block is shared with rapids-beats,
    # so its regmap is not stream collateral.
    rel = os.path.join("projects", "components", "misc", "rtl", "regs",
                       "generated", "slvmon_regs_top_regmap.py")
    d = here
    for _ in range(12):
        cand = os.path.join(d, rel)
        if os.path.isfile(cand):
            return cand
        parent = os.path.dirname(d)
        if parent == d:
            break
        d = parent
    raise FileNotFoundError("slvmon_regs_top_regmap.py not found; "
                            "set SLVMON_REGMAP or regenerate the regblock")


def _pfx(side: str) -> str:
    """'rd'/'wr' -> the RDL register-name prefix."""
    s = side.lower()
    if s not in ("rd", "wr"):
        raise ValueError(f"side must be 'rd' or 'wr', got {side!r}")
    return "RDSLV" if s == "rd" else "WRSLV"


class SlaveMon(Device):
    """The slave-side monitor pair, addressed by name."""

    def __init__(self, bridge, name: str = "slvmon", *,
                 regs_base: int = SLVMON_APB_BASE,
                 regmap_file: Optional[str] = None,
                 log: Optional[logging.Logger] = None):
        super().__init__(bridge, name, regs_base=regs_base,
                         regmap_file=regmap_file or _default_regmap(), log=log)

    # ----- class enables ---------------------------------------------------
    def classes(self, side: str, **flags: bool) -> int:
        """Set per-class enables by name: classes('rd', compl=False, perf=True).

        Unnamed classes keep their current value -- important because the monbus
        is a shared, rate-limited resource and turning everything on at once
        congests it. Field preservation is `rmw=True` on the shared
        UartRegisterMap, not a hand-rolled read-back loop here.
        """
        named = {}
        for k, v in flags.items():
            f = k.upper() if k.upper().endswith("_EN") else f"{k.upper()}_EN"
            if f not in _CLASS_FIELDS:
                raise KeyError(f"unknown class {k!r}; have {_CLASS_FIELDS}")
            named[f] = 1 if v else 0
        return self.write(f"{_pfx(side)}_ENABLE", rmw=True, **named)

    # ----- provoking each packet class -------------------------------------
    def arm_timeout(self, side: str, cycles: int) -> None:
        """Lower the timeout so a slow response trips TIMEOUT.

        Reset default is 0xFFFF, which is why timeouts never fired: the old
        hardwired value was the maximum.
        """
        self.write(f"{_pfx(side)}_TIMEOUT", TIMEOUT_CYCLES=cycles)
        self.classes(side, timeout=True)

    def arm_threshold(self, side: str, cycles: int) -> None:
        """Lower the latency threshold so a slow response trips THRESHOLD.

        Reset default is 0xFFFFFFFF -- the value that was tied off inside the
        module, and the reason THRESHOLD was unreachable on the slave side.
        """
        self.write(f"{_pfx(side)}_LATENCY_THRESH", VALUE=cycles)
        self.classes(side, thresh=True)

    def arm_addr_range(self, side: str, low: int, high: int,
                       check: bool = True) -> None:
        """Enable the address checker over [low, high] -> AddrMatch packets."""
        p = _pfx(side)
        self.write(f"{p}_ADDR_RANGE_LOW", VALUE=low)
        self.write(f"{p}_ADDR_RANGE_HIGH", VALUE=high)
        self.write(f"{p}_ENABLE", rmw=True,
                   ADDR_CHECK_EN=1 if check else 0,
                   ADDR_RANGE_EN=1 if check else 0)

    def pkt_mask(self, side: str, mask: int, err_select: int = 0) -> None:
        """Drop mask at the monbus entry: bit[type]=1 drops that packet type."""
        self.write(f"{_pfx(side)}_PKT_MASK", PKT_MASK=mask, ERR_SELECT=err_select)

    def event_masks(self, side: str, **kw: int) -> None:
        """Per-event-code drop masks, e.g. event_masks('rd', ERROR_MASK=0)."""
        p = _pfx(side)
        groups = {"MASK1": ("ERROR_MASK", "TIMEOUT_MASK"),
                  "MASK2": ("COMPL_MASK", "THRESH_MASK"),
                  "MASK3": ("PERF_MASK", "ADDR_MASK"),
                  "MASK4": ("DEBUG_MASK",)}
        for reg, fields in groups.items():
            named = {f: kw[f] for f in fields if f in kw}
            if named:
                self.write(f"{p}_{reg}", rmw=True, **named)

    def defaults(self, side: str) -> None:
        """Restore the reset state = the pre-regblock hardwired behaviour."""
        p = _pfx(side)
        self.write(f"{p}_ENABLE", **{f: 1 for f in _CLASS_FIELDS},
                   ADDR_CHECK_EN=0, ADDR_RANGE_EN=0)
        self.write(f"{p}_TIMEOUT", TIMEOUT_CYCLES=0xFFFF)
        self.write(f"{p}_LATENCY_THRESH", VALUE=0xFFFFFFFF)
        self.pkt_mask(side, 0)
        for reg in ("MASK1", "MASK2", "MASK3", "MASK4"):
            self.write(f"{p}_{reg}")


def build_slave_mon(bridge, log: Optional[logging.Logger] = None) -> SlaveMon:
    """One slave-monitor device over an injected bridge (sim or FPGA)."""
    return SlaveMon(bridge, log=log)
