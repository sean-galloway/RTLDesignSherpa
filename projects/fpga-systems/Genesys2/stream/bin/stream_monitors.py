# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""Program the in-core STREAM monitors -- the mon build's twin of the obs
campaign's `configure_observers`.

ONE place that knows how to arm DAXMON / RDMON / WRMON, route the monbus group
and arm the address-range checker, all BY NAME through the generated regmap.
Five host programs used to carry their own copy of this (enable_monitors,
_mon_common, configure_monitors, program_error_config, an inline block), and
they disagreed: one allowed every packet type, one hardcoded the ENABLE layout
from a stale comment, one routed records to the capture memory while sweeping
the tally. Each disagreement read as a monitor defect.

WHERE this runs matters more than what it writes. CTRL.SOFT_RESET clears every
monitor CSR (they sit in the unit_aresetn domain -- pinned by
cocotb_test_soft_reset_scope), and the board's program,
`CharacterizationRunner.run_config`, starts with that reset. So monitor
programming written BEFORE run_config is silently wiped, and programming
written in a hand-rolled reset/configure/kick sequence is a second copy of the
board's program. The two hooks the runner offers are the only correct places:

  * `runner.mon_config = MonitorProgram(...)` -- applied INSIDE
    `configure_stream()`, after the reset, exactly where the runner programs
    its own legacy monitor defaults (which it otherwise would, overwriting
    anything written earlier).
  * `runner.run_config(cfg, pre_kick=fn)` -- `fn(bridge)` runs after
    configure_stream and before the kick, for everything else here
    (`route_monbus`, `arm_addr_ranges`, per-scenario timeouts, the tally CAM).

The cosim (`test_stream_mon_compress`) drives the same objects over the same
runner, so the sequence is proven in sim before it reaches silicon.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import AbstractSet, Callable, FrozenSet, Iterable, List, Tuple

import os as _os
import sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
from stream_addrs import A, compose, write_reg   # noqa: E402  (by name, never offsets)
from bridge_windows import W                      # noqa: E402  (bridge windows by name)

# Packet types == PKT_MASK bit index (monbus_types.PktType*).
PKT_ERROR     = 0x0
PKT_COMPL     = 0x1
PKT_THRESHOLD = 0x2
PKT_TIMEOUT   = 0x3
PKT_PERF      = 0x4
PKT_ADDRMATCH = 0x8
PKT_PERFWIN   = 0xD    # CSR-only: no RTL emit path (perfmon RFC pending)
PKT_PERFHIST  = 0xE    # CSR-only
PKT_DEBUG     = 0xF

# The cosim's "allow basic" set: Error, Completion, Threshold, Timeout. Allowing
# EVERYTHING (mask 0x0000) admits the perf stream the obs campaign measures at
# ~1.1M packets; on the board that flooded the group, came back as an empty
# capture and wedged the UART. This is the set the cosim proves.
BASIC_CLASSES: FrozenSet[int] = frozenset({PKT_ERROR, PKT_COMPL, PKT_THRESHOLD, PKT_TIMEOUT})

ALL_MONITORS: Tuple[str, ...] = ("DAXMON", "RDMON", "WRMON")
DATAPATH_MONITORS: Tuple[str, ...] = ("RDMON", "WRMON")

# pkt_type -> the <MON>_ENABLE field that arms that cone. Field NAMES, placed by
# the regmap, never bit indices: THRESH_EN was added at bit 6 after every
# hand-assembled 0x0F in the tree had been written. AddrMatch (8) has no
# enable -- it comes from the addr-range checker (arm_addr_ranges).
_EN_FIELD = {PKT_ERROR: "ERR_EN", PKT_COMPL: "COMPL_EN", PKT_THRESHOLD: "THRESH_EN",
             PKT_TIMEOUT: "TIMEOUT_EN", PKT_PERF: "PERF_EN"}

_CLASS_NAME = {PKT_ERROR: "error", PKT_COMPL: "compl", PKT_THRESHOLD: "threshold",
               PKT_TIMEOUT: "timeout", PKT_PERF: "perf", PKT_ADDRMATCH: "addrmatch",
               PKT_PERFWIN: "perfwin", PKT_PERFHIST: "perfhist", PKT_DEBUG: "debug"}


@dataclass(frozen=True)
class MonitorProgram:
    """The cone set for the in-core monitors, as a `CharacterizationRunner.mon_config`.

    `classes` are the packet types allowed through PKT_MASK (and whose cones are
    enabled). Monitors not in `monitors` are switched off with a drop-all mask,
    so a scenario can isolate the datapath monitors from the descriptor-fetch
    one. Every per-event-code mask is CLEARED: their RDL defaults are not
    uniform (TIMEOUT/THRESH/ADDR drop-all, COMPL/PERF allow-all), which is how
    Timeout and Threshold packets were dropped after the type filter for months
    while the cones were firing.

    COMPRESS_EN is written 0 here; the runner's own `compression` flag sets it
    afterwards (read-modify-write, last thing configure_stream does). The
    `compress` attribute is informational, mirroring mon_configs.MonConfig.
    """
    classes: AbstractSet[int]          # normalised to a frozenset
    monitors: Tuple[str, ...] = ALL_MONITORS
    name: str = ""
    compress: bool = False

    def __post_init__(self):
        object.__setattr__(self, "classes", frozenset(self.classes))
        for m in self.monitors:
            if m not in ALL_MONITORS:
                raise ValueError(f"unknown monitor {m!r}; choose from {ALL_MONITORS}")
        for t in self.classes:
            if not 0 <= t <= 0xF:
                raise ValueError(f"packet type {t!r} outside 0..15")
        if not self.name:
            object.__setattr__(self, "name", "mon:" + "+".join(
                _CLASS_NAME.get(t, f"type{t:x}") for t in sorted(self.classes)))

    # Names the runner's vlog prints, so it reads like a MonConfig preset.
    @property
    def cones(self) -> Tuple[str, ...]:
        return tuple(_CLASS_NAME.get(t, f"type{t:x}") for t in sorted(self.classes))

    def pkt_mask(self) -> int:
        """1 = DROP that type (RTL: pkt_drop = cfg_pkt_mask[pkt_type])."""
        mask = 0xFFFF
        for t in self.classes:
            mask &= ~(1 << t)
        return mask & 0xFFFF

    def register_writes(self) -> List[Tuple[int, int]]:
        writes: List[Tuple[int, int]] = []
        for m in ALL_MONITORS:
            active = m in self.monitors
            en_fields = {_EN_FIELD[t]: 1 for t in self.classes if t in _EN_FIELD} if active else {}
            if m == "WRMON":
                en_fields["COMPRESS_EN"] = 0      # the runner's flag decides, after this
            writes.append((A(f"{m}_ENABLE"),
                           compose(f"{m}_ENABLE", MON_EN=1 if active else 0, **en_fields)))
            writes.append((A(f"{m}_PKT_MASK"),
                           compose(f"{m}_PKT_MASK", PKT_MASK=self.pkt_mask() if active else 0xFFFF)))
            # ERR_SELECT=0 routes every type to the bulk trace (tally / capture
            # memory); ERR_MASK is a per-event-code DROP mask whose reset value
            # 0xFFFF discards every error event -- the capture "comes back empty".
            writes.append((A(f"{m}_ERR_CFG"), compose(f"{m}_ERR_CFG", ERR_SELECT=0, ERR_MASK=0)))
            writes.append((A(f"{m}_MASK1"), compose(f"{m}_MASK1", TIMEOUT_MASK=0, COMPL_MASK=0)))
            writes.append((A(f"{m}_MASK2"), compose(f"{m}_MASK2", THRESH_MASK=0, PERF_MASK=0)))
            writes.append((A(f"{m}_MASK3"), compose(f"{m}_MASK3", ADDR_MASK=0, DEBUG_MASK=0)))
        return writes

    def apply(self, write: Callable[[int, int], object]) -> None:
        """Program all three monitors via `write(addr, value)` (runner hook)."""
        for addr, val in self.register_writes():
            write(addr, val)


def route_monbus(bridge, window: str) -> Tuple[int, int]:
    """Aim the in-core monbus group's bulk-trace master at a bridge window.

    `stream_tally` when the caller SWEEPS BINS (raw 3-beat records the tally
    reassembles), `comp_sram` when it DECODES a capture (compressed slots). The
    two are exclusive, which is why this takes a name and not a flag. Flush
    watermark 0 = emit every complete record; the default of 16 records sits on
    a short workload until the 1024-cycle flush timeout. Returns (base, limit).
    """
    base, limit = W(window)
    write_reg(bridge, "MON_GROUP_BASE_ADDR", VALUE=base)
    write_reg(bridge, "MON_GROUP_LIMIT_ADDR", VALUE=limit)
    write_reg(bridge, "MON_GROUP_FLUSH_WATERMARK", VALUE=0)
    return base, limit


# Address-range checker (axi_monitor_addr_check), built whenever N_ADDR_RANGES>0
# (=4 here) independent of the error cone. Ranges 0,1 are DEBUG-flavoured
# (a hit emits AddrMatch), ranges 2,3 ERROR-flavoured (an allowlist MISS emits
# Error/ADDR_RANGE). Modes:
#   off        -- every range disabled, range2 benign (any address in-range)
#   match_all  -- range0 = whole space, CHECK+MATCH: every AR/AW emits AddrMatch
#   miss       -- range2 = a tiny high window the DMA never touches, CHECK+MISS
#                 and NOTHING ELSE. addr_check is the lowest-priority monbus
#                 source, so a simultaneous match-all range floods it with
#                 AddrMatch and starves its own error stream: measured on
#                 build-mon, r0+r2+CHECK+MATCH+MISS -> 0 error packets,
#                 r2+CHECK+MISS -> 384.
_RANGE_MODES = ("off", "match_all", "miss")


def arm_addr_ranges(bridge, mode: str, monitors: Iterable[str] = DATAPATH_MONITORS) -> None:
    if mode not in _RANGE_MODES:
        raise ValueError(f"unknown addr-range mode {mode!r}; choose from {_RANGE_MODES}")
    for m in monitors:
        write_reg(bridge, f"{m}_ADDR_RANGE_CTRL", RANGE_EN=0, CHECK_EN=0, MATCH_EN=0, MISS_EN=0)
        write_reg(bridge, f"{m}_ADDR_RANGE2_LOW",  VALUE=0x0000_0000)
        write_reg(bridge, f"{m}_ADDR_RANGE2_HIGH", VALUE=0xFFFF_FFFF)
        if mode == "match_all":
            write_reg(bridge, f"{m}_ADDR_RANGE0_LOW",  VALUE=0x0000_0000)
            write_reg(bridge, f"{m}_ADDR_RANGE0_HIGH", VALUE=0xFFFF_FFFF)
            write_reg(bridge, f"{m}_ADDR_RANGE_CTRL", RANGE_EN=0b0001, CHECK_EN=1, MATCH_EN=1)
        elif mode == "miss":
            write_reg(bridge, f"{m}_ADDR_RANGE2_LOW",  VALUE=0xFFFF_FFF0)
            write_reg(bridge, f"{m}_ADDR_RANGE2_HIGH", VALUE=0xFFFF_FFFF)
            write_reg(bridge, f"{m}_ADDR_RANGE_CTRL", RANGE_EN=0b0100, CHECK_EN=1, MISS_EN=1)


def set_timeouts(bridge, *, timeout_us: int | None = None,
                 latency_thresh_clk: int | None = None,
                 monitors: Iterable[str] = DATAPATH_MONITORS) -> None:
    """UNITS DIFFER: TIMEOUT counts the monitor's 1 us frequency-invariant tick,
    LATENCY_THRESH counts raw aclk clocks (axi_monitor_timer). A timeout of 100
    written "in cycles" is 100 us = 6000 clocks at 60 MHz -- above any stall the
    harness delay blocks impose, so the cone never fired and read as absent."""
    for m in monitors:
        if timeout_us is not None:
            write_reg(bridge, f"{m}_TIMEOUT", TIMEOUT_CYCLES=timeout_us)
        if latency_thresh_clk is not None:
            write_reg(bridge, f"{m}_LATENCY_THRESH", LATENCY_THRESH=latency_thresh_clk)


def run_perf_windows(bridge, window_cycles: int | None = None,
                     monitors: Iterable[str] = ALL_MONITORS) -> None:
    """Open the in-core perf windows (RUN=1). The rollup reporter emits only in
    the idle gap AFTER traffic stops, so callers give it a short pause before
    freezing the tally."""
    for m in monitors:
        if window_cycles is not None:
            bridge.write(A(f"{m}_PERF_WINDOW_CYCLES"), window_cycles)
        write_reg(bridge, f"{m}_PERF_CTRL", RUN=1)
