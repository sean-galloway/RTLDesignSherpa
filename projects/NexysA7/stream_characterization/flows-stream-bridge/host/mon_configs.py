#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Module: mon_configs.py
# Purpose: Named monitor-configuration presets for stream_char captures.
#
# The three STREAM AXI monitors -- DAXMON (descriptor-fetch), RDMON
# (read-engine) and WRMON (write-engine) -- each expose the same cfg
# register block in stream_regs. A "config" here is a named selection of
# which monitor cones emit packets, applied uniformly to all three:
#
#   perf-mon    : only PktTypePerf flows. Low packet rate -- the trace
#                 SRAM fills slowly and the records are sparse, so the
#                 monbus compressor is NOT needed for this config.
#
#   debug-*     : richer event mixes (errors / completions / timeouts /
#                 threshold / perf). High SRAM traffic -- intended to be
#                 run on a USE_MON_COMPRESSION=1 build so the bulk-trace
#                 path stays inside the AXI budget.
#
# "Fully enabling" a cone takes THREE register actions, not one:
#   1. set the cone's ENABLE bit (only error/compl/timeout/perf have one)
#   2. clear the cone's PKT_MASK bit  (1 = drop that packet type)
#   3. clear the cone's event-code mask (ERR_MASK / TIMEOUT_MASK /
#      THRESH_MASK ... default to 0xFF = every event code masked)
# Forgetting #3 is why "PKT_MASK looks right but no error packets show
# up" -- the event-code mask drops them after the type filter.
#
# Register layout (offsets relative to each monitor's ENABLE base; see
# projects/components/stream/regs/generated/.../stream_regs.html):
#   +0x00 ENABLE   [MON_EN, ERR_EN, COMPL_EN, TIMEOUT_EN, PERF_EN]
#   +0x0C PKT_MASK [15:0]  1 = drop that packet type at monbus entry
#   +0x10 ERR_CFG  [3:0] ERR_SELECT, [15:8] ERR_MASK
#   +0x14 MASK1    [7:0] TIMEOUT_MASK, [15:8] COMPL_MASK
#   +0x18 MASK2    [7:0] THRESH_MASK,  [15:8] PERF_MASK
#   +0x1C MASK3    [7:0] ADDR_MASK,    [15:8] DEBUG_MASK
#
# Source map (what flows into the top group, and which protocol gates it):
#   PROTOCOL_AXI  (DAXMON filter) : descriptor-fetch AXI bus monitor
#   PROTOCOL_AXIS (RDMON filter)  : read-engine AXI bus monitor
#   PROTOCOL_CORE (WRMON filter)  : write-engine bus monitor PLUS the
#                                   per-channel scheduler and descriptor-
#                                   engine monitors. scheduler.sv /
#                                   descriptor_engine.sv emit Completion /
#                                   Error as PROTOCOL_CORE, aggregated up
#                                   through each scheduler_group's
#                                   monbus_arbiter to the top group.
#
# So "even the arbiters": scheduler / arbiter / scheduling activity rides
# the CORE protocol. Any config whose CORE (WRMON) filter passes
# Error / Completion / Timeout captures it -- no extra source needed.
# perf-mon's CORE filter passes only Perf, so the scheduler's Compl/Error
# are dropped there and perf-mon stays a clean low-rate perf stream.
# Per-source isolation of write-engine vs scheduler vs desc-engine (all
# CORE) is not a filter knob -- it is done via the per-source ENABLE regs
# (WRMON_ENABLE / SCHED_CONFIG cone bits / DESCENG_CONFIG), which
# per_source_capture.py drives.

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Dict, List, Optional, Tuple

# --------------------------------------------------------------------------
# Register geometry
# --------------------------------------------------------------------------

STREAM_APB_BASE = 0x0000_0000

# Per-monitor ENABLE base (stride 0x20). desc / read / write.
MON_BASES: Dict[str, int] = {
    "daxmon": STREAM_APB_BASE + 0x240,   # descriptor-fetch AXI monitor
    "rdmon":  STREAM_APB_BASE + 0x260,   # read-engine AXI monitor
    "wrmon":  STREAM_APB_BASE + 0x280,   # write-engine AXI monitor
}

# Register offsets within a monitor block.
OFF_ENABLE   = 0x00
OFF_PKT_MASK = 0x0C
OFF_ERR_CFG  = 0x10
OFF_MASK1    = 0x14
OFF_MASK2    = 0x18
OFF_MASK3    = 0x1C

# ENABLE register bit positions.
EN_MON     = 1 << 0
EN_ERR     = 1 << 1
EN_COMPL   = 1 << 2
EN_TIMEOUT = 1 << 3
EN_PERF    = 1 << 4

# Packet-type values == PKT_MASK bit index (monbus_types.PktType*).
PKT_ERROR     = 0x0
PKT_COMPL     = 0x1
PKT_THRESHOLD = 0x2
PKT_TIMEOUT   = 0x3
PKT_PERF      = 0x4
PKT_ADDRMATCH = 0x8
PKT_DEBUG     = 0xF

PKT_MASK_ALL_DROP = 0xFFFF


@dataclass(frozen=True)
class Cone:
    """One monitor reporting cone and where its three gates live."""
    name: str
    pkt_type: int                  # PKT_MASK bit / packet type
    enable_bit: Optional[int]      # ENABLE bit, or None (no runtime enable)
    mask_off: Optional[int]        # event-mask register offset, or None
    mask_lsb: int = 0              # field LSB of the 8-bit event mask


# Runtime-controllable cones. error/compl/timeout/perf have ENABLE bits;
# threshold/debug are build-gated (ENABLE_*_LOGIC) but their PKT_MASK +
# event mask still gate them at runtime when the build includes them.
CONES: Dict[str, Cone] = {
    "error":     Cone("error",     PKT_ERROR,     EN_ERR,     OFF_ERR_CFG, 8),
    "compl":     Cone("compl",     PKT_COMPL,     EN_COMPL,   OFF_MASK1,   8),
    "timeout":   Cone("timeout",   PKT_TIMEOUT,   EN_TIMEOUT, OFF_MASK1,   0),
    "threshold": Cone("threshold", PKT_THRESHOLD, None,       OFF_MASK2,   0),
    "perf":      Cone("perf",      PKT_PERF,      EN_PERF,    OFF_MASK2,   8),
    "addr":      Cone("addr",      PKT_ADDRMATCH, None,       OFF_MASK3,   0),
    "debug":     Cone("debug",     PKT_DEBUG,     None,       OFF_MASK3,   8),
}
# Scheduler / descriptor-engine / arbiter activity is NOT a separate cone:
# it arrives as PROTOCOL_CORE Error/Completion and is gated by the same
# CORE (WRMON) error/compl/timeout cones above.

# Which top-group protocol filter each monitor block implements. A config
# only programs the cones onto the protocols it lists; monitors for the
# other protocols are turned off (ENABLE=0) and their filter set to
# drop-all, so that protocol contributes nothing to the trace.
MON_PROTOCOL: Dict[str, str] = {
    "daxmon": "axi",    # descriptor-fetch AXI bus monitor
    "rdmon":  "axis",   # read-engine AXI bus monitor
    "wrmon":  "core",   # write-engine + scheduler + desc-engine + arbiter
}
ALL_PROTOCOLS: Tuple[str, ...] = ("axi", "axis", "core")


@dataclass(frozen=True)
class MonConfig:
    """A named monitor configuration.

    `cones` is the set of reporting cones (event types) to pass; `protocols`
    restricts that to a subset of {axi, axis, core}. A monitor whose
    protocol is not listed is disabled and its top-group filter drops
    everything, so e.g. protocols=("core",) isolates scheduler / arbiter /
    write-engine traffic from the AXI/AXIS bus monitors.
    """
    name: str
    description: str
    cones: Tuple[str, ...]
    # True => high traffic, run on a USE_MON_COMPRESSION=1 build.
    compress: bool = False
    protocols: Tuple[str, ...] = ALL_PROTOCOLS

    def __post_init__(self):
        for c in self.cones:
            if c not in CONES:
                raise ValueError(f"{self.name}: unknown cone {c!r}")
        for p in self.protocols:
            if p not in ALL_PROTOCOLS:
                raise ValueError(
                    f"{self.name}: unknown protocol {p!r}; "
                    f"choose from {list(ALL_PROTOCOLS)}")

    # ------------------------------------------------------------------
    # Register synthesis (per cone-set; an inactive monitor passes set())
    # ------------------------------------------------------------------

    @staticmethod
    def _enable_value(cones) -> int:
        val = EN_MON
        for c in cones:
            bit = CONES[c].enable_bit
            if bit is not None:
                val |= bit
        return val

    @staticmethod
    def _pkt_mask_value(cones) -> int:
        """0xFFFF (drop all) with each enabled cone's type bit cleared."""
        val = PKT_MASK_ALL_DROP
        for c in cones:
            val &= ~(1 << CONES[c].pkt_type) & 0xFFFF
        return val

    @staticmethod
    def _event_mask_regs(cones) -> Dict[int, int]:
        """The four mask registers (ERR_CFG/MASK1/MASK2/MASK3).

        Each 8-bit field is 0x00 (pass all event codes) when its cone is in
        `cones`, else 0xFF (mask all). Iterating CONES (not just the active
        set) guarantees fields with no config -- e.g. ADDR_MASK -- stay
        masked rather than left at 0x00 (pass-all).
        """
        cones = set(cones)
        regs = {OFF_ERR_CFG: 0, OFF_MASK1: 0, OFF_MASK2: 0, OFF_MASK3: 0}
        for cone in CONES.values():
            if cone.mask_off is None:
                continue
            field_val = 0x00 if cone.name in cones else 0xFF
            regs[cone.mask_off] |= field_val << cone.mask_lsb
        return regs

    def register_writes(self) -> List[Tuple[int, int]]:
        """Full (absolute_addr, value) program for all three monitors.

        Active-protocol monitors get the cone set; inactive ones are
        switched off (ENABLE=0) with a drop-all filter.
        """
        active = set(self.protocols)
        writes: List[Tuple[int, int]] = []
        for name, base in MON_BASES.items():
            if MON_PROTOCOL[name] in active:
                cones = set(self.cones)
                enable = self._enable_value(cones)
            else:
                cones = set()         # nothing passes this protocol
                enable = 0            # bus-monitor source off
            pkt_mask = self._pkt_mask_value(cones)
            masks = self._event_mask_regs(cones)
            writes.append((base + OFF_ENABLE, enable))
            writes.append((base + OFF_PKT_MASK, pkt_mask))
            writes.append((base + OFF_ERR_CFG, masks[OFF_ERR_CFG]))
            writes.append((base + OFF_MASK1, masks[OFF_MASK1]))
            writes.append((base + OFF_MASK2, masks[OFF_MASK2]))
            writes.append((base + OFF_MASK3, masks[OFF_MASK3]))
        return writes

    def apply(self, write: Callable[[int, int], object]) -> None:
        """Program all three monitors via `write(addr, value)`."""
        for addr, val in self.register_writes():
            write(addr, val)


# --------------------------------------------------------------------------
# The named suite
# --------------------------------------------------------------------------

PERF_MON = MonConfig(
    name="perf-mon",
    description="Performance metrics only; low packet rate, no compression.",
    cones=("perf",),
    compress=False,
)

DEBUG_BASIC = MonConfig(
    name="debug-basic",
    description="Error + completion + timeout across all protocols. The CORE "
                "cones also pass scheduler / descriptor-engine / arbiter "
                "activity. Moderate-to-high traffic.",
    cones=("error", "compl", "timeout"),
    compress=True,
)

DEBUG_COMPL = MonConfig(
    name="debug-compl",
    description="Completions only; high-volume single-type stream "
                "(includes scheduler/arbiter CORE completions).",
    cones=("compl",),
    compress=True,
)

DEBUG_ALL = MonConfig(
    name="debug-all",
    description="Every runtime cone (error/compl/timeout/threshold/perf) on "
                "every protocol -- AXI bus, AXIS bus, and CORE (write-engine "
                "+ scheduler + descriptor-engine + arbiter). Maximum traffic "
                "mix -> compressed path.",
    cones=("error", "compl", "timeout", "threshold", "perf"),
    compress=True,
)

DEBUG_CORE = MonConfig(
    name="debug-core",
    description="CORE protocol only: write-engine + scheduler + descriptor-"
                "engine + arbiter Error/Completion/Timeout. AXI and AXIS bus "
                "monitors are off, isolating scheduling/arbiter traffic.",
    cones=("error", "compl", "timeout"),
    compress=True,
    protocols=("core",),
)

CONFIGS: Dict[str, MonConfig] = {
    c.name: c for c in
    (PERF_MON, DEBUG_BASIC, DEBUG_COMPL, DEBUG_ALL, DEBUG_CORE)
}


def get(name: str) -> MonConfig:
    if name not in CONFIGS:
        raise KeyError(
            f"unknown mon config {name!r}; choose from {sorted(CONFIGS)}"
        )
    return CONFIGS[name]


if __name__ == "__main__":
    # Quick human-readable dump of every config's register program.
    for cfg in CONFIGS.values():
        tag = "  (compressed build)" if cfg.compress else ""
        print(f"\n=== {cfg.name}{tag} ===")
        print(f"  {cfg.description}")
        print(f"  cones: {', '.join(cfg.cones)}")
        # Show one monitor's program (all three are identical).
        for addr, val in cfg.register_writes()[:6]:
            print(f"    0x{addr:04X} = 0x{val:08X}")
