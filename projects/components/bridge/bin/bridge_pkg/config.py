#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Configuration Data Structures for Bridge Generator

from dataclasses import dataclass, field
from typing import List, Dict


# Valid bridge-level monitor presets. Drive `BridgeConfig.mon_preset` —
# each port's reporter sub-block enables (ENABLE_ERROR_LOGIC etc.) start
# from the preset and apply the per-port additive `mon_add` on top.
MON_PRESETS = {
    "all":        {"error": True,  "timeout": True,  "compl": True,  "threshold": True,  "perf": True,  "debug": True},
    "error_only": {"error": True,  "timeout": False, "compl": False, "threshold": False, "perf": False, "debug": False},
    "functional": {"error": True,  "timeout": True,  "compl": True,  "threshold": False, "perf": False, "debug": False},
    "none":       {"error": False, "timeout": False, "compl": False, "threshold": False, "perf": False, "debug": False},
}
MON_CONES = ("error", "timeout", "compl", "threshold", "perf", "debug")


@dataclass
class MonGroupConfig:
    """Protocol + sizing config for the bridge's internal monbus group.

    The post-arbiter aggregator is the monbus_<p1>_<p2>_group family in
    rtl/amba/shared/ (commit 3d91e4de), where p1 = slave-read protocol
    (the IRQ-status / error-FIFO read port the SoC polls) and p2 =
    master-write protocol (the packet-log write port to memory). Each
    side is independently "axil" or "axi4", giving four permutations:
      monbus_axil_axil_group  monbus_axil_axi4_group
      monbus_axi4_axil_group  monbus_axi4_axi4_group

    Configured per-bridge via the TOML [bridge.mon_group] sub-table:
      [bridge.mon_group]
      slave_protocol  = "axil"   # "axil" | "axi4"
      master_protocol = "axi4"   # "axil" | "axi4"
      axi_id_width    = 8        # used when either side is axi4
      max_burst_beats = 64       # used when master is axi4

    Defaults reproduce the legacy axil/axil group so configs that omit
    the table keep their existing top-level surface and tests.
    """
    slave_protocol: str = "axil"      # "axil" | "axi4" -- s_mon read port
    master_protocol: str = "axil"     # "axil" | "axi4" -- m_mon write port
    # Core sizing (passed as module parameters).
    fifo_depth_err: int = 64
    fifo_depth_write: int = 96        # beats (new family default)
    flush_timeout_cycles: int = 1024
    use_compression: int = 0
    # AXI4-only sizing -- ignored when both sides are axil.
    axi_id_width: int = 8             # slave-read and/or master-write id
    axi_user_width: int = 1
    max_burst_beats: int = 64         # master-write burst cap (axi4 master)

    _VALID_PROTOCOLS = ("axil", "axi4")

    def __post_init__(self):
        for label, p in (("slave_protocol", self.slave_protocol),
                         ("master_protocol", self.master_protocol)):
            if p not in self._VALID_PROTOCOLS:
                raise ValueError(
                    f"[bridge.mon_group].{label} = {p!r} is not one of "
                    f"{list(self._VALID_PROTOCOLS)}"
                )

    @property
    def module_name(self) -> str:
        """Wrapper module from the monbus_<p1>_<p2>_group family."""
        return f"monbus_{self.slave_protocol}_{self.master_protocol}_group"

    @property
    def slave_is_axi4(self) -> bool:
        return self.slave_protocol == "axi4"

    @property
    def master_is_axi4(self) -> bool:
        return self.master_protocol == "axi4"


@dataclass
class PortSpec:
    """Specification for a single AXI4 port (master or slave)"""
    port_name: str          # Unique identifier (e.g., "cpu_master", "ddr_slave")
    direction: str          # "master" or "slave"
    protocol: str           # "axi4" or "apb"
    channels: str           # "rw" (read/write), "wr" (write-only), "rd" (read-only)
    prefix: str             # Signal prefix (e.g., "cpu_m_axi_", "ddr_s_axi_")
    data_width: int         # Data width in bits
    addr_width: int         # Address width in bits
    id_width: int = 0       # AXI ID width (0 for APB)
    base_addr: int = 0      # Slave base address (masters don't use)
    addr_range: int = 0     # Slave address range (masters don't use)
    enable_ooo: bool = False  # Slave supports out-of-order responses
    # Per-port USE_MONITOR override. Only meaningful on bridges whose
    # variant is "mon". Default True keeps the existing behaviour; set
    # to False on individual ports to omit their axi_monitor_filtered
    # instance at synthesis (area savings) while preserving the bridge-
    # top monbus/cfg surface so the harness wiring stays uniform. The
    # disabled wrapper's monbus_valid stays 0 -- the arbiter sees it
    # as an inert client.
    use_monitor: bool = True
    # Per-port additive list of reporter sub-block enables. Names come
    # from MON_CONES. The bridge-level mon_preset sets the baseline; for
    # ports that want extras (e.g. a CPU port that needs perf rollups
    # while the other ports stay error-only), name them here:
    #   [[bridge.masters]]
    #   name = "cpu"
    #   mon_add = ["perf", "compl"]
    # mon_remove subtracts cones from the preset (rarely needed).
    mon_add: List[str] = field(default_factory=list)
    mon_remove: List[str] = field(default_factory=list)

    def get_mon_enables(self, preset: str) -> Dict[str, bool]:
        """Compute the 5 ENABLE_*_LOGIC values for this port: preset
        baseline + mon_add - mon_remove. Returns a dict keyed by cone
        name (error/timeout/compl/threshold/perf)."""
        if preset not in MON_PRESETS:
            raise ValueError(
                f"unknown mon_preset {preset!r}; expected one of "
                f"{sorted(MON_PRESETS.keys())}"
            )
        enables = dict(MON_PRESETS[preset])
        for c in self.mon_add:
            if c not in MON_CONES:
                raise ValueError(
                    f"port {self.port_name!r}: mon_add entry {c!r} not "
                    f"in {list(MON_CONES)}"
                )
            enables[c] = True
        for c in self.mon_remove:
            if c not in MON_CONES:
                raise ValueError(
                    f"port {self.port_name!r}: mon_remove entry {c!r} not "
                    f"in {list(MON_CONES)}"
                )
            enables[c] = False
        return enables

    def has_write_channels(self) -> bool:
        """Returns True if this port has write channels (AW, W, B)"""
        return self.channels in ('wr', 'rw')

    def has_read_channels(self) -> bool:
        """Returns True if this port has read channels (AR, R)"""
        return self.channels in ('rd', 'rw')


@dataclass
class BridgeConfig:
    """Complete bridge configuration"""
    name: str = ""           # From TOML/YAML [bridge].name; empty = let
                             # generate_bridge() auto-name from topology.
    masters: List[PortSpec] = field(default_factory=list)
    slaves: List[PortSpec] = field(default_factory=list)
    connectivity: Dict[str, List[str]] = field(default_factory=dict)

    # Crossbar configuration (derived)
    crossbar_data_width: int = 0
    crossbar_addr_width: int = 0
    crossbar_id_width: int = 0        # Master-side ID width
    crossbar_slave_id_width: int = 0  # Slave-side ID width (master ID + routing bits)

    # Optional features
    expose_arbiter_signals: bool = False

    # Interface wrapper configuration
    enable_interface_wrappers: bool = True   # Use axi4_master/slave wrappers (timing)
    # variants: explicit per-bridge build set driven by the TOML
    # `[bridge].variants` field. Allowed values per entry: "no" (no
    # monitor) emits the bare <bridge_name>, "mon" emits
    # <bridge_name>_mon. The TOML loader REQUIRES the field with at
    # least one entry; the Python default exists only for the legacy
    # CSV path, which has no concept of monitor variants.
    variants: List[str] = field(default_factory=lambda: ["no"])

    # internal_axil_group: per-bridge selector for the monbus
    # aggregation topology used by the "mon" variant. When True
    # (default, backward-compatible) the bridge instantiates its own
    # monbus_arbiter + monbus_axil_group and exposes the group's AXIL
    # slave/master, cfg, and IRQ at the bridge top. When False the
    # bridge still arbitrates per-port packets internally but skips
    # the AXIL group; it surfaces the arbiter's aggregated stream as
    # monbus_agg_* at the top so the integrator can merge with an
    # existing external monbus_axil_group (e.g., STREAM's internal
    # group in the stream_char harness). Has no effect on the "no"
    # variant.
    internal_axil_group: bool = True

    # mon_group: protocol + sizing for the internal monbus group used by
    # the "mon" variant when internal_axil_group=True. Selects which
    # member of the monbus_<p1>_<p2>_group family is instantiated and
    # what slave-read / master-write surface the bridge top exposes.
    # Defaults to axil/axil (the legacy group) so configs that omit the
    # [bridge.mon_group] table are unchanged.
    mon_group: MonGroupConfig = field(default_factory=MonGroupConfig)

    # Bridge-level monitor override switches (matching STREAM's pattern).
    # Both default False. When True, override every port's per-port
    # `use_monitor` field. Mutually exclusive -- both True is a config
    # error.
    #   use_all_monitors = true  -> every wrapper USE_MONITOR=1
    #                               (overrides per-port `use_monitor=false`)
    #   use_no_monitors  = true  -> every wrapper USE_MONITOR=0
    #                               (overrides per-port `use_monitor=true`)
    # Per the user's spec: eventually, when use_no_monitors=true the
    # bridge should also omit the monbus_arbiter + monbus_axil_group
    # entirely and tie off the top-level monitor surface. That second-
    # level optimisation is not implemented yet -- today the arbiter +
    # group are still emitted, but every client wrapper ties
    # monbus_valid=0 so they pass no traffic.
    use_all_monitors: bool = False
    use_no_monitors: bool = False
    # Task 90.3: opt-in PeakRDL regblock-backed cfg subsystem.
    use_cfg_regblock: bool = False

    # Skid buffer depths (per wrapper)
    skid_depth_ar: int = 2    # AR channel buffer depth
    skid_depth_aw: int = 2    # AW channel buffer depth
    skid_depth_w: int = 4     # W channel buffer depth (deeper for data)
    skid_depth_r: int = 2     # R channel buffer depth
    skid_depth_b: int = 2     # B channel buffer depth

    # Monitor configuration (only used by variants that include "mon")
    mon_error_enable: bool = True
    mon_compl_enable: bool = True
    mon_timeout_enable: bool = True
    mon_perf_enable: bool = False  # Avoid packet congestion

    # Bridge-level monitor preset — sets the baseline ENABLE_*_LOGIC for
    # every adapter port's _mon wrapper. Per-port `mon_add` / `mon_remove`
    # adjust from there. "error_only" is the default bridge area-minimum
    # build per the post-Stage-A.5 0.9-monitor refactor; integrators
    # opt in to compl/timeout/threshold/perf cones per-port (e.g. CPU
    # port gets "perf", the rest stay error-only).
    #
    # Valid: "all", "error_only", "functional", "none". See MON_PRESETS.
    mon_preset: str = "error_only"

    def num_masters(self) -> int:
        return len(self.masters)

    def num_slaves(self) -> int:
        return len(self.slaves)

    def get_master_by_name(self, name: str) -> PortSpec:
        """Get master port by name"""
        for m in self.masters:
            if m.port_name == name:
                return m
        raise ValueError(f"Master '{name}' not found")

    def get_slave_by_name(self, name: str) -> PortSpec:
        """Get slave port by name"""
        for s in self.slaves:
            if s.port_name == name:
                return s
        raise ValueError(f"Slave '{name}' not found")
