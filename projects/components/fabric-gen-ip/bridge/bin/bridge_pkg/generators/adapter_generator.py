"""
Bridge Adapter Generator

Generates per-master adapter modules that contain:
- Interface wrapper (timing isolation)
- Address decode logic
- Width converters (or direct passthrough)
- APB protocol converters (for APB slaves)
- Struct-based outputs

Author: RTL Design Sherpa
Date: 2025-11-03
"""

from typing import List, Dict, Optional, Tuple
from dataclasses import dataclass
from ..width_utils import get_connected_slave_widths
from ..emit_utils import generate_monitor_ports
from ..signal_naming import SignalNaming, Direction, AXI4Channel, AXI4_MASTER_SIGNALS, PortDirection, SignalInfo


# Widths in bits for the 15 cfg_* inputs every axi4_*_mon variant
# exposes. Mirrors the SV declarations in
# rtl/amba/axi4/axi4_{master,slave}_{wr,rd}_mon.sv.
_MONITOR_CFG_WIDTHS = {
    'cfg_monitor_enable':       1,
    'cfg_error_enable':         1,
    'cfg_timeout_enable':       1,
    'cfg_perf_enable':          1,
    # Added post-#114 — wrapper-level dedicated cfg inputs.
    'cfg_compl_enable':         1,
    'cfg_threshold_enable':     1,
    'cfg_debug_enable':         1,
    'cfg_timeout_cycles':      16,
    # counter_freq_invariant LUT index (was hardcoded 4'b0000 inside the wrapper).
    'cfg_freq_sel':             4,
    'cfg_latency_threshold':   32,
    'cfg_axi_pkt_mask':        16,
    'cfg_axi_err_select':      16,
    'cfg_axi_error_mask':      16,
    'cfg_axi_timeout_mask':    16,
    'cfg_axi_compl_mask':      16,
    'cfg_axi_thresh_mask':     16,
    'cfg_axi_perf_mask':       16,
    'cfg_axi_addr_mask':       16,
    'cfg_axi_debug_mask':      16,
}


def _ensure_trailing_comma(port_lines: List[str]) -> None:
    """In-place: find the last non-blank, non-comment, non-bare-")"
    port-declaration line and ensure it ends with ','. Used when a new
    group of ports is appended after a block whose final entry was
    deliberately comma-less."""
    for idx in range(len(port_lines) - 1, -1, -1):
        ln = port_lines[idx]
        stripped = ln.strip()
        if not stripped:
            continue
        if stripped.startswith('//'):
            continue
        if stripped in (');',):
            continue
        # First real declaration line from the end.
        if not stripped.endswith(','):
            port_lines[idx] = ln.rstrip() + ','
        return


@dataclass
class SlaveInfo:
    """Information about a slave port."""
    name: str
    prefix: str  # Signal prefix (e.g., "sram_buffer_s_axi_", "apb_periph_")
    base_addr: int
    addr_range: int
    data_width: int
    addr_width: int  # Address width in bits
    protocol: str = 'axi4'  # Protocol type: 'axi4', 'axi5', 'apb', or 'axil'
    enable_ooo: bool = False  # Slave supports out-of-order responses (use CAM vs FIFO)
    max_outstanding: int = 16  # response tracker depth (PortSpec.max_outstanding)
    # Timing-wrapper skid depths {aw,w,b,ar,r}; 0 = stage cut (PortSpec.latency)
    skid_depths: Optional[Dict[str, int]] = None
    cdc: bool = False  # bridge TASK-006 (was BRIDGE-017): own clock; axi4_cdc_{wr,rd} before the boundary
    timeout_cycles: int = 0  # GitHub #119 L3: > 0 = axi4_slave_watchdog before the boundary
    use_monitor: bool = True  # Per-port USE_MONITOR override (see PortSpec)
    # Internal slaves have no top-level pins -- the bridge instantiates
    # something for them and wires the crossbar to it. See PortSpec.internal.
    internal: bool = False
    # Reporter sub-block enables (preset + add - remove resolved upstream).
    # Keys: error/timeout/compl/threshold/perf. Default all True keeps
    # legacy behaviour; bridge generator overrides per-port from TOML.
    mon_enables: Optional[Dict[str, bool]] = None
    # AXI5 sideband features exposed on this port (protocol='axi5' only;
    # A5-2 slice 1). Validated upstream to the interop set:
    # nsaid/trace/mpam/mecid/unique. The features terminate/default at
    # the adapter's axi5_master_* boundary wrapper -- the fabric side
    # stays AXI4.
    axi5_features: Optional[List[str]] = None


@dataclass
class MasterConfig:
    """Configuration for a master port."""
    name: str
    prefix: str
    data_width: int
    addr_width: int
    id_width: int
    channels: str  # "wr", "rd", or "rw"
    slave_connections: List[int]  # Indices of connected slaves
    use_monitor: bool = True  # Per-port USE_MONITOR override (see PortSpec)
    # External protocol seen by the SoC integrator. The crossbar fabric
    # is always AXI4 internally, but when this is 'axil' the bridge top
    # exposes only AXIL signals on this master port (no id/len/burst/
    # cache/qos/region/user/last). The host-side wrapper handles the
    # AXIL->AXI4 translation when transactions enter the fabric.
    # 'axi5' (A5-1) exposes the AXI5 surface (AXI4 minus region, plus
    # the enabled sideband features below) and terminates the features
    # at the axi5_slave_* timing wrapper.
    protocol: str = 'axi4'
    # Reporter sub-block enables (preset + add - remove resolved upstream).
    mon_enables: Optional[Dict[str, bool]] = None
    # AXI5 sideband features exposed on this port (protocol='axi5' only;
    # validated upstream to the A5-1 set: nsaid/trace/mpam/mecid/unique).
    axi5_features: Optional[List[str]] = None
    # Tracker depth / outstanding limit per direction (PortSpec.max_outstanding).
    max_outstanding: int = 16
    # Rate-matching buffer depth, wide beats, on upsized paths into a shared
    # slave (PortSpec.rate_buffer; 0 = off).
    rate_buffer: int = 16
    # Timing-wrapper skid depths {aw,w,b,ar,r}; 0 = stage cut (PortSpec.latency)
    skid_depths: Optional[Dict[str, int]] = None
    # Own clock domain (GitHub #119 L2): the bridge top gains `<name>_aclk` /
    # `<name>_aresetn` and axi4_cdc_{wr,rd} carry the port onto aclk ahead
    # of the timing wrapper. AXI4 only (validate_cdc_constraints).
    cdc: bool = False


class AdapterGenerator:
    """
    Generates per-master adapter modules for bridge crossbars.

    Each adapter contains:
    - Timing wrapper (axi4_slave_rd/wr)
    - Address decode (one-hot slave selection)
    - Width converters or direct passthrough
    - Struct-based outputs for clean interface
    """

    def __init__(self, bridge_name: str, num_slaves: int, master_config: MasterConfig, slaves: List[SlaveInfo], all_masters: List[MasterConfig] = None, enable_monitoring: bool = False, master_index: int = 0, id_track_bits: int = 4):
        """
        Initialize adapter generator.

        Args:
            bridge_name: Name of bridge (e.g., "bridge_1x2_wr")
            num_slaves: Total number of slaves in bridge
            master_config: Configuration for this master
            slaves: List of all slave configurations
            all_masters: List of ALL masters in bridge (for LCD calculation)
            enable_monitoring: Use *_mon wrapper versions (default: False)
            master_index: Index of this master in bridge (0, 1, 2, ...) for BRIDGE_ID
        """
        self.bridge_name = bridge_name
        self.num_slaves = num_slaves
        self.master = master_config
        self.slaves = slaves
        self.all_masters = all_masters if all_masters is not None else [master_config]
        self.enable_monitoring = enable_monitoring
        self.master_index = master_index
        # Per-ID target tracking (replaces the one-outstanding-target gate):
        # 2**id_track_bits entries indexed by the ID's low bits.
        self.id_track_bits = int(id_track_bits)

        # AXI5 native sideband (A5-2 slice 2): the struct-field union for
        # the whole bridge, and this master's own feature set. EVERY
        # master packs every union field (its own features from fub
        # wires, the rest '0) so the xbar can forward fields
        # unconditionally.
        from bridge_pkg.sideband import sideband_union, port_features
        self.sb_union = sideband_union(self.all_masters, self.slaves)
        # bridge TASK-007 (was BRIDGE-018): the width-independent aw/ar/b structs size their
        # data-scaled sideband (MTE tags) for the widest port in the bridge;
        # this adapter fits its own-width fub wires to that.
        self.bridge_max_dw = max([m.data_width for m in (all_masters or [master_config])]
                                 + [sl.data_width for sl in slaves])
        self.sb_own = port_features(self.master) & self.sb_union

        # Skid buffer depths (configurable)
        # Per-port timing-wrapper depths (bridge GitHub #119 L7: these were a
        # fixed 2/4/2/2/2 and the TOML skid_depths were silently ignored).
        sd = getattr(master_config, 'skid_depths', None) or {}
        self.skid_depth_aw = sd.get('aw', 2)
        self.skid_depth_ar = sd.get('ar', 2)
        self.skid_depth_w = sd.get('w', 4)
        self.skid_depth_r = sd.get('r', 2)
        self.skid_depth_b = sd.get('b', 2)

    def generate(self) -> str:
        """
        Generate complete adapter module.

        Returns:
            SystemVerilog adapter module source code
        """
        lines = []

        # Header
        lines.extend(self._generate_header())

        # Module declaration
        lines.extend(self._generate_module_declaration())

        # Internal signals
        lines.extend(self._generate_internal_signals())

        # Timing wrapper instantiation
        lines.extend(self._generate_wrapper())

        # Address decode
        lines.extend(self._generate_address_decode())

        # Width adaptation (converter or direct passthrough)
        lines.extend(self._generate_width_adaptation())

        # NOTE: APB protocol conversion is handled at the bridge level,
        # after the crossbar, not in the adapter. The adapter only does
        # timing isolation, address decode, and width conversion.

        # ILA observation taps (amber bring-up; compiled out unless
        # AMBER_ILA_DBG is defined).
        lines.extend(self._generate_ila_taps())

        # Module end
        lines.append("endmodule : " + self._get_module_name())
        lines.append("")

        return "\n".join(lines)

    def _generate_ila_taps(self) -> List[str]:
        """ILA observation taps for the amber Genesys2 bring-up (round 5).

        Emitted only for read-capable adapters and compiled to nothing unless
        AMBER_ILA_DBG is defined (amber fpga/tcl/build_ila.tcl defines it
        project-wide), so no other bridge build, sim, or lint ever sees these
        nets. The taps give the adapter-internal AR gate (ar_trk_*/ar_gate_ok)
        and the axi4_slave_rd timing wrapper (wrapper_rd_busy) post-synth
        names, so the board ILA can tell a silicon-corrupted AR tracker from a
        wedged read wrapper. Pure observation -- no functional effect.
        """
        if self.master.channels not in ("rd", "rw"):
            return []
        lines = []
        lines.append("")
        lines.append("    // -------- ILA observation taps (AMBER_ILA_DBG builds only) --------")
        lines.append("    // Amber bring-up round 5: name the adapter-internal AR tracker,")
        lines.append("    // AR gate, and read-wrapper terms post-synth so the board ILA can")
        lines.append("    // distinguish a corrupted ar_trk_full from a wedged axi4_slave_rd.")
        lines.append("    // Pure observation; compiled out unless AMBER_ILA_DBG is defined.")
        lines.append("`ifdef AMBER_ILA_DBG")
        lines.append("    (* mark_debug = \"true\" *) logic             dbg_ad_ar_trk_full;")
        lines.append("    (* mark_debug = \"true\" *) logic [AR_TRK_AW:0] dbg_ad_ar_out_cnt;")
        lines.append("    (* mark_debug = \"true\" *) logic             dbg_ad_ar_gate_ok;")
        lines.append("    (* mark_debug = \"true\" *) logic             dbg_ad_ar_push;")
        lines.append("    (* mark_debug = \"true\" *) logic             dbg_ad_ar_pop;")
        lines.append("    (* mark_debug = \"true\" *) logic             dbg_ad_host_arvalid;")
        lines.append("    (* mark_debug = \"true\" *) logic             dbg_ad_host_arready;")
        lines.append("    (* mark_debug = \"true\" *) logic             dbg_ad_fub_arvalid;")
        lines.append("    (* mark_debug = \"true\" *) logic             dbg_ad_fub_arready;")
        lines.append("    (* mark_debug = \"true\" *) logic             dbg_ad_wrapper_rd_busy;")
        lines.append("    (* mark_debug = \"true\" *) logic             dbg_ad_fub_rvalid;")
        lines.append("    (* mark_debug = \"true\" *) logic             dbg_ad_fub_rready;")
        lines.append("    (* mark_debug = \"true\" *) logic             dbg_ad_fub_rlast;")
        lines.append("")
        lines.append("    assign dbg_ad_ar_trk_full      = ar_trk_full;")
        lines.append("    assign dbg_ad_ar_out_cnt       = ar_out_cnt;")
        lines.append("    assign dbg_ad_ar_gate_ok       = ar_gate_ok;")
        lines.append("    assign dbg_ad_ar_push          = ar_idt_push;")
        lines.append("    assign dbg_ad_ar_pop           = ar_idt_pop;")
        lines.append("    assign dbg_ad_host_arvalid     = host_axi_arvalid;")
        lines.append("    assign dbg_ad_host_arready     = host_axi_arready;")
        lines.append("    assign dbg_ad_fub_arvalid      = fub_axi_arvalid;")
        lines.append("    assign dbg_ad_fub_arready      = fub_axi_arready;")
        lines.append("    assign dbg_ad_wrapper_rd_busy  = wrapper_rd_busy;")
        lines.append("    assign dbg_ad_fub_rvalid       = fub_axi_rvalid;")
        lines.append("    assign dbg_ad_fub_rready       = fub_axi_rready;")
        lines.append("    assign dbg_ad_fub_rlast        = fub_axi_rlast;")
        lines.append("`endif")
        lines.append("")
        return lines

    def _generate_header(self) -> List[str]:
        """Generate file header."""
        return [
            f"// {self.master.name.upper()} Master Adapter Module",
            "// Generated by: AdapterGenerator",
            f"// Handles timing isolation, address decode, and width conversion for {self.master.name} master",
            "",
            "`timescale 1ns / 1ps",
            "",
            '`include "reset_defs.svh"',   # ALWAYS_FF_RST / RST_ASSERTED
            "",
            ""
        ]

    def _generate_module_declaration(self) -> List[str]:
        """Generate module declaration with ports."""
        lines = []
        module_name = self._get_module_name()

        # Module header with parameters
        lines.append(f"module {module_name}")
        lines.append(f"    import {self.bridge_name}_pkg::*;")
        lines.append("#(")
        lines.append(f"    parameter NUM_SLAVES = {self.num_slaves},")

        # Calculate BRIDGE_ID_WIDTH
        num_masters = len(self.all_masters)
        bridge_id_width = max(1, (num_masters - 1).bit_length())  # $clog2(NUM_MASTERS)
        lines.append(f"    parameter BRIDGE_ID = {self.master_index},  // Unique ID for this master")
        lines.append(f"    parameter BRIDGE_ID_WIDTH = {bridge_id_width},")

        if self.master.channels in ["wr", "rw"]:
            lines.append(f"    parameter SKID_DEPTH_AW = {self.skid_depth_aw},")
            lines.append(f"    parameter SKID_DEPTH_W = {self.skid_depth_w},")
            lines.append(f"    parameter SKID_DEPTH_B = {self.skid_depth_b}")
        if self.master.channels in ["rd", "rw"]:
            if self.master.channels == "rw":
                lines.append("    ,")  # Add comma if both wr and rd
            lines.append(f"    parameter SKID_DEPTH_AR = {self.skid_depth_ar},")
            lines.append(f"    parameter SKID_DEPTH_R = {self.skid_depth_r}")

        # USE_MONITOR_WR / USE_MONITOR_RD parameters (mon variant only).
        # Default from the TOML's per-master `use_monitor` field but the
        # bridge top overrides them with the effective-after-global-knobs
        # value at instantiation -- the default only matters when the
        # adapter is instantiated standalone for unit tests.
        if self.enable_monitoring:
            default_lit = "1'b1" if self.master.use_monitor else "1'b0"
            if self.master.channels in ("wr", "rw"):
                lines.append(f"   ,parameter bit USE_MONITOR_WR = {default_lit}")
            if self.master.channels in ("rd", "rw"):
                lines.append(f"   ,parameter bit USE_MONITOR_RD = {default_lit}")

        lines.append(") (")
        lines.append("    input  logic aclk,")
        lines.append("    input  logic aresetn,")
        if self.is_cdc:
            # GitHub #119 L2: the external port's own clock domain.
            lines.append("    input  logic ext_aclk,")
            lines.append("    input  logic ext_aresetn,")
        lines.append("")

        # External AXI interface
        lines.append(f"    // External AXI interface (from {self.master.name} master)")
        lines.extend(self._generate_external_ports())

        # Address decode outputs
        lines.append("")
        lines.append("    // Address decode outputs (full width one-hot)")
        if self.master.channels in ["wr", "rw"]:
            lines.append("    output logic [NUM_SLAVES-1:0] slave_select_aw,")
            lines.append("    output logic [BRIDGE_ID_WIDTH-1:0] bridge_id_aw,")
        if self.master.channels in ["rd", "rw"]:
            lines.append("    output logic [NUM_SLAVES-1:0] slave_select_ar,")
            lines.append("    output logic [BRIDGE_ID_WIDTH-1:0] bridge_id_ar,")
        if self.has_wakeup:
            lines.append("    // AWAKEUP toward wake-capable AXI5 slave ports (A14.1.1)")
            lines.append("    output logic wakeup_req,")

        # Width-specific outputs via structs
        lines.append("")
        lines.append(f"    // {self.master.data_width}b width outputs (to crossbar)")
        lines.extend(self._generate_struct_ports())

        # Monitor side-band ports. Only emitted when use_monitor=true so
        # non-monitored builds have an unchanged port surface. Each
        # wrapper instance gets its own monbus output trio + 15 cfg
        # inputs; bridge top binds them to externally driven nets.
        if self.enable_monitoring:
            _ensure_trailing_comma(lines)
            lines.append("")
            lines.extend(self._generate_monitor_ports())

        lines.append(");")
        lines.append("")

        return lines

    def _generate_monitor_ports(self) -> List[str]:
        """Per-wrapper monbus output + cfg input ports for this adapter.

        Delegates to emit_utils.generate_monitor_ports (shared with
        SlaveAdapterGenerator) — see its docstring for the naming scheme
        and i_mon_time rationale."""
        return generate_monitor_ports(self.master.channels)

    def _generate_external_ports(self) -> List[str]:
        """
        Generate external AXI port declarations using SignalNaming.

        Uses SignalNaming.get_all_axi4_signals() for consistent naming across
        the entire bridge (top-level, adapters, and crossbar).

        IMPORTANT: Adapter module is an intermediary that receives signals from
        external master and passes them through timing wrapper. Port directions
        are INVERTED from the master's perspective:
        - Request signals (awid, awaddr, etc.): INPUT to adapter (from external master)
        - Response signals (awready, bid, etc.): OUTPUT from adapter (to external master)

        Signal format: <master_name>_axi_<channel><signal>
        Example: cpu_axi_awaddr (NOT cpu_m_axi_awaddr)

        AXI5 masters (protocol='axi5', A5-1): the surface is the AXI4
        set MINUS aw/arregion (AXI5 removed REGION), PLUS the enabled
        sideband features' signals appended per channel. Disabled
        features' signals are NOT exposed -- they tie off inside at the
        axi5_slave_* wrapper instantiation.
        """
        from ..components.axi4_timing_wrapper_component import (
            axi5_exposed_ext_signals,
        )
        # An APB or Wishbone requester port has no AXI surface at all: the
        # adapter is the completer and the AXI4 face it feeds the wrapper
        # with is internal (see _generate_front_end).
        if self.is_front_end_master:
            if self.master.protocol == 'wb4':
                return self._generate_wb4_external_ports()
            if self.master.protocol == 'axi3':
                return self._generate_axi3_external_ports()
            return self._generate_apb_external_ports()

        lines = []
        is_axi5 = (self.master.protocol == 'axi5')
        # Normalised prefix for the hand-emitted AXI5 extras (SignalNaming
        # normalises internally for the base set).
        axi5_prefix = self.master.prefix
        if axi5_prefix and not axi5_prefix.endswith('_'):
            axi5_prefix = axi5_prefix + '_'

        # Width parameters for signal info queries
        width_values = {
            # The AXI4-face ports (awid/bid/arid/rid on an AXI4-Lite master
            # are declared but tied off at the bridge top) are sized by the
            # same rule as the face itself -- see fub_id_width. For a real
            # AXI4/AXI5 master this IS master.id_width, so nothing moves.
            'ID_WIDTH': self.fub_id_width,
            'ADDR_WIDTH': 32,  # Global address width
            'DATA_WIDTH': self.master.data_width,
            'STRB_WIDTH': self.master.data_width // 8,
            'USER_WIDTH': 1
        }

        # Determine which channels to generate based on master type
        channels = SignalNaming.channels_from_type(self.master.channels)

        # Get all AXI4 signals using SignalNaming (same as bridge top-level).
        # Pass `prefix` so the adapter's external ports honour the .toml
        # prefix setting — Bug C in TASK-011. Bridge top-level instantiation
        # uses the same prefix to wire adapter ports to bridge external ports.
        all_signals = SignalNaming.get_all_axi4_signals(
            port_name=self.master.name,
            direction=Direction.MASTER,
            channels=channels,
            prefix=self.master.prefix
        )

        # Generate declarations for each channel with INVERTED directions
        first_channel = True
        for channel, channel_signals in all_signals.items():
            if not first_channel:
                lines.append("")
            first_channel = False

            for sig_name, sig_info in channel_signals:
                # AXI5 has no REGION -- drop it from the base set.
                if is_axi5 and sig_info.name == 'region':
                    continue

                # Invert port direction (adapter is intermediary, not the master)
                inverted_direction = PortDirection.OUTPUT if sig_info.direction == PortDirection.INPUT else PortDirection.INPUT

                # Create inverted signal info
                inverted_sig = SignalInfo(
                    name=sig_info.name,
                    direction=inverted_direction,
                    width_expr=sig_info.width_expr,
                    width_param=sig_info.width_param,
                    is_vector=sig_info.is_vector,
                    description=sig_info.description
                )

                # Get complete signal declaration with inverted direction
                declaration = inverted_sig.get_declaration(sig_name, width_values)
                lines.append(f"    {declaration},")

            # AXI5 sideband extras for this channel (enabled features
            # only). Signals driven by the external master are adapter
            # inputs; b/r-side extras are adapter outputs.
            if is_axi5:
                for name, width, ext_in in axi5_exposed_ext_signals(
                        channel.value, self.master.axi5_features, self.master.data_width,
                        port_channels=self.master.channels):
                    dir_str = 'input' if ext_in else 'output'
                    sig_name = f"{axi5_prefix}{name}"
                    if width > 1:
                        lines.append(
                            f"    {dir_str}  logic [{width-1}:0]  {sig_name},")
                    else:
                        lines.append(
                            f"    {dir_str}  logic         {sig_name},")

        return lines

    # ------------------------------------------------------------------
    # Requester ports with a protocol FRONT END (bridge TASK-004 (was BRIDGE-014) APB/APB5,
    # bridge TASK-008 (was BRIDGE-019) WB4): the adapter is the completer on the boundary and a
    # converter produces the AXI4 face the ordinary axi4_slave_{wr,rd}
    # timing wrapper consumes. One net prefix per family, declared and
    # connected from the one helper below.
    # ------------------------------------------------------------------

    FRONT_END_MODULES = {
        'apb':  'apb4_to_axi4',
        'apb5': 'apb5_to_axi4',
        'wb4':  'wb4_to_axi4',
        'axi3': 'axi3_to_axi4',
    }
    APB_AXI_PREFIX = 'apbx_axi_'
    WB4_AXI_PREFIX = 'wbx_axi_'
    AXI3_AXI_PREFIX = 'a3x_axi_'

    @property
    def is_front_end_master(self) -> bool:
        return self.master.protocol in self.FRONT_END_MODULES

    @property
    def is_apb_master(self) -> bool:
        return self.master.protocol in ('apb', 'apb5')

    @property
    def front_end_prefix(self) -> str:
        if self.master.protocol == 'wb4':
            return self.WB4_AXI_PREFIX
        if self.master.protocol == 'axi3':
            return self.AXI3_AXI_PREFIX
        return self.APB_AXI_PREFIX

    # ------------------------------------------------------------------
    # CDC master ports (GitHub #119 L2)
    # ------------------------------------------------------------------

    CDC_AXI_PREFIX = 'cdcx_axi_'
    _CDC_WR_SIGS = ('awid', 'awaddr', 'awlen', 'awsize', 'awburst', 'awlock', 'awcache',
                    'awprot', 'awqos', 'awregion', 'awuser', 'awvalid', 'awready',
                    'wdata', 'wstrb', 'wlast', 'wuser', 'wvalid', 'wready',
                    'bid', 'bresp', 'buser', 'bvalid', 'bready')
    _CDC_RD_SIGS = ('arid', 'araddr', 'arlen', 'arsize', 'arburst', 'arlock', 'arcache',
                    'arprot', 'arqos', 'arregion', 'aruser', 'arvalid', 'arready',
                    'rid', 'rdata', 'rresp', 'rlast', 'ruser', 'rvalid', 'rready')

    @property
    def is_cdc(self) -> bool:
        """The external port runs on ext_aclk; axi4_cdc_{wr,rd} carry it
        onto aclk ahead of the timing wrapper (GitHub #119 L2)."""
        return bool(getattr(self.master, 'cdc', False))

    def _generate_cdc_stage(self, ext_prefix: str, int_prefix: str) -> List[str]:
        """axi4_cdc_wr / axi4_cdc_rd: `ext_prefix` (ext_aclk, the external
        port) -> `int_prefix` (aclk, the timing wrapper's external side).
        Everything downstream -- wrapper, monitor, decode, ID tracking --
        stays on aclk and does not know the port crosses. One instance per
        direction present; only that direction's nets are declared."""
        wr = self.master.channels in ('wr', 'rw')
        rd = self.master.channels in ('rd', 'rw')
        keep = set((self._CDC_WR_SIGS if wr else ()) + (self._CDC_RD_SIGS if rd else ()))
        lines: List[str] = []
        lines.append("    // ================================================================")
        lines.append(f"    // Clock-domain crossing from the {self.master.name} port (ext_aclk)")
        lines.append("    // onto aclk, ahead of the timing wrapper (GitHub #119 L2)")
        lines.append("    // ================================================================")
        lines.extend(d for d in self._apb_axi_net_decls(int_prefix)
                     if d.rstrip(';').split()[-1][len(int_prefix):] in keep)
        lines.append("")
        common = [f"        .AXI_ID_WIDTH({self.fub_id_width}),",
                  "        .AXI_ADDR_WIDTH(32),",
                  f"        .AXI_DATA_WIDTH({self.master.data_width}),",
                  "        .AXI_USER_WIDTH(1),",
                  "        .CDC_DEPTH(8),",
                  "        .USE_JOHNSON(0)"]
        clocks = ["        .s_aclk(ext_aclk), .s_aresetn(ext_aresetn),",
                  "        .m_aclk(aclk), .m_aresetn(aresetn),"]
        for present, module, inst, sigs in ((wr, 'axi4_cdc_wr', 'u_cdc_wr', self._CDC_WR_SIGS),
                                            (rd, 'axi4_cdc_rd', 'u_cdc_rd', self._CDC_RD_SIGS)):
            if not present:
                continue
            lines.append(f"    {module} #(")
            lines.extend(common)
            lines.append(f"    ) {inst} (")
            lines.extend(clocks)
            for sig in sigs:
                lines.append(f"        .s_axi_{sig}({ext_prefix}{sig}),")
            for i, sig in enumerate(sigs):
                sep = ',' if i < len(sigs) - 1 else ''
                lines.append(f"        .m_axi_{sig}({int_prefix}{sig}){sep}")
            lines.append("    );")
            lines.append("")
        return lines

    def _generate_wb4_external_ports(self) -> List[str]:
        """Wishbone B4 completer surface (the bridge is the completer): the
        requester drives CYC/STB/WE/ADR/DAT_W/SEL/CTI/BTE, the adapter
        answers STALL/ACK/ERR/RTY/DAT_R. From bridge_pkg/wb4_signals, the one
        table the bridge top reads too."""
        from ..wb4_signals import port_decl_lines
        return port_decl_lines(self.master.prefix, 'completer', 32,
                               self.master.data_width)

    def _generate_apb_external_ports(self) -> List[str]:
        """APB completer surface: the external requester drives PSEL..PPROT,
        the adapter answers PREADY/PRDATA/PSLVERR. apb5 adds the requester's
        PAUSER/PWUSER/PWAKEUP and the completer's PRUSER/PBUSER, one bit each
        (the fabric USER width), mirroring the apb5 slave-port surface."""
        p = self.master.prefix
        dw = self.master.data_width
        sw = dw // 8
        lines = [
            f"    input  logic                  {p}PSEL,",
            f"    input  logic                  {p}PENABLE,",
            f"    output logic                  {p}PREADY,",
            f"    input  logic [31:0]           {p}PADDR,",
            f"    input  logic                  {p}PWRITE,",
            f"    input  logic [{dw-1}:0] {p}PWDATA,",
            f"    input  logic [{sw-1}:0] {p}PSTRB,",
            f"    input  logic [2:0]            {p}PPROT,",
            f"    output logic [{dw-1}:0] {p}PRDATA,",
            f"    output logic                  {p}PSLVERR,",
        ]
        if self.master.protocol == 'apb5':
            lines += [
                f"    input  logic                  {p}PAUSER,",
                f"    input  logic                  {p}PWUSER,",
                f"    input  logic                  {p}PWAKEUP,",
                f"    output logic                  {p}PRUSER,",
                f"    output logic                  {p}PBUSER,",
            ]
        return lines

    @staticmethod
    def generate_axi3_ports(master) -> List[str]:
        """AXI3 requester surface: the bridge/adapter is the slave, so the
        external master drives aw/ar/w and the bridge answers b/r. AXI3
        narrows the AXI4 set to 4-bit awlen/arlen, adds wid on W, widens
        awlock/arlock to 2 bits, and drops qos/region (bridge GitHub #97)."""
        p = master.prefix
        addr_w = master.addr_width
        id_w = master.id_width
        dw = master.data_width
        sw = dw // 8
        lines: List[str] = []
        if master.channels in ('wr', 'rw'):
            lines += [
                f"    input  logic [{id_w-1}:0] {p}awid,",
                f"    input  logic [{addr_w-1}:0] {p}awaddr,",
                f"    input  logic [3:0]  {p}awlen,",
                f"    input  logic [2:0]  {p}awsize,",
                f"    input  logic [1:0]  {p}awburst,",
                f"    input  logic [1:0]  {p}awlock,",
                f"    input  logic [3:0]  {p}awcache,",
                f"    input  logic [2:0]  {p}awprot,",
                f"    input  logic        {p}awuser,",
                f"    input  logic        {p}awvalid,",
                f"    output logic        {p}awready,",
                f"    input  logic [{dw-1}:0] {p}wdata,",
                f"    input  logic [{sw-1}:0] {p}wstrb,",
                f"    input  logic [{id_w-1}:0] {p}wid,",
                f"    input  logic        {p}wlast,",
                f"    input  logic        {p}wuser,",
                f"    input  logic        {p}wvalid,",
                f"    output logic        {p}wready,",
                f"    output logic [{id_w-1}:0] {p}bid,",
                f"    output logic [1:0]  {p}bresp,",
                f"    output logic        {p}buser,",
                f"    output logic        {p}bvalid,",
                f"    input  logic        {p}bready,",
            ]
        if master.channels in ('rd', 'rw'):
            lines += [
                f"    input  logic [{id_w-1}:0] {p}arid,",
                f"    input  logic [{addr_w-1}:0] {p}araddr,",
                f"    input  logic [3:0]  {p}arlen,",
                f"    input  logic [2:0]  {p}arsize,",
                f"    input  logic [1:0]  {p}arburst,",
                f"    input  logic [1:0]  {p}arlock,",
                f"    input  logic [3:0]  {p}arcache,",
                f"    input  logic [2:0]  {p}arprot,",
                f"    input  logic        {p}aruser,",
                f"    input  logic        {p}arvalid,",
                f"    output logic        {p}arready,",
                f"    output logic [{id_w-1}:0] {p}rid,",
                f"    output logic [{dw-1}:0] {p}rdata,",
                f"    output logic [1:0]  {p}rresp,",
                f"    output logic        {p}rlast,",
                f"    output logic        {p}ruser,",
                f"    output logic        {p}rvalid,",
                f"    input  logic        {p}rready,",
            ]
        return lines

    def _generate_axi3_external_ports(self) -> List[str]:
        return self.generate_axi3_ports(self.master)

    def _apb_axi_net_decls(self, prefix: str) -> List[str]:
        """`logic [W-1:0] {prefix}{sig};` for the full AXI4 channel set the
        protocol front end (APB, WB4, or AXI3) drives into the timing
        wrapper. ID is the internal face width (fub_id_width), USER is the
        fabric's 1 bit. NOTE: addr width is hard-coded to 32 to match the
        timing wrapper; parameterizing it ripples to the wrapper and the
        APB/WB4 converters, so it stays aligned with the existing house
        convention."""
        id_w = self.fub_id_width
        dw = self.master.data_width
        sw = dw // 8
        return [
            f"    logic [{id_w-1}:0] {prefix}awid;",
            f"    logic [31:0] {prefix}awaddr;",
            f"    logic [7:0]  {prefix}awlen;",
            f"    logic [2:0]  {prefix}awsize;",
            f"    logic [1:0]  {prefix}awburst;",
            f"    logic        {prefix}awlock;",
            f"    logic [3:0]  {prefix}awcache;",
            f"    logic [2:0]  {prefix}awprot;",
            f"    logic [3:0]  {prefix}awqos;",
            f"    logic [3:0]  {prefix}awregion;",
            f"    logic        {prefix}awuser;",
            f"    logic        {prefix}awvalid;",
            f"    logic        {prefix}awready;",
            f"    logic [{dw-1}:0] {prefix}wdata;",
            f"    logic [{sw-1}:0] {prefix}wstrb;",
            f"    logic        {prefix}wlast;",
            f"    logic        {prefix}wuser;",
            f"    logic        {prefix}wvalid;",
            f"    logic        {prefix}wready;",
            f"    logic [{id_w-1}:0] {prefix}bid;",
            f"    logic [1:0]  {prefix}bresp;",
            f"    logic        {prefix}buser;",
            f"    logic        {prefix}bvalid;",
            f"    logic        {prefix}bready;",
            f"    logic [{id_w-1}:0] {prefix}arid;",
            f"    logic [31:0] {prefix}araddr;",
            f"    logic [7:0]  {prefix}arlen;",
            f"    logic [2:0]  {prefix}arsize;",
            f"    logic [1:0]  {prefix}arburst;",
            f"    logic        {prefix}arlock;",
            f"    logic [3:0]  {prefix}arcache;",
            f"    logic [2:0]  {prefix}arprot;",
            f"    logic [3:0]  {prefix}arqos;",
            f"    logic [3:0]  {prefix}arregion;",
            f"    logic        {prefix}aruser;",
            f"    logic        {prefix}arvalid;",
            f"    logic        {prefix}arready;",
            f"    logic [{id_w-1}:0] {prefix}rid;",
            f"    logic [{dw-1}:0] {prefix}rdata;",
            f"    logic [1:0]  {prefix}rresp;",
            f"    logic        {prefix}rlast;",
            f"    logic        {prefix}ruser;",
            f"    logic        {prefix}rvalid;",
            f"    logic        {prefix}rready;",
        ]

    def _generate_front_end(self) -> List[str]:
        """Instantiate the port's protocol front end (apb4_to_axi4 /
        apb5_to_axi4 / wb4_to_axi4 / axi3_to_axi4) between its completer
        surface and the AXI4 timing wrapper. Named for the APB family that
        came first; WB4 (bridge TASK-008, was BRIDGE-019) and AXI3
        (bridge GitHub #97) ride the same path.

        APB: one APB transfer -> one single-beat AXI4 transaction, both
        SLVERR and DECERR folded to PSLVERR. From the wrapper onward the
        port is indistinguishable from an AXI4-Lite master with awlen=0.
        USER is the fabric's 1 bit: PAUSER[0]/PWUSER[0] ride awuser/wuser
        and come back on PBUSER/PRUSER from buser/ruser.

        AXI3: the converter presents a full AXI3 slave surface and produces
        a full AXI4 master surface; the nets between converter and timing
        wrapper are the standard AXI4 set at port width."""
        p = self.master.prefix
        x = self.front_end_prefix
        proto = self.master.protocol
        apb5 = (proto == 'apb5')
        module = self.FRONT_END_MODULES[proto]
        if proto == 'wb4':
            label = 'Wishbone B4'
        elif proto == 'axi3':
            label = 'AXI3'
        else:
            label = 'APB'
        lines: List[str] = []
        lines.append("    // ================================================================")
        lines.append(f"    // {label} requester front end ({module}): {label} completer -> AXI4")
        if proto in ('apb', 'apb5', 'wb4'):
            lines.append("    // single-beat requester, feeding the timing wrapper below.")
        lines.append("    // ================================================================")
        lines.extend(self._apb_axi_net_decls(x))
        lines.append("")
        lines.append(f"    {module} #(")
        if proto == 'wb4':
            lines.append(f"        .ADDR_WIDTH(32),")
            lines.append(f"        .DATA_WIDTH({self.master.data_width}),")
        elif proto == 'axi3':
            lines.append(f"        .AXI_ID_WIDTH({self.master.id_width}),")
            lines.append(f"        .AXI_ADDR_WIDTH({self.master.addr_width}),")
            lines.append(f"        .AXI_DATA_WIDTH({self.master.data_width}),")
            lines.append(f"        .AXI_USER_WIDTH(1)")
        else:
            lines.append(f"        .APB_ADDR_WIDTH(32),")
            lines.append(f"        .APB_DATA_WIDTH({self.master.data_width}),")
        if apb5:
            for k in ('APB_AUSER_WIDTH', 'APB_WUSER_WIDTH', 'APB_RUSER_WIDTH', 'APB_BUSER_WIDTH'):
                lines.append(f"        .{k}(1),")
        if proto != 'axi3':
            lines.append(f"        .AXI_ID_WIDTH({self.fub_id_width}),")
            lines.append(f"        .AXI_USER_WIDTH(1)")
        if proto == 'wb4':
            instance_label = 'wb4'
        elif proto == 'axi3':
            instance_label = 'axi3'
        else:
            instance_label = 'apb'
        lines.append(f"    ) u_{instance_label}_front_end (")
        lines.append(f"        .aclk(aclk),")
        lines.append(f"        .aresetn(aresetn),")
        if proto == 'wb4':
            from ..wb4_signals import wb4_names
            for sig in wb4_names():
                lines.append(f"        .s_wb_{sig}({p}{sig}),")
        elif proto == 'axi3':
            # AXI3 requester front end: connect only the channels the master
            # actually exposes. The AXI3 converter is a full slave surface;
            # tie unused inputs to the house constants and leave unused
            # outputs unconnected, matching the APB/AXIL/WB4 converter
            # tie-off pattern.
            id_w = self.master.id_width
            aw = self.master.addr_width
            dw = self.master.data_width
            sw = dw // 8
            if self.master.channels in ('wr', 'rw'):
                for sig in ('awid', 'awaddr', 'awlen', 'awsize', 'awburst', 'awlock',
                            'awcache', 'awprot', 'awuser', 'awvalid'):
                    lines.append(f"        .s_axi3_{sig}({p}{sig}),")
                lines.append(f"        .s_axi3_awready({p}awready),")
                for sig in ('wid', 'wdata', 'wstrb', 'wlast', 'wuser', 'wvalid'):
                    lines.append(f"        .s_axi3_{sig}({p}{sig}),")
                lines.append(f"        .s_axi3_wready({p}wready),")
                lines.append(f"        .s_axi3_bid   ({p}bid),")
                lines.append(f"        .s_axi3_bresp ({p}bresp),")
                lines.append(f"        .s_axi3_buser ({p}buser),")
                lines.append(f"        .s_axi3_bvalid({p}bvalid),")
                lines.append(f"        .s_axi3_bready({p}bready),")
            else:
                # Write channels absent: tie inputs to 0, leave outputs open.
                lines.append(f"        .s_axi3_awid   ({id_w}'d0),")
                lines.append(f"        .s_axi3_awaddr ({aw}'d0),")
                lines.append(f"        .s_axi3_awlen  (4'd0),")
                lines.append(f"        .s_axi3_awsize (3'd0),")
                lines.append(f"        .s_axi3_awburst(2'd0),")
                lines.append(f"        .s_axi3_awlock (2'd0),")
                lines.append(f"        .s_axi3_awcache(4'd0),")
                lines.append(f"        .s_axi3_awprot (3'd0),")
                lines.append(f"        .s_axi3_awuser (1'b0),")
                lines.append(f"        .s_axi3_awvalid(1'b0),")
                lines.append(f"        .s_axi3_awready(),")
                lines.append(f"        .s_axi3_wid    ({id_w}'d0),")
                lines.append(f"        .s_axi3_wdata  ({dw}'d0),")
                lines.append(f"        .s_axi3_wstrb  ({sw}'d0),")
                lines.append(f"        .s_axi3_wlast  (1'b0),")
                lines.append(f"        .s_axi3_wuser  (1'b0),")
                lines.append(f"        .s_axi3_wvalid (1'b0),")
                lines.append(f"        .s_axi3_wready (),")
                lines.append(f"        .s_axi3_bid    (),")
                lines.append(f"        .s_axi3_bresp  (),")
                lines.append(f"        .s_axi3_buser  (),")
                lines.append(f"        .s_axi3_bvalid (),")
                lines.append(f"        .s_axi3_bready (1'b0),")
            if self.master.channels in ('rd', 'rw'):
                for sig in ('arid', 'araddr', 'arlen', 'arsize', 'arburst', 'arlock',
                            'arcache', 'arprot', 'aruser', 'arvalid'):
                    lines.append(f"        .s_axi3_{sig}({p}{sig}),")
                lines.append(f"        .s_axi3_arready({p}arready),")
                lines.append(f"        .s_axi3_rid    ({p}rid),")
                lines.append(f"        .s_axi3_rdata  ({p}rdata),")
                lines.append(f"        .s_axi3_rresp  ({p}rresp),")
                lines.append(f"        .s_axi3_rlast  ({p}rlast),")
                lines.append(f"        .s_axi3_ruser  ({p}ruser),")
                lines.append(f"        .s_axi3_rvalid ({p}rvalid),")
                lines.append(f"        .s_axi3_rready ({p}rready),")
            else:
                # Read channels absent: tie inputs to 0, leave outputs open.
                lines.append(f"        .s_axi3_arid   ({id_w}'d0),")
                lines.append(f"        .s_axi3_araddr ({aw}'d0),")
                lines.append(f"        .s_axi3_arlen  (4'd0),")
                lines.append(f"        .s_axi3_arsize (3'd0),")
                lines.append(f"        .s_axi3_arburst(2'd0),")
                lines.append(f"        .s_axi3_arlock (2'd0),")
                lines.append(f"        .s_axi3_arcache(4'd0),")
                lines.append(f"        .s_axi3_arprot (3'd0),")
                lines.append(f"        .s_axi3_aruser (1'b0),")
                lines.append(f"        .s_axi3_arvalid(1'b0),")
                lines.append(f"        .s_axi3_arready(),")
                lines.append(f"        .s_axi3_rid    (),")
                lines.append(f"        .s_axi3_rdata  (),")
                lines.append(f"        .s_axi3_rresp  (),")
                lines.append(f"        .s_axi3_rlast  (),")
                lines.append(f"        .s_axi3_ruser  (),")
                lines.append(f"        .s_axi3_rvalid (),")
                lines.append(f"        .s_axi3_rready (1'b0),")
        else:
            for sig in ('PSEL', 'PENABLE', 'PREADY', 'PADDR', 'PWRITE', 'PWDATA',
                        'PSTRB', 'PPROT', 'PRDATA', 'PSLVERR'):
                lines.append(f"        .s_apb_{sig}({p}{sig}),")
            if apb5:
                for sig in ('PAUSER', 'PWUSER', 'PWAKEUP', 'PRUSER', 'PBUSER'):
                    lines.append(f"        .s_apb_{sig}({p}{sig}),")
        axi_sigs = ('awid', 'awaddr', 'awlen', 'awsize', 'awburst', 'awlock',
                    'awcache', 'awprot', 'awqos', 'awregion', 'awuser',
                    'awvalid', 'awready',
                    'wdata', 'wstrb', 'wlast', 'wuser', 'wvalid', 'wready',
                    'bid', 'bresp', 'buser', 'bvalid', 'bready',
                    'arid', 'araddr', 'arlen', 'arsize', 'arburst', 'arlock',
                    'arcache', 'arprot', 'arqos', 'arregion', 'aruser',
                    'arvalid', 'arready',
                    'rid', 'rdata', 'rresp', 'rlast', 'ruser', 'rvalid', 'rready')
        for i, sig in enumerate(axi_sigs):
            sep = ',' if i < len(axi_sigs) - 1 else ''
            lines.append(f"        .m_axi_{sig}({x}{sig}){sep}")
        lines.append("    );")
        lines.append("")
        return lines

    def _generate_struct_ports(self) -> List[str]:
        """
        Generate struct-based output port declarations.

        Creates ports for each unique slave width this master connects to.
        """
        lines = []

        # Get all unique slave widths
        slave_widths = self._get_connected_slave_widths()

        # Generate ports for each width
        for i, width in enumerate(slave_widths):
            suffix = f"{width}b"
            is_last_width = (i == len(slave_widths) - 1)

            # AW channel
            if self.master.channels in ["wr", "rw"]:
                lines.append(f"    output axi4_aw_t     {self.master.name}_{suffix}_aw,")
                lines.append(f"    output logic         {self.master.name}_{suffix}_awvalid,")
                lines.append(f"    input  logic         {self.master.name}_{suffix}_awready,")
                lines.append("")

            # W channel
            if self.master.channels in ["wr", "rw"]:
                lines.append(f"    output axi4_w_{suffix}_t  {self.master.name}_{suffix}_w,")
                lines.append(f"    output logic         {self.master.name}_{suffix}_wvalid,")
                lines.append(f"    input  logic         {self.master.name}_{suffix}_wready,")
                lines.append("")

            # B channel
            if self.master.channels in ["wr", "rw"]:
                lines.append(f"    input  axi4_b_t      {self.master.name}_{suffix}_b,")
                lines.append(f"    input  logic         {self.master.name}_{suffix}_bvalid,")
                # Add comma if not last port
                if self.master.channels == "wr" and is_last_width:
                    lines.append(f"    output logic         {self.master.name}_{suffix}_bready")
                else:
                    lines.append(f"    output logic         {self.master.name}_{suffix}_bready,")
                    if self.master.channels == "wr" and not is_last_width:
                        lines.append("")  # Blank line between widths

            # AR channel
            if self.master.channels in ["rd", "rw"]:
                if self.master.channels == "rw":
                    lines.append("")
                lines.append(f"    output axi4_ar_t     {self.master.name}_{suffix}_ar,")
                lines.append(f"    output logic         {self.master.name}_{suffix}_arvalid,")
                lines.append(f"    input  logic         {self.master.name}_{suffix}_arready,")
                lines.append("")

            # R channel
            if self.master.channels in ["rd", "rw"]:
                lines.append(f"    input  axi4_r_{suffix}_t  {self.master.name}_{suffix}_r,")
                lines.append(f"    input  logic         {self.master.name}_{suffix}_rvalid,")
                # Add comma if not last port
                if is_last_width:
                    lines.append(f"    output logic         {self.master.name}_{suffix}_rready")
                else:
                    lines.append(f"    output logic         {self.master.name}_{suffix}_rready,")
                    lines.append("")  # Blank line between widths

        return lines

    # --- AXI5 native-sideband emission helpers (A5-2 slice 2) -------

    def _sb_fields(self, channel, feats):
        from bridge_pkg.sideband import channel_fields
        return channel_fields(feats, channel)

    def _sb_struct_to_fub(self, channel, width, struct_expr, path_dw):
        """A response-struct sideband field as this master's fub-width
        expression (bridge TASK-007 (was BRIDGE-018): struct fields are sized by struct_dw --
        the path's width for r, the bridge-wide max for b -- and the fub
        wires by this master's own data width)."""
        from bridge_pkg.sideband import field_width, fit_expr, struct_dw
        sw = field_width(width, struct_dw(channel, path_dw, self.bridge_max_dw))
        fw = field_width(width, self.master.data_width)
        return fit_expr(struct_expr, sw, fw)

    # --- bridge BUG-010 (was BRIDGE-012): response trace is echoed at the boundary ---------------
    # AXI5 wants the response trace bit to follow the request's. From this
    # master's port the BRIDGE is the Subordinate, and this port advertises
    # trace, so the promise is the adapter's to keep -- whatever sits behind
    # the path. It cannot be kept by forwarding: sideband a slave does not
    # implement terminates mid-fabric (A5-2 slice 2) and its response carries
    # trace=0, so a traced write to a trace-less slave came back untraced and
    # the AXI5 checker at the port called each one a violation.
    #
    # The AW/AR tracking FIFO already holds one entry per outstanding request,
    # in the order responses return (the in-order contract, bridge BUG-008 (was BRIDGE-010)), so
    # the request's trace rides in the entry that routes its response. Echo
    # from there; keep the slave's own bit for a check rather than trusting it.
    #
    # Only `trace` echoes. `poison` on R is slave-sourced data integrity: a
    # request never predicts it, and echoing it would launder corrupt data.

    @property
    def _trace_echo(self) -> bool:
        return 'trace' in self.sb_own

    # --- bridge TASK-002 (was BRIDGE-002) A5-3b: read-return atomics ride natively ---------------
    # A read-return atomic (AWATOP[5]: AtomicLoad/Swap/Compare) is issued on
    # AW and answers with the location's original data on R, using the AW
    # ID. Every R-return tracker in this fabric learns from ARs, so A5-3a
    # terminated those classes at the boundary with axi5_atomic_filter. With
    # a read path on this port there is somewhere for the R to go: the AW
    # also claims a slot in the AR->R tracking FIFO (so the response mux
    # selects its slave in order) and the slave adapter tracks it per ID.
    # A write-only master has no R path and keeps the filter.
    @property
    def rr_atomic(self) -> bool:
        return 'atomic' in self.sb_own and self.master.channels == 'rw'

    # --- bridge TASK-005 (was BRIDGE-016): master-unique IDs ---------------------------------------
    # Inside the fabric every ID is {master index, master id}. The wrapper's
    # fub_axi_*id is this master's own width; the fabric-facing copy carries
    # BRIDGE_ID on top. Responses come back with the prefix and the existing
    # [fub_id_width-1:0] selects strip it. Zero prefix bits for one master, so
    # single-master bridges are byte-identical to before.
    @property
    def id_prefix_width(self) -> int:
        from bridge_pkg.width_utils import id_prefix_width
        return id_prefix_width(self.all_masters or [self.master])

    @property
    def xbar_id_width(self) -> int:
        from bridge_pkg.width_utils import xbar_id_width
        return xbar_id_width(self.all_masters or [self.master])

    def xid(self, chan: str) -> str:
        """Name of the fabric-facing ID net for 'aw' / 'ar'."""
        return f"xbar_axi_{chan}id" if self.id_prefix_width else f"fub_axi_{chan}id"

    @property
    def rr_local_idx(self):
        """Index of the internal (subtractive) slave, or None. A read-return
        atomic that decodes to it gets its R beat generated HERE: that slave
        answers DECERR on B and knows nothing about R, and without a local
        answer the port's R-return tracker would hold a slot for a beat that
        never comes -- every later read blocked behind it, which is the shape
        of bridge BUG-007 (was BRIDGE-009) on the atomic path."""
        if not self.rr_atomic:
            return None
        for i, s in enumerate(self.slaves):
            if getattr(s, 'internal', False):
                return i
        return None

    def _trace_capable_mask(self) -> str:
        """Representative-slave mask of width paths whose EVERY connected
        slave implements trace. {b,r}_slave_select names a path by one
        representative slave (the response mux is per path), so a per-slave
        mask would check the wrong slave whenever a path mixes trace-capable
        and trace-less slaves; such a path is simply not checked."""
        from bridge_pkg.sideband import port_features
        conn = [i for i in self.master.slave_connections]
        groups = {}
        for i in conn:
            groups.setdefault(self.slaves[i].data_width, []).append(i)
        rep_ok = {g[0] for g in groups.values()
                  if all('trace' in port_features(self.slaves[i]) for i in g)}
        bits = ''.join('1' if i in rep_ok else '0'
                       for i in range(len(self.slaves) - 1, -1, -1))
        return f"{len(self.slaves)}'b{bits}"

    def _trace_capable_slave_mask(self) -> str:
        """One-hot mask of connected slaves that implement trace themselves."""
        from bridge_pkg.sideband import port_features
        bits = ''.join(
            '1' if (i in self.master.slave_connections
                    and 'trace' in port_features(self.slaves[i])) else '0'
            for i in range(len(self.slaves) - 1, -1, -1))
        return f"{len(self.slaves)}'b{bits}"

    def _trace_echo_lines(self, resp: str) -> List[str]:
        """Drive {b,r}trace from the tracked request trace, and check the
        slave's own bit against it wherever the slave implements trace."""
        chan = 'aw' if resp == 'b' else 'ar'
        sel = f"{resp}_slave_select" if resp == 'b' else "r_slave_select"
        return [
            "",
            f"    // bridge BUG-010 (was BRIDGE-012): the port promises trace; echo the request's bit.",
            f"    assign fub_axi_{resp}trace = {resp}_trk_trace;",
            "",
            "`ifndef SYNTHESIS",
            f"    // A slave that DOES implement trace must echo it too. Echoing at the",
            f"    // boundary keeps this port correct whatever the slave does, but it",
            f"    // must not launder a trace-capable slave that returns the wrong bit.",
            f"    localparam logic [NUM_SLAVES-1:0] {resp.upper()}_TRACE_CAPABLE = {self._trace_capable_mask()};",
            "    always_ff @(posedge aclk) begin",
            f"        if (aresetn && fub_axi_{resp}valid && fub_axi_{resp}ready &&",
            f"            |({sel} & {resp.upper()}_TRACE_CAPABLE) &&",
            f"            ({resp}_slave_trace !== {resp}_trk_trace)) begin",
            f'            $error("%m: bridge BUG-010 (was BRIDGE-012): trace-capable slave returned {resp}trace=%b for a request with trace=%b",',
            f"                   {resp}_slave_trace, {resp}_trk_trace);",
            "        end",
            "    end",
            "`endif",
        ]

    def _sb_wire_decls(self) -> List[str]:
        """fub_axi_* wire declarations for this master's own sideband
        features (both directions; the wrapper's fub side binds them)."""
        lines = []
        if not self.sb_own:
            return lines
        chans = []
        if self.master.channels in ("wr", "rw"):
            chans += ['aw', 'w', 'b']
        if self.master.channels in ("rd", "rw"):
            chans += ['ar', 'r']
        from bridge_pkg.sideband import channel_fields
        for ch in chans:
            for _f, width, feat, base in channel_fields(self.sb_own, ch, self.master.data_width):
                decl = ("    logic         " if width == 1
                        else f"    logic [{width-1}:0]  ")
                lines.append(f"{decl}fub_axi_{base};  // AXI5 sideband ({feat})")
        if lines:
            lines.insert(0, "    // AXI5 native sideband (A5-2 slice 2)")
            lines.append("")
        return lines

    def _sb_pack_lines(self, channel, suffix) -> List[str]:
        """Direct-path struct packs for `channel`: own features come
        from the fub wires, other union fields tie '0."""
        lines = []
        from bridge_pkg.sideband import field_width, fit_expr, struct_dw
        for field, w, feat, base in self._sb_fields(channel, self.sb_union):
            dst = f"{self.master.name}_{suffix}_{channel}.{field}"
            if feat in self.sb_own:
                # the direct arm's path width is this master's own
                sw = field_width(w, struct_dw(channel, self.master.data_width, self.bridge_max_dw))
                fw = field_width(w, self.master.data_width)
                lines.append(f"    assign {dst} = {fit_expr(f'fub_axi_{base}', fw, sw)};  // AXI5 sideband")
            else:
                lines.append(f"    assign {dst} = '0;  // AXI5 sideband (not on this master)")
        return lines

    def _sb_conv_tie_lines(self, suffix) -> List[str]:
        """Converter-path struct sideband ties: per-transaction and
        per-beat sideband cannot traverse the dwidth-converter IP, so
        every union field packs '0 on this path."""
        lines = []
        chans = []
        if self.master.channels in ("wr", "rw"):
            chans += ['aw', 'w']
        if self.master.channels in ("rd", "rw"):
            chans += ['ar']
        for ch in chans:
            for field, _w, _feat, _b in self._sb_fields(ch, self.sb_union):
                lines.append(
                    f"    assign {self.master.name}_{suffix}_{ch}.{field} = '0;"
                    f"  // AXI5 sideband: dropped across dwidth conversion")
        if lines:
            lines.append("")
        return lines

    # --- GitHub #102 item 5: BIDUNQ/RIDUNQ and AWAKEUP at the boundary ----
    @property
    def has_idunq(self) -> bool:
        """This AXI5 master port carries the unique-ID indicators."""
        from bridge_pkg.sideband import port_features
        return 'unique' in port_features(self.master)

    @property
    def has_wakeup(self) -> bool:
        """This AXI5 master port carries AWAKEUP (A14.1.1)."""
        from bridge_pkg.sideband import port_features
        return 'wakeup' in port_features(self.master)

    @property
    def wr_fub_prefix(self) -> str:
        """Net prefix on the wr wrapper's fub face: pref_axi_ when the
        atomic filter sits between it and the fabric, else fub_axi_."""
        return ('pref_axi_' if ('atomic' in self.sb_own and not self.rr_atomic)
                else 'fub_axi_')

    def _boundary_wire_decls(self) -> List[str]:
        """Nets the boundary drives or consumes that are not struct
        sideband: the regenerated BIDUNQ/RIDUNQ and the per-wrapper
        AWAKEUP copies."""
        lines = []
        wr = self.master.channels in ("wr", "rw")
        rd = self.master.channels in ("rd", "rw")
        if self.has_idunq:
            if wr:
                lines.append(f"    logic         {self.wr_fub_prefix}bidunq;  // regenerated (A5.2)")
            if rd:
                lines.append("    logic         fub_axi_ridunq;  // regenerated (A5.2)")
        if self.has_wakeup:
            if wr:
                lines.append("    logic         w_awakeup_wr;    // wr wrapper's AWAKEUP copy")
            if rd:
                lines.append("    logic         w_awakeup_rd;    // rd wrapper's AWAKEUP copy")
        if lines:
            lines.insert(0, "    // AXI5 boundary-generated signals (GitHub #102 item 5)")
            lines.append("")
        return lines

    def _idunq_echo_lines(self) -> List[str]:
        """Regenerate BIDUNQ/RIDUNQ from the request indicator (A5.2).

        A5.2 makes the response indicator a function of the request:
        BIDUNQ == AWIDUNQ, RIDUNQ == ARIDUNQ, and an atomic's RIDUNQ ==
        its AWIDUNQ. The request indicator is droppable sideband (it does
        not survive an AXI4 slave, a dwidth converter, the subtractive
        DECERR slave or the atomic filter's local response), so the
        slave's copy cannot be forwarded. Instead the boundary remembers
        the indicator PER ID: A5.2 forbids an AxIDUNQ=1 request while any
        same-ID request is outstanding and any request reusing the ID of
        an outstanding AxIDUNQ=1 one, so every outstanding transaction of
        one ID carries the same indicator and a per-ID bit is exact under
        any response order. Atomic IDs are unique across both directions
        (A6.4), so a read-return atomic may write the read table too."""
        if not self.has_idunq:
            return []
        idw = self.fub_id_width
        lines = [
            "",
            "    // ================================================================",
            "    // BIDUNQ / RIDUNQ regenerated per ID (IHI 0022L A5.2)",
            "    // ================================================================",
            f"    localparam int IDUNQ_IDS = 1 << {idw};",
        ]
        if self.master.channels in ("wr", "rw"):
            p = self.wr_fub_prefix
            lines += [
                "    logic [IDUNQ_IDS-1:0] r_awidunq_by_id;",
                "    `ALWAYS_FF_RST(aclk, aresetn,",
                "        if (`RST_ASSERTED(aresetn)) begin",
                "            r_awidunq_by_id <= '0;",
                f"        end else if ({p}awvalid && {p}awready) begin",
                f"            r_awidunq_by_id[{p}awid] <= {p}awidunq;",
                "        end",
                "    )",
                f"    assign {p}bidunq = r_awidunq_by_id[{p}bid];",
            ]
        if self.master.channels in ("rd", "rw"):
            lines += [
                "    logic [IDUNQ_IDS-1:0] r_aridunq_by_id;",
                "    `ALWAYS_FF_RST(aclk, aresetn,",
                "        if (`RST_ASSERTED(aresetn)) begin",
                "            r_aridunq_by_id <= '0;",
                "        end else begin",
                "            if (fub_axi_arvalid && fub_axi_arready)",
                "                r_aridunq_by_id[fub_axi_arid] <= fub_axi_aridunq;",
            ]
            if self.rr_atomic:
                lines += [
                    "            // A read-return atomic's R carries the AW ID and AWIDUNQ.",
                    "            if (fub_axi_awvalid && fub_axi_awready && fub_axi_awatop[5])",
                    "                r_aridunq_by_id[fub_axi_awid] <= fub_axi_awidunq;",
                ]
            lines += [
                "        end",
                "    )",
                "    assign fub_axi_ridunq = r_aridunq_by_id[fub_axi_rid];",
            ]
        lines.append("")
        return lines

    def _wakeup_out_lines(self) -> List[str]:
        """One AWAKEUP covers both request channels (A14.1.1): OR the two
        wrappers' copies. Each copy is the external AWAKEUP OR'd with the
        wrapper's own held-request flops, so the OR stays glitch-free."""
        if not self.has_wakeup:
            return []
        terms = []
        if self.master.channels in ("wr", "rw"):
            terms.append("w_awakeup_wr")
        if self.master.channels in ("rd", "rw"):
            terms.append("w_awakeup_rd")
        return [
            "    // AWAKEUP toward the wake-capable slave ports (A14.1.1)",
            f"    assign wakeup_req = {' | '.join(terms)};",
            "",
        ]

    def _generate_atomic_filter(self) -> List[str]:
        """axi5_atomic_filter between the wr wrapper (pref_axi_*) and
        the fabric-facing fub_axi_* namespace (A5-3a). Handshakes and
        the B payload go THROUGH the filter; everything else is a
        payload pass-through. Swallowed (read-return) atomics never
        assert fub_axi_awvalid, so stale pass-through payload is inert.
        btrace passes through untouched: a local DECERR response
        carries whatever the mux holds, which the AXI atomic ID rule
        keeps a compliant master from pairing with a traced write.

        Only write-only ports carry the filter (an rw port forwards
        read-return atomics natively, see rr_atomic), so its R channel
        has no upstream to merge into: the local R beats are drained and
        discarded and the downstream R input is idle. BIDUNQ, when the
        port has it, is regenerated on the pref side of the filter
        (_idunq_echo_lines), so a local DECERR carries the right bit."""
        lines = []
        lines.append("    // ================================================================")
        lines.append("    // axi5_atomic_filter: DECERR read-return atomics locally;")
        lines.append("    // store-class atomics and plain writes pass through (A5-3a)")
        lines.append("    // ================================================================")
        for sig in ('awid', 'awaddr', 'awlen', 'awsize', 'awburst',
                    'awlock', 'awcache', 'awprot', 'awqos', 'awuser',
                    'wdata', 'wstrb', 'wlast', 'wuser'):
            lines.append(f"    assign fub_axi_{sig} = pref_axi_{sig};")
        for ch in ('aw', 'w'):
            for _f, _w, _feat, base in self._sb_fields(ch, self.sb_own):
                lines.append(f"    assign fub_axi_{base} = pref_axi_{base};")
        for _f, _w, _feat, base in self._sb_fields('b', self.sb_own):
            lines.append(f"    assign pref_axi_{base} = fub_axi_{base};")
        lines.append("")
        lines.append("    axi5_atomic_filter #(")
        lines.append(f"        .AXI_ID_WIDTH({self.fub_id_width})")
        lines.append("    ) u_atomic_filter (")
        lines.append("        .aclk(aclk),")
        lines.append("        .aresetn(aresetn),")
        lines.append("        .s_awvalid(pref_axi_awvalid),")
        lines.append("        .s_awready(pref_axi_awready),")
        lines.append("        .s_awid(pref_axi_awid),")
        lines.append("        .s_awatop(pref_axi_awatop),")
        lines.append("        .s_awlen(pref_axi_awlen),")
        lines.append("        .s_wvalid(pref_axi_wvalid),")
        lines.append("        .s_wready(pref_axi_wready),")
        lines.append("        .s_wlast(pref_axi_wlast),")
        lines.append("        .s_bvalid(pref_axi_bvalid),")
        lines.append("        .s_bready(pref_axi_bready),")
        lines.append("        .s_bid(pref_axi_bid),")
        lines.append("        .s_bresp(pref_axi_bresp),")
        lines.append("        // R: a write-only port has no read data channel, so the read")
        lines.append("        // transfers the filter owes a swallowed load-class atomic")
        lines.append("        // (A6.4.8) have nowhere to go. They are accepted and discarded")
        lines.append("        // (s_rready=1) so the filter's read-return queue drains and never")
        lines.append("        // stalls AW; the atomic completes with DECERR on B only. A manager")
        lines.append("        // must not issue load-class atomics on a write-only port (HAS 4.4).")
        lines.append("        .s_rvalid(),")
        lines.append("        .s_rready(1'b1),")
        lines.append("        .s_rid(),")
        lines.append("        .s_rresp(),")
        lines.append("        .s_rlast(),")
        lines.append("        .m_awvalid(fub_axi_awvalid),")
        lines.append("        .m_awready(fub_axi_awready),")
        lines.append("        .m_wvalid(fub_axi_wvalid),")
        lines.append("        .m_wready(fub_axi_wready),")
        lines.append("        .m_bvalid(fub_axi_bvalid),")
        lines.append("        .m_bready(fub_axi_bready),")
        lines.append("        .m_bid(fub_axi_bid),")
        lines.append("        .m_bresp(fub_axi_bresp),")
        lines.append("        // No downstream R on a write-only port.")
        lines.append("        .m_rvalid(1'b0),")
        lines.append("        .m_rready(),")
        lines.append("        .m_rid('0),")
        lines.append("        .m_rresp(2'b00),")
        lines.append("        .m_rlast(1'b0)")
        lines.append("    );")
        lines.append("")
        return lines

    @property
    def fub_id_width(self) -> int:
        """ID width of the adapter's INTERNAL AXI4 face.

        An AXI4-Lite master port has id_width 0, and used unclamped that makes
        every `fub_axi_*id` declaration `logic [-1:0]` -- malformed
        SystemVerilog that Verilator happens to elaborate as 2 bits and other
        tools may reject outright.

        The placeholder width is the BRIDGE's struct ID width, not 1. AXI4-Lite
        carries no ID, so the value is a don't-care and any consistent width is
        correct -- but this face connects directly to the crossbar's channel
        structs, whose `id` field is that width. Picking 1 instead leaves every
        one of those connections width-mismatched, which Verilator reports as
        WIDTHEXPAND on the way in and WIDTHTRUNC on the way out. Same
        expression as bridge_module_generator uses to size the package structs,
        so the two cannot disagree.

        EVERY site that sizes something on this face reads this, including the
        parameter overrides of instantiated modules. Clamping only the
        declarations (as the first version of this fix did) leaves the
        instantiated module's own ports at [-1:0] while the nets driving them
        are a different width -- Verilator reports ASCRANGE and the build dies
        on warnings, which is how this was found.
        """
        if self.master.id_width:
            return self.master.id_width
        masters = self.all_masters or [self.master]
        return max([max(1, m.id_width or 0) for m in masters] or [4])

    def _generate_internal_signals(self) -> List[str]:
        """Generate internal signal declarations (fub_axi_*)."""
        lines = []
        id_width = self.fub_id_width
        addr_width = 32  # Use global 32-bit address width
        data_width = self.master.data_width
        strb_width = data_width // 8

        lines.append("    // ================================================================")
        lines.append("    // Localparams")
        lines.append("    // ================================================================")
        lines.append(f"    localparam ADDR_WIDTH = {addr_width};")
        lines.append(f"    localparam DATA_WIDTH = {data_width};")
        lines.append(f"    localparam ID_WIDTH = {id_width};")
        lines.append("")
        lines.append("    // ================================================================")
        lines.append("    // Internal signals after wrapper (timing isolation)")
        if self.master.id_width:
            lines.append(f"    // Note: ID width matches external ({id_width}-bit)")
        else:
            lines.append(f"    // Note: {id_width}-bit ID placeholder. This port is AXI4-Lite and")
            lines.append( "    // has no external ID; the width matches the crossbar's struct")
            lines.append( "    // field so every connection to it is width-exact. The value is")
            lines.append( "    // tied to zero end to end.")
        lines.append("    // ================================================================")

        # Write channels
        if self.master.channels in ["wr", "rw"]:
            lines.append(f"    logic [{id_width-1}:0]   fub_axi_awid;")
            lines.append(f"    logic [{addr_width-1}:0]  fub_axi_awaddr;")
            lines.append("    logic [7:0]   fub_axi_awlen;")
            lines.append("    logic [2:0]   fub_axi_awsize;")
            lines.append("    logic [1:0]   fub_axi_awburst;")
            lines.append("    logic         fub_axi_awlock;")
            lines.append("    logic [3:0]   fub_axi_awcache;")
            lines.append("    logic [2:0]   fub_axi_awprot;")
            lines.append("    logic [3:0]   fub_axi_awqos;")
            if self.master.protocol != 'axi5':
                lines.append("    logic [3:0]   fub_axi_awregion;")
            lines.append("    logic         fub_axi_awuser;")
            lines.append("    logic         fub_axi_awvalid;")
            lines.append("    logic         fub_axi_awready;")
            lines.append("")

            lines.append(f"    logic [{data_width-1}:0]  fub_axi_wdata;")
            lines.append(f"    logic [{strb_width-1}:0]   fub_axi_wstrb;")
            lines.append("    logic         fub_axi_wlast;")
            lines.append("    logic         fub_axi_wuser;")
            lines.append("    logic         fub_axi_wvalid;")
            lines.append("    logic         fub_axi_wready;")
            lines.append("")

            lines.append(f"    logic [{id_width-1}:0]   fub_axi_bid;")
            lines.append("    logic [1:0]   fub_axi_bresp;")
            lines.append("    logic         fub_axi_bvalid;")
            lines.append("    logic         fub_axi_bready;")
            lines.append("")

        # Read channels
        if self.master.channels in ["rd", "rw"]:
            lines.append(f"    logic [{id_width-1}:0]   fub_axi_arid;")
            lines.append(f"    logic [{addr_width-1}:0]  fub_axi_araddr;")
            lines.append("    logic [7:0]   fub_axi_arlen;")
            lines.append("    logic [2:0]   fub_axi_arsize;")
            lines.append("    logic [1:0]   fub_axi_arburst;")
            lines.append("    logic         fub_axi_arlock;")
            lines.append("    logic [3:0]   fub_axi_arcache;")
            lines.append("    logic [2:0]   fub_axi_arprot;")
            lines.append("    logic [3:0]   fub_axi_arqos;")
            if self.master.protocol != 'axi5':
                lines.append("    logic [3:0]   fub_axi_arregion;")
            lines.append("    logic         fub_axi_aruser;")
            lines.append("    logic         fub_axi_arvalid;")
            lines.append("    logic         fub_axi_arready;")
            lines.append("")

            lines.append(f"    logic [{id_width-1}:0]   fub_axi_rid;")
            lines.append(f"    logic [{data_width-1}:0]  fub_axi_rdata;")
            lines.append("    logic [1:0]   fub_axi_rresp;")
            lines.append("    logic         fub_axi_rlast;")
            lines.append("    logic         fub_axi_rvalid;")
            lines.append("    logic         fub_axi_rready;")
            lines.append("")

        # Wrapper busy signals
        if self.master.channels in ["wr", "rw"]:
            lines.append("    logic         wrapper_wr_busy;")
        if self.master.channels in ["rd", "rw"]:
            lines.append("    logic         wrapper_rd_busy;")
        lines.append("")

        # AXI5 native-sideband fub wires (A5-2 slice 2)
        lines.extend(self._sb_wire_decls())
        lines.extend(self._boundary_wire_decls())

        # bridge TASK-005 (was BRIDGE-016): fabric-facing IDs carry this master's index on top.
        if self.id_prefix_width:
            lines.append("    // Master-unique fabric IDs: {BRIDGE_ID, id} (bridge TASK-005, was BRIDGE-016). Responses")
            lines.append("    // return with the prefix; the response muxes select the low bits.")
            if self.master.channels in ("wr", "rw"):
                lines.append("    logic [XBAR_ID_WIDTH-1:0] xbar_axi_awid;")
                lines.append("    assign xbar_axi_awid = {BRIDGE_ID_WIDTH'(BRIDGE_ID), MASTER_ID_WIDTH'(fub_axi_awid)};")
            if self.master.channels in ("rd", "rw"):
                lines.append("    logic [XBAR_ID_WIDTH-1:0] xbar_axi_arid;")
                lines.append("    assign xbar_axi_arid = {BRIDGE_ID_WIDTH'(BRIDGE_ID), MASTER_ID_WIDTH'(fub_axi_arid)};")
            lines.append("")

        # Pre-filter (wrapper-side) wr signals when this master carries
        # 'atomic' on a write-only port (A5-3a): the axi5_atomic_filter sits
        # pref -> fub. An rw atomic port forwards read-return atomics
        # natively (A5-3b, see rr_atomic) and needs no filter.
        if 'atomic' in self.sb_own and not self.rr_atomic:
            id_w = self.fub_id_width
            dw = self.master.data_width
            lines.append("    // Pre-filter wr signals (axi5_atomic_filter upstream side)")
            lines.append(f"    logic [{id_w-1}:0]   pref_axi_awid;")
            lines.append("    logic [31:0]  pref_axi_awaddr;")
            lines.append("    logic [7:0]   pref_axi_awlen;")
            lines.append("    logic [2:0]   pref_axi_awsize;")
            lines.append("    logic [1:0]   pref_axi_awburst;")
            lines.append("    logic         pref_axi_awlock;")
            lines.append("    logic [3:0]   pref_axi_awcache;")
            lines.append("    logic [2:0]   pref_axi_awprot;")
            lines.append("    logic [3:0]   pref_axi_awqos;")
            lines.append("    logic         pref_axi_awuser;")
            lines.append("    logic         pref_axi_awvalid;")
            lines.append("    logic         pref_axi_awready;")
            lines.append(f"    logic [{dw-1}:0]  pref_axi_wdata;")
            lines.append(f"    logic [{dw//8-1}:0]   pref_axi_wstrb;")
            lines.append("    logic         pref_axi_wlast;")
            lines.append("    logic         pref_axi_wuser;")
            lines.append("    logic         pref_axi_wvalid;")
            lines.append("    logic         pref_axi_wready;")
            lines.append(f"    logic [{id_w-1}:0]   pref_axi_bid;")
            lines.append("    logic [1:0]   pref_axi_bresp;")
            lines.append("    logic         pref_axi_bvalid;")
            lines.append("    logic         pref_axi_bready;")
            for ch in ('aw', 'w', 'b'):
                for _f, width, feat, base in self._sb_fields(ch, self.sb_own):
                    decl = ("    logic         " if width == 1
                            else f"    logic [{width-1}:0]  ")
                    lines.append(f"{decl}pref_axi_{base};")
            lines.append("")

        return lines

    def _generate_wrapper(self) -> List[str]:
        """Generate timing wrapper instantiations via the typed
        Axi4TimingWrapper component (one axi4_slave_wr and one
        axi4_slave_rd, modulo channels)."""
        from ..components.axi4_timing_wrapper_component import Axi4TimingWrapper

        lines: List[str] = []

        # Use the master's configured prefix so the adapter's wrapper port
        # connections match its external port names (which are built from
        # master.prefix). Normalise to ensure a trailing `_` separator:
        # configs sometimes set prefix="cpu_m_axi" without one, which
        # would produce "cpu_m_axiawid".
        signal_prefix = self.master.prefix
        if signal_prefix and not signal_prefix.endswith("_"):
            signal_prefix = signal_prefix + "_"

        # A front-end requester port has no external AXI4 signals; the
        # wrapper's external side connects to the AXI4 face the converter
        # drives (APB/WB4/AXI3 front end).
        if self.is_front_end_master:
            lines.extend(self._generate_front_end())
            signal_prefix = self.front_end_prefix

        # A CDC port (GitHub #119 L2) is crossed onto aclk first; the
        # wrapper's external side then takes the aclk-side nets.
        if self.is_cdc:
            lines.extend(self._generate_cdc_stage(signal_prefix, self.CDC_AXI_PREFIX))
            signal_prefix = self.CDC_AXI_PREFIX

        # Monitor identity: UNIT_ID=2 marks every master-side wrapper
        # (axi4_slave_*_mon -- the bridge looks like a slave to the
        # external master), AGENT_ID = (master_index << 4) | channel_bit
        # so each per-port wrapper produces uniquely tagged monbus packets.
        # channel_bit: 0 = rd, 1 = wr. Mirrors the SV defaults' UNIT_ID=2.
        master_unit_id = 2 if self.enable_monitoring else None
        wr_agent_id = ((self.master_index << 4) | 0x1) if self.enable_monitoring else None
        rd_agent_id = ((self.master_index << 4) | 0x0) if self.enable_monitoring else None

        # Boundary wrapper family: an axi5 master port gets the
        # axi5_slave_* wrappers (AXI5 external face, AXI4 fub face --
        # sideband features terminate at the wrapper). Everything else
        # ('axi4' and 'axil', whose adapter still speaks full AXI4)
        # keeps the axi4_slave_* wrappers.
        wrapper_protocol = 'axi5' if self.master.protocol == 'axi5' else 'axi4'
        wrapper_features = (list(self.master.axi5_features or [])
                            if wrapper_protocol == 'axi5' else None)

        # Write wrapper
        if self.master.channels in ["wr", "rw"]:
            wrapper = Axi4TimingWrapper(
                side='slave', channel='wr', mon=self.enable_monitoring,
                instance_name='u_timing_wrapper_wr',
                id_width=self.fub_id_width,
                addr_width=32,
                data_width=self.master.data_width,
                # The SV module sets default skid depths from top-level
                # bridge parameters; pass those parameter names through
                # so the override block references SKID_DEPTH_AW/W/B.
                skid_depth_ax='SKID_DEPTH_AW',
                skid_depth_data='SKID_DEPTH_W',
                skid_depth_resp='SKID_DEPTH_B',
                unit_id=master_unit_id,
                agent_id=wr_agent_id,
                use_monitor_param=(
                    'USE_MONITOR_WR' if self.enable_monitoring else None
                ),
                mon_enables=(self.master.mon_enables
                             if self.enable_monitoring else None),
                protocol=wrapper_protocol,
                axi5_features=wrapper_features,
                native_sideband=bool(self.sb_own),
            )
            wrapper.connect_clocks_and_resets()
            # External side comes from the master's prefix (slave-of-
            # external-master). Bridge-internal side uses fub_axi_*,
            # EXCEPT when this master carries 'atomic': then the wr
            # wrapper lands on pref_axi_* and the axi5_atomic_filter
            # sits between pref and fub (A5-3a — read-return atomics
            # must not reach a fabric that cannot route their R data).
            wrapper.connect_external(connector_prefix=signal_prefix)
            wr_fub_prefix = self.wr_fub_prefix
            wrapper.connect_bridge_internal(
                connector_prefix=wr_fub_prefix,
                overrides=({'awakeup': 'w_awakeup_wr'} if self.has_wakeup else None))
            wrapper.add_status(busy_connector='wrapper_wr_busy')
            if self.enable_monitoring:
                wrapper.connect_monbus(
                    valid='monbus_wr_valid',
                    ready='monbus_wr_ready',
                    packet='monbus_wr_packet',
                    timestamp='monbus_wr_timestamp',
                    mon_time='i_mon_time',
                )
                wrapper.connect_cfg(connector_prefix='cfg_wr_')
                wrapper.add_addr_range_tieoff()
                wrapper.add_perfmon_tieoff()
            lines.append("    // ================================================================")
            lines.append(f"    // Timing isolation wrapper ({wrapper_protocol}_slave_wr{'_monlite' if self.enable_monitoring else ''})")
            lines.append("    // ================================================================")
            lines.extend(wrapper.generate_lines())
            if 'atomic' in self.sb_own and not self.rr_atomic:
                lines.extend(self._generate_atomic_filter())

        # Read wrapper
        if self.master.channels in ["rd", "rw"]:
            wrapper = Axi4TimingWrapper(
                side='slave', channel='rd', mon=self.enable_monitoring,
                instance_name='u_timing_wrapper_rd',
                id_width=self.fub_id_width,
                addr_width=32,
                data_width=self.master.data_width,
                skid_depth_ax='SKID_DEPTH_AR',
                skid_depth_data='SKID_DEPTH_R',
                unit_id=master_unit_id,
                agent_id=rd_agent_id,
                use_monitor_param=(
                    'USE_MONITOR_RD' if self.enable_monitoring else None
                ),
                mon_enables=(self.master.mon_enables
                             if self.enable_monitoring else None),
                protocol=wrapper_protocol,
                axi5_features=wrapper_features,
                native_sideband=bool(self.sb_own),
            )
            wrapper.connect_clocks_and_resets()
            wrapper.connect_external(connector_prefix=signal_prefix)
            wrapper.connect_bridge_internal(
                connector_prefix='fub_axi_',
                overrides=({'awakeup': 'w_awakeup_rd'} if self.has_wakeup else None))
            wrapper.add_status(busy_connector='wrapper_rd_busy')
            if self.enable_monitoring:
                wrapper.connect_monbus(
                    valid='monbus_rd_valid',
                    ready='monbus_rd_ready',
                    packet='monbus_rd_packet',
                    timestamp='monbus_rd_timestamp',
                    mon_time='i_mon_time',
                )
                wrapper.connect_cfg(connector_prefix='cfg_rd_')
                wrapper.add_addr_range_tieoff()
                wrapper.add_perfmon_tieoff()
            lines.append("    // ================================================================")
            lines.append(f"    // Timing isolation wrapper ({wrapper_protocol}_slave_rd{'_monlite' if self.enable_monitoring else ''})")
            lines.append("    // ================================================================")
            lines.extend(wrapper.generate_lines())

        lines.extend(self._idunq_echo_lines())
        lines.extend(self._wakeup_out_lines())
        return lines

    def _generate_address_decode(self) -> List[str]:
        """Generate address decode logic.

        The internal `comb_slave_select_{ar,aw}` are combinational decodes
        of `fub_axi_{ar,aw}addr`. They are valid only while {ar,aw}valid is
        asserted -- after the handshake completes the address bus reverts
        and the decode flips back to slave 0 (or all-zero), so anything
        downstream that needs to know which slave a request was targeted
        at *after* the handshake (the xbar AR/AW gating, the B/R response
        MUX) must use the FIFO-tracked output `slave_select_{ar,aw}`
        instead. See _generate_response_mux for the tracking FIFOs.
        """
        lines = []

        # Forward-declare the FIFO-head signals so width-adaptation
        # can use them for response/data gating. Drivers live in
        # _generate_response_mux further down.
        #   b_slave_select : AW->B order, popped on B (response MUX)
        #   w_slave_select : AW->W order, popped on W (wlast). W needs
        #                    its OWN FIFO because multiple writes can
        #                    be in flight (AW#1, AW#2 issued; W#1 may
        #                    still be streaming when W#2 starts). Gating
        #                    W on b_slave_select would hold W#2 routing
        #                    on AW#1's slave until B#1 returns, stamping
        #                    W#2's data onto AW#1's path. Real bug --
        #                    caught by the multi-master memory-backed TB.
        #   r_slave_select : AR->R order, popped on R-last (response MUX)
        if self.master.channels in ("wr", "rw"):
            lines.append("    logic [NUM_SLAVES-1:0] b_slave_select;")
            lines.append("    logic [NUM_SLAVES-1:0] w_slave_select;")
        if self.master.channels in ("rd", "rw"):
            lines.append("    logic [NUM_SLAVES-1:0] r_slave_select;")
        if self.rr_atomic:
            lines.append("    // A5-3b: a read-return atomic (AWATOP[5]) answers on R, so its AW")
            lines.append("    // is also counted in the AR per-ID table under its AWID and must pass")
            lines.append("    // the read side's per-ID gate. Declared here, driven in the")
            lines.append("    // read-tracking section, consumed by aw_gate_ok.")
            lines.append("    wire  aw_rr_atomic = fub_axi_awatop[5];")
            lines.append("    logic aw_rr_gate_ok;")
            if self.rr_local_idx is not None:
                lines.append("    // ... and one that decoded to the subtractive slave is answered locally")
                lines.append("    // on R (DECERR); r_local_head is the R path arbiter's grant to it.")
                lines.append("    logic r_local_head;")
        lines.append("")

        # Write address decode
        if self.master.channels in ["wr", "rw"]:
            lines.append("    // ================================================================")
            lines.append("    // Address decode (slave selection) - Write")
            lines.extend(self._generate_decode_comment())
            lines.append("    // ================================================================")
            lines.append("    logic [NUM_SLAVES-1:0] comb_slave_select_aw;")
            lines.append("    always_comb begin")
            lines.append("        comb_slave_select_aw = '0;")
            lines.extend(self._generate_decode_logic("fub_axi_awaddr", "comb_slave_select_aw"))
            lines.append("    end")
            lines.append("")
            lines.append("    // Bridge ID for write channel (constant - tied to BRIDGE_ID parameter)")
            lines.append(f"    assign bridge_id_aw = BRIDGE_ID_WIDTH'(BRIDGE_ID);")
            lines.append("")

        # Read address decode
        if self.master.channels in ["rd", "rw"]:
            lines.append("    // ================================================================")
            lines.append("    // Address decode (slave selection) - Read")
            lines.extend(self._generate_decode_comment())
            lines.append("    // ================================================================")
            lines.append("    logic [NUM_SLAVES-1:0] comb_slave_select_ar;")
            lines.append("    always_comb begin")
            lines.append("        comb_slave_select_ar = '0;")
            lines.extend(self._generate_decode_logic("fub_axi_araddr", "comb_slave_select_ar"))
            lines.append("    end")
            lines.append("")
            lines.append("    // Bridge ID for read channel (constant - tied to BRIDGE_ID parameter)")
            lines.append(f"    assign bridge_id_ar = BRIDGE_ID_WIDTH'(BRIDGE_ID);")
            lines.append("")

        return lines

    def _generate_decode_comment(self) -> List[str]:
        """Generate comment listing slave address ranges."""
        lines = []
        for idx in self.master.slave_connections:
            slave = self.slaves[idx]
            lines.append(f"    // Slave {idx} ({slave.name}): 0x{slave.base_addr:08X} - 0x{slave.base_addr + slave.addr_range - 1:08X}")
        return lines

    def _generate_decode_logic(self, addr_signal: str, select_signal: str) -> List[str]:
        """Generate address decode logic for one channel."""
        lines = []
        addr_width = 32  # Use global 32-bit address width
        max_addr = (1 << addr_width) - 1  # Maximum address value for this width

        # Simple decode based on address ranges
        for i, idx in enumerate(self.master.slave_connections):
            slave = self.slaves[idx]
            end_addr = slave.base_addr + slave.addr_range - 1

            # Build comparison string intelligently to avoid Verilator warnings
            # - Skip "addr >= 0" (unsigned is always >= 0)
            # - Skip "addr <= max" when max is full address range

            if slave.base_addr == 0 and end_addr == max_addr:
                # Full address range - no comparison needed (catch-all)
                if i == 0:
                    lines.append(f"        if (1'b1) begin  // Full address range")
                else:
                    lines.append(f"        else begin  // Full address range (catch-all)")
            elif slave.base_addr == 0:
                # Starts at 0 - only upper bound check
                if i == 0:
                    lines.append(f"        if ({addr_signal} <= {addr_width}'h{end_addr:08X}) begin")
                else:
                    lines.append(f"        else if ({addr_signal} <= {addr_width}'h{end_addr:08X}) begin")
            elif end_addr == max_addr:
                # Ends at max - only lower bound check
                if i == 0:
                    lines.append(f"        if ({addr_signal} >= {addr_width}'h{slave.base_addr:08X}) begin")
                else:
                    lines.append(f"        else if ({addr_signal} >= {addr_width}'h{slave.base_addr:08X}) begin")
            else:
                # Both bounds needed
                if i == 0:
                    lines.append(f"        if ({addr_signal} >= {addr_width}'h{slave.base_addr:08X} && {addr_signal} <= {addr_width}'h{end_addr:08X}) begin")
                else:
                    lines.append(f"        else if ({addr_signal} >= {addr_width}'h{slave.base_addr:08X} && {addr_signal} <= {addr_width}'h{end_addr:08X}) begin")

            lines.append(f"            {select_signal}[{idx}] = 1'b1;  // {slave.name}")
            lines.append("        end")

        return lines

    def _get_connected_slave_widths(self) -> List[int]:
        """
        Get unique adapter output widths for slaves this master connects to.

        Delegates to width_utils.get_connected_slave_widths — see its
        docstring for why slave.data_width is always used (LCD bug history).
        """
        return get_connected_slave_widths(self.master, self.slaves)

    def _generate_width_adaptation(self) -> List[str]:
        """
        Generate width converters and/or direct passthrough.

        Creates one output path per unique slave width:
        - If master_width == slave_width: direct passthrough
        - If master_width != slave_width: converter instance
        """
        lines = []

        # Get unique slave widths this master connects to
        slave_widths = self._get_connected_slave_widths()

        lines.append("    // ================================================================")
        lines.append(f"    // Width adaptation - Master: {self.master.data_width}b")
        lines.append(f"    // Connected to slaves with widths: {slave_widths}")
        lines.append("    // ================================================================")
        lines.append("")

        # Per-width valid gating. fub_axi_awvalid/fub_axi_arvalid is
        # broadcast to every width path, so without gating an unselected
        # converter would accept the AW (its s_axi_awready handshakes
        # locally) and then sit stuck waiting for an m_axi_awready that
        # never comes — leaking the stuck transaction into the wrong slave
        # when the NEXT transaction's slave_select happens to match.
        # `<W>b_aw_path_active` is HIGH only when the currently-selected
        # slave actually has data_width == W; we feed it into each
        # converter/passthrough's s_axi_awvalid (and s_axi_arvalid for
        # reads) so only the matching path sees the request.
        if slave_widths and (self.master.channels in ("wr", "rw") or self.master.channels in ("rd", "rw")):
            lines.append("    // Per-width path-active gates (see comment in adapter_generator.py).")
            # Request gates: declared here (before first
            # use in the path actives), assigned in the tracking section.
            if self.master.channels in ("wr", "rw"):
                lines.append("    logic aw_gate_ok;")
            if self.master.channels in ("rd", "rw"):
                lines.append("    logic ar_gate_ok;")
            for slave_width in slave_widths:
                slaves_at_w = [
                    si for si in self.master.slave_connections
                    if self.slaves[si].data_width == slave_width
                ]
                if self.master.channels in ("wr", "rw"):
                    aw_terms = " | ".join(f"comb_slave_select_aw[{si}]" for si in slaves_at_w)
                    lines.append(
                        f"    logic aw_path_active_{slave_width}b;"
                    )
                    lines.append(
                        f"    assign aw_path_active_{slave_width}b = ({aw_terms}) && aw_gate_ok;"
                    )
                    # W beats arrive after AW; by then fub_axi_awaddr may
                    # have reverted (wrapper popped its skid) and the
                    # combinational decode flips back to a different slave.
                    # Use w_slave_select (FIFO popped on wlast, defined in
                    # the response-MUX section below) so W#2's gating
                    # doesn't block on B#1 returning. Previously this used
                    # b_slave_select (popped on B), which made back-to-back
                    # writes route W#2's data onto AW#1's slave's width
                    # bucket until B#1 settled.
                    w_terms = " | ".join(f"w_slave_select[{si}]" for si in slaves_at_w)
                    lines.append(
                        f"    logic w_path_active_{slave_width}b;"
                    )
                    lines.append(
                        f"    assign w_path_active_{slave_width}b = {w_terms};"
                    )
                if self.master.channels in ("rd", "rw"):
                    ar_terms = " | ".join(f"comb_slave_select_ar[{si}]" for si in slaves_at_w)
                    lines.append(
                        f"    logic ar_path_active_{slave_width}b;"
                    )
                    lines.append(
                        f"    assign ar_path_active_{slave_width}b = ({ar_terms}) && ar_gate_ok;"
                    )
                # Response-side path actives. The response MUX gates
                # rvalid/bvalid by the tracked r/b_slave_select head, but
                # the per-path readies used to be the RAW fub ready — an
                # unselected path holding a response beat saw ready high
                # and handshook the beat into the void (dropped R/B under
                # any cross-path concurrency). Gate each path's ready by
                # the same head that gates its valid.
                if self.master.channels in ("wr", "rw"):
                    b_terms = " | ".join(f"b_slave_select[{si}]" for si in slaves_at_w)
                    lines.append(
                        f"    logic b_path_active_{slave_width}b;"
                    )
                    lines.append(
                        f"    assign b_path_active_{slave_width}b = {b_terms};"
                    )
                if self.master.channels in ("rd", "rw"):
                    r_terms = " | ".join(f"r_slave_select[{si}]" for si in slaves_at_w)
                    if self.rr_local_idx is not None:
                        # A locally answered R beat must not hand a slave's
                        # beat through underneath it.
                        r_terms = f"({r_terms}) && !r_local_head"
                    lines.append(
                        f"    logic r_path_active_{slave_width}b;"
                    )
                    lines.append(
                        f"    assign r_path_active_{slave_width}b = {r_terms};"
                    )
            lines.append("")

        # Generate one path per unique width
        for slave_width in slave_widths:
            if slave_width == self.master.data_width:
                # Direct passthrough - no conversion
                lines.extend(self._generate_direct_passthrough(slave_width))
            else:
                # Width conversion needed
                lines.extend(self._generate_converter_instance(slave_width))

        # Always generate the response MUX. The matched-width / direct-passthrough
        # path used to skip this entirely, leaving fub_axi_r* and fub_axi_b*
        # declared but undriven — so a master could never see a B or R
        # response come back. The MUX template handles direct-passthrough
        # (slave_width == master_width) by routing master.<W>b_* signals,
        # so it works for both converter and passthrough slaves.
        lines.extend(self._generate_response_mux(slave_widths))

        return lines

    # --- bridge GitHub #119 L1: fixes the one-target-per-master limitation -----
    # The adapter used to accept a new AW/AR only while every outstanding one
    # went to the SAME slave, because responses were replayed in issue order
    # from a FIFO of targets. Now responses are taken in whatever order the
    # paths offer them -- the crossbar arbitrates among slaves on one width
    # path, and _path_arb_lines below arbitrates among the paths -- and the
    # only ordering kept is the one AXI requires: same ID, same order. A
    # per-ID table (count + target, indexed by the ID's low id_track_bits
    # bits) holds a request whose ID is already in flight to a DIFFERENT
    # slave; requests with other IDs flow to any slave.
    #
    # Every port takes this path (GitHub #119 L1b). Read-return-atomic and
    # trace-echo ports used to keep an in-order FIFO, because their
    # per-request state rode the FIFO entry; the per-ID table now carries it:
    # a trace bit per ID (a request whose ID is in flight with a DIFFERENT
    # trace waits, so the bit is single-valued per ID), an atomic AW counted
    # in the AR table under its AWID (its R comes back with that ID), and a
    # local-DECERR queue that joins the R path arbiter as one more source.
    @property
    def multi_target(self) -> bool:
        return True

    @property
    def id_track_k(self) -> int:
        """Index bits of the per-ID table: never more than the port's ID."""
        return max(0, min(self.id_track_bits, self.fub_id_width))

    def _id_table_lines(self, chan: str, resp_hs: str, resp_id: str,
                        trace: Optional[str] = None, atomic: bool = False) -> List[str]:
        """Per-ID {count, target[, trace]} table and outstanding counter for
        'aw'/'ar'. Declares {chan}_id_ok and {chan}_trk_full; the caller
        builds the gate. `trace` is the request's trace signal (trace-echo
        ports). `atomic` (AR table of an rr_atomic port) adds a second push,
        ar_idt_push_aw, for read-return atomic AWs, which answer on R."""
        up, k = chan.upper(), self.id_track_k
        widx = f"fub_axi_{chan}id[{k-1}:0]" if k else "1'b0"
        ridx = f"{resp_id}[{k-1}:0]" if k else "1'b0"
        iw = max(1, k)
        lines = [
            f"    // -------- {up} per-ID target table (fixes bridge GitHub #119 L1) --------",
            f"    // {2**k} entries indexed by the ID's low {k} bit(s). An ID with requests",
            f"    // in flight may only add more to the SAME slave (AXI same-ID order);",
            f"    // any other ID may go to any slave. IDs that share the index bits are",
            f"    // treated as one ID: safe, at worst a needless stall.",
            f"    localparam int {up}_IDT_N = {2**k};",
            f"    logic [{up}_TRK_AW:0]   {chan}_idt_cnt [{up}_IDT_N];",
            f"    logic [NUM_SLAVES-1:0] {chan}_idt_tgt [{up}_IDT_N];",
            f"    logic [{up}_TRK_AW:0]   {chan}_out_cnt;",
            f"    // Next counts, and registered flags taken from them, so the gate a",
            f"    // request sees is a 1-bit lookup and a one-hot AND, not a counter",
            f"    // mux and compare in series with the crossbar's arbitration.",
            f"    logic [{up}_TRK_AW:0]   {chan}_idt_cnt_nx [{up}_IDT_N];",
            f"    logic [{up}_TRK_AW:0]   {chan}_out_cnt_nx;",
            f"    logic [{up}_IDT_N-1:0] {chan}_idt_busy;",
            f"    logic                  {chan}_trk_full;",
            f"    logic [{iw-1}:0] {chan}_idt_widx, {chan}_idt_ridx;",
        ] + ([f"    logic                  {chan}_idt_trace [{up}_IDT_N];  // trace of the in-flight ID"]
             if trace else []) + ([
            f"    // A5-3b: a read-return atomic AW answers on R with its AWID, so it",
            f"    // is counted here too (second push port).",
            f"    logic [{iw-1}:0] ar_idt_widx_aw;",
            f"    logic ar_idt_push_aw;",
            f"    assign ar_idt_widx_aw = " + (f"fub_axi_awid[{k-1}:0];" if k else "1'b0;"),
            f"    assign ar_idt_push_aw = fub_axi_awvalid && fub_axi_awready && aw_rr_atomic;",
        ] if atomic else []) + [
            f"    logic {chan}_idt_push, {chan}_idt_pop;",
            f"    assign {chan}_idt_widx = {widx};",
            f"    assign {chan}_idt_ridx = {ridx};",
            f"    assign {chan}_idt_push = fub_axi_{chan}valid && fub_axi_{chan}ready;",
            f"    assign {chan}_idt_pop  = {resp_hs};",
            f"    logic [1:0] {chan}_inc_n;   // pushes this cycle",
            f"    assign {chan}_inc_n = 2'({chan}_idt_push)" + (" + 2'(ar_idt_push_aw);" if atomic else ";"),
            "",
            "    always_comb begin",
            f"        for (int i = 0; i < {up}_IDT_N; i++) begin",
            f"            {chan}_idt_cnt_nx[i] = {chan}_idt_cnt[i]",
            f"                + ({up}_TRK_AW+1)'({chan}_idt_push && ({chan}_idt_widx == {iw}'(i)))",
        ] + ([f"                + ({up}_TRK_AW+1)'(ar_idt_push_aw && (ar_idt_widx_aw == {iw}'(i)))"] if atomic else []) + [
            f"                - ({up}_TRK_AW+1)'({chan}_idt_pop  && ({chan}_idt_ridx == {iw}'(i)));",
            "        end",
            f"        {chan}_out_cnt_nx = {chan}_out_cnt + ({up}_TRK_AW+1)'({chan}_idt_push)"
            + (f" + ({up}_TRK_AW+1)'(ar_idt_push_aw)" if atomic else ""),
            f"                          - ({up}_TRK_AW+1)'({chan}_idt_pop);",
            "    end",
            "",
            "    `ALWAYS_FF_RST(aclk, aresetn,",
            "        if (`RST_ASSERTED(aresetn)) begin",
            f"            for (int i = 0; i < {up}_IDT_N; i++) begin",
            f"                {chan}_idt_cnt[i] <= '0;",
            f"                {chan}_idt_tgt[i] <= '0;",
        ] + ([f"                {chan}_idt_trace[i] <= 1'b0;"] if trace else []) + [
            "            end",
            f"            {chan}_idt_busy <= '0;",
            f"            {chan}_out_cnt <= '0;",
            f"            {chan}_trk_full <= 1'b0;",
            "        end else begin",
            f"            if ({chan}_idt_push) {chan}_idt_tgt[{chan}_idt_widx] <= comb_slave_select_{chan};",
        ] + ([f"            if ({chan}_idt_push) {chan}_idt_trace[{chan}_idt_widx] <= {trace};"] if trace else []) + ([
            "            if (ar_idt_push_aw) ar_idt_tgt[ar_idt_widx_aw] <= comb_slave_select_aw;",
        ] + (["            if (ar_idt_push_aw) ar_idt_trace[ar_idt_widx_aw] <= fub_axi_awtrace;"] if trace else [])
            if atomic else []) + [
            # The flags compare the REGISTERED counts; push and pop, which
            # depend on the crossbar's grant this cycle, only select between
            # the compares. Deriving them from the next counts put the
            # grant through the counter adder and a compare.
            f"            for (int i = 0; i < {up}_IDT_N; i++) begin",
            f"                {chan}_idt_cnt[i]  <= {chan}_idt_cnt_nx[i];",
            f"                {chan}_idt_busy[i] <= ({chan}_idt_push && ({chan}_idt_widx == {iw}'(i)))",
        ] + ([f"                                    || (ar_idt_push_aw && (ar_idt_widx_aw == {iw}'(i)))"] if atomic else []) + [
            f"                                    || ({chan}_idt_cnt[i] > ({up}_TRK_AW+1)'(1))",
            f"                                    || (({chan}_idt_cnt[i] == ({up}_TRK_AW+1)'(1)) &&",
            f"                                        !({chan}_idt_pop && ({chan}_idt_ridx == {iw}'(i))));",
            "            end",
            f"            {chan}_out_cnt  <= {chan}_out_cnt_nx;",
            f"            {chan}_trk_full <=",
            f"                (({chan}_out_cnt == ({up}_TRK_AW+1)'({up}_TRK_DEPTH))   && ({chan}_inc_n == 2'({chan}_idt_pop))) ||",
            f"                (({chan}_out_cnt == ({up}_TRK_AW+1)'({up}_TRK_DEPTH-1)) && ({chan}_inc_n == 2'({chan}_idt_pop) + 2'd1))"
            + (" ||" if atomic else ";"),
        ] + ([
            f"                (({chan}_out_cnt == ({up}_TRK_AW+1)'({up}_TRK_DEPTH-2)) && ({chan}_inc_n == 2'd2) && !{chan}_idt_pop);",
        ] if atomic else []) + [
            "        end",
            "    )",
            "",
            f"    // bridge BUG-009 (was BRIDGE-011): a bounded number in flight, so no",
            f"    // count wraps; {up}_TRK_DEPTH is the port's outstanding limit.",
            f"    // Target match is a one-hot AND: the stored target and the decode",
            f"    // are both one-hot (no hit selects the catch-all).",
            f"    logic {chan}_id_ok;",
            f"    assign {chan}_id_ok    = !{chan}_idt_busy[{chan}_idt_widx] ||",
            f"                           ((|({chan}_idt_tgt[{chan}_idt_widx] & comb_slave_select_{chan}))"
            + (f" &&\n                            ({chan}_idt_trace[{chan}_idt_widx] == {trace}));" if trace else ");"),
        ]
        return lines

    def _path_arb_lines(self, resp: str, slave_widths: List[int],
                        width_to_slaves, local: Optional[str] = None) -> List[str]:
        """{b,r}_slave_select for multi-target mode: which width path's
        response goes to the master. Values are a representative slave of
        the path (the response mux muxes per path, not per slave). `local`
        is the valid of one more source with no path behind it (the R side's
        local DECERR queue); its grant is r_local_head and selects no slave."""
        sel = f"{resp}_slave_select"
        widths = sorted(set(slave_widths))
        n = len(self.slaves)
        reps = []
        for w in widths:
            i = width_to_slaves[w][0]
            reps.append(f"{n}'b" + ''.join('1' if j == i else '0' for j in range(n - 1, -1, -1)))
        p = len(widths) + (1 if local else 0)
        if p == 1:
            return [f"    // One width path: every response arrives on it; the crossbar has",
                    f"    // already chosen among the slaves behind it.",
                    f"    assign {sel} = {reps[0]};", ""]
        mw = self.master.data_width
        valids = [f"{self.master.name}_{w}b_{resp}valid" if w == mw else f"conv_{w}b_{resp}valid"
                  for w in widths]
        labels = [f"{w}b path" for w in widths]
        if local:
            valids.append(local)
            labels.append("local DECERR queue")
        pw = max(1, (p - 1).bit_length())
        L = [f"    // -------- {resp.upper()} path arbiter (fixes bridge GitHub #119 L1) --------",
             f"    // Round robin over the {p} width paths. A grant holds while its",
             f"    // response is offered and not taken; R switches per beat, since the",
             f"    // slaves (and the width converters, per ID) may interleave R bursts.",
             f"    logic [{p-1}:0] {resp}_pv, {resp}_pgnt, r_{resp}_held;",
             f"    logic           r_{resp}_hold;",
             f"    logic [{pw-1}:0] r_{resp}_last;"]
        for i, v in enumerate(valids):
            L.append(f"    assign {resp}_pv[{i}] = {v};  // {labels[i]}")
        L += ["    always_comb begin",
              f"        {resp}_pgnt = '0;",
              f"        if (r_{resp}_hold) begin",
              f"            {resp}_pgnt = r_{resp}_held;",
              "        end else begin",
              f"            case (r_{resp}_last)"]
        for l in range(p):
            order = [(l + k) % p for k in range(1, p + 1)]  # priority, highest first
            L.append(f"                {pw}'d{l}: begin")
            for j in reversed(order):
                L.append(f"                    if ({resp}_pv[{j}]) {resp}_pgnt = {p}'b"
                         + ''.join('1' if b == j else '0' for b in range(p - 1, -1, -1)) + ";")
            L.append("                end")
        L += ["                default: ;",
              "            endcase",
              "        end",
              "    end",
              "",
              "    `ALWAYS_FF_RST(aclk, aresetn,",
              "        if (`RST_ASSERTED(aresetn)) begin",
              f"            r_{resp}_hold <= 1'b0;",
              f"            r_{resp}_held <= '0;",
              f"            r_{resp}_last <= '0;",
              "        end else begin",
              f"            r_{resp}_hold <= fub_axi_{resp}valid && !fub_axi_{resp}ready;",
              f"            r_{resp}_held <= {resp}_pgnt;",
              f"            if (fub_axi_{resp}valid && fub_axi_{resp}ready) begin"]
        for i in range(p):
            L.append(f"                if ({resp}_pgnt[{i}]) r_{resp}_last <= {pw}'d{i};")
        L += ["            end",
              "        end",
              "    )",
              "",
              f"    assign {sel} = " + "\n                          | ".join(
                  f"({{NUM_SLAVES{{{resp}_pgnt[{i}]}}}} & {reps[i]})" for i in range(len(reps))) + ";",
              ""]
        if local:
            L += [f"    assign r_local_head = {resp}_pgnt[{p-1}];  // the local queue holds R", ""]
        return L

    def _generate_response_mux(self, slave_widths: List[int]) -> List[str]:
        """
        Generate MUX logic to route responses from converters/passthroughs back to fub_axi_*.

        The MUX selects based on slave_select signals (address decode output).
        """
        lines = []

        lines.append("    // ================================================================")
        lines.append("    // Response MUX - Route responses from width-specific paths")
        lines.append("    // back to fub_axi_* based on address decode")
        lines.append("    //")
        lines.append("    // Request side (arready/awready/wready) uses the combinational")
        lines.append("    // slave_select_{ar,aw} (valid while {ar,aw}valid is asserted).")
        lines.append("    //")
        lines.append("    // Response side (rvalid/rdata/..., bvalid/bid/...) cannot reuse")
        lines.append("    // the combinational decode because fub_axi_{ar,aw}addr no longer")
        lines.append("    // holds the request address once the {AR,AW} handshake completes")
        lines.append("    // -- the decode reverts (typically to slave 0) and drops the")
        lines.append("    // response. So we track slave_select_{ar,aw} per outstanding")
        lines.append("    // request in a small FIFO captured at handshake, popped at")
        lines.append("    // R-last / B; the FIFO head drives the response MUX.")
        lines.append("    // ================================================================")
        lines.append("")

        master_width = self.master.data_width

        # Build mapping: adapter_output_width -> list of slave indices with that width.
        # Always uses slave.data_width — see _get_connected_slave_widths for
        # why the LCD-for-APB path was dropped (kept adapter and crossbar
        # disagreeing on the suffix).
        width_to_slaves = {}

        for slave_idx in self.master.slave_connections:
            slave = self.slaves[slave_idx]
            adapter_output_width = slave.data_width

            if adapter_output_width not in width_to_slaves:
                width_to_slaves[adapter_output_width] = []
            width_to_slaves[adapter_output_width].append(slave_idx)

        num_slaves = len(self.slaves)

        # Tracker depth = this port's outstanding limit per direction
        # ([bridge]/port max_outstanding, power of two 2..64; was a fixed 16
        # until bridge GitHub #119 L5).
        fifo_depth = int(getattr(self.master, 'max_outstanding', 16))
        fifo_aw_bits = fifo_depth.bit_length() - 1

        # Generate response-tracking FIFOs (one per channel direction).
        # The FIFO captures `comb_slave_select_{ar,aw}` at the {ar,aw}
        # handshake so the slave selection is available for the response
        # MUX (B/R) even after fub_axi_{ar,aw}addr reverts.
        #
        # The OUTPUT `slave_select_{ar,aw}` keeps the combinational
        # semantics: it's the live decode of the current request address.
        # The xbar handles the "address reverts after handshake" problem
        # by re-decoding the converter/passthrough's m_axi address bus
        # instead of relying on `slave_select_*` (see crossbar_generator
        # _generate_*_channel_routing).
        if self.master.channels in ("wr", "rw"):
            lines.append("    // OUTPUT slave_select_aw mirrors the live combinational decode.")
            lines.append("    assign slave_select_aw = comb_slave_select_aw;")
            lines.append("")
            lines.append(f"    localparam int AW_TRK_DEPTH = {fifo_depth};")
            lines.append(f"    localparam int AW_TRK_AW    = {fifo_aw_bits};")
        tr = "fub_axi_awtrace" if self._trace_echo else None
        if self.master.channels in ("wr", "rw"):
            lines.extend(self._id_table_lines('aw', "fub_axi_bvalid && fub_axi_bready", "fub_axi_bid",
                                              trace=tr))
            lines.append("")
            lines.extend(self._path_arb_lines('b', slave_widths, width_to_slaves))
            if self._trace_echo:
                lines.append("    // bridge BUG-010 (was BRIDGE-012): the B echoes its request's trace,")
                lines.append("    // looked up by the returning ID (single-valued per in-flight ID).")
                lines.append("    logic b_trk_trace;")
                lines.append("    assign b_trk_trace = aw_idt_trace[aw_idt_ridx];")
                lines.append("")
            lines.append("    // -------- AW->W slave_select tracking FIFO --------")
            lines.append("    // Same push as AW (records slave_select at handshake);")
            lines.append("    // pops on wlast so W#2's path-active gating doesn't wait")
            lines.append("    // for B#1 to return. Without this, back-to-back writes")
            lines.append("    // to different-width slaves stamp W#2's data on AW#1's")
            lines.append("    // bucket (see multi-master 128b->32b/128b regression).")
            lines.append(f"    logic [NUM_SLAVES-1:0] w_trk_mem [AW_TRK_DEPTH];")
            lines.append("    logic [AW_TRK_AW:0] w_trk_wptr, w_trk_rptr;")
            lines.append("    logic w_trk_push, w_trk_pop;")
            lines.append("")
            lines.append("    assign w_trk_push = fub_axi_awvalid && fub_axi_awready;")
            lines.append("    assign w_trk_pop  = fub_axi_wvalid && fub_axi_wready && fub_axi_wlast;")
            lines.append("")
            lines.append("    `ALWAYS_FF_RST(aclk, aresetn,")
            lines.append("        if (`RST_ASSERTED(aresetn)) begin")
            lines.append("            w_trk_wptr <= '0;")
            lines.append("            w_trk_rptr <= '0;")
            lines.append("        end else begin")
            lines.append("            if (w_trk_push) begin")
            lines.append("                w_trk_mem[w_trk_wptr[AW_TRK_AW-1:0]] <= comb_slave_select_aw;")
            lines.append("                w_trk_wptr <= w_trk_wptr + 1'b1;")
            lines.append("            end")
            lines.append("            if (w_trk_pop) begin")
            lines.append("                w_trk_rptr <= w_trk_rptr + 1'b1;")
            lines.append("            end")
            lines.append("        end")
            lines.append("    )")
            lines.append("")
            lines.append("    assign w_slave_select = (w_trk_wptr != w_trk_rptr)")
            lines.append("                          ? w_trk_mem[w_trk_rptr[AW_TRK_AW-1:0]]")
            lines.append("                          : '0;")
            lines.append("")
            lines.append("    // A new AW may target a different slave only once every W burst")
            lines.append("    // already accepted has gone: W carries no ID and follows AW order,")
            lines.append("    // so two masters each with W owed to two slaves could otherwise")
            lines.append("    // wait on each other at the slaves' W ports (crossed W deadlock).")
            lines.append("    assign aw_gate_ok = aw_id_ok && !aw_trk_full &&")
            lines.append("                        ((w_trk_wptr == w_trk_rptr) ||")
            if self.rr_atomic:
                lines.append("                         (|(w_slave_select & comb_slave_select_aw))) &&")
                lines.append("                        // A5-3b: a read-return atomic also takes an AR-table slot")
                lines.append("                        (!aw_rr_atomic || aw_rr_gate_ok);")
            else:
                lines.append("                         (|(w_slave_select & comb_slave_select_aw)));")
            lines.append("")

        if self.master.channels in ("rd", "rw"):
            lines.append("    // OUTPUT slave_select_ar mirrors the live combinational decode.")
            lines.append("    assign slave_select_ar = comb_slave_select_ar;")
            lines.append("")
            lines.append(f"    localparam int AR_TRK_DEPTH = {fifo_depth};")
            lines.append(f"    localparam int AR_TRK_AW    = {fifo_aw_bits};")
            lines.extend(self._id_table_lines(
                'ar', "fub_axi_rvalid && fub_axi_rready && fub_axi_rlast", "fub_axi_rid",
                trace=("fub_axi_artrace" if self._trace_echo else None), atomic=self.rr_atomic))
            lines.append("    assign ar_gate_ok = ar_id_ok && !ar_trk_full;")
            lines.append("")
            if self.rr_atomic:
                k = self.id_track_k
                lines.append("    // A5-3b: the read-return atomic AW's own gate, against the AR table")
                lines.append("    // under its AWID: same per-ID rule as AR, one free slot counting an AR")
                lines.append("    // that pushes this cycle, and it yields to an AR pushing the SAME ID")
                lines.append("    // index this cycle (two pushes would race for one entry's target).")
                trace_term = (" &&\n                                 (ar_idt_trace[ar_idt_widx_aw] == fub_axi_awtrace)"
                              if self._trace_echo else "")
                lines.append("    logic ar_id_ok_aw;")
                lines.append("    assign ar_id_ok_aw = !ar_idt_busy[ar_idt_widx_aw] ||")
                lines.append("                         ((|(ar_idt_tgt[ar_idt_widx_aw] & comb_slave_select_aw))"
                             + trace_term + ");")
                lines.append("    assign aw_rr_gate_ok = ar_id_ok_aw &&")
                lines.append("                           ((ar_out_cnt + (AR_TRK_AW+1)'(ar_idt_push)) <")
                lines.append("                            (AR_TRK_AW+1)'(AR_TRK_DEPTH)) &&")
                lines.append("                           !(ar_idt_push && (ar_idt_widx == ar_idt_widx_aw));")
                lines.append("")
            local = None
            if self.rr_local_idx is not None:
                local = "lr_valid"
                idw = self.fub_id_width
                lines.append("    // A5-3b: a read-return atomic that decoded to the subtractive slave")
                lines.append("    // is answered HERE with one DECERR R beat (that slave answers B only).")
                lines.append("    // Its ID waits in this queue; the R path arbiter grants it like a path.")
                lines.append(f"    wire  aw_rr_local = aw_rr_atomic && comb_slave_select_aw[{self.rr_local_idx}];")
                lines.append(f"    logic [{idw-1}:0] lr_mem [AR_TRK_DEPTH];")
                lines.append("    logic [AR_TRK_AW:0] lr_wptr, lr_rptr;")
                lines.append("    logic lr_valid;")
                lines.append(f"    logic [{idw-1}:0] r_local_id;")
                lines.append("    `ALWAYS_FF_RST(aclk, aresetn,")
                lines.append("        if (`RST_ASSERTED(aresetn)) begin")
                lines.append("            lr_wptr <= '0;")
                lines.append("            lr_rptr <= '0;")
                lines.append("        end else begin")
                lines.append("            if (fub_axi_awvalid && fub_axi_awready && aw_rr_local) begin")
                lines.append("                lr_mem[lr_wptr[AR_TRK_AW-1:0]] <= fub_axi_awid;")
                lines.append("                lr_wptr <= lr_wptr + 1'b1;")
                lines.append("            end")
                lines.append("            if (r_local_head && fub_axi_rvalid && fub_axi_rready) begin")
                lines.append("                lr_rptr <= lr_rptr + 1'b1;")
                lines.append("            end")
                lines.append("        end")
                lines.append("    )")
                lines.append("    assign lr_valid   = (lr_wptr != lr_rptr);")
                lines.append("    assign r_local_id = lr_mem[lr_rptr[AR_TRK_AW-1:0]];")
                lines.append("")
            lines.extend(self._path_arb_lines('r', slave_widths, width_to_slaves, local=local))
            if self._trace_echo:
                lines.append("    // bridge BUG-010: the R echoes its request's trace (an atomic's AW trace).")
                lines.append("    logic r_trk_trace;")
                lines.append("    assign r_trk_trace = ar_idt_trace[ar_idt_ridx];")
                lines.append("")

        # Write channel MUX
        if self.master.channels in ["wr", "rw"]:
            # AW-ready uses the live combinational decode (fub_axi_awaddr
            # is still valid while awvalid is asserted).
            lines.append("    // AW-ready MUX (combinational comb_slave_select_aw — awaddr is live during awvalid)")
            lines.append("    always_comb begin")
            lines.append("        fub_axi_awready = 1'b0;")
            lines.append("        case (comb_slave_select_aw)")
            for slave_width in sorted(set(slave_widths)):
                suffix = f"{slave_width}b"
                slave_indices = width_to_slaves[slave_width]
                for slave_idx in slave_indices:
                    pattern = f"{num_slaves}'b" + ''.join(
                        '1' if i == slave_idx else '0'
                        for i in range(num_slaves - 1, -1, -1)
                    )
                    lines.append(f"            {pattern}: begin  // Slave {slave_idx} ({slave_width}b)")
                    if slave_width == master_width:
                        lines.append(f"                fub_axi_awready = {self.master.name}_{suffix}_awready;")
                    else:
                        lines.append(f"                fub_axi_awready = conv_{suffix}_awready;")
                    lines.append("            end")
            lines.append("            default: begin")
            lines.append("                // No slave selected")
            lines.append("            end")
            lines.append("        endcase")
            lines.append("        // Hold off a new AW the gate refuses (see aw_gate_ok).")
            lines.append("        if (!aw_gate_ok) fub_axi_awready = 1'b0;")
            lines.append("    end")
            lines.append("")

            # W-ready uses w_slave_select (FIFO head, popped on wlast).
            # By the time W beats arrive, the AW handshake is long
            # done and fub_axi_awaddr has reverted -- comb_slave_select_aw
            # would route W to the wrong bucket (or default to 0, which
            # holds wready low and the master deadlocks). w_slave_select
            # is the FIFO-tracked slave from AW push order, advanced
            # only when each W burst's wlast completes -- so W#2 of
            # back-to-back writes gets W#2's slave's wready immediately
            # after W#1 finishes, without waiting for B#1.
            lines.append("    // W-ready MUX (FIFO-tracked w_slave_select — awaddr has already reverted by W phase)")
            lines.append("    always_comb begin")
            lines.append("        fub_axi_wready = 1'b0;")
            lines.append("        case (w_slave_select)")
            for slave_width in sorted(set(slave_widths)):
                suffix = f"{slave_width}b"
                slave_indices = width_to_slaves[slave_width]
                for slave_idx in slave_indices:
                    pattern = f"{num_slaves}'b" + ''.join(
                        '1' if i == slave_idx else '0'
                        for i in range(num_slaves - 1, -1, -1)
                    )
                    lines.append(f"            {pattern}: begin  // Slave {slave_idx} ({slave_width}b)")
                    if slave_width == master_width:
                        lines.append(f"                fub_axi_wready = {self.master.name}_{suffix}_wready;")
                    else:
                        lines.append(f"                fub_axi_wready = conv_{suffix}_wready;")
                    lines.append("            end")
            lines.append("            default: begin")
            lines.append("                // No active W transaction")
            lines.append("            end")
            lines.append("        endcase")
            lines.append("    end")
            lines.append("")

            lines.append("    // Write response MUX (B channel - uses b_slave_select FIFO head)")
            if self._trace_echo:
                lines.append("    // btrace is NOT driven here: the mux records what the SLAVE said")
                lines.append("    // (checked below) while the port echoes the request (bridge BUG-010, was BRIDGE-012).")
                lines.append("    logic b_slave_trace;")
            lines.append("    always_comb begin")

            # Default assignments
            lines.append(f"        fub_axi_bid = {self.fub_id_width}'d0;")
            lines.append("        fub_axi_bresp = 2'b00;")
            lines.append("        fub_axi_bvalid = 1'b0;")
            for _f, _w, feat, base in self._sb_fields('b', self.sb_own):
                tgt = "b_slave_trace" if base == 'btrace' else f"fub_axi_{base}"
                lines.append(f"        {tgt} = '0;  // AXI5 sideband ({feat})")
            lines.append("")

            # Case statement based on b_slave_select (was slave_select_aw)
            lines.append("        case (b_slave_select)")
            for width_idx, slave_width in enumerate(sorted(set(slave_widths))):
                suffix = f"{slave_width}b"
                slave_indices = width_to_slaves[slave_width]

                # Build one-hot pattern for these slaves
                # Example: If slaves 0, 2 connect to 32b → pattern is 4'b0101
                for slave_idx in slave_indices:
                    pattern = f"{len(self.slaves)}'b" + ''.join(
                        '1' if i == slave_idx else '0'
                        for i in range(len(self.slaves)-1, -1, -1)
                    )
                    lines.append(f"            {pattern}: begin  // Slave {slave_idx} ({slave_width}b)")

                    if slave_width == master_width:
                        # Direct passthrough signals
                        # The fabric struct carries the bridge-wide ID
                        # width; this port's may be narrower (an axil port
                        # has ID_WIDTH 0). Outbound the port's ID is
                        # zero-extended into the struct, so narrowing back
                        # here recovers exactly what was sent -- but say so
                        # with an explicit select instead of leaving lint to
                        # report an implicit truncation.
                        lines.append(f"                fub_axi_bid = {self.master.name}_{suffix}_b.id[{self.fub_id_width - 1}:0];")
                        lines.append(f"                fub_axi_bresp = {self.master.name}_{suffix}_b.resp;")
                        lines.append(f"                fub_axi_bvalid = {self.master.name}_{suffix}_bvalid;")
                        for field, w, _feat, base in self._sb_fields('b', self.sb_own):
                            tgt = "b_slave_trace" if base == 'btrace' else f"fub_axi_{base}"
                            src = self._sb_struct_to_fub('b', w, f"{self.master.name}_{suffix}_b.{field}", slave_width)
                            lines.append(f"                {tgt} = {src};")
                    else:
                        # Converter intermediate signals
                        lines.append(f"                fub_axi_bid = conv_{suffix}_bid"
                                     + (f"[{self.fub_id_width - 1}:0];" if self.id_prefix_width else ";"))
                        lines.append(f"                fub_axi_bresp = conv_{suffix}_bresp;")
                        lines.append(f"                fub_axi_bvalid = conv_{suffix}_bvalid;")

                    lines.append("            end")

            lines.append("            default: begin")
            lines.append("                // No slave selected - hold defaults")
            lines.append("            end")
            lines.append("        endcase")
            lines.append("    end")
            lines.append("")
            if self._trace_echo:
                lines.extend(self._trace_echo_lines('b'))
                lines.append("")

        # Read channel MUX
        if self.master.channels in ["rd", "rw"]:
            # AR-ready MUX: request-side decode is valid while arvalid is asserted.
            lines.append("    // AR-ready MUX (request side: uses combinational comb_slave_select_ar)")
            lines.append("    always_comb begin")
            lines.append("        fub_axi_arready = 1'b0;")
            lines.append("        case (comb_slave_select_ar)")
            for slave_width in sorted(set(slave_widths)):
                suffix = f"{slave_width}b"
                slave_indices = width_to_slaves[slave_width]
                for slave_idx in slave_indices:
                    pattern = f"{num_slaves}'b" + ''.join(
                        '1' if i == slave_idx else '0'
                        for i in range(num_slaves - 1, -1, -1)
                    )
                    lines.append(f"            {pattern}: begin  // Slave {slave_idx} ({slave_width}b)")
                    if slave_width == master_width:
                        lines.append(f"                fub_axi_arready = {self.master.name}_{suffix}_arready;")
                    else:
                        lines.append(f"                fub_axi_arready = conv_{suffix}_arready;")
                    lines.append("            end")
            lines.append("            default: begin")
            lines.append("                // No slave selected")
            lines.append("            end")
            lines.append("        endcase")
            lines.append("        // Hold off a new AR the gate refuses (see ar_gate_ok).")
            lines.append("        if (!ar_gate_ok) fub_axi_arready = 1'b0;")
            lines.append("    end")
            lines.append("")

            lines.append("    // Read response MUX (R channel - uses r_slave_select FIFO head)")
            if self._trace_echo:
                lines.append("    // rtrace is NOT driven here -- see the B-channel note (bridge BUG-010, was BRIDGE-012).")
                lines.append("    logic r_slave_trace;")
            lines.append("    always_comb begin")

            # Default assignments
            lines.append(f"        fub_axi_rid = {self.fub_id_width}'d0;")
            lines.append(f"        fub_axi_rdata = {master_width}'d0;")
            lines.append("        fub_axi_rresp = 2'b00;")
            lines.append("        fub_axi_rlast = 1'b0;")
            lines.append("        fub_axi_rvalid = 1'b0;")
            for _f, _w, feat, base in self._sb_fields('r', self.sb_own):
                tgt = "r_slave_trace" if base == 'rtrace' else f"fub_axi_{base}"
                lines.append(f"        {tgt} = '0;  // AXI5 sideband ({feat})")
            lines.append("")

            # Case statement based on r_slave_select (was slave_select_ar)
            lines.append("        case (r_slave_select)")
            for width_idx, slave_width in enumerate(sorted(set(slave_widths))):
                suffix = f"{slave_width}b"
                slave_indices = width_to_slaves[slave_width]

                for slave_idx in slave_indices:
                    pattern = f"{len(self.slaves)}'b" + ''.join(
                        '1' if i == slave_idx else '0'
                        for i in range(len(self.slaves)-1, -1, -1)
                    )
                    lines.append(f"            {pattern}: begin  // Slave {slave_idx} ({slave_width}b)")

                    if slave_width == master_width:
                        # Direct passthrough signals
                        lines.append(f"                fub_axi_rid = {self.master.name}_{suffix}_r.id[{self.fub_id_width - 1}:0];")
                        lines.append(f"                fub_axi_rdata = {self.master.name}_{suffix}_r.data;")
                        lines.append(f"                fub_axi_rresp = {self.master.name}_{suffix}_r.resp;")
                        lines.append(f"                fub_axi_rlast = {self.master.name}_{suffix}_r.last;")
                        lines.append(f"                fub_axi_rvalid = {self.master.name}_{suffix}_rvalid;")
                        for field, w, _feat, base in self._sb_fields('r', self.sb_own):
                            tgt = "r_slave_trace" if base == 'rtrace' else f"fub_axi_{base}"
                            src = self._sb_struct_to_fub('r', w, f"{self.master.name}_{suffix}_r.{field}", slave_width)
                            lines.append(f"                {tgt} = {src};")
                    else:
                        # Converter intermediate signals
                        lines.append(f"                fub_axi_rid = conv_{suffix}_rid"
                                     + (f"[{self.fub_id_width - 1}:0];" if self.id_prefix_width else ";"))
                        lines.append(f"                fub_axi_rdata = conv_{suffix}_rdata;")
                        lines.append(f"                fub_axi_rresp = conv_{suffix}_rresp;")
                        lines.append(f"                fub_axi_rlast = conv_{suffix}_rlast;")
                        lines.append(f"                fub_axi_rvalid = conv_{suffix}_rvalid;")

                    lines.append("            end")

            lines.append("            default: begin")
            lines.append("                // No slave selected - hold defaults")
            lines.append("            end")
            lines.append("        endcase")
            if self.rr_local_idx is not None:
                lines.append("        // A5-3b: a read-return atomic that decoded to the subtractive")
                lines.append("        // slave is answered here -- DECERR, one beat, the AW's ID. The")
                lines.append("        // subtractive slave has already been held off via r_path_active.")
                lines.append("        if (r_local_head) begin")
                lines.append(f"            fub_axi_rid    = r_local_id;")
                lines.append(f"            fub_axi_rdata  = {master_width}'d0;")
                lines.append("            fub_axi_rresp  = 2'b11;")
                lines.append("            fub_axi_rlast  = 1'b1;")
                lines.append("            fub_axi_rvalid = 1'b1;")
                lines.append("        end")
            lines.append("    end")
            lines.append("")
            if self._trace_echo:
                lines.extend(self._trace_echo_lines('r'))
                lines.append("")

        return lines

    def _generate_direct_passthrough(self, width: int) -> List[str]:
        """
        Generate direct assign passthrough for matching width.

        NOTE: Requests broadcast to output, responses come from MUX (not direct assigns).
        """
        lines = []
        suffix = f"{width}b"

        lines.append(f"    // ================================================================")
        lines.append(f"    // Direct passthrough: {self.master.data_width}b → {width}b (no converter)")
        lines.append(f"    // Requests: fub_axi_* → {self.master.name}_{suffix}_*")
        lines.append(f"    // Responses: {self.master.name}_{suffix}_* → MUX → fub_axi_*")
        lines.append(f"    // ================================================================")
        lines.append("")

        # Write channels
        if self.master.channels in ["wr", "rw"]:
            lines.append("    // AW channel (request: fub → output)")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.id     = {self.xid('aw')};")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.addr   = fub_axi_awaddr;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.len    = fub_axi_awlen;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.size   = fub_axi_awsize;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.burst  = fub_axi_awburst;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.lock   = fub_axi_awlock;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.cache  = fub_axi_awcache;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.prot   = fub_axi_awprot;")
            # Carry the master's real qos/region/user instead of zeroing
            # them. These were tied off while the crossbar had no mux for
            # them; it does now, and tying here would have made the mux
            # route constant 0 -- lint-clean and silently lossy.
            lines.append(f"    assign {self.master.name}_{suffix}_aw.qos    = fub_axi_awqos;")
            if self.master.protocol == 'axi5':
                # AXI5 removed REGION: the axi5_slave_* wrapper has no
                # awregion port, so there is nothing to route and '0 is the
                # correct value rather than a dropped signal.
                lines.append(f"    assign {self.master.name}_{suffix}_aw.region = 4'b0;  // AXI5 has no REGION")
            else:
                lines.append(f"    assign {self.master.name}_{suffix}_aw.region = fub_axi_awregion;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.user   = fub_axi_awuser;")
            lines.extend(self._sb_pack_lines('aw', suffix))
            # Gate by `<W>b_aw_path_active` so only the path matching the
            # currently selected slave's data_width drives awvalid (see big
            # comment in _generate_width_adaptation).
            lines.append(f"    assign {self.master.name}_{suffix}_awvalid   = fub_axi_awvalid && aw_path_active_{width}b;")
            lines.append("    // awready routed via MUX")
            lines.append("")

            lines.append("    // W channel (request: fub → output)")
            lines.append(f"    assign {self.master.name}_{suffix}_w.data  = fub_axi_wdata;")
            lines.append(f"    assign {self.master.name}_{suffix}_w.strb  = fub_axi_wstrb;")
            lines.append(f"    assign {self.master.name}_{suffix}_w.last  = fub_axi_wlast;")
            lines.append(f"    assign {self.master.name}_{suffix}_w.user  = fub_axi_wuser;")
            lines.extend(self._sb_pack_lines('w', suffix))
            # Gate by `<W>b_w_path_active` (FIFO-tracked) -- aw_path_active
            # is combinational and would revert mid-burst once fub_axi_awaddr
            # changes.
            lines.append(f"    assign {self.master.name}_{suffix}_wvalid  = fub_axi_wvalid && w_path_active_{width}b;")
            lines.append("    // wready routed via MUX")
            lines.append("")

            lines.append("    // B channel (response: output → MUX → fub)")
            lines.append("    // Ready gated by the response head — see b_path_active comment.")
            lines.append(f"    assign {self.master.name}_{suffix}_bready = fub_axi_bready && b_path_active_{width}b;")
            lines.append("    // bid, bresp, bvalid routed via MUX (user field ignored)")
            lines.append("")

        # Read channels
        if self.master.channels in ["rd", "rw"]:
            lines.append("    // AR channel (request: fub → output)")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.id     = {self.xid('ar')};")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.addr   = fub_axi_araddr;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.len    = fub_axi_arlen;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.size   = fub_axi_arsize;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.burst  = fub_axi_arburst;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.lock   = fub_axi_arlock;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.cache  = fub_axi_arcache;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.prot   = fub_axi_arprot;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.qos    = fub_axi_arqos;")
            if self.master.protocol == 'axi5':
                lines.append(f"    assign {self.master.name}_{suffix}_ar.region = 4'b0;  // AXI5 has no REGION")
            else:
                lines.append(f"    assign {self.master.name}_{suffix}_ar.region = fub_axi_arregion;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.user   = fub_axi_aruser;")
            lines.extend(self._sb_pack_lines('ar', suffix))
            # Gate by `<W>b_ar_path_active` (only the matching width path
            # drives arvalid; see comment in _generate_width_adaptation).
            lines.append(f"    assign {self.master.name}_{suffix}_arvalid   = fub_axi_arvalid && ar_path_active_{width}b;")
            lines.append("    // arready routed via MUX")
            lines.append("")

            lines.append("    // R channel (response: output → MUX → fub)")
            lines.append("    // Ready gated by the response head — see r_path_active comment.")
            lines.append(f"    assign {self.master.name}_{suffix}_rready = fub_axi_rready && r_path_active_{width}b;")
            lines.append("    // rid, rdata, rresp, rlast, rvalid routed via MUX (user field ignored)")
            lines.append("")

        return lines

    def _rate_buffer_depth(self, slave_width: int, use_aligner: bool) -> int:
        """Wide beats of rate-matching buffer on this width path, or 0.

        Only an UPSIZED burst path into a slave that another master also
        reaches: there the shared slave's channel would otherwise run at
        this master's narrow rate for the whole burst (bridge W2). A slave
        this master has to itself loses nothing to the narrow rate, and the
        single-beat aligners (AXI4-Lite / APB / WB4 requesters) have no
        burst to buffer."""
        depth = int(getattr(self.master, 'rate_buffer', 0) or 0)
        if depth == 0 or use_aligner or self.master.data_width >= slave_width:
            return 0
        for si in self.master.slave_connections:
            sl = self.slaves[si]
            if sl.data_width != slave_width:
                continue
            sharers = sum(1 for m in self.all_masters if si in m.slave_connections)
            if sharers >= 2:
                return depth
        return 0

    def _generate_converter_instance(self, slave_width: int) -> List[str]:
        """Generate width converter instance for mismatched width with proper signal isolation."""
        lines = []
        suffix = f"{slave_width}b"
        master_width = self.master.data_width

        lines.append(f"    // ================================================================")
        lines.append(f"    // Width converter: {master_width}b → {slave_width}b")
        lines.append(f"    // ================================================================")
        lines.append("")

        # Intermediate signals for converter slave side (from fub_axi_*)
        # These isolate converter responses from direct fub_axi_* assignments
        lines.append(f"    // Intermediate signals for {suffix} converter")
        if self.master.channels in ["wr", "rw"]:
            lines.append(f"    logic conv_{suffix}_awready;")
            lines.append(f"    logic conv_{suffix}_wready;")
            lines.append(f"    logic [{self.xbar_id_width-1}:0] conv_{suffix}_bid;")
            lines.append(f"    logic [1:0] conv_{suffix}_bresp;")
            lines.append(f"    logic conv_{suffix}_bvalid;")
        if self.master.channels in ["rd", "rw"]:
            lines.append(f"    logic conv_{suffix}_arready;")
            lines.append(f"    logic [{self.xbar_id_width-1}:0] conv_{suffix}_rid;")
            lines.append(f"    logic [{master_width-1}:0] conv_{suffix}_rdata;")
            lines.append(f"    logic [1:0] conv_{suffix}_rresp;")
            lines.append(f"    logic conv_{suffix}_rlast;")
            lines.append(f"    logic conv_{suffix}_rvalid;")
        lines.append("")

        # AXI5 sideband never traverses the converter (A5-2 slice 2)
        lines.extend(self._sb_conv_tie_lines(suffix))

        from ..components.axi4_dwidth_converter_component import Axi4DwidthConverter

        struct_prefix = f"{self.master.name}_{suffix}"

        # For an AXIL master upsizing to a wider slave, axi_data_upsize
        # (the burst-counter aggregator inside axi4_dwidth_converter_wr/rd)
        # always places the narrow beat at lane 0 of the wide bus and
        # ignores awaddr's low bits. That violates AXI4 sub-wide byte-lane
        # semantics — wstrb[b]=1 must enable wdata[8*b +: 8]. For real
        # AXI4-compliant slaves (e.g. byte-strobed BRAMs) every narrow
        # beat overwrites lane 0 of the row, corrupting prior writes.
        # Substitute the dedicated master-side aligner modules instead;
        # they emit one wide single-beat write/read with wdata/wstrb
        # positioned at slot = awaddr[ROW_LSB-1:SLOT_LSB].
        # APB requesters produce the same single-beat, awlen=0 stream (via
        # apb{4,5}_to_axi4), so they take the aligner for the same reason.
        use_aligner = (self.master.protocol in ('axil', 'axil5', 'apb', 'apb5', 'wb4')) and \
                      (master_width < slave_width)

        # Write converter
        if self.master.channels in ["wr", "rw"]:
            if use_aligner:
                lines.extend(self._generate_axil_align_wr_instance(
                    instance_name=f'u_wr_conv_{suffix}',
                    s_data_width=master_width,
                    m_data_width=slave_width,
                    id_width=self.xbar_id_width,  # fabric side: {master index, id} (bridge TASK-005, was BRIDGE-016)
                    user_width=getattr(self.master, 'user_width', 1) or 1,
                    addr_width=getattr(self.master, 'addr_width', 32),
                    suffix=suffix,
                    struct_prefix=struct_prefix,
                ))
            else:
                conv_wr = Axi4DwidthConverter(
                    direction='wr',
                    instance_name=f'u_wr_conv_{suffix}',
                    s_data_width=master_width,
                    m_data_width=slave_width,
                    id_width=self.xbar_id_width,  # fabric side: {master index, id} (bridge TASK-005, was BRIDGE-016)
                )
                conv_wr.connect_clocks_and_resets()
                conv_wr.connect_s_axi_write(s_awid_signal=self.xid('aw'), 
                    fub_prefix='fub_axi_',
                    aw_valid_gate=f'fub_axi_awvalid && aw_path_active_{slave_width}b',
                    w_valid_gate=f'fub_axi_wvalid && w_path_active_{slave_width}b',
                    b_intercept_prefix=f'conv_{suffix}',
                    bready_expr=f'fub_axi_bready && b_path_active_{slave_width}b',
                )
                rb = self._rate_buffer_depth(slave_width, use_aligner)
                rbp = f'{struct_prefix}_rb'
                conv_wr.connect_m_axi_write(
                    struct_prefix=struct_prefix,
                    valid_signal=(f'{rbp}_awvalid' if rb else f'{struct_prefix}_awvalid'),
                    ready_signal=(f'{rbp}_awready' if rb else f'{struct_prefix}_awready'),
                    bvalid_signal=f'{struct_prefix}_bvalid',
                    bready_signal=f'{struct_prefix}_bready',
                    aw_w_prefix=(rbp if rb else None),
                )
                if rb:
                    lines.append(f"    // Write rate buffer ({rb} x {slave_width}b): the converter's wide side")
                    lines.append(f"    // feeds it, and a burst of up to {rb} beats reaches the crossbar only once")
                    lines.append(f"    // it is buffered whole, so the shared slave's W runs at its full rate")
                    lines.append(f"    // (bridge W2). Longer bursts pass through.")
                    lines.append(f"    axi4_aw_t {rbp}_aw;")
                    lines.append(f"    axi4_w_{suffix}_t {rbp}_w;")
                    lines.append(f"    logic {rbp}_awvalid, {rbp}_awready, {rbp}_wvalid, {rbp}_wready;")
                lines.extend(conv_wr.generate_lines())
                if rb:
                    mo = int(getattr(self.master, 'max_outstanding', 16))
                    lines.append(f"    bridge_wr_rate_buf #(")
                    lines.append(f"        .AW_WIDTH        ($bits(axi4_aw_t)),")
                    lines.append(f"        .W_WIDTH         ($bits(axi4_w_{suffix}_t)),")
                    lines.append(f"        .DEPTH           ({rb}),")
                    lines.append(f"        .AW_DEPTH        (4),")
                    lines.append(f"        .MAX_OUTSTANDING ({mo})")
                    lines.append(f"    ) u_wr_rbuf_{suffix} (")
                    lines.append(f"        .aclk      (aclk),")
                    lines.append(f"        .aresetn   (aresetn),")
                    lines.append(f"        .s_aw      ({rbp}_aw),")
                    lines.append(f"        .s_awlen   ({rbp}_aw.len),")
                    lines.append(f"        .s_awvalid ({rbp}_awvalid),")
                    lines.append(f"        .s_awready ({rbp}_awready),")
                    lines.append(f"        .s_w       ({rbp}_w),")
                    lines.append(f"        .s_wlast   ({rbp}_w.last),")
                    lines.append(f"        .s_wvalid  ({rbp}_wvalid),")
                    lines.append(f"        .s_wready  ({rbp}_wready),")
                    lines.append(f"        .m_aw      ({struct_prefix}_aw),")
                    lines.append(f"        .m_awvalid ({struct_prefix}_awvalid),")
                    lines.append(f"        .m_awready ({struct_prefix}_awready),")
                    lines.append(f"        .m_w       ({struct_prefix}_w),")
                    lines.append(f"        .m_wvalid  ({struct_prefix}_wvalid),")
                    lines.append(f"        .m_wready  ({struct_prefix}_wready)")
                    lines.append(f"    );")
                    lines.append("")

        # Read converter
        if self.master.channels in ["rd", "rw"]:
            if use_aligner:
                lines.extend(self._generate_axil_align_rd_instance(
                    instance_name=f'u_rd_conv_{suffix}',
                    s_data_width=master_width,
                    m_data_width=slave_width,
                    id_width=self.xbar_id_width,  # fabric side: {master index, id} (bridge TASK-005, was BRIDGE-016)
                    user_width=getattr(self.master, 'user_width', 1) or 1,
                    addr_width=getattr(self.master, 'addr_width', 32),
                    suffix=suffix,
                    struct_prefix=struct_prefix,
                ))
            else:
                conv_rd = Axi4DwidthConverter(
                    direction='rd',
                    instance_name=f'u_rd_conv_{suffix}',
                    s_data_width=master_width,
                    m_data_width=slave_width,
                    id_width=self.xbar_id_width,  # fabric side: {master index, id} (bridge TASK-005, was BRIDGE-016)
                )
                conv_rd.connect_clocks_and_resets()
                conv_rd.connect_s_axi_read(s_arid_signal=self.xid('ar'), 
                    fub_prefix='fub_axi_',
                    ar_valid_gate=f'fub_axi_arvalid && ar_path_active_{slave_width}b',
                    r_intercept_prefix=f'conv_{suffix}',
                    rready_expr=f'fub_axi_rready && r_path_active_{slave_width}b',
                )
                rb = self._rate_buffer_depth(slave_width, use_aligner)
                rbp = f'{struct_prefix}_rb'
                conv_rd.connect_m_axi_read(
                    struct_prefix=struct_prefix,
                    arvalid_signal=f'{struct_prefix}_arvalid',
                    arready_signal=f'{struct_prefix}_arready',
                    rvalid_signal=(f'{rbp}_rvalid' if rb else f'{struct_prefix}_rvalid'),
                    rready_signal=(f'{rbp}_rready' if rb else f'{struct_prefix}_rready'),
                    r_prefix=(rbp if rb else None),
                )
                if rb:
                    lines.append(f"    // Read rate buffer ({rb} x {slave_width}b): R is taken from the crossbar")
                    lines.append(f"    // at the slave's full rate and drained at this master's narrow rate, so")
                    lines.append(f"    // the shared slave's R is not held by a slow consumer (bridge W2).")
                    lines.append(f"    axi4_r_{suffix}_t {rbp}_r;")
                    lines.append(f"    logic {rbp}_rvalid, {rbp}_rready;")
                lines.extend(conv_rd.generate_lines())
                if rb:
                    lines.append(f"    gaxi_fifo_sync #(")
                    lines.append(f"        .DATA_WIDTH ($bits(axi4_r_{suffix}_t)),")
                    lines.append(f"        .DEPTH      ({rb})")
                    lines.append(f"    ) u_rd_rbuf_{suffix} (")
                    lines.append(f"        .axi_aclk    (aclk),")
                    lines.append(f"        .axi_aresetn (aresetn),")
                    lines.append(f"        .wr_valid    ({struct_prefix}_rvalid),")
                    lines.append(f"        .wr_ready    ({struct_prefix}_rready),")
                    lines.append(f"        .wr_data     ({struct_prefix}_r),")
                    lines.append(f"        .rd_ready    ({rbp}_rready),")
                    lines.append(f"        /* verilator lint_off PINCONNECTEMPTY */")
                    lines.append(f"        .count       (),")
                    lines.append(f"        /* verilator lint_on PINCONNECTEMPTY */")
                    lines.append(f"        .rd_valid    ({rbp}_rvalid),")
                    lines.append(f"        .rd_data     ({rbp}_r)")
                    lines.append(f"    );")
                    lines.append("")

        return lines

    # ------------------------------------------------------------------
    # AXIL-master alignment helpers (drop-in replacements for the
    # axi_data_upsize-based dwidth converters when master.protocol=='axil'
    # and we're upsizing into a wider slave). See
    # projects/components/utility-ip/converters/rtl/axil_to_axi4_wide_align_{wr,rd}.sv
    # for the SystemVerilog semantics.
    # ------------------------------------------------------------------

    def _generate_axil_align_wr_instance(self, *, instance_name: str,
                                          s_data_width: int, m_data_width: int,
                                          id_width: int, user_width: int,
                                          addr_width: int, suffix: str,
                                          struct_prefix: str) -> List[str]:
        """Emit an axil_to_axi4_wide_align_wr instantiation with the
        same slave-side and master-side wiring contract as
        Axi4DwidthConverter('wr')."""
        lines: List[str] = []
        lines.append(f"    // Master-side AXIL alignment (no aggregation): every narrow")
        lines.append(f"    // single-beat AXIL write becomes one wide AXI4 single-beat with")
        lines.append(f"    // wdata/wstrb shifted by awaddr's low bits.")
        lines.append(f"    axil_to_axi4_wide_align_wr #(")
        lines.append(f"        .S_AXI_DATA_WIDTH({s_data_width}),")
        lines.append(f"        .M_AXI_DATA_WIDTH({m_data_width}),")
        lines.append(f"        .AXI_ID_WIDTH({id_width}),")
        lines.append(f"        .AXI_ADDR_WIDTH({addr_width}),")
        lines.append(f"        .AXI_USER_WIDTH({user_width})")
        lines.append(f"    ) {instance_name} (")
        lines.append(f"        .aclk(aclk),")
        lines.append(f"        .aresetn(aresetn),")
        # Slave side (from master via wrapper). awvalid/wvalid are gated
        # by the per-width path-active signals; awready/wready are
        # captured as conv_{suffix}_*ready so the wrapper sees them
        # only when this path is selected.
        lines.append(f"        .s_axi_awid({self.xid('aw')}),")
        lines.append(f"        .s_axi_awaddr(fub_axi_awaddr),")
        lines.append(f"        .s_axi_awlen(fub_axi_awlen),")
        lines.append(f"        .s_axi_awsize(fub_axi_awsize),")
        lines.append(f"        .s_axi_awburst(fub_axi_awburst),")
        lines.append(f"        .s_axi_awlock(fub_axi_awlock),")
        lines.append(f"        .s_axi_awcache(fub_axi_awcache),")
        lines.append(f"        .s_axi_awprot(fub_axi_awprot),")
        lines.append(f"        .s_axi_awqos(4'b0),")
        lines.append(f"        .s_axi_awregion(4'b0),")
        lines.append(f"        .s_axi_awuser(1'b0),")
        lines.append(f"        .s_axi_awvalid(fub_axi_awvalid && aw_path_active_{suffix}),")
        lines.append(f"        .s_axi_awready(conv_{suffix}_awready),")
        lines.append(f"        .s_axi_wdata(fub_axi_wdata),")
        lines.append(f"        .s_axi_wstrb(fub_axi_wstrb),")
        lines.append(f"        .s_axi_wlast(fub_axi_wlast),")
        lines.append(f"        .s_axi_wuser(1'b0),")
        lines.append(f"        .s_axi_wvalid(fub_axi_wvalid && w_path_active_{suffix}),")
        lines.append(f"        .s_axi_wready(conv_{suffix}_wready),")
        lines.append(f"        .s_axi_bid(conv_{suffix}_bid),")
        lines.append(f"        .s_axi_bresp(conv_{suffix}_bresp),")
        lines.append(f"        .s_axi_buser(),")
        lines.append(f"        .s_axi_bvalid(conv_{suffix}_bvalid),")
        lines.append(f"        .s_axi_bready(fub_axi_bready && b_path_active_{suffix}),")  # head-gated: see b_path_active comment
        # Master side (to crossbar) — struct fields.
        lines.append(f"        .m_axi_awid({struct_prefix}_aw.id),")
        lines.append(f"        .m_axi_awaddr({struct_prefix}_aw.addr),")
        lines.append(f"        .m_axi_awlen({struct_prefix}_aw.len),")
        lines.append(f"        .m_axi_awsize({struct_prefix}_aw.size),")
        lines.append(f"        .m_axi_awburst({struct_prefix}_aw.burst),")
        lines.append(f"        .m_axi_awlock({struct_prefix}_aw.lock),")
        lines.append(f"        .m_axi_awcache({struct_prefix}_aw.cache),")
        lines.append(f"        .m_axi_awprot({struct_prefix}_aw.prot),")
        lines.append(f"        .m_axi_awqos({struct_prefix}_aw.qos),")
        lines.append(f"        .m_axi_awregion({struct_prefix}_aw.region),")
        lines.append(f"        .m_axi_awuser({struct_prefix}_aw.user),")
        lines.append(f"        .m_axi_awvalid({struct_prefix}_awvalid),")
        lines.append(f"        .m_axi_awready({struct_prefix}_awready),")
        lines.append(f"        .m_axi_wdata({struct_prefix}_w.data),")
        lines.append(f"        .m_axi_wstrb({struct_prefix}_w.strb),")
        lines.append(f"        .m_axi_wlast({struct_prefix}_w.last),")
        lines.append(f"        .m_axi_wuser({struct_prefix}_w.user),")
        lines.append(f"        .m_axi_wvalid({struct_prefix}_wvalid),")
        lines.append(f"        .m_axi_wready({struct_prefix}_wready),")
        lines.append(f"        .m_axi_bid({struct_prefix}_b.id),")
        lines.append(f"        .m_axi_bresp({struct_prefix}_b.resp),")
        lines.append(f"        .m_axi_buser({struct_prefix}_b.user),")
        lines.append(f"        .m_axi_bvalid({struct_prefix}_bvalid),")
        lines.append(f"        .m_axi_bready({struct_prefix}_bready)")
        lines.append(f"    );")
        lines.append("")
        return lines

    def _generate_axil_align_rd_instance(self, *, instance_name: str,
                                          s_data_width: int, m_data_width: int,
                                          id_width: int, user_width: int,
                                          addr_width: int, suffix: str,
                                          struct_prefix: str) -> List[str]:
        """Emit an axil_to_axi4_wide_align_rd instantiation."""
        lines: List[str] = []
        lines.append(f"    // Master-side AXIL alignment (read direction).")
        lines.append(f"    axil_to_axi4_wide_align_rd #(")
        lines.append(f"        .S_AXI_DATA_WIDTH({s_data_width}),")
        lines.append(f"        .M_AXI_DATA_WIDTH({m_data_width}),")
        lines.append(f"        .AXI_ID_WIDTH({id_width}),")
        lines.append(f"        .AXI_ADDR_WIDTH({addr_width}),")
        lines.append(f"        .AXI_USER_WIDTH({user_width})")
        lines.append(f"    ) {instance_name} (")
        lines.append(f"        .aclk(aclk),")
        lines.append(f"        .aresetn(aresetn),")
        lines.append(f"        .s_axi_arid({self.xid('ar')}),")
        lines.append(f"        .s_axi_araddr(fub_axi_araddr),")
        lines.append(f"        .s_axi_arlen(fub_axi_arlen),")
        lines.append(f"        .s_axi_arsize(fub_axi_arsize),")
        lines.append(f"        .s_axi_arburst(fub_axi_arburst),")
        lines.append(f"        .s_axi_arlock(fub_axi_arlock),")
        lines.append(f"        .s_axi_arcache(fub_axi_arcache),")
        lines.append(f"        .s_axi_arprot(fub_axi_arprot),")
        lines.append(f"        .s_axi_arqos(4'b0),")
        lines.append(f"        .s_axi_arregion(4'b0),")
        lines.append(f"        .s_axi_aruser(1'b0),")
        lines.append(f"        .s_axi_arvalid(fub_axi_arvalid && ar_path_active_{suffix}),")
        lines.append(f"        .s_axi_arready(conv_{suffix}_arready),")
        lines.append(f"        .s_axi_rid(conv_{suffix}_rid),")
        lines.append(f"        .s_axi_rdata(conv_{suffix}_rdata),")
        lines.append(f"        .s_axi_rresp(conv_{suffix}_rresp),")
        lines.append(f"        .s_axi_rlast(conv_{suffix}_rlast),")
        lines.append(f"        .s_axi_ruser(),")
        lines.append(f"        .s_axi_rvalid(conv_{suffix}_rvalid),")
        lines.append(f"        .s_axi_rready(fub_axi_rready && r_path_active_{suffix}),")  # head-gated: see r_path_active comment
        lines.append(f"        .m_axi_arid({struct_prefix}_ar.id),")
        lines.append(f"        .m_axi_araddr({struct_prefix}_ar.addr),")
        lines.append(f"        .m_axi_arlen({struct_prefix}_ar.len),")
        lines.append(f"        .m_axi_arsize({struct_prefix}_ar.size),")
        lines.append(f"        .m_axi_arburst({struct_prefix}_ar.burst),")
        lines.append(f"        .m_axi_arlock({struct_prefix}_ar.lock),")
        lines.append(f"        .m_axi_arcache({struct_prefix}_ar.cache),")
        lines.append(f"        .m_axi_arprot({struct_prefix}_ar.prot),")
        lines.append(f"        .m_axi_arqos({struct_prefix}_ar.qos),")
        lines.append(f"        .m_axi_arregion({struct_prefix}_ar.region),")
        lines.append(f"        .m_axi_aruser({struct_prefix}_ar.user),")
        lines.append(f"        .m_axi_arvalid({struct_prefix}_arvalid),")
        lines.append(f"        .m_axi_arready({struct_prefix}_arready),")
        lines.append(f"        .m_axi_rid({struct_prefix}_r.id),")
        lines.append(f"        .m_axi_rdata({struct_prefix}_r.data),")
        lines.append(f"        .m_axi_rresp({struct_prefix}_r.resp),")
        lines.append(f"        .m_axi_rlast({struct_prefix}_r.last),")
        lines.append(f"        .m_axi_ruser({struct_prefix}_r.user),")
        lines.append(f"        .m_axi_rvalid({struct_prefix}_rvalid),")
        lines.append(f"        .m_axi_rready({struct_prefix}_rready)")
        lines.append(f"    );")
        lines.append("")
        return lines

    def _get_module_name(self) -> str:
        """Get adapter module name."""
        from bridge_pkg.module_naming import adapter_module_name
        return adapter_module_name(self.bridge_name, self.master.name)


def test_adapter_generator():
    """Test adapter generator with example configuration."""
    from bridge_pkg.generators.package_generator import PackageGenerator

    # Example configuration
    slaves = [
        SlaveInfo("ddr", 0x00000000, 0x80000000, 32, 32),
        SlaveInfo("sram", 0x80000000, 0x80000000, 32, 32)
    ]

    master_config = MasterConfig(
        name="cpu",
        prefix="cpu_m_axi_",
        data_width=32,
        addr_width=32,
        id_width=4,
        channels="wr",
        slave_connections=[0, 1]
    )

    gen = AdapterGenerator("bridge_1x2_wr", 2, master_config, slaves)
    adapter_src = gen.generate()
    print(adapter_src)


if __name__ == "__main__":
    test_adapter_generator()
