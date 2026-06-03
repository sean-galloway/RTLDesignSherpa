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

from typing import List, Dict, Tuple
from dataclasses import dataclass
from ..components.apb_shim_adapter import ApbShimAdapter
from ..signal_naming import SignalNaming, Direction, AXI4Channel, AXI4_MASTER_SIGNALS, PortDirection, SignalInfo


# Widths in bits for the 15 cfg_* inputs every axi4_*_mon variant
# exposes. Mirrors the SV declarations in
# rtl/amba/axi4/axi4_{master,slave}_{wr,rd}_mon.sv.
_MONITOR_CFG_WIDTHS = {
    'cfg_monitor_enable':       1,
    'cfg_error_enable':         1,
    'cfg_timeout_enable':       1,
    'cfg_perf_enable':          1,
    'cfg_timeout_cycles':      16,
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
    protocol: str = 'axi4'  # Protocol type: 'axi4' or 'apb'
    enable_ooo: bool = False  # Slave supports out-of-order responses (use CAM vs FIFO)
    use_monitor: bool = True  # Per-port USE_MONITOR override (see PortSpec)


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


class AdapterGenerator:
    """
    Generates per-master adapter modules for bridge crossbars.

    Each adapter contains:
    - Timing wrapper (axi4_slave_rd/wr)
    - Address decode (one-hot slave selection)
    - Width converters or direct passthrough
    - Struct-based outputs for clean interface
    """

    def __init__(self, bridge_name: str, num_slaves: int, master_config: MasterConfig, slaves: List[SlaveInfo], all_masters: List[MasterConfig] = None, enable_monitoring: bool = False, master_index: int = 0):
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

        # Skid buffer depths (configurable)
        self.skid_depth_aw = 2
        self.skid_depth_ar = 2
        self.skid_depth_w = 4
        self.skid_depth_r = 2
        self.skid_depth_b = 2

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

        # Module end
        lines.append("endmodule : " + self._get_module_name())
        lines.append("")

        return "\n".join(lines)

    def _generate_header(self) -> List[str]:
        """Generate file header."""
        return [
            f"// {self.master.name.upper()} Master Adapter Module",
            "// Generated by: AdapterGenerator",
            f"// Handles timing isolation, address decode, and width conversion for {self.master.name} master",
            "",
            "`timescale 1ns / 1ps",
            "",
            f"import {self.bridge_name}_pkg::*;",
            ""
        ]

    def _generate_module_declaration(self) -> List[str]:
        """Generate module declaration with ports."""
        lines = []
        module_name = self._get_module_name()

        # Module header with parameters
        lines.append(f"module {module_name} #(")
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
        Names use the adapter-local channel suffix (`_wr` / `_rd`) -- the
        bridge top binds them to {port_name}_{port_idx}-prefixed nets so
        each monbus stream and cfg group is uniquely identifiable.

        After the 64->128-bit packet widening, every channel also gets a
        64-bit `monbus_<chan>_timestamp` side-band output (paired with
        the packet). A single shared `i_mon_time` input is declared once
        per adapter (not per channel) because every wrapper instance
        consumes the same free-running counter from monbus_axil_group's
        `mon_time_out`."""
        from ..components.axi4_timing_wrapper_component import Axi4TimingWrapper

        lines: List[str] = []
        channels: List[str] = []
        if self.master.channels in ("wr", "rw"):
            channels.append("wr")
        if self.master.channels in ("rd", "rw"):
            channels.append("rd")

        # Shared free-running monitor-time -- one input shared by every
        # internal wrapper instance. Always emit when monitoring is
        # enabled, regardless of which channel(s) are present.
        if channels:
            lines.append("    // Shared free-running monitor-time (from monbus_axil_group.mon_time_out)")
            lines.append("    input  monitor_common_pkg::monbus_timestamp_t i_mon_time,")
            lines.append("")

        last_chan = channels[-1] if channels else None
        for chan in channels:
            lines.append(f"    // Monitor side-band: {chan} wrapper")
            lines.append(f"    output logic                                  monbus_{chan}_valid,")
            lines.append(f"    input  logic                                  monbus_{chan}_ready,")
            lines.append(f"    output monitor_common_pkg::monitor_packet_t   monbus_{chan}_packet,")
            lines.append(f"    output monitor_common_pkg::monbus_timestamp_t monbus_{chan}_timestamp,")
            lines.append("")
            for i, sig in enumerate(Axi4TimingWrapper.MONITOR_CFG_SIGNALS):
                is_final_cfg = (chan == last_chan and i == len(Axi4TimingWrapper.MONITOR_CFG_SIGNALS) - 1)
                width = _MONITOR_CFG_WIDTHS[sig]
                width_decl = "       " if width == 1 else f"[{width-1}:0]"
                base = sig[len("cfg_"):]
                sep = "" if is_final_cfg else ","
                lines.append(f"    input  logic {width_decl} cfg_{chan}_{base}{sep}")
            if chan != last_chan:
                lines.append("")
        return lines

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
        """
        lines = []

        # Width parameters for signal info queries
        width_values = {
            'ID_WIDTH': self.master.id_width,
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

    def _generate_internal_signals(self) -> List[str]:
        """Generate internal signal declarations (fub_axi_*)."""
        lines = []
        id_width = self.master.id_width
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
        lines.append(f"    // Note: ID width matches external ({id_width}-bit)")
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
            lines.append("    logic         fub_axi_awvalid;")
            lines.append("    logic         fub_axi_awready;")
            lines.append("")

            lines.append(f"    logic [{data_width-1}:0]  fub_axi_wdata;")
            lines.append(f"    logic [{strb_width-1}:0]   fub_axi_wstrb;")
            lines.append("    logic         fub_axi_wlast;")
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

        # Monitor identity: UNIT_ID=2 marks every master-side wrapper
        # (axi4_slave_*_mon -- the bridge looks like a slave to the
        # external master), AGENT_ID = (master_index << 4) | channel_bit
        # so each per-port wrapper produces uniquely tagged monbus packets.
        # channel_bit: 0 = rd, 1 = wr. Mirrors the SV defaults' UNIT_ID=2.
        master_unit_id = 2 if self.enable_monitoring else None
        wr_agent_id = ((self.master_index << 4) | 0x1) if self.enable_monitoring else None
        rd_agent_id = ((self.master_index << 4) | 0x0) if self.enable_monitoring else None

        # Write wrapper
        if self.master.channels in ["wr", "rw"]:
            wrapper = Axi4TimingWrapper(
                side='slave', channel='wr', mon=self.enable_monitoring,
                instance_name='u_timing_wrapper_wr',
                id_width=self.master.id_width,
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
            )
            wrapper.connect_clocks_and_resets()
            # External side comes from the master's prefix (slave-of-
            # external-master). Bridge-internal side uses fub_axi_*.
            wrapper.connect_external(connector_prefix=signal_prefix)
            wrapper.connect_bridge_internal(connector_prefix='fub_axi_')
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
            lines.append("    // ================================================================")
            lines.append(f"    // Timing isolation wrapper (axi4_slave_wr{'_mon' if self.enable_monitoring else ''})")
            lines.append("    // ================================================================")
            lines.extend(wrapper.generate_lines())

        # Read wrapper
        if self.master.channels in ["rd", "rw"]:
            wrapper = Axi4TimingWrapper(
                side='slave', channel='rd', mon=self.enable_monitoring,
                instance_name='u_timing_wrapper_rd',
                id_width=self.master.id_width,
                addr_width=32,
                data_width=self.master.data_width,
                skid_depth_ax='SKID_DEPTH_AR',
                skid_depth_data='SKID_DEPTH_R',
                unit_id=master_unit_id,
                agent_id=rd_agent_id,
                use_monitor_param=(
                    'USE_MONITOR_RD' if self.enable_monitoring else None
                ),
            )
            wrapper.connect_clocks_and_resets()
            wrapper.connect_external(connector_prefix=signal_prefix)
            wrapper.connect_bridge_internal(connector_prefix='fub_axi_')
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
            lines.append("    // ================================================================")
            lines.append(f"    // Timing isolation wrapper (axi4_slave_rd{'_mon' if self.enable_monitoring else ''})")
            lines.append("    // ================================================================")
            lines.extend(wrapper.generate_lines())

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

        Always uses the slave's data_width — the bridge has one width
        parameter per slave, regardless of protocol. The adapter handles
        any width conversion locally for that slave; the crossbar only
        sees the slave's data_width on the wire.

        Earlier versions used a "LCD width" for APB slaves (min of master
        widths connecting to the same APB), which left the adapter and
        crossbar disagreeing on the suffix to use — adapter emitted
        cpu_master_64b_*, crossbar referenced cpu_master_32b_*. Dropping
        the LCD path means both sides read slave.data_width and
        get the same answer.
        """
        widths = set()
        for idx in self.master.slave_connections:
            widths.add(self.slaves[idx].data_width)
        return sorted(list(widths))

    def _get_masters_connecting_to_apb_slaves(self) -> List[MasterConfig]:
        """
        Get all masters (including this one) that connect to the same APB slaves.

        This is used for LCD (Lowest Common Denominator) width calculation:
        When multiple masters with different widths connect to the same APB slaves,
        we need to find the minimum width among them.

        Returns:
            List of MasterConfig objects that connect to same APB slaves as this master
        """
        # Find APB slaves this master connects to
        apb_slave_indices = [idx for idx in self.master.slave_connections
                             if self.slaves[idx].protocol == 'apb']

        if not apb_slave_indices:
            return []  # This master doesn't connect to any APB slaves

        # Find all masters that connect to ANY of these APB slaves
        connecting_masters = []
        seen_names = set()  # Track by name to avoid duplicates
        for apb_idx in apb_slave_indices:
            for master in self.all_masters:
                if apb_idx in master.slave_connections and master.name not in seen_names:
                    connecting_masters.append(master)
                    seen_names.add(master.name)

        return connecting_masters

    def _calculate_lcd_width_for_apb(self) -> int:
        """
        Calculate LCD (Lowest Common Denominator) width for APB slave connections.

        Returns the minimum data width among all masters connecting to the same
        APB slaves. This width will be used as the adapter output width.

        Returns:
            LCD width in bits, or master's native width if no APB connections
        """
        masters_to_apb = self._get_masters_connecting_to_apb_slaves()

        if not masters_to_apb:
            # No APB connections - use master's native width
            return self.master.data_width

        # Find minimum width among all masters connecting to APB
        lcd_width = min(m.data_width for m in masters_to_apb)

        if lcd_width != self.master.data_width:
            master_names = ', '.join(f"{m.name}({m.data_width}b)" for m in masters_to_apb)
            print(f"INFO: Adapter '{self.master.name}' LCD width for APB: {lcd_width}b")
            print(f"      Masters connecting to same APB slaves: {master_names}")

        return lcd_width

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
                        f"    assign aw_path_active_{slave_width}b = {aw_terms};"
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
                        f"    assign ar_path_active_{slave_width}b = {ar_terms};"
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

        # FIFO depth: needs to cover max outstanding requests. 16 is a safe default;
        # adapter wrappers typically don't accept more outstanding than this anyway.
        fifo_depth = 16
        fifo_aw_bits = 4  # $clog2(16)

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
            lines.append("    // -------- AW->B slave_select tracking FIFO --------")
            lines.append(f"    localparam int AW_TRK_DEPTH = {fifo_depth};")
            lines.append(f"    localparam int AW_TRK_AW    = {fifo_aw_bits};")
            lines.append(f"    logic [NUM_SLAVES-1:0] aw_trk_mem [AW_TRK_DEPTH];")
            lines.append("    logic [AW_TRK_AW:0] aw_trk_wptr, aw_trk_rptr;")
            lines.append("    logic aw_trk_push, aw_trk_pop;")
            # b_slave_select declared at the top of the module (see
            # _generate_address_decode) so width-adaptation can use it.
            lines.append("")
            lines.append("    assign aw_trk_push = fub_axi_awvalid && fub_axi_awready;")
            lines.append("    assign aw_trk_pop  = fub_axi_bvalid && fub_axi_bready;")
            lines.append("")
            lines.append("    always_ff @(posedge aclk or negedge aresetn) begin")
            lines.append("        if (!aresetn) begin")
            lines.append("            aw_trk_wptr <= '0;")
            lines.append("            aw_trk_rptr <= '0;")
            lines.append("        end else begin")
            lines.append("            if (aw_trk_push) begin")
            lines.append("                aw_trk_mem[aw_trk_wptr[AW_TRK_AW-1:0]] <= comb_slave_select_aw;")
            lines.append("                aw_trk_wptr <= aw_trk_wptr + 1'b1;")
            lines.append("            end")
            lines.append("            if (aw_trk_pop) begin")
            lines.append("                aw_trk_rptr <= aw_trk_rptr + 1'b1;")
            lines.append("            end")
            lines.append("        end")
            lines.append("    end")
            lines.append("")
            lines.append("    assign b_slave_select = (aw_trk_wptr != aw_trk_rptr)")
            lines.append("                          ? aw_trk_mem[aw_trk_rptr[AW_TRK_AW-1:0]]")
            lines.append("                          : '0;")
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
            lines.append("    always_ff @(posedge aclk or negedge aresetn) begin")
            lines.append("        if (!aresetn) begin")
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
            lines.append("    end")
            lines.append("")
            lines.append("    assign w_slave_select = (w_trk_wptr != w_trk_rptr)")
            lines.append("                          ? w_trk_mem[w_trk_rptr[AW_TRK_AW-1:0]]")
            lines.append("                          : '0;")
            lines.append("")

        if self.master.channels in ("rd", "rw"):
            lines.append("    // OUTPUT slave_select_ar mirrors the live combinational decode.")
            lines.append("    assign slave_select_ar = comb_slave_select_ar;")
            lines.append("")
            lines.append("    // -------- AR->R slave_select tracking FIFO --------")
            lines.append(f"    localparam int AR_TRK_DEPTH = {fifo_depth};")
            lines.append(f"    localparam int AR_TRK_AW    = {fifo_aw_bits};")
            lines.append(f"    logic [NUM_SLAVES-1:0] ar_trk_mem [AR_TRK_DEPTH];")
            lines.append("    logic [AR_TRK_AW:0] ar_trk_wptr, ar_trk_rptr;")
            lines.append("    logic ar_trk_push, ar_trk_pop;")
            # r_slave_select declared at the top of the module.
            lines.append("")
            lines.append("    assign ar_trk_push = fub_axi_arvalid && fub_axi_arready;")
            lines.append("    assign ar_trk_pop  = fub_axi_rvalid && fub_axi_rready && fub_axi_rlast;")
            lines.append("")
            lines.append("    always_ff @(posedge aclk or negedge aresetn) begin")
            lines.append("        if (!aresetn) begin")
            lines.append("            ar_trk_wptr <= '0;")
            lines.append("            ar_trk_rptr <= '0;")
            lines.append("        end else begin")
            lines.append("            if (ar_trk_push) begin")
            lines.append("                ar_trk_mem[ar_trk_wptr[AR_TRK_AW-1:0]] <= comb_slave_select_ar;")
            lines.append("                ar_trk_wptr <= ar_trk_wptr + 1'b1;")
            lines.append("            end")
            lines.append("            if (ar_trk_pop) begin")
            lines.append("                ar_trk_rptr <= ar_trk_rptr + 1'b1;")
            lines.append("            end")
            lines.append("        end")
            lines.append("    end")
            lines.append("")
            lines.append("    assign r_slave_select = (ar_trk_wptr != ar_trk_rptr)")
            lines.append("                          ? ar_trk_mem[ar_trk_rptr[AR_TRK_AW-1:0]]")
            lines.append("                          : '0;")
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
            lines.append("    always_comb begin")

            # Default assignments
            lines.append(f"        fub_axi_bid = {self.master.id_width}'d0;")
            lines.append("        fub_axi_bresp = 2'b00;")
            lines.append("        fub_axi_bvalid = 1'b0;")
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
                        lines.append(f"                fub_axi_bid = {self.master.name}_{suffix}_b.id;")
                        lines.append(f"                fub_axi_bresp = {self.master.name}_{suffix}_b.resp;")
                        lines.append(f"                fub_axi_bvalid = {self.master.name}_{suffix}_bvalid;")
                    else:
                        # Converter intermediate signals
                        lines.append(f"                fub_axi_bid = conv_{suffix}_bid;")
                        lines.append(f"                fub_axi_bresp = conv_{suffix}_bresp;")
                        lines.append(f"                fub_axi_bvalid = conv_{suffix}_bvalid;")

                    lines.append("            end")

            lines.append("            default: begin")
            lines.append("                // No slave selected - hold defaults")
            lines.append("            end")
            lines.append("        endcase")
            lines.append("    end")
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
            lines.append("    end")
            lines.append("")

            lines.append("    // Read response MUX (R channel - uses r_slave_select FIFO head)")
            lines.append("    always_comb begin")

            # Default assignments
            lines.append(f"        fub_axi_rid = {self.master.id_width}'d0;")
            lines.append(f"        fub_axi_rdata = {master_width}'d0;")
            lines.append("        fub_axi_rresp = 2'b00;")
            lines.append("        fub_axi_rlast = 1'b0;")
            lines.append("        fub_axi_rvalid = 1'b0;")
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
                        lines.append(f"                fub_axi_rid = {self.master.name}_{suffix}_r.id;")
                        lines.append(f"                fub_axi_rdata = {self.master.name}_{suffix}_r.data;")
                        lines.append(f"                fub_axi_rresp = {self.master.name}_{suffix}_r.resp;")
                        lines.append(f"                fub_axi_rlast = {self.master.name}_{suffix}_r.last;")
                        lines.append(f"                fub_axi_rvalid = {self.master.name}_{suffix}_rvalid;")
                    else:
                        # Converter intermediate signals
                        lines.append(f"                fub_axi_rid = conv_{suffix}_rid;")
                        lines.append(f"                fub_axi_rdata = conv_{suffix}_rdata;")
                        lines.append(f"                fub_axi_rresp = conv_{suffix}_rresp;")
                        lines.append(f"                fub_axi_rlast = conv_{suffix}_rlast;")
                        lines.append(f"                fub_axi_rvalid = conv_{suffix}_rvalid;")

                    lines.append("            end")

            lines.append("            default: begin")
            lines.append("                // No slave selected - hold defaults")
            lines.append("            end")
            lines.append("        endcase")
            lines.append("    end")
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
            lines.append(f"    assign {self.master.name}_{suffix}_aw.id     = fub_axi_awid;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.addr   = fub_axi_awaddr;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.len    = fub_axi_awlen;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.size   = fub_axi_awsize;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.burst  = fub_axi_awburst;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.lock   = fub_axi_awlock;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.cache  = fub_axi_awcache;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.prot   = fub_axi_awprot;")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.qos    = 4'b0;  // Tie to 0")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.region = 4'b0;  // Tie to 0")
            lines.append(f"    assign {self.master.name}_{suffix}_aw.user   = 1'b0;  // Tie to 0")
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
            lines.append(f"    assign {self.master.name}_{suffix}_w.user  = 1'b0;  // Tie to 0")
            # Gate by `<W>b_w_path_active` (FIFO-tracked) -- aw_path_active
            # is combinational and would revert mid-burst once fub_axi_awaddr
            # changes.
            lines.append(f"    assign {self.master.name}_{suffix}_wvalid  = fub_axi_wvalid && w_path_active_{width}b;")
            lines.append("    // wready routed via MUX")
            lines.append("")

            lines.append("    // B channel (response: output → MUX → fub)")
            lines.append(f"    assign {self.master.name}_{suffix}_bready = fub_axi_bready;")
            lines.append("    // bid, bresp, bvalid routed via MUX (user field ignored)")
            lines.append("")

        # Read channels
        if self.master.channels in ["rd", "rw"]:
            lines.append("    // AR channel (request: fub → output)")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.id     = fub_axi_arid;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.addr   = fub_axi_araddr;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.len    = fub_axi_arlen;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.size   = fub_axi_arsize;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.burst  = fub_axi_arburst;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.lock   = fub_axi_arlock;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.cache  = fub_axi_arcache;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.prot   = fub_axi_arprot;")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.qos    = 4'b0;  // Tie to 0")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.region = 4'b0;  // Tie to 0")
            lines.append(f"    assign {self.master.name}_{suffix}_ar.user   = 1'b0;  // Tie to 0")
            # Gate by `<W>b_ar_path_active` (only the matching width path
            # drives arvalid; see comment in _generate_width_adaptation).
            lines.append(f"    assign {self.master.name}_{suffix}_arvalid   = fub_axi_arvalid && ar_path_active_{width}b;")
            lines.append("    // arready routed via MUX")
            lines.append("")

            lines.append("    // R channel (response: output → MUX → fub)")
            lines.append(f"    assign {self.master.name}_{suffix}_rready = fub_axi_rready;")
            lines.append("    // rid, rdata, rresp, rlast, rvalid routed via MUX (user field ignored)")
            lines.append("")

        return lines

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
            lines.append(f"    logic [{self.master.id_width-1}:0] conv_{suffix}_bid;")
            lines.append(f"    logic [1:0] conv_{suffix}_bresp;")
            lines.append(f"    logic conv_{suffix}_bvalid;")
        if self.master.channels in ["rd", "rw"]:
            lines.append(f"    logic conv_{suffix}_arready;")
            lines.append(f"    logic [{self.master.id_width-1}:0] conv_{suffix}_rid;")
            lines.append(f"    logic [{master_width-1}:0] conv_{suffix}_rdata;")
            lines.append(f"    logic [1:0] conv_{suffix}_rresp;")
            lines.append(f"    logic conv_{suffix}_rlast;")
            lines.append(f"    logic conv_{suffix}_rvalid;")
        lines.append("")

        from ..components.axi4_dwidth_converter_component import Axi4DwidthConverter

        struct_prefix = f"{self.master.name}_{suffix}"

        # Write converter
        if self.master.channels in ["wr", "rw"]:
            conv_wr = Axi4DwidthConverter(
                direction='wr',
                instance_name=f'u_wr_conv_{suffix}',
                s_data_width=master_width,
                m_data_width=slave_width,
                id_width=self.master.id_width,
            )
            conv_wr.connect_clocks_and_resets()
            conv_wr.connect_s_axi_write(
                fub_prefix='fub_axi_',
                aw_valid_gate=f'fub_axi_awvalid && aw_path_active_{slave_width}b',
                w_valid_gate=f'fub_axi_wvalid && w_path_active_{slave_width}b',
                b_intercept_prefix=f'conv_{suffix}',
            )
            conv_wr.connect_m_axi_write(
                struct_prefix=struct_prefix,
                valid_signal=f'{struct_prefix}_awvalid',
                ready_signal=f'{struct_prefix}_awready',
                bvalid_signal=f'{struct_prefix}_bvalid',
                bready_signal=f'{struct_prefix}_bready',
            )
            lines.extend(conv_wr.generate_lines())

        # Read converter
        if self.master.channels in ["rd", "rw"]:
            conv_rd = Axi4DwidthConverter(
                direction='rd',
                instance_name=f'u_rd_conv_{suffix}',
                s_data_width=master_width,
                m_data_width=slave_width,
                id_width=self.master.id_width,
            )
            conv_rd.connect_clocks_and_resets()
            conv_rd.connect_s_axi_read(
                fub_prefix='fub_axi_',
                ar_valid_gate=f'fub_axi_arvalid && ar_path_active_{slave_width}b',
                r_intercept_prefix=f'conv_{suffix}',
            )
            conv_rd.connect_m_axi_read(
                struct_prefix=struct_prefix,
                arvalid_signal=f'{struct_prefix}_arvalid',
                arready_signal=f'{struct_prefix}_arready',
                rvalid_signal=f'{struct_prefix}_rvalid',
                rready_signal=f'{struct_prefix}_rready',
            )
            lines.extend(conv_rd.generate_lines())

        return lines

    def _get_module_name(self) -> str:
        """Get adapter module name."""
        return f"{self.master.name}_adapter"


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
