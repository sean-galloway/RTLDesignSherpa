"""
Bridge Module Generator

Generates complete bridge modules using adapter architecture:
- Package file with AXI channel structs
- Per-master adapter modules
- Main bridge module with crossbar routing

Author: RTL Design Sherpa
Date: 2025-11-03
"""

import os
from typing import List, Dict
from dataclasses import dataclass

import sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../..'))

from bridge_pkg.generators.package_generator import PackageGenerator
from bridge_pkg.generators.adapter_generator import AdapterGenerator, MasterConfig, SlaveInfo, _MONITOR_CFG_WIDTHS, _ensure_trailing_comma
from bridge_pkg.generators.slave_adapter_generator import SlaveAdapterGenerator
from bridge_pkg.generators.crossbar_generator import CrossbarGenerator
from bridge_pkg.signal_naming import SignalNaming, Direction, AXI4Channel, Protocol, AXI4_MASTER_SIGNALS, PortDirection, SignalInfo
from bridge_pkg.components.axi4_timing_wrapper_component import Axi4TimingWrapper


@dataclass
class MonitoredWrapper:
    """One AXI4 _mon wrapper instance inside the bridge. The bridge top
    references each by a `{port_name}_{port_idx}_{channel}` prefix when
    naming the per-port cfg inputs, monbus internal wires, and the
    adapter-instance connector list."""
    port_name: str        # 'cpu', 'ddr', etc. -- from TOML
    port_idx: int         # master_index or slave_index
    side: str             # 'master' or 'slave'
    channel: str          # 'wr' or 'rd'

    @property
    def top_prefix(self) -> str:
        """`<port>_<idx>_<wr|rd>` -- prefix used at the bridge top
        for both monbus internal nets and per-port cfg inputs."""
        return f"{self.port_name}_{self.port_idx}_{self.channel}"

    @property
    def monbus_valid(self) -> str:
        return f"monbus_{self.top_prefix}_valid"

    @property
    def monbus_ready(self) -> str:
        return f"monbus_{self.top_prefix}_ready"

    @property
    def monbus_packet(self) -> str:
        return f"monbus_{self.top_prefix}_packet"

    @property
    def monbus_timestamp(self) -> str:
        return f"monbus_{self.top_prefix}_timestamp"

    def cfg_signal(self, base: str) -> str:
        """`cfg_<port>_<idx>_<wr|rd>_<base>` for a cfg signal whose
        wrapper-side port name is `cfg_<base>`."""
        return f"cfg_{self.top_prefix}_{base}"


class BridgeModuleGenerator:
    """
    Generates complete bridge modules with adapter architecture.

    Produces:
    - SystemVerilog package with AXI channel structs
    - Per-master adapter modules
    - Main bridge module with crossbar

    Example:
        gen = BridgeModuleGenerator("bridge_1x2_wr")
        gen.add_master(MasterConfig(...))
        gen.add_slave(SlaveInfo(...))
        gen.generate_all("/output/dir")
    """

    def __init__(self, bridge_name: str, enable_monitoring: bool = False,
                 internal_axil_group: bool = True,
                 use_all_monitors: bool = False,
                 use_no_monitors:  bool = False):
        """
        Initialize bridge generator.

        Args:
            bridge_name: Name of bridge (e.g., "bridge_1x2_wr")
            enable_monitoring: Use *_mon wrapper versions
            internal_axil_group: When True (default, backward-compatible),
                the bridge instantiates its own monbus_arbiter +
                monbus_axil_group internally, and exposes the group's
                AXIL slave/master, cfg, and IRQ at the bridge top --
                drop-in monitoring for a fresh SoC. When False, the
                bridge still instantiates the per-port arbiter but
                skips the AXIL group; instead it exposes a single
                aggregated monbus stream (monbus_agg_*) at the top
                so the integrator can merge it with an EXTERNAL
                monbus_axil_group that already exists in the SoC
                (the stream_char harness uses STREAM's internal
                group, for example). When False, the bridge requires
                `i_mon_time` as a top-level INPUT (fed from the
                external group's `mon_time_out`).
        """
        self.bridge_name = bridge_name
        self.enable_monitoring = enable_monitoring
        self.internal_axil_group = internal_axil_group
        # Defaults for the bridge-top USE_ALL_MONITORS / USE_NO_MONITORS
        # SV parameters. The harness can still override these at
        # instantiation -- the TOML just picks the build-time default.
        self.use_all_monitors = use_all_monitors
        self.use_no_monitors  = use_no_monitors
        self.masters: List[MasterConfig] = []
        self.slaves: List[SlaveInfo] = []

    def add_master(self, master: MasterConfig):
        """Add a master port to the bridge."""
        self.masters.append(master)

    def add_slave(self, slave: SlaveInfo):
        """Add a slave port to the bridge."""
        self.slaves.append(slave)

    def generate_all(self, output_dir: str) -> Dict[str, str]:
        """
        Generate all bridge files and write to output directory.

        Args:
            output_dir: Directory to write generated files

        Returns:
            Dictionary mapping filenames to file paths
        """
        os.makedirs(output_dir, exist_ok=True)

        generated_files = {}

        # 1. Generate package file
        pkg_src = self._generate_package()
        pkg_path = os.path.join(output_dir, f"{self.bridge_name}_pkg.sv")
        with open(pkg_path, 'w') as f:
            f.write(pkg_src)
        generated_files['package'] = pkg_path

        # 2. Generate master adapter modules
        for master_idx, master in enumerate(self.masters):
            adapter_src = self._generate_adapter(master, master_idx)
            adapter_path = os.path.join(output_dir, f"{master.name}_adapter.sv")
            with open(adapter_path, 'w') as f:
                f.write(adapter_src)
            generated_files[f'adapter_{master.name}'] = adapter_path

        # 3. Generate slave adapter modules. Pass the enumerated index so
        # SlaveAdapterGenerator can derive per-port AGENT_ID values for
        # monbus packet tagging.
        for slave_idx, slave in enumerate(self.slaves):
            slave_adapter_src = self._generate_slave_adapter(slave, slave_idx)
            slave_adapter_path = os.path.join(output_dir, f"{slave.name}_adapter.sv")
            with open(slave_adapter_path, 'w') as f:
                f.write(slave_adapter_src)
            generated_files[f'slave_adapter_{slave.name}'] = slave_adapter_path

        # 4. Generate crossbar module
        xbar_src = self._generate_crossbar()
        xbar_path = os.path.join(output_dir, f"{self.bridge_name}_xbar.sv")
        with open(xbar_path, 'w') as f:
            f.write(xbar_src)
        generated_files['crossbar'] = xbar_path

        # 5. Generate main bridge module
        bridge_src = self._generate_main_bridge()
        bridge_path = os.path.join(output_dir, f"{self.bridge_name}.sv")
        with open(bridge_path, 'w') as f:
            f.write(bridge_src)
        generated_files['bridge'] = bridge_path

        return generated_files

    def _generate_package(self) -> str:
        """Generate SystemVerilog package with AXI channel structs."""
        # Collect unique ID width (use first master's)
        id_width = self.masters[0].id_width if self.masters else 4

        # Use single global address width parameter (32 bits for simplicity)
        # This prevents width mismatch issues across different ports
        addr_width = 32

        # Collect unique data widths from all masters and slaves
        # APB slave widths ARE needed for struct generation (master may connect via converter)
        data_widths = set()
        for master in self.masters:
            data_widths.add(master.data_width)
        for slave in self.slaves:
            data_widths.add(slave.data_width)

        # Generate package with address width and num_masters
        num_masters = len(self.masters)
        pkg_gen = PackageGenerator(self.bridge_name, id_width=id_width, addr_width=addr_width, num_masters=num_masters)
        for width in data_widths:
            pkg_gen.add_data_width(width)

        return pkg_gen.generate()

    def _generate_adapter(self, master: MasterConfig, master_idx: int) -> str:
        """
        Generate adapter module for a master port.

        Args:
            master: Master configuration
            master_idx: Index of this master (for BRIDGE_ID)

        Returns:
            SystemVerilog adapter module source
        """
        adapter_gen = AdapterGenerator(
            self.bridge_name,
            len(self.slaves),
            master,
            self.slaves,
            all_masters=self.masters,  # Pass full master list for LCD calculation
            enable_monitoring=self.enable_monitoring,
            master_index=master_idx  # Pass master index for BRIDGE_ID
        )
        return adapter_gen.generate()

    def _generate_slave_adapter(self, slave: SlaveInfo, slave_index: int = 0) -> str:
        """
        Generate slave adapter module for a slave port.

        Args:
            slave: Slave configuration
            slave_index: Index of this slave in self.slaves; used by the
                slave-side wrapper to derive its monbus AGENT_ID.

        Returns:
            SystemVerilog slave adapter module source
        """
        # Determine channels based on masters connecting to this slave
        connecting_masters = self._get_masters_connecting_to_slave(slave)
        has_write = any(m.channels in ["wr", "rw"] for m in connecting_masters)
        has_read = any(m.channels in ["rd", "rw"] for m in connecting_masters)

        # Determine channel type
        if has_write and has_read:
            channels = "rw"
        elif has_write:
            channels = "wr"
        elif has_read:
            channels = "rd"
        else:
            channels = "rw"  # Default

        # Compute crossbar internal width (max of all master widths)
        crossbar_data_width = max(m.data_width for m in self.masters) if self.masters else 32
        crossbar_id_width = max(m.id_width for m in self.masters) if self.masters else 4

        slave_adapter_gen = SlaveAdapterGenerator(
            bridge_name=self.bridge_name,
            slave_config=slave,
            channels=channels,
            id_width=crossbar_id_width,
            data_width=crossbar_data_width,
            enable_monitoring=self.enable_monitoring,
            slave_index=slave_index,
        )
        return slave_adapter_gen.generate()

    # ==================================================================
    # Monitor aggregation (use_monitor=true only)
    # ==================================================================

    def _collect_monitored_wrappers(self) -> List[MonitoredWrapper]:
        """Enumerate every per-port AXI4 _mon wrapper instance in the
        bridge, ordered master-side first then slave-side. Every slave
        adapter -- AXI4, AXIL, or APB -- contributes a wrapper: AXI4
        slaves wrap their axi4_master_*_mon timing isolation between
        xbar and external; AXIL/APB slaves insert axi4_master_*_mon on
        the bridge-internal AXI4 path upstream of their converter shim
        (the crossbar fabric is always AXI4, so the AXI4 monitor sees
        the same traffic regardless of the slave's external protocol).
        The order here defines the indexing of monbus_arbiter inputs at
        the bridge top."""
        wrappers: List[MonitoredWrapper] = []
        for m_idx, m in enumerate(self.masters):
            if m.channels in ('wr', 'rw'):
                wrappers.append(MonitoredWrapper(m.name, m_idx, 'master', 'wr'))
            if m.channels in ('rd', 'rw'):
                wrappers.append(MonitoredWrapper(m.name, m_idx, 'master', 'rd'))
        for s_idx, s in enumerate(self.slaves):
            connecting = self._get_masters_connecting_to_slave(s)
            has_write = any(m.channels in ('wr', 'rw') for m in connecting)
            has_read = any(m.channels in ('rd', 'rw') for m in connecting)
            if has_write:
                wrappers.append(MonitoredWrapper(s.name, s_idx, 'slave', 'wr'))
            if has_read:
                wrappers.append(MonitoredWrapper(s.name, s_idx, 'slave', 'rd'))
        return wrappers

    # The monbus_axil_group's own port-level cfg signals (NOT the
    # per-port wrapper cfg). Surfaced as `cfg_mon_group_<base>` at the
    # bridge top so the SoC integrator drives the post-arbiter filter
    # behaviour. Mirrors monbus_axil_group's port list in
    # rtl/amba/shared/monbus_axil_group.sv (unified location).
    _MON_GROUP_CFG = (
        # Address window for the AXIL master write region
        ('base_addr',           32),
        ('limit_addr',          32),
        # Per-protocol filter masks (AXI, AXIS, CORE)
        ('axi_pkt_mask',        16),
        ('axi_err_select',      16),
        ('axi_error_mask',      16),
        ('axi_timeout_mask',    16),
        ('axi_compl_mask',      16),
        ('axi_thresh_mask',     16),
        ('axi_perf_mask',       16),
        ('axi_addr_mask',       16),
        ('axi_debug_mask',      16),
        ('axis_pkt_mask',       16),
        ('axis_err_select',     16),
        ('axis_error_mask',     16),
        ('axis_timeout_mask',   16),
        ('axis_compl_mask',     16),
        ('axis_credit_mask',    16),
        ('axis_channel_mask',   16),
        ('axis_stream_mask',    16),
        ('core_pkt_mask',       16),
        ('core_err_select',     16),
        ('core_error_mask',     16),
        ('core_timeout_mask',   16),
        ('core_compl_mask',     16),
        ('core_thresh_mask',    16),
        ('core_perf_mask',      16),
        ('core_debug_mask',     16),
    )

    def _generate_monitor_top_ports(self, wrappers: List[MonitoredWrapper]) -> List[str]:
        """Per-wrapper cfg inputs + monbus_axil_group's AXIL slave,
        AXIL master, cfg_mon_group_*, and mon_irq_out ports. Caller has
        already ensured a trailing comma after the prior port group."""
        lines: List[str] = []

        # Per-wrapper cfg inputs (15 sigs each)
        lines.append("")
        lines.append("    // ============================================================")
        lines.append("    // Monitor per-port cfg inputs (use_monitor=true)")
        lines.append("    // ============================================================")
        for w in wrappers:
            lines.append(f"    // {w.side} {w.port_name} (idx {w.port_idx}, {w.channel})")
            for sig in Axi4TimingWrapper.MONITOR_CFG_SIGNALS:
                base = sig[len('cfg_'):]
                width = _MONITOR_CFG_WIDTHS[sig]
                width_decl = "       " if width == 1 else f"[{width-1}:0]"
                lines.append(f"    input  logic {width_decl} {w.cfg_signal(base)},")
            lines.append("")

        if self.internal_axil_group:
            # monbus_axil_group ports -- the post-arbiter consumer.
            lines.append("    // ============================================================")
            lines.append("    // monbus_axil_group access ports + config + IRQ")
            lines.append("    // ============================================================")
            # AXIL slave (config / IRQ status reads). 64-bit data: a CPU
            # drains one error packet (packet + source_ts) in 3 beats via
            # the unified monbus_axil_group's slice-counter read path.
            lines.append("    // AXIL slave (IRQ-status reads, 64-bit data)")
            lines.append("    input  logic        s_mon_axil_arvalid,")
            lines.append("    output logic        s_mon_axil_arready,")
            lines.append("    input  logic [31:0] s_mon_axil_araddr,")
            lines.append("    input  logic [2:0]  s_mon_axil_arprot,")
            lines.append("    output logic        s_mon_axil_rvalid,")
            lines.append("    input  logic        s_mon_axil_rready,")
            lines.append("    output logic [63:0] s_mon_axil_rdata,")
            lines.append("    output logic [1:0]  s_mon_axil_rresp,")
            lines.append("")
            # AXIL master (packet log writes). The monbus_axil_group module
            # exposes a 64-bit master (M_AXIL_DATA_WIDTH=64) so the captured
            # write records are wide enough for the 128-bit packet split
            # across two beats; bump wdata 32->64 and wstrb 4->8 to match.
            lines.append("    // AXIL master (packet log writes)")
            lines.append("    output logic        m_mon_axil_awvalid,")
            lines.append("    input  logic        m_mon_axil_awready,")
            lines.append("    output logic [31:0] m_mon_axil_awaddr,")
            lines.append("    output logic [2:0]  m_mon_axil_awprot,")
            lines.append("    output logic        m_mon_axil_wvalid,")
            lines.append("    input  logic        m_mon_axil_wready,")
            lines.append("    output logic [63:0] m_mon_axil_wdata,")
            lines.append("    output logic [7:0]  m_mon_axil_wstrb,")
            lines.append("    input  logic        m_mon_axil_bvalid,")
            lines.append("    output logic        m_mon_axil_bready,")
            lines.append("    input  logic [1:0]  m_mon_axil_bresp,")
            lines.append("")
            # monbus_axil_group cfg
            lines.append("    // monbus_axil_group cfg")
            for base, width in self._MON_GROUP_CFG:
                width_decl = "       " if width == 1 else f"[{width-1}:0]"
                lines.append(f"    input  logic {width_decl} cfg_mon_group_{base},")
            # IRQ output -- last port, no trailing comma.
            lines.append("    // IRQ (asserted while error FIFO non-empty)")
            lines.append("    output logic        mon_irq_out")
        else:
            # External-aggregator mode: bridge does per-port monitoring +
            # arbitration but expects the integrator's existing
            # monbus_axil_group to consume the merged stream. We surface
            # the aggregated monbus output plus a free-running monitor-
            # time input the external group must drive.
            lines.append("    // ============================================================")
            lines.append("    // Aggregated monbus output (consumed by external axil_group)")
            lines.append("    // ============================================================")
            lines.append("    // Free-running monitor-time INPUT -- drive from external")
            lines.append("    // monbus_axil_group's mon_time_out so every internal wrapper")
            lines.append("    // and the external group share one timebase.")
            lines.append("    input  monitor_common_pkg::monbus_timestamp_t i_mon_time,")
            lines.append("")
            lines.append("    // Post-arbiter aggregated stream (merge externally with other")
            lines.append("    // monbus sources, e.g. STREAM's monbus_axil_group input).")
            lines.append("    output logic                                  monbus_agg_valid,")
            lines.append("    input  logic                                  monbus_agg_ready,")
            lines.append("    output monitor_common_pkg::monitor_packet_t   monbus_agg_packet,")
            lines.append("    // Last port -- no trailing comma.")
            lines.append("    output monitor_common_pkg::monbus_timestamp_t monbus_agg_timestamp")
        return lines

    def _generate_monitor_internal_signals(self, wrappers: List[MonitoredWrapper]) -> List[str]:
        """Per-wrapper monbus internal wires + the arbiter's output
        net. Each wrapper's adapter output feeds a unique 4-wire stream
        named monbus_<port>_<idx>_<chan>_{valid,ready,packet,timestamp}.

        Packet uses monitor_common_pkg::monitor_packet_t (128-bit typedef).
        Timestamp is monitor_common_pkg::monbus_timestamp_t (64-bit), a
        side-band that travels alongside the packet.

        A single shared `mon_time_w` net is also declared here -- the
        monbus_axil_group drives it (mon_time_out) and every wrapper
        consumes it through its i_mon_time input."""
        lines: List[str] = []
        lines.append("    // ============================================================")
        lines.append("    // Per-wrapper monbus streams (adapter -> arbiter input)")
        lines.append("    // ============================================================")
        # Shared timestamp net: monbus_axil_group's mon_time_out feeds
        # every wrapper's i_mon_time input.
        lines.append("    // Shared free-running timestamp from monbus_axil_group")
        lines.append("    monitor_common_pkg::monbus_timestamp_t mon_time_w;")
        lines.append("")
        for w in wrappers:
            lines.append(f"    logic                                  {w.monbus_valid};")
            lines.append(f"    logic                                  {w.monbus_ready};")
            lines.append(f"    monitor_common_pkg::monitor_packet_t   {w.monbus_packet};")
            lines.append(f"    monitor_common_pkg::monbus_timestamp_t {w.monbus_timestamp};")
        lines.append("")
        lines.append("    // Arbiter output (-> monbus_axil_group input)")
        lines.append("    logic                                  mon_arb_monbus_valid;")
        lines.append("    logic                                  mon_arb_monbus_ready;")
        lines.append("    monitor_common_pkg::monitor_packet_t   mon_arb_monbus_packet;")
        lines.append("    monitor_common_pkg::monbus_timestamp_t mon_arb_monbus_timestamp;")
        lines.append("")
        return lines

    def _generate_master_monitor_connections(self, wrappers: List[MonitoredWrapper]) -> List[str]:
        """Adapter-instantiation port connections for this master's
        monbus + cfg ports. The adapter exposes channel-suffixed names
        (monbus_wr_valid, cfg_rd_axi_pkt_mask, ...) and the bridge top
        binds them to {port}_{idx}_{chan}-prefixed nets.

        The shared `i_mon_time` net is bound once (not per channel) since
        the underlying wrappers share the same free-running counter from
        monbus_axil_group's mon_time_out. The per-wrapper
        `monbus_timestamp` side-band is paired with the matching packet
        wire so the arbiter can keep timestamps aligned with packets."""
        lines: List[str] = []
        # Sort so wr comes before rd (matches port-list order)
        ordered = sorted(wrappers, key=lambda w: 0 if w.channel == 'wr' else 1)
        all_pairs: List[tuple] = []  # (adapter_port, bridge_connector)
        # Single shared monitor-time input on the adapter -- bind once.
        all_pairs.append(('i_mon_time', 'mon_time_w'))
        for w in ordered:
            all_pairs.append((f'monbus_{w.channel}_valid',     w.monbus_valid))
            all_pairs.append((f'monbus_{w.channel}_ready',     w.monbus_ready))
            all_pairs.append((f'monbus_{w.channel}_packet',    w.monbus_packet))
            all_pairs.append((f'monbus_{w.channel}_timestamp', w.monbus_timestamp))
            for sig in Axi4TimingWrapper.MONITOR_CFG_SIGNALS:
                base = sig[len('cfg_'):]
                adapter_port = f'cfg_{w.channel}_{base}'
                all_pairs.append((adapter_port, w.cfg_signal(base)))
        last_idx = len(all_pairs) - 1
        for i, (port, conn) in enumerate(all_pairs):
            sep = '' if i == last_idx else ','
            lines.append(f"        .{port}({conn}){sep}")
        return lines

    def _generate_monitor_aggregator(self, wrappers: List[MonitoredWrapper]) -> List[str]:
        """Instantiate monbus_arbiter (always) and monbus_axil_group
        (only when internal_axil_group=True). With internal_axil_group=
        False the arbiter's aggregated output is surfaced at the bridge
        top via monbus_agg_* so the integrator can merge with an
        existing external axil_group."""
        lines: List[str] = []
        n = len(wrappers)
        lines.append("    // ============================================================")
        if self.internal_axil_group:
            lines.append(f"    // Monitor aggregator -- {n} client(s) -> arbiter -> axil_group")
        else:
            lines.append(f"    // Monitor aggregator -- {n} client(s) -> arbiter -> top-level monbus_agg_*")
            lines.append("    // (axil_group lives outside the bridge; integrator merges this stream)")
        lines.append("    // ============================================================")
        # monbus_arbiter: unpacked-array inputs across CLIENTS
        lines.append("    logic                                  mon_arb_monbus_valid_in     [{}];".format(n))
        lines.append("    logic                                  mon_arb_monbus_ready_in     [{}];".format(n))
        lines.append("    monitor_common_pkg::monitor_packet_t   mon_arb_monbus_packet_in    [{}];".format(n))
        lines.append("    monitor_common_pkg::monbus_timestamp_t mon_arb_monbus_timestamp_in [{}];".format(n))
        for i, w in enumerate(wrappers):
            lines.append(f"    assign mon_arb_monbus_valid_in[{i}]     = {w.monbus_valid};")
            lines.append(f"    assign {w.monbus_ready} = mon_arb_monbus_ready_in[{i}];")
            lines.append(f"    assign mon_arb_monbus_packet_in[{i}]    = {w.monbus_packet};")
            lines.append(f"    assign mon_arb_monbus_timestamp_in[{i}] = {w.monbus_timestamp};")
        lines.append("")
        lines.append("    monbus_arbiter #(")
        lines.append(f"        .CLIENTS            ({n}),")
        lines.append("        .INPUT_SKID_ENABLE  (1),")
        lines.append("        .OUTPUT_SKID_ENABLE (1),")
        lines.append("        .INPUT_SKID_DEPTH   (2),")
        lines.append("        .OUTPUT_SKID_DEPTH  (2)")
        lines.append("    ) u_mon_arbiter (")
        lines.append("        .axi_aclk            (aclk),")
        lines.append("        .axi_aresetn         (aresetn),")
        lines.append("        .block_arb           (1'b0),")
        lines.append("        .monbus_valid_in     (mon_arb_monbus_valid_in),")
        lines.append("        .monbus_ready_in     (mon_arb_monbus_ready_in),")
        lines.append("        .monbus_packet_in    (mon_arb_monbus_packet_in),")
        lines.append("        .monbus_timestamp_in (mon_arb_monbus_timestamp_in),")
        lines.append("        .monbus_valid        (mon_arb_monbus_valid),")
        lines.append("        .monbus_ready        (mon_arb_monbus_ready),")
        lines.append("        .monbus_packet       (mon_arb_monbus_packet),")
        lines.append("        .monbus_timestamp    (mon_arb_monbus_timestamp),")
        lines.append("        /* verilator lint_off PINCONNECTEMPTY */")
        lines.append("        .grant_valid         (),")
        lines.append("        .grant               (),")
        lines.append("        .grant_id            (),")
        lines.append("        .last_grant          ()")
        lines.append("        /* verilator lint_on PINCONNECTEMPTY */")
        lines.append("    );")
        lines.append("")
        if self.internal_axil_group:
            lines.append("    monbus_axil_group #(")
            lines.append("        .FIFO_DEPTH_ERR    (64),")
            lines.append("        .FIFO_DEPTH_WRITE  (32),")
            lines.append("        .ADDR_WIDTH        (32),")
            lines.append("        .S_AXIL_DATA_WIDTH (64),")
            lines.append("        // S_AXIL_DATA_WIDTH=64: the unified group drains one")
            lines.append("        // err_fifo entry ({packet[127:0], source_ts[63:0]} = 192 bits)")
            lines.append("        // over three 64-bit reads via an internal slice counter.")
            lines.append("        // M_AXIL_DATA_WIDTH defaults to 64 — module emits the same")
            lines.append("        // 24-byte record on the bulk-trace write path: three 64-bit")
            lines.append("        // beats {packet[63:0], packet[127:64], source_ts[63:0]}.")
            lines.append("        .NUM_PROTOCOLS     (3)")
            lines.append("    ) u_mon_axil_group (")
            lines.append("        .axi_aclk          (aclk),")
            lines.append("        .axi_aresetn       (aresetn),")
            lines.append("        // Arbiter output as the single monbus input + side-band timestamp")
            lines.append("        .monbus_valid      (mon_arb_monbus_valid),")
            lines.append("        .monbus_ready      (mon_arb_monbus_ready),")
            lines.append("        .monbus_packet     (mon_arb_monbus_packet),")
            lines.append("        .monbus_timestamp  (mon_arb_monbus_timestamp),")
            lines.append("        // Free-running timestamp shared with every wrapper's i_mon_time")
            lines.append("        .mon_time_out      (mon_time_w),")
            lines.append("        // AXIL slave")
            for s in ('arvalid','arready','araddr','arprot','rvalid','rready','rdata','rresp'):
                lines.append(f"        .s_axil_{s}      (s_mon_axil_{s}),")
            lines.append("        // AXIL master")
            for s in ('awvalid','awready','awaddr','awprot','wvalid','wready','wdata','wstrb','bvalid','bready','bresp'):
                lines.append(f"        .m_axil_{s}      (m_mon_axil_{s}),")
            lines.append("        // IRQ")
            lines.append("        .irq_out           (mon_irq_out),")
            lines.append("        // Group-level cfg")
            for base, _width in self._MON_GROUP_CFG:
                lines.append(f"        .cfg_{base}     (cfg_mon_group_{base}),")
            lines.append("        /* verilator lint_off PINCONNECTEMPTY */")
            lines.append("        .err_fifo_full     (),")
            lines.append("        .write_fifo_full   (),")
            lines.append("        .err_fifo_count    (),")
            lines.append("        .write_fifo_count  ()")
            lines.append("        /* verilator lint_on PINCONNECTEMPTY */")
            lines.append("    );")
            lines.append("")
        else:
            # No internal monbus_axil_group: surface the arbiter's
            # aggregated stream + shared timestamp net to the bridge top.
            lines.append("    // Surface the arbiter's aggregated monbus stream at the bridge top.")
            lines.append("    // i_mon_time is an INPUT here (driven by external monbus_axil_group.mon_time_out)")
            lines.append("    // and is also assigned to the shared mon_time_w net that every wrapper")
            lines.append("    // consumes via its i_mon_time input.")
            lines.append("    assign mon_time_w           = i_mon_time;")
            lines.append("    assign monbus_agg_valid     = mon_arb_monbus_valid;")
            lines.append("    assign mon_arb_monbus_ready = monbus_agg_ready;")
            lines.append("    assign monbus_agg_packet    = mon_arb_monbus_packet;")
            lines.append("    assign monbus_agg_timestamp = mon_arb_monbus_timestamp;")
            lines.append("")
        return lines

    def _generate_crossbar(self) -> str:
        """
        Generate crossbar module that routes adapter outputs to slaves.

        The crossbar handles ALL slaves (AXI4 and APB). For APB slaves, it generates
        AXI4 outputs that connect to the APB protocol converter adapter.

        Returns:
            SystemVerilog crossbar module source
        """
        xbar_gen = CrossbarGenerator(self.bridge_name, self.masters, self.slaves)
        return xbar_gen.generate()

    def _generate_main_bridge(self) -> str:
        """
        Generate main bridge module that instantiates adapters and crossbar.

        Returns:
            SystemVerilog main bridge module source
        """
        lines = []

        # Header
        lines.extend(self._generate_header())

        # Module declaration
        lines.extend(self._generate_module_declaration())

        # Internal signals (adapter outputs)
        lines.extend(self._generate_internal_signals())

        # Monitor side-band internal nets (use_monitor=true only).
        monitored: List[MonitoredWrapper] = []
        if self.enable_monitoring:
            monitored = self._collect_monitored_wrappers()
            if monitored:
                lines.extend(self._generate_monitor_internal_signals(monitored))

        # Adapter instantiations
        lines.extend(self._generate_adapter_instantiations(monitored))

        # Crossbar routing
        lines.extend(self._generate_crossbar_routing())

        # Slave adapter instantiations for ALL slaves. The adapter
        # module per-protocol wraps the timing isolator or protocol
        # converter AND the bridge_id-tracking FIFO -- the bridge top
        # used to direct-instantiate axi4_to_apb_shim here, which left
        # rid_*/bid_* undriven and broke APB responses end-to-end.
        lines.extend(self._generate_slave_adapter_instantiations(monitored))

        # Monitor aggregator (monbus_arbiter + monbus_axil_group).
        if self.enable_monitoring and monitored:
            lines.extend(self._generate_monitor_aggregator(monitored))

        # Module end
        lines.append(f"endmodule : {self.bridge_name}")
        lines.append("")

        return "\n".join(lines)

    def _generate_header(self) -> List[str]:
        """Generate file header."""
        return [
            f"// Bridge: {self.bridge_name}",
            "// Generated by: BridgeModuleGenerator",
            "// ",
            "// Architecture:",
            "//   Master → Master Adapter → Crossbar → Slave Adapter → Slave",
            "//",
            "//   Master Adapter contains:",
            "//   - Timing wrapper (axi4_slave_wr/rd)",
            "//   - Address decode",
            "//   - Width adaptation",
            "//",
            "//   Slave Adapter contains:",
            "//   - Timing wrapper (axi4_master_wr/rd) or Protocol converter (axi4_to_apb/axil)",
            "",
            "`timescale 1ns / 1ps",
            "",
            f"import {self.bridge_name}_pkg::*;",
            ""
        ]

    def _generate_module_declaration(self) -> List[str]:
        """Generate module declaration with all ports.

        For monitored bridges, exposes a parameter block on the top:
        - Per-wrapper USE_MONITOR_<port>_<wr|rd> with TOML defaults
        - Global USE_ALL_MONITORS, USE_NO_MONITORS (both default 1'b0)

        The integrator (harness) overrides any of these at instantiation
        to flip monitor enables without regenerating the bridge. Effective
        per-wrapper values are computed via localparam EFF_USE_MON_*
        right after the port list and passed down to adapter instances."""
        lines = []

        # Collect wrappers up-front so we know whether to emit a
        # parameter block before the port list.
        mon_wrappers = (self._collect_monitored_wrappers()
                        if self.enable_monitoring else [])

        if mon_wrappers:
            lines.append(f"module {self.bridge_name} #(")
            param_lines: List[str] = []
            param_lines.append("    // Per-wrapper USE_MONITOR knobs (TOML defaults; override at instantiation)")
            for w in mon_wrappers:
                if w.side == 'master':
                    default_bit = self.masters[w.port_idx].use_monitor
                else:
                    default_bit = self.slaves[w.port_idx].use_monitor
                default_lit = "1'b1" if default_bit else "1'b0"
                pname = f"USE_MONITOR_{w.port_name}_{w.channel}"
                param_lines.append(f"    parameter bit {pname} = {default_lit}")
            param_lines.append("    // Global overrides (mutually exclusive; both 0 = use per-port)")
            use_all_lit = "1'b1" if self.use_all_monitors else "1'b0"
            use_no_lit  = "1'b1" if self.use_no_monitors  else "1'b0"
            param_lines.append(f"   ,parameter bit USE_ALL_MONITORS = {use_all_lit}")
            param_lines.append(f"   ,parameter bit USE_NO_MONITORS  = {use_no_lit}")
            # Join with commas (the parameter-block doesn't use a
            # trailing comma; we already use leading commas on the
            # globals). Add commas between consecutive parameters.
            for i in range(1, len(param_lines)):
                stripped = param_lines[i].lstrip()
                if not stripped.startswith(("//", ",")):
                    # This is a parameter line; previous emitted line
                    # needs a trailing comma if it was also a parameter.
                    prev = param_lines[i - 1].rstrip()
                    if (not prev.lstrip().startswith("//")
                            and not prev.endswith(",")
                            and not prev.endswith("(")):
                        param_lines[i - 1] = prev + ","
            lines.extend(param_lines)
            lines.append(") (")
        else:
            lines.append(f"module {self.bridge_name} (")

        lines.append("    input  logic aclk,")
        lines.append("    input  logic aresetn,")
        lines.append("")

        # Master ports
        for i, master in enumerate(self.masters):
            lines.append(f"    // Master {i}: {master.name} ({master.channels})")
            master_ports = self._generate_master_ports(master)
            # Add comma if there are more masters or any slaves
            if i < len(self.masters) - 1 or len(self.slaves) > 0:
                master_ports[-1] = master_ports[-1] + ","
            lines.extend(master_ports)
            lines.append("")

        # Slave ports
        for i, slave in enumerate(self.slaves):
            lines.append(f"    // Slave {i}: {slave.name}")
            slave_ports = self._generate_slave_ports(slave)
            # Add comma if there are more slaves
            if i < len(self.slaves) - 1:
                slave_ports[-1] = slave_ports[-1] + ","
            lines.extend(slave_ports)
            if i < len(self.slaves) - 1:
                lines.append("")

        # Monitor side-band top ports (use_monitor=true only)
        if self.enable_monitoring:
            wrappers = self._collect_monitored_wrappers()
            if wrappers:
                _ensure_trailing_comma(lines)
                lines.extend(self._generate_monitor_top_ports(wrappers))

        lines.append(");")
        lines.append("")

        # Localparams
        lines.append(f"    localparam NUM_SLAVES = {len(self.slaves)};")
        lines.append("")

        # Effective per-wrapper USE_MONITOR after applying the global
        # USE_ALL_MONITORS / USE_NO_MONITORS overrides. These localparams
        # are referenced when instantiating each adapter so a single
        # bridge can be reconfigured at integration time -- no regen.
        if mon_wrappers:
            lines.append("    // ============================================================")
            lines.append("    // Effective per-wrapper USE_MONITOR (after global override)")
            lines.append("    // ============================================================")
            for w in mon_wrappers:
                src_param = f"USE_MONITOR_{w.port_name}_{w.channel}"
                eff_param = f"EFF_USE_MON_{w.port_name}_{w.channel}"
                lines.append(
                    f"    localparam bit {eff_param} = "
                    f"USE_NO_MONITORS  ? 1'b0 : "
                    f"USE_ALL_MONITORS ? 1'b1 : "
                    f"{src_param};"
                )
            lines.append("")

        return lines

    def _generate_master_ports(self, master: MasterConfig) -> List[str]:
        """
        Generate master port declarations using SignalNaming.

        IMPORTANT: Bridge top-level is an intermediary that receives signals from
        external master. Port directions are INVERTED from the master's perspective:
        - Request signals (awid, awaddr, etc.): INPUT to bridge (from external master)
        - Response signals (awready, bid, etc.): OUTPUT from bridge (to external master)

        Protocol branching: an 'axil' master exposes ONLY the AXIL signal
        set on the bridge top (addr/prot/data/strb/resp/valid/ready). The
        internal crossbar is still AXI4; the master's adapter does the
        AXIL->AXI4 promotion. Without this branch, the bridge top forced
        every master into the full AXI4 signal set even when the .toml
        declared the master as axil — making the SoC integrator dummy out
        a dozen unused signals per AXIL master.
        """
        lines = []

        # Width parameters for signal info queries
        width_values = {
            'ID_WIDTH': master.id_width,
            'ADDR_WIDTH': 32,  # Global address width
            'DATA_WIDTH': master.data_width,
            'STRB_WIDTH': master.data_width // 8,
            'USER_WIDTH': 1
        }

        lines.append(f"    // Master: {master.name} ({master.protocol}, {master.channels})")

        if master.protocol == 'axil':
            # AXIL master — emit only AXIL signals (no id/len/burst/cache/
            # qos/region/user/last). Mirror of the AXIL slave port handling
            # in _generate_slave_ports.
            addr_w = master.addr_width
            data_w = master.data_width
            strb_w = data_w // 8
            pfx    = master.prefix
            has_write = master.channels in ('wr', 'rw')
            has_read  = master.channels in ('rd', 'rw')

            if has_write:
                lines.append(f"    input  logic [{addr_w-1}:0] {pfx}awaddr,")
                lines.append(f"    input  logic [2:0]            {pfx}awprot,")
                lines.append(f"    input  logic                  {pfx}awvalid,")
                lines.append(f"    output logic                  {pfx}awready,")
                lines.append(f"    input  logic [{data_w-1}:0] {pfx}wdata,")
                lines.append(f"    input  logic [{strb_w-1}:0] {pfx}wstrb,")
                lines.append(f"    input  logic                  {pfx}wvalid,")
                lines.append(f"    output logic                  {pfx}wready,")
                lines.append(f"    output logic [1:0]            {pfx}bresp,")
                lines.append(f"    output logic                  {pfx}bvalid,")
                lines.append(f"    input  logic                  {pfx}bready,")
            if has_read:
                lines.append(f"    input  logic [{addr_w-1}:0] {pfx}araddr,")
                lines.append(f"    input  logic [2:0]            {pfx}arprot,")
                lines.append(f"    input  logic                  {pfx}arvalid,")
                lines.append(f"    output logic                  {pfx}arready,")
                lines.append(f"    output logic [{data_w-1}:0] {pfx}rdata,")
                lines.append(f"    output logic [1:0]            {pfx}rresp,")
                lines.append(f"    output logic                  {pfx}rvalid,")
                lines.append(f"    input  logic                  {pfx}rready,")

            # Trim trailing comma; caller re-appends if needed.
            if lines and lines[-1].endswith(','):
                lines[-1] = lines[-1][:-1]
            return lines

        # Determine which channels to generate based on master type
        channels = SignalNaming.channels_from_type(master.channels)

        # Get all AXI4 signals from SignalNaming. Pass `prefix` so the
        # bridge's external master ports honour the .toml's prefix setting
        # (e.g. prefix="host_" -> host_awvalid). Without this they'd be
        # forced to `<name>_axi_*` — Bug C in TASK-011.
        all_signals = SignalNaming.get_all_axi4_signals(
            port_name=master.name,
            direction=Direction.MASTER,
            channels=channels,
            prefix=master.prefix
        )

        # Generate declarations for each channel with INVERTED directions
        first_channel = True
        for channel, channel_signals in all_signals.items():
            if not first_channel:
                lines.append("")
            first_channel = False

            for sig_name, sig_info in channel_signals:
                # Invert port direction (bridge is intermediary, not the actual master)
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

        # Remove trailing comma from last signal
        if lines and lines[-1].endswith(','):
            lines[-1] = lines[-1][:-1]

        return lines

    def _generate_slave_ports(self, slave: SlaveInfo) -> List[str]:
        """Generate slave port declarations (AXI4 or APB based on protocol).

        The AXI4 transaction ID (*_awid/*_bid/*_arid/*_rid) is a pass-through
        from the master, so the slave-side port ID width must equal the
        master's id_width. Hardcoding it to 4 (the previous behaviour) breaks
        for any master with id_width != 4 — see Bug B in TASK-011.
        """
        lines = []

        # Master id_width drives the slave-port ID width (pass-through).
        # Floor at 1 to avoid `[-1:0]` when id_width=0 (Bug A).
        master_id_width = max(m.id_width for m in self.masters) if self.masters else 4
        master_id_width = max(master_id_width, 1)

        # Width parameters for signal info queries
        width_values = {
            'ID_WIDTH': master_id_width,
            'ADDR_WIDTH': 32,  # Global address width
            'DATA_WIDTH': slave.data_width,
            'STRB_WIDTH': slave.data_width // 8,
            'USER_WIDTH': 1
        }

        # Check protocol and generate appropriate ports
        if slave.protocol == 'apb':
            # APB slave ports - use SignalNaming for consistency
            lines.append(f"    // APB Slave: {slave.name}")

            # Get all APB signals from SignalNaming
            # Pass prefix so bridge's APB slave ports honour the .toml
            # prefix (Bug C in TASK-011).
            apb_signals = SignalNaming.get_all_apb_signals(
                slave.name, Direction.MASTER, prefix=slave.prefix
            )

            for sig_name, sig_info in apb_signals:
                # Get complete signal declaration
                declaration = sig_info.get_declaration(sig_name, width_values)
                lines.append(f"    {declaration},")

            # Remove trailing comma from last signal
            if lines and lines[-1].endswith(','):
                lines[-1] = lines[-1][:-1]

        elif slave.protocol == 'axil':
            # AXI4-Lite slave ports. The crossbar carries full AXI4 across
            # the fabric, and the per-slave adapter shims AXI4 → AXIL at
            # the slave boundary (see SlaveAdapterGenerator
            # ._generate_axil_external_ports). So the bridge top must
            # expose only AXIL signals here — no id/len/burst/etc.
            lines.append(f"    // AXI4-Lite Slave: {slave.name}")

            connecting_masters = self._get_masters_connecting_to_slave(slave)
            has_write = any(m.channels in ["wr", "rw"] for m in connecting_masters)
            has_read = any(m.channels in ["rd", "rw"] for m in connecting_masters)

            addr_w = slave.addr_width
            data_w = slave.data_width
            strb_w = data_w // 8
            pfx = slave.prefix

            if has_write:
                lines.append(f"    output logic [{addr_w-1}:0] {pfx}awaddr,")
                lines.append(f"    output logic [2:0]            {pfx}awprot,")
                lines.append(f"    output logic                  {pfx}awvalid,")
                lines.append(f"    input  logic                  {pfx}awready,")
                lines.append(f"    output logic [{data_w-1}:0] {pfx}wdata,")
                lines.append(f"    output logic [{strb_w-1}:0] {pfx}wstrb,")
                lines.append(f"    output logic                  {pfx}wvalid,")
                lines.append(f"    input  logic                  {pfx}wready,")
                lines.append(f"    input  logic [1:0]            {pfx}bresp,")
                lines.append(f"    input  logic                  {pfx}bvalid,")
                lines.append(f"    output logic                  {pfx}bready,")
            if has_read:
                lines.append(f"    output logic [{addr_w-1}:0] {pfx}araddr,")
                lines.append(f"    output logic [2:0]            {pfx}arprot,")
                lines.append(f"    output logic                  {pfx}arvalid,")
                lines.append(f"    input  logic                  {pfx}arready,")
                lines.append(f"    input  logic [{data_w-1}:0] {pfx}rdata,")
                lines.append(f"    input  logic [1:0]            {pfx}rresp,")
                lines.append(f"    input  logic                  {pfx}rvalid,")
                lines.append(f"    output logic                  {pfx}rready,")

            # Drop trailing comma so the caller can splice the slave
            # ports between other port blocks.
            if lines and lines[-1].endswith(','):
                lines[-1] = lines[-1][:-1]

        else:
            # AXI4 slave ports - use SignalNaming for complete signal information
            lines.append(f"    // AXI4 Slave: {slave.name}")

            # Determine required channels based on masters connecting to this slave
            connecting_masters = self._get_masters_connecting_to_slave(slave)
            has_write = any(m.channels in ["wr", "rw"] for m in connecting_masters)
            has_read = any(m.channels in ["rd", "rw"] for m in connecting_masters)

            channels = []
            if has_write:
                channels.extend([AXI4Channel.AW, AXI4Channel.W, AXI4Channel.B])
            if has_read:
                channels.extend([AXI4Channel.AR, AXI4Channel.R])

            # Get all AXI4 signals from SignalNaming
            # Bridge acts as master to external slaves (same perspective as crossbar).
            # Pass prefix so the bridge's external slave ports honour the
            # .toml prefix setting — Bug C in TASK-011.
            all_signals = SignalNaming.get_all_axi4_signals(
                port_name=slave.name,
                direction=Direction.MASTER,
                channels=channels,
                prefix=slave.prefix
            )

            # Generate declarations for each channel
            first_channel = True
            for channel, channel_signals in all_signals.items():
                if not first_channel:
                    lines.append("")
                first_channel = False

                for sig_name, sig_info in channel_signals:
                    # Get complete signal declaration
                    declaration = sig_info.get_declaration(sig_name, width_values)
                    lines.append(f"    {declaration},")

            # Remove trailing comma from last signal
            if lines and lines[-1].endswith(','):
                lines[-1] = lines[-1][:-1]

        return lines

    def _generate_internal_signals(self) -> List[str]:
        """
        Generate internal signal declarations (adapter outputs).

        For each master, declares signals for ALL unique slave widths it connects to.
        """
        lines = []

        for master in self.masters:
            lines.append(f"    // {master.name} Adapter outputs")

            # Get unique slave widths this master connects to
            slave_widths = self._get_connected_slave_widths(master)

            # Address decode signals (one set per master)
            if master.channels in ["wr", "rw"]:
                lines.append(f"    logic [NUM_SLAVES-1:0] {master.name}_slave_select_aw;")
                lines.append(f"    logic [BRIDGE_ID_WIDTH-1:0] {master.name}_bridge_id_aw;")
            if master.channels in ["rd", "rw"]:
                lines.append(f"    logic [NUM_SLAVES-1:0] {master.name}_slave_select_ar;")
                lines.append(f"    logic [BRIDGE_ID_WIDTH-1:0] {master.name}_bridge_id_ar;")

            # Width-specific signals for each unique width
            for width in slave_widths:
                suffix = f"{width}b"
                lines.append(f"    // {width}b path")

                # Write channels
                if master.channels in ["wr", "rw"]:
                    lines.append(f"    axi4_aw_t     {master.name}_{suffix}_aw;")
                    lines.append(f"    logic         {master.name}_{suffix}_awvalid;")
                    lines.append(f"    logic         {master.name}_{suffix}_awready;")
                    lines.append(f"    axi4_w_{suffix}_t  {master.name}_{suffix}_w;")
                    lines.append(f"    logic         {master.name}_{suffix}_wvalid;")
                    lines.append(f"    logic         {master.name}_{suffix}_wready;")
                    lines.append(f"    axi4_b_t      {master.name}_{suffix}_b;")
                    lines.append(f"    logic         {master.name}_{suffix}_bvalid;")
                    lines.append(f"    logic         {master.name}_{suffix}_bready;")

                # Read channels
                if master.channels in ["rd", "rw"]:
                    lines.append(f"    axi4_ar_t     {master.name}_{suffix}_ar;")
                    lines.append(f"    logic         {master.name}_{suffix}_arvalid;")
                    lines.append(f"    logic         {master.name}_{suffix}_arready;")
                    lines.append(f"    axi4_r_{suffix}_t  {master.name}_{suffix}_r;")
                    lines.append(f"    logic         {master.name}_{suffix}_rvalid;")
                    lines.append(f"    logic         {master.name}_{suffix}_rready;")

            lines.append("")

        # Add crossbar-to-slave AXI4 signals for ALL slaves
        # These are internal wires connecting crossbar slave outputs to slave adapters.
        # The AXI4 *id signals (awid/bid/arid/rid) carry the master's transaction ID
        # pass-through, so they need to be sized at the master's id_width — NOT
        # hardcoded to 4 bits, which only happens to work when master.id_width == 4.
        # Bug B in TASK-011 (projects/components/bridge/TASKS.md).
        # Floor at 1 so id_width=0 (AXIL's "no ID" case) emits a degenerate
        # 1-bit signal rather than an invalid `[-1:0]` SV range — Bug A.
        crossbar_id_width = max(m.id_width for m in self.masters) if self.masters else 4
        crossbar_id_width = max(crossbar_id_width, 1)
        lines.append("    // Crossbar-to-Slave Internal AXI4 Signals")
        for slave in self.slaves:
            prefix = f"xbar_{slave.name}_axi_"

            # Determine which channels based on connecting masters
            connecting_masters = self._get_masters_connecting_to_slave(slave)
            has_write = any(m.channels in ["wr", "rw"] for m in connecting_masters)
            has_read = any(m.channels in ["rd", "rw"] for m in connecting_masters)

            # Determine AXI4 data width
            # All slaves (both AXI4 and APB) use their native data width at crossbar interface
            # Width adaptation happens in master adapter, not at crossbar
            # This allows multiple slaves of same width to share the same width-specific bus
            axi_data_width = slave.data_width

            axi_strb_width = axi_data_width // 8
            lines.append(f"    // {slave.name} ({slave.protocol.upper()}, {axi_data_width}b AXI4 interface)")

            # Width of the AXI4 transaction-ID signals (awid/bid/arid/rid).
            # These carry the master's per-txn tag pass-through, so they MUST
            # match the master's id_width. The cache/qos/region literals stay
            # at [3:0] (those AXI4 fields are spec-fixed at 4 bits).
            id_w = crossbar_id_width

            # Write channels
            if has_write:
                lines.append(f"    logic [{id_w-1}:0]            {prefix}awid;")
                lines.append(f"    logic [31:0]               {prefix}awaddr;")
                lines.append(f"    logic [7:0]                {prefix}awlen;")
                lines.append(f"    logic [2:0]                {prefix}awsize;")
                lines.append(f"    logic [1:0]                {prefix}awburst;")
                lines.append(f"    logic                      {prefix}awlock;")
                lines.append(f"    logic [3:0]                {prefix}awcache;")
                lines.append(f"    logic [2:0]                {prefix}awprot;")
                lines.append(f"    logic [3:0]                {prefix}awqos;")
                lines.append(f"    logic [3:0]                {prefix}awregion;")
                lines.append(f"    logic                      {prefix}awuser;")
                lines.append(f"    logic                      {prefix}awvalid;")
                lines.append(f"    logic                      {prefix}awready;")
                lines.append(f"    logic [{axi_data_width-1}:0] {prefix}wdata;")
                lines.append(f"    logic [{axi_strb_width-1}:0] {prefix}wstrb;")
                lines.append(f"    logic                      {prefix}wlast;")
                lines.append(f"    logic                      {prefix}wuser;")
                lines.append(f"    logic                      {prefix}wvalid;")
                lines.append(f"    logic                      {prefix}wready;")
                lines.append(f"    logic [{id_w-1}:0]            {prefix}bid;")
                lines.append(f"    logic [1:0]                {prefix}bresp;")
                lines.append(f"    logic                      {prefix}buser;")
                lines.append(f"    logic                      {prefix}bvalid;")
                lines.append(f"    logic                      {prefix}bready;")

            # Read channels
            if has_read:
                lines.append(f"    logic [{id_w-1}:0]            {prefix}arid;")
                lines.append(f"    logic [31:0]               {prefix}araddr;")
                lines.append(f"    logic [7:0]                {prefix}arlen;")
                lines.append(f"    logic [2:0]                {prefix}arsize;")
                lines.append(f"    logic [1:0]                {prefix}arburst;")
                lines.append(f"    logic                      {prefix}arlock;")
                lines.append(f"    logic [3:0]                {prefix}arcache;")
                lines.append(f"    logic [2:0]                {prefix}arprot;")
                lines.append(f"    logic [3:0]                {prefix}arqos;")
                lines.append(f"    logic [3:0]                {prefix}arregion;")
                lines.append(f"    logic                      {prefix}aruser;")
                lines.append(f"    logic                      {prefix}arvalid;")
                lines.append(f"    logic                      {prefix}arready;")
                lines.append(f"    logic [{id_w-1}:0]            {prefix}rid;")
                lines.append(f"    logic [{axi_data_width-1}:0] {prefix}rdata;")
                lines.append(f"    logic [1:0]                {prefix}rresp;")
                lines.append(f"    logic                      {prefix}rlast;")
                lines.append(f"    logic                      {prefix}ruser;")
                lines.append(f"    logic                      {prefix}rvalid;")
                lines.append(f"    logic                      {prefix}rready;")

            # Bridge ID tracking signals (for slave adapters)
            # All slave adapters have bridge_id tracking (AXI4 interface on crossbar side)
            if True:  # All slaves with adapters need bridge_id signals
                if has_write:
                    lines.append(f"    logic [BRIDGE_ID_WIDTH-1:0] {slave.name}_axi_bridge_id_aw;")
                    lines.append(f"    logic [BRIDGE_ID_WIDTH-1:0] {slave.name}_axi_bid_bridge_id;")
                    lines.append(f"    logic                       {slave.name}_axi_bid_valid;")
                if has_read:
                    lines.append(f"    logic [BRIDGE_ID_WIDTH-1:0] {slave.name}_axi_bridge_id_ar;")
                    lines.append(f"    logic [BRIDGE_ID_WIDTH-1:0] {slave.name}_axi_rid_bridge_id;")
                    lines.append(f"    logic                       {slave.name}_axi_rid_valid;")

            lines.append("")

        # Note: Old APB and AXI4 slave signal declaration code removed.
        # All slave signals now declared by unified code above (lines 492-573).

        return lines

    def _calculate_lcd_width_for_apb(self, master: MasterConfig) -> int:
        """
        Calculate LCD (Lowest Common Denominator) width for APB slave connections.

        Finds all masters connecting to the same APB slaves and returns the minimum
        data width among them. This ensures all masters can communicate through the
        same adapter output width.

        Args:
            master: Master to calculate LCD for

        Returns:
            LCD width in bits (minimum width among all masters connecting to same APB slaves)
        """
        # Get APB slaves this master connects to
        apb_slave_indices = [idx for idx in master.slave_connections
                             if self.slaves[idx].protocol == 'apb']

        if not apb_slave_indices:
            return master.data_width

        # Find all masters that connect to ANY of these APB slaves
        connecting_masters = []
        seen_names = set()  # Track by name to avoid duplicates

        for apb_idx in apb_slave_indices:
            for m in self.masters:
                if apb_idx in m.slave_connections and m.name not in seen_names:
                    connecting_masters.append(m)
                    seen_names.add(m.name)

        if not connecting_masters:
            return master.data_width

        # Find minimum width among all masters connecting to APB
        lcd_width = min(m.data_width for m in connecting_masters)

        if lcd_width != master.data_width:
            master_names = ', '.join(f"{m.name}({m.data_width}b)" for m in connecting_masters)
            print(f"INFO: Master '{master.name}' LCD width for APB: {lcd_width}b")
            print(f"      Masters connecting to same APB slaves: {master_names}")

        return lcd_width

    def _get_connected_slave_widths(self, master: MasterConfig) -> List[int]:
        """
        Get sorted list of unique ADAPTER OUTPUT widths for slaves this master connects to.

        Always uses slave.data_width — must match the adapter generator's
        and crossbar generator's choice. The previous LCD-for-APB path
        here disagreed with the regenerated adapter and crossbar (which
        both now use slave.data_width), leaving the bridge top
        instantiating the xbar with widths that don't exist as ports.
        """
        widths = set()
        for idx in master.slave_connections:
            widths.add(self.slaves[idx].data_width)
        return sorted(list(widths))

    def _get_masters_connecting_to_slave(self, slave: SlaveInfo) -> List[MasterConfig]:
        """
        Get list of masters that connect to a specific slave.

        Args:
            slave: Slave to check connections for

        Returns:
            List of MasterConfig objects that have this slave in their connections
        """
        # Find slave index
        try:
            slave_idx = self.slaves.index(slave)
        except ValueError:
            return []

        # Find all masters that connect to this slave
        connecting_masters = []
        for master in self.masters:
            if slave_idx in master.slave_connections:
                connecting_masters.append(master)

        return connecting_masters

    def _generate_adapter_instantiations(self, monitored: List[MonitoredWrapper] = None) -> List[str]:
        """
        Generate adapter module instantiations using SignalNaming.

        Connects ALL width paths from adapter to internal signals.
        Now uses SignalNaming for correct port connection names.

        Args:
            monitored: list of MonitoredWrapper entries the bridge top
                tracks for monbus aggregation. When non-empty, this
                method also wires each master adapter's monbus + cfg
                ports to the matching bridge-top nets.
        """
        lines = []
        monitored = monitored or []

        for m_idx, master in enumerate(self.masters):
            lines.append("    // ================================================================")
            lines.append(f"    // {master.name.upper()} Adapter")
            lines.append("    // ================================================================")
            # Parameter override block -- pass the bridge-top's effective
            # USE_MONITOR localparams down to the adapter so per-port
            # monitor enables can be flipped at bridge instantiation
            # without regenerating. Only emitted on monitored variants.
            mon_params: List[str] = []
            if self.enable_monitoring:
                if master.channels in ("wr", "rw"):
                    mon_params.append(
                        f"        .USE_MONITOR_WR(EFF_USE_MON_{master.name}_wr)"
                    )
                if master.channels in ("rd", "rw"):
                    mon_params.append(
                        f"        .USE_MONITOR_RD(EFF_USE_MON_{master.name}_rd)"
                    )
            if mon_params:
                lines.append(f"    {master.name}_adapter #(")
                for i, p in enumerate(mon_params):
                    sep = "," if i < len(mon_params) - 1 else ""
                    lines.append(p + sep)
                lines.append(f"    ) u_{master.name}_adapter (")
            else:
                lines.append(f"    {master.name}_adapter u_{master.name}_adapter (")
            lines.append("        .aclk(aclk),")
            lines.append("        .aresetn(aresetn),")
            lines.append("")
            lines.append("        // External interface")

            # Use master.prefix from the .toml config (Bug C in TASK-011).
            # The adapter's external port names also use master.prefix (see
            # AdapterGenerator._generate_external_ports), so .{sig}({sig})
            # connects adapter ports to identically-named bridge top-level
            # wires/ports. Normalise to ensure trailing `_` so configs that
            # set prefix="cpu_m_axi" still produce "cpu_m_axi_awid".
            signal_prefix = master.prefix
            if signal_prefix and not signal_prefix.endswith("_"):
                signal_prefix = signal_prefix + "_"

            # Get channels for this master
            channels = SignalNaming.channels_from_type(master.channels)

            # Generate port connections using SignalNaming
            signal_db = AXI4_MASTER_SIGNALS  # Master direction

            # Signals on the AXIL surface (the rest are AXI4 extras).
            axil_surface = {
                'awaddr', 'awprot', 'awvalid', 'awready',
                'wdata',  'wstrb',  'wvalid',  'wready',
                'bresp',  'bvalid', 'bready',
                'araddr', 'arprot', 'arvalid', 'arready',
                'rdata',  'rresp',  'rvalid',  'rready',
            }
            # Default literals for the AXI4 extras when an AXIL master's
            # adapter still expects them. INCR burst, single-beat (len=0,
            # last=1), and size = $clog2(DATA_WIDTH/8). Outputs from the
            # bridge towards the master are dropped.
            strb_w = master.data_width // 8
            axsize_val = 0
            while (1 << axsize_val) < strb_w:
                axsize_val += 1
            axi4_extra_defaults = {
                'awid':     f"{master.id_width}'h0",
                'awlen':    "8'h0",
                'awsize':   f"3'd{axsize_val}",
                'awburst':  "2'b01",
                'awlock':   "1'b0",
                'awcache':  "4'h0",
                'awqos':    "4'h0",
                'awregion': "4'h0",
                'awuser':   "1'b0",
                'wlast':    "1'b1",
                'wuser':    "1'b0",
                'arid':     f"{master.id_width}'h0",
                'arlen':    "8'h0",
                'arsize':   f"3'd{axsize_val}",
                'arburst':  "2'b01",
                'arlock':   "1'b0",
                'arcache':  "4'h0",
                'arqos':    "4'h0",
                'arregion': "4'h0",
                'aruser':   "1'b0",
            }

            for channel in channels:
                if channel not in signal_db:
                    continue

                for sig_info in signal_db[channel]:
                    full_name = f"{channel.value}{sig_info.name}"
                    sig_name = f"{signal_prefix}{full_name}"

                    if master.protocol != 'axil' or full_name in axil_surface:
                        # AXI4 master, or AXIL master & this signal IS on
                        # the AXIL surface — wire directly to the top.
                        lines.append(f"        .{sig_name}({sig_name}),")
                    else:
                        # AXIL master & this signal is an AXI4 extra. The
                        # adapter still expects every AXI4 port, so we
                        # default the inputs and leave outputs floating.
                        if sig_info.direction == PortDirection.OUTPUT:
                            # Master OUTPUT == bridge INPUT (master->bridge).
                            # AXIL master can't drive this; supply a sane
                            # default so the adapter sees valid semantics.
                            default = axi4_extra_defaults.get(full_name, "1'b0")
                            lines.append(f"        .{sig_name}({default}),")
                        else:
                            # Master INPUT == bridge OUTPUT (bridge->master).
                            # AXIL master doesn't observe this; leave the
                            # adapter port unconnected.
                            lines.append(f"        .{sig_name}(),")

            lines.append("")
            lines.append("        // Decode outputs")
            if master.channels in ["wr", "rw"]:
                lines.append(f"        .slave_select_aw({master.name}_slave_select_aw),")
                lines.append(f"        .bridge_id_aw({master.name}_bridge_id_aw),")
            if master.channels in ["rd", "rw"]:
                lines.append(f"        .slave_select_ar({master.name}_slave_select_ar),")
                lines.append(f"        .bridge_id_ar({master.name}_bridge_id_ar),")

            # Connect ALL width paths
            slave_widths = self._get_connected_slave_widths(master)
            for width_idx, width in enumerate(slave_widths):
                suffix = f"{width}b"
                is_last_width = (width_idx == len(slave_widths) - 1)

                lines.append("")
                lines.append(f"        // {width}b path")

                # Write struct connections
                if master.channels in ["wr", "rw"]:
                    lines.append(f"        .{master.name}_{suffix}_aw({master.name}_{suffix}_aw),")
                    lines.append(f"        .{master.name}_{suffix}_awvalid({master.name}_{suffix}_awvalid),")
                    lines.append(f"        .{master.name}_{suffix}_awready({master.name}_{suffix}_awready),")
                    lines.append(f"        .{master.name}_{suffix}_w({master.name}_{suffix}_w),")
                    lines.append(f"        .{master.name}_{suffix}_wvalid({master.name}_{suffix}_wvalid),")
                    lines.append(f"        .{master.name}_{suffix}_wready({master.name}_{suffix}_wready),")
                    lines.append(f"        .{master.name}_{suffix}_b({master.name}_{suffix}_b),")
                    lines.append(f"        .{master.name}_{suffix}_bvalid({master.name}_{suffix}_bvalid),")
                    # Determine if comma needed
                    if master.channels == "wr" and is_last_width:
                        lines.append(f"        .{master.name}_{suffix}_bready({master.name}_{suffix}_bready)")
                    else:
                        lines.append(f"        .{master.name}_{suffix}_bready({master.name}_{suffix}_bready),")

                # Read struct connections
                if master.channels in ["rd", "rw"]:
                    lines.append(f"        .{master.name}_{suffix}_ar({master.name}_{suffix}_ar),")
                    lines.append(f"        .{master.name}_{suffix}_arvalid({master.name}_{suffix}_arvalid),")
                    lines.append(f"        .{master.name}_{suffix}_arready({master.name}_{suffix}_arready),")
                    lines.append(f"        .{master.name}_{suffix}_r({master.name}_{suffix}_r),")
                    lines.append(f"        .{master.name}_{suffix}_rvalid({master.name}_{suffix}_rvalid),")
                    # Determine if comma needed
                    if is_last_width:
                        lines.append(f"        .{master.name}_{suffix}_rready({master.name}_{suffix}_rready)")
                    else:
                        lines.append(f"        .{master.name}_{suffix}_rready({master.name}_{suffix}_rready),")

            # Per-master monbus + cfg wiring -- only emit when this
            # master has at least one monitored wrapper in the bridge
            # top. The adapter's port names are channel-suffixed
            # (monbus_wr_*, cfg_rd_*); the bridge-top connectors carry
            # the {port}_{idx}_{chan} prefix.
            my_wrappers = [w for w in monitored
                           if w.side == 'master' and w.port_name == master.name]
            if my_wrappers:
                _ensure_trailing_comma(lines)
                lines.append("")
                lines.append("        // Monitor side-band")
                lines.extend(self._generate_master_monitor_connections(my_wrappers))

            lines.append("    );")
            lines.append("")

        return lines

    def _generate_crossbar_routing(self) -> List[str]:
        """
        Generate crossbar module instantiation.

        Instantiates the separate crossbar module that handles routing.
        """
        lines = []

        lines.append("    // ================================================================")
        lines.append("    // Crossbar Module Instantiation")
        lines.append("    // ================================================================")
        lines.append(f"    {self.bridge_name}_xbar u_xbar (")
        lines.append("        .aclk(aclk),")
        lines.append("        .aresetn(aresetn),")
        lines.append("")

        # Connect adapter outputs to crossbar inputs
        for master_idx, master in enumerate(self.masters):
            slave_widths = self._get_connected_slave_widths(master)

            lines.append(f"        // {master.name} adapter outputs")

            # Address decode signals
            if master.channels in ["wr", "rw"]:
                lines.append(f"        .{master.name}_slave_select_aw({master.name}_slave_select_aw),")
                lines.append(f"        .{master.name}_bridge_id_aw({master.name}_bridge_id_aw),")
            if master.channels in ["rd", "rw"]:
                lines.append(f"        .{master.name}_slave_select_ar({master.name}_slave_select_ar),")
                lines.append(f"        .{master.name}_bridge_id_ar({master.name}_bridge_id_ar),")

            # Determine if this is the last master (for comma handling)
            is_last_master = (master_idx == len(self.masters) - 1)

            # Width-specific paths
            for width_idx, width in enumerate(slave_widths):
                suffix = f"{width}b"
                is_last_width = (width_idx == len(slave_widths) - 1)

                lines.append(f"        // {width}b path")

                # Write channels
                if master.channels in ["wr", "rw"]:
                    lines.append(f"        .{master.name}_{suffix}_aw({master.name}_{suffix}_aw),")
                    lines.append(f"        .{master.name}_{suffix}_awvalid({master.name}_{suffix}_awvalid),")
                    lines.append(f"        .{master.name}_{suffix}_awready({master.name}_{suffix}_awready),")
                    lines.append(f"        .{master.name}_{suffix}_w({master.name}_{suffix}_w),")
                    lines.append(f"        .{master.name}_{suffix}_wvalid({master.name}_{suffix}_wvalid),")
                    lines.append(f"        .{master.name}_{suffix}_wready({master.name}_{suffix}_wready),")
                    lines.append(f"        .{master.name}_{suffix}_b({master.name}_{suffix}_b),")
                    lines.append(f"        .{master.name}_{suffix}_bvalid({master.name}_{suffix}_bvalid),")

                    # Determine if comma needed (check if slaves follow)
                    needs_comma = not (is_last_width and is_last_master and len(self.slaves) == 0)
                    comma = "," if needs_comma else ""
                    lines.append(f"        .{master.name}_{suffix}_bready({master.name}_{suffix}_bready){comma}")

                # Read channels
                if master.channels in ["rd", "rw"]:
                    lines.append(f"        .{master.name}_{suffix}_ar({master.name}_{suffix}_ar),")
                    lines.append(f"        .{master.name}_{suffix}_arvalid({master.name}_{suffix}_arvalid),")
                    lines.append(f"        .{master.name}_{suffix}_arready({master.name}_{suffix}_arready),")
                    lines.append(f"        .{master.name}_{suffix}_r({master.name}_{suffix}_r),")
                    lines.append(f"        .{master.name}_{suffix}_rvalid({master.name}_{suffix}_rvalid),")

                    # Determine if comma needed (last signal of last master)
                    if is_last_width and is_last_master:
                        # Check if there are slave ports following
                        if len(self.slaves) > 0:
                            lines.append(f"        .{master.name}_{suffix}_rready({master.name}_{suffix}_rready),")
                        else:
                            lines.append(f"        .{master.name}_{suffix}_rready({master.name}_{suffix}_rready)")
                    else:
                        lines.append(f"        .{master.name}_{suffix}_rready({master.name}_{suffix}_rready),")

            if not (is_last_master):
                lines.append("")

        # Connect slave ports (all slaves - crossbar generates AXI4 outputs for all)
        if len(self.slaves) > 0:
            lines.append("")
            for slave_idx, slave in enumerate(self.slaves):
                is_last_slave = (slave_idx == len(self.slaves) - 1)

                lines.append(f"        // Slave {slave_idx}: {slave.name}")

                # Determine which channels to generate based on masters connecting to this slave
                connecting_masters = self._get_masters_connecting_to_slave(slave)
                has_write = any(m.channels in ["wr", "rw"] for m in connecting_masters)
                has_read = any(m.channels in ["rd", "rw"] for m in connecting_masters)

                bridge_channels = []
                if has_write:
                    bridge_channels.extend([AXI4Channel.AW, AXI4Channel.W, AXI4Channel.B])
                if has_read:
                    bridge_channels.extend([AXI4Channel.AR, AXI4Channel.R])

                # Connect crossbar to internal xbar_{slave}_axi_* signals
                # (slave adapter sits between crossbar and external port)
                signal_prefix = f"xbar_{slave.name}_axi_"

                # Get signal info from AXI4_SLAVE_SIGNALS database
                signal_db = AXI4_MASTER_SIGNALS  # Bridge connecting to crossbar slave outputs

                # Generate port connections
                signal_list = []
                for channel in bridge_channels:
                    if channel not in signal_db:
                        continue
                    for sig_info in signal_db[channel]:
                        # Build signal name using correct naming convention
                        sig_name = f"{signal_prefix}{channel.value}{sig_info.name}"
                        signal_list.append((sig_name, sig_info))

                # Generate connections with proper comma handling
                for idx, (sig_name, sig_info) in enumerate(signal_list):
                    is_last_regular_signal = (idx == len(signal_list) - 1)
                    # All slaves have bridge_id signals, so always add comma on last regular signal
                    # Only omit comma if this is NOT the last regular signal AND this is the last slave
                    needs_comma = True  # Always comma because bridge_id signals always follow
                    comma = "," if needs_comma else ""
                    # Use signal name for both port name and connection (signals already declared)
                    lines.append(f"        .{sig_name.replace('xbar_', '')}({sig_name}){comma}")

                # Bridge ID tracking signals (connect crossbar outputs to slave adapter inputs)
                # All slave adapters have bridge_id tracking (AXI4 interface on crossbar side)
                if True:  # All slaves with adapters need bridge_id
                    if has_write:
                        lines.append(f"        .{slave.name}_axi_bridge_id_aw({slave.name}_axi_bridge_id_aw),")
                        lines.append(f"        .{slave.name}_axi_bid_bridge_id({slave.name}_axi_bid_bridge_id),")
                        if has_read:
                            # More read signals coming
                            lines.append(f"        .{slave.name}_axi_bid_valid({slave.name}_axi_bid_valid),")
                        else:
                            # Last write signal - check if this is last slave
                            comma = "" if is_last_slave else ","
                            lines.append(f"        .{slave.name}_axi_bid_valid({slave.name}_axi_bid_valid){comma}")
                    if has_read:
                        if has_write:
                            lines.append("")
                        lines.append(f"        .{slave.name}_axi_bridge_id_ar({slave.name}_axi_bridge_id_ar),")
                        lines.append(f"        .{slave.name}_axi_rid_bridge_id({slave.name}_axi_rid_bridge_id),")
                        # Last signal - check if this is last slave
                        comma = "" if is_last_slave else ","
                        lines.append(f"        .{slave.name}_axi_rid_valid({slave.name}_axi_rid_valid){comma}")

                if not is_last_slave:
                    lines.append("")

        lines.append("    );")
        lines.append("")

        return lines

    def _generate_slave_adapter_instantiations(self, monitored: List[MonitoredWrapper] = None) -> List[str]:
        """Generate slave-adapter instantiations for ALL slaves via the
        typed SlaveAdapterInstance component.

        The slave_adapter_generator emits protocol-aware adapter
        modules (axi4 wrapper, axi4_to_apb_shim wrapper, or axi4_to_axil
        shim wrapper). The bridge top needs to instantiate each with
        the matching port list -- the component keeps the bridge top
        and the adapter generator in lockstep so the two can't drift
        apart silently (which left `rid_bridge_id`/`rid_valid`/`bid_*`
        undriven for APB slaves in a previous regression).

        Args:
            monitored: when non-empty, wire each AXI4 slave adapter's
                monbus + cfg ports to the matching bridge-top nets."""
        from .slave_adapter_instance_component import SlaveAdapterInstance

        lines = []
        monitored = monitored or []
        if not self.slaves:
            return lines

        lines.append("    // ================================================================")
        lines.append("    // Slave Adapter Instantiations")
        lines.append("    // AXI4 slaves: timing-isolation wrapper (axi4_master_wr/rd)")
        lines.append("    // APB / AXIL slaves: protocol-converter wrapper")
        lines.append("    // All adapters carry bridge_id tracking FIFOs.")
        lines.append("    // ================================================================")
        lines.append("")

        for slave in self.slaves:
            connecting_masters = self._get_masters_connecting_to_slave(slave)
            has_write = any(m.channels in ["wr", "rw"] for m in connecting_masters)
            has_read = any(m.channels in ["rd", "rw"] for m in connecting_masters)
            if not (has_write or has_read):
                continue

            inst = SlaveAdapterInstance(
                slave_name=slave.name,
                slave_prefix=slave.prefix,
                protocol=slave.protocol,
                has_write=has_write,
                has_read=has_read,
            )
            inst.connect_clocks_and_resets()
            inst.connect_xbar_interface()
            inst.connect_external_interface()
            inst.connect_bridge_id_tracking()
            # Wire the AXI4 slave adapter's monbus+cfg ports if this
            # slave participates in monitor aggregation.
            slave_wrappers = [w for w in monitored
                              if w.side == 'slave' and w.port_name == slave.name]
            if slave_wrappers:
                inst.connect_monitor(slave_wrappers)
                # Pass bridge-top EFF_USE_MON_* localparams down to the
                # adapter's USE_MONITOR_WR / USE_MONITOR_RD parameters so
                # the integrator's runtime knobs reach every wrapper.
                eff_wr = (f"EFF_USE_MON_{slave.name}_wr"
                          if any(w.channel == 'wr' for w in slave_wrappers)
                          else None)
                eff_rd = (f"EFF_USE_MON_{slave.name}_rd"
                          if any(w.channel == 'rd' for w in slave_wrappers)
                          else None)
                inst.set_use_monitor_params(eff_wr=eff_wr, eff_rd=eff_rd)
            lines.extend(inst.generate_lines())

        return lines

# Old implementation below - keeping for reference during migration
def _generate_crossbar_routing_OLD(self) -> List[str]:
        """
        OLD IMPLEMENTATION - Inline crossbar routing (deprecated).

        For now, simplified mux-based routing.
        Future: Full crossbar with arbitration.
        """
        lines = []

        lines.append("    // ================================================================")
        lines.append("    // Crossbar routing (simplified)")
        lines.append("    // TODO: Add arbitration for multi-master")
        lines.append("    // ================================================================")
        lines.append("")

        # For now, only support single master (as in test script)
        if len(self.masters) == 1:
            master = self.masters[0]
            suffix = f"{master.data_width}b"

            # Route to each slave
            for i, slave in enumerate(self.slaves):
                lines.append(f"    // Slave {i}: {slave.name}")

                if master.channels in ["wr", "rw"]:
                    # AW channel
                    lines.append(f"    assign {slave.name}_s_axi_awid     = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_aw.id : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_awaddr   = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_aw.addr : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_awlen    = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_aw.len : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_awsize   = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_aw.size : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_awburst  = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_aw.burst : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_awlock   = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_aw.lock : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_awcache  = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_aw.cache : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_awprot   = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_aw.prot : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_awqos    = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_aw.qos : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_awregion = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_aw.region : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_awuser   = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_aw.user : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_awvalid  = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_awvalid : '0;")
                    lines.append("")

                    # W channel
                    lines.append(f"    assign {slave.name}_s_axi_wdata  = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_w.data : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_wstrb  = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_w.strb : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_wlast  = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_w.last : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_wuser  = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_w.user : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_wvalid = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_wvalid : '0;")
                    lines.append("")

                if master.channels in ["rd", "rw"]:
                    # AR channel
                    lines.append(f"    assign {slave.name}_s_axi_arid     = {master.name}_slave_select_ar[{i}] ? {master.name}_{suffix}_ar.id : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_araddr   = {master.name}_slave_select_ar[{i}] ? {master.name}_{suffix}_ar.addr : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_arlen    = {master.name}_slave_select_ar[{i}] ? {master.name}_{suffix}_ar.len : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_arsize   = {master.name}_slave_select_ar[{i}] ? {master.name}_{suffix}_ar.size : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_arburst  = {master.name}_slave_select_ar[{i}] ? {master.name}_{suffix}_ar.burst : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_arlock   = {master.name}_slave_select_ar[{i}] ? {master.name}_{suffix}_ar.lock : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_arcache  = {master.name}_slave_select_ar[{i}] ? {master.name}_{suffix}_ar.cache : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_arprot   = {master.name}_slave_select_ar[{i}] ? {master.name}_{suffix}_ar.prot : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_arqos    = {master.name}_slave_select_ar[{i}] ? {master.name}_{suffix}_ar.qos : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_arregion = {master.name}_slave_select_ar[{i}] ? {master.name}_{suffix}_ar.region : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_aruser   = {master.name}_slave_select_ar[{i}] ? {master.name}_{suffix}_ar.user : '0;")
                    lines.append(f"    assign {slave.name}_s_axi_arvalid  = {master.name}_slave_select_ar[{i}] ? {master.name}_{suffix}_arvalid : '0;")
                    lines.append("")

            # Ready/response muxes
            if master.channels in ["wr", "rw"]:
                lines.append(f"    // AW/W ready muxes")
                lines.append(f"    assign {master.name}_{suffix}_awready = ")
                for i, slave in enumerate(self.slaves):
                    suffix_str = " : '0;" if i == len(self.slaves) - 1 else " :"
                    lines.append(f"        {master.name}_slave_select_aw[{i}] ? {slave.name}_s_axi_awready{suffix_str}")
                lines.append("")

                lines.append(f"    assign {master.name}_{suffix}_wready = ")
                for i, slave in enumerate(self.slaves):
                    suffix_str = " : '0;" if i == len(self.slaves) - 1 else " :"
                    lines.append(f"        {master.name}_slave_select_aw[{i}] ? {slave.name}_s_axi_wready{suffix_str}")
                lines.append("")

                # B channel
                lines.append("    // B channel responses")
                lines.append(f"    assign {master.name}_{suffix}_b.id = ")
                for i, slave in enumerate(self.slaves):
                    suffix_str = " : '0;" if i == len(self.slaves) - 1 else " :"
                    lines.append(f"        {master.name}_slave_select_aw[{i}] ? {slave.name}_s_axi_bid{suffix_str}")

                lines.append(f"    assign {master.name}_{suffix}_b.resp = ")
                for i, slave in enumerate(self.slaves):
                    suffix_str = " : '0;" if i == len(self.slaves) - 1 else " :"
                    lines.append(f"        {master.name}_slave_select_aw[{i}] ? {slave.name}_s_axi_bresp{suffix_str}")

                lines.append(f"    assign {master.name}_{suffix}_b.user = ")
                for i, slave in enumerate(self.slaves):
                    suffix_str = " : '0;" if i == len(self.slaves) - 1 else " :"
                    lines.append(f"        {master.name}_slave_select_aw[{i}] ? {slave.name}_s_axi_buser{suffix_str}")

                lines.append(f"    assign {master.name}_{suffix}_bvalid = ")
                for i, slave in enumerate(self.slaves):
                    suffix_str = " : '0;" if i == len(self.slaves) - 1 else " :"
                    lines.append(f"        {master.name}_slave_select_aw[{i}] ? {slave.name}_s_axi_bvalid{suffix_str}")
                lines.append("")

                # Bready distribution
                for i, slave in enumerate(self.slaves):
                    lines.append(f"    assign {slave.name}_s_axi_bready = {master.name}_slave_select_aw[{i}] ? {master.name}_{suffix}_bready : '0;")
                lines.append("")

            if master.channels in ["rd", "rw"]:
                lines.append(f"    // AR ready mux")
                lines.append(f"    assign {master.name}_{suffix}_arready = ")
                for i, slave in enumerate(self.slaves):
                    suffix_str = " : '0;" if i == len(self.slaves) - 1 else " :"
                    lines.append(f"        {master.name}_slave_select_ar[{i}] ? {slave.name}_s_axi_arready{suffix_str}")
                lines.append("")

                # R channel
                lines.append("    // R channel responses")
                lines.append(f"    assign {master.name}_{suffix}_r.id = ")
                for i, slave in enumerate(self.slaves):
                    suffix_str = " : '0;" if i == len(self.slaves) - 1 else " :"
                    lines.append(f"        {master.name}_slave_select_ar[{i}] ? {slave.name}_s_axi_rid{suffix_str}")

                lines.append(f"    assign {master.name}_{suffix}_r.data = ")
                for i, slave in enumerate(self.slaves):
                    suffix_str = " : '0;" if i == len(self.slaves) - 1 else " :"
                    lines.append(f"        {master.name}_slave_select_ar[{i}] ? {slave.name}_s_axi_rdata{suffix_str}")

                lines.append(f"    assign {master.name}_{suffix}_r.resp = ")
                for i, slave in enumerate(self.slaves):
                    suffix_str = " : '0;" if i == len(self.slaves) - 1 else " :"
                    lines.append(f"        {master.name}_slave_select_ar[{i}] ? {slave.name}_s_axi_rresp{suffix_str}")

                lines.append(f"    assign {master.name}_{suffix}_r.last = ")
                for i, slave in enumerate(self.slaves):
                    suffix_str = " : '0;" if i == len(self.slaves) - 1 else " :"
                    lines.append(f"        {master.name}_slave_select_ar[{i}] ? {slave.name}_s_axi_rlast{suffix_str}")

                lines.append(f"    assign {master.name}_{suffix}_r.user = ")
                for i, slave in enumerate(self.slaves):
                    suffix_str = " : '0;" if i == len(self.slaves) - 1 else " :"
                    lines.append(f"        {master.name}_slave_select_ar[{i}] ? {slave.name}_s_axi_ruser{suffix_str}")

                lines.append(f"    assign {master.name}_{suffix}_rvalid = ")
                for i, slave in enumerate(self.slaves):
                    suffix_str = " : '0;" if i == len(self.slaves) - 1 else " :"
                    lines.append(f"        {master.name}_slave_select_ar[{i}] ? {slave.name}_s_axi_rvalid{suffix_str}")
                lines.append("")

                # Rready distribution
                for i, slave in enumerate(self.slaves):
                    lines.append(f"    assign {slave.name}_s_axi_rready = {master.name}_slave_select_ar[{i}] ? {master.name}_{suffix}_rready : '0;")
                lines.append("")

        else:
            lines.append("    // TODO: Multi-master crossbar with arbitration")
            lines.append("")

        return lines


# Example usage
if __name__ == "__main__":
    # Example configuration
    slaves = [
        SlaveInfo("ddr", 0x00000000, 0x80000000, 32, 32),
        SlaveInfo("sram", 0x80000000, 0x80000000, 32, 32)
    ]

    master = MasterConfig(
        name="cpu",
        prefix="cpu_m_axi_",
        data_width=32,
        addr_width=32,
        id_width=4,
        channels="wr",
        slave_connections=[0, 1]
    )

    gen = BridgeModuleGenerator("bridge_1x2_wr")
    gen.add_master(master)
    for slave in slaves:
        gen.add_slave(slave)

    files = gen.generate_all("/tmp/bridge_test")
    print("Generated files:")
    for name, path in files.items():
        print(f"  {name}: {path}")
