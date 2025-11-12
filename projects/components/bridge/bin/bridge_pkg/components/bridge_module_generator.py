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
from bridge_pkg.generators.adapter_generator import AdapterGenerator, MasterConfig, SlaveInfo
from bridge_pkg.generators.slave_adapter_generator import SlaveAdapterGenerator
from bridge_pkg.generators.crossbar_generator import CrossbarGenerator
from bridge_pkg.signal_naming import SignalNaming, Direction, AXI4Channel, Protocol, AXI4_MASTER_SIGNALS, PortDirection, SignalInfo


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

    def __init__(self, bridge_name: str, enable_monitoring: bool = False):
        """
        Initialize bridge generator.

        Args:
            bridge_name: Name of bridge (e.g., "bridge_1x2_wr")
            enable_monitoring: Use *_mon wrapper versions
        """
        self.bridge_name = bridge_name
        self.enable_monitoring = enable_monitoring
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

        # 3. Generate slave adapter modules
        for slave in self.slaves:
            slave_adapter_src = self._generate_slave_adapter(slave)
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

    def _generate_slave_adapter(self, slave: SlaveInfo) -> str:
        """
        Generate slave adapter module for a slave port.

        Args:
            slave: Slave configuration

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
            data_width=crossbar_data_width
        )
        return slave_adapter_gen.generate()

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

        # Adapter instantiations
        lines.extend(self._generate_adapter_instantiations())

        # Crossbar routing
        lines.extend(self._generate_crossbar_routing())

        # Slave adapter instantiations (for AXI4 slaves)
        lines.extend(self._generate_slave_adapter_instantiations())

        # APB shim instantiations (for APB slaves)
        lines.extend(self._generate_apb_shims())

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
        """Generate module declaration with all ports."""
        lines = []

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

        lines.append(");")
        lines.append("")

        # Localparams
        lines.append(f"    localparam NUM_SLAVES = {len(self.slaves)};")
        lines.append("")

        return lines

    def _generate_master_ports(self, master: MasterConfig) -> List[str]:
        """
        Generate master port declarations using SignalNaming.

        IMPORTANT: Bridge top-level is an intermediary that receives signals from
        external master. Port directions are INVERTED from the master's perspective:
        - Request signals (awid, awaddr, etc.): INPUT to bridge (from external master)
        - Response signals (awready, bid, etc.): OUTPUT from bridge (to external master)
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

        lines.append(f"    // Master: {master.name} ({master.channels})")

        # Determine which channels to generate based on master type
        channels = SignalNaming.channels_from_type(master.channels)

        # Get all AXI4 signals from SignalNaming
        all_signals = SignalNaming.get_all_axi4_signals(
            port_name=master.name,
            direction=Direction.MASTER,
            channels=channels
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
        """Generate slave port declarations (AXI4 or APB based on protocol)."""
        lines = []

        # Width parameters for signal info queries
        width_values = {
            'ID_WIDTH': 4,  # Standard 4-bit ID for slaves
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
            apb_signals = SignalNaming.get_all_apb_signals(slave.name, Direction.MASTER)

            for sig_name, sig_info in apb_signals:
                # Get complete signal declaration
                declaration = sig_info.get_declaration(sig_name, width_values)
                lines.append(f"    {declaration},")

            # Remove trailing comma from last signal
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
            # Bridge acts as master to external slaves (same perspective as crossbar)
            all_signals = SignalNaming.get_all_axi4_signals(
                port_name=slave.name,
                direction=Direction.MASTER,
                channels=channels
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
        # These are internal wires connecting crossbar slave outputs to slave adapters
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

            # Write channels
            if has_write:
                lines.append(f"    logic [3:0]                {prefix}awid;")
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
                lines.append(f"    logic [3:0]                {prefix}bid;")
                lines.append(f"    logic [1:0]                {prefix}bresp;")
                lines.append(f"    logic                      {prefix}buser;")
                lines.append(f"    logic                      {prefix}bvalid;")
                lines.append(f"    logic                      {prefix}bready;")

            # Read channels
            if has_read:
                lines.append(f"    logic [3:0]                {prefix}arid;")
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
                lines.append(f"    logic [3:0]                {prefix}rid;")
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

        For AXI4 slaves: uses native slave width
        For APB slaves: uses LCD (Lowest Common Denominator) width
        """
        widths = set()

        # Separate AXI4 and APB slaves
        axi4_slave_indices = [idx for idx in master.slave_connections
                              if self.slaves[idx].protocol == 'axi4']
        apb_slave_indices = [idx for idx in master.slave_connections
                             if self.slaves[idx].protocol == 'apb']

        # For AXI4 slaves: use their native widths
        for idx in axi4_slave_indices:
            widths.add(self.slaves[idx].data_width)

        # For APB slaves: use LCD width (calculated once for all APB connections)
        if apb_slave_indices:
            lcd_width = self._calculate_lcd_width_for_apb(master)
            widths.add(lcd_width)

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

    def _generate_adapter_instantiations(self) -> List[str]:
        """
        Generate adapter module instantiations using SignalNaming.

        Connects ALL width paths from adapter to internal signals.
        Now uses SignalNaming for correct port connection names.
        """
        lines = []

        for master in self.masters:
            lines.append("    // ================================================================")
            lines.append(f"    // {master.name.upper()} Adapter")
            lines.append("    // ================================================================")
            lines.append(f"    {master.name}_adapter u_{master.name}_adapter (")
            lines.append("        .aclk(aclk),")
            lines.append("        .aresetn(aresetn),")
            lines.append("")
            lines.append("        // External interface")

            # Use SignalNaming.get_all_axi4_signals() for consistent naming
            # Signal naming: <port_name>_axi_<channel><signal> (no direction prefix)
            signal_prefix = f"{master.name}_axi_"

            # Get channels for this master
            channels = SignalNaming.channels_from_type(master.channels)

            # Generate port connections using SignalNaming
            signal_db = AXI4_MASTER_SIGNALS  # Master direction

            for channel in channels:
                if channel not in signal_db:
                    continue

                for sig_info in signal_db[channel]:
                    # Build signal name using correct naming convention
                    sig_name = f"{signal_prefix}{channel.value}{sig_info.name}"
                    lines.append(f"        .{sig_name}({sig_name}),")

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

    def _generate_slave_adapter_instantiations(self) -> List[str]:
        """
        Generate slave adapter instantiations for AXI4 slaves.

        Instantiates slave adapters between crossbar outputs and external slave ports.
        """
        lines = []

        # Filter for AXI4 slaves only
        axi4_slaves = [s for s in self.slaves if s.protocol == 'axi4']

        if not axi4_slaves:
            return lines

        lines.append("    // ================================================================")
        lines.append("    // Slave Adapter Instantiations (AXI4 Slaves)")
        lines.append("    // Provides timing isolation (axi4_master_wr/rd wrappers)")
        lines.append("    // ================================================================")
        lines.append("")

        for slave in axi4_slaves:
            # Determine channels needed
            connecting_masters = self._get_masters_connecting_to_slave(slave)
            has_write = any(m.channels in ["wr", "rw"] for m in connecting_masters)
            has_read = any(m.channels in ["rd", "rw"] for m in connecting_masters)

            channels = []
            if has_write:
                channels.extend([AXI4Channel.AW, AXI4Channel.W, AXI4Channel.B])
            if has_read:
                channels.extend([AXI4Channel.AR, AXI4Channel.R])

            lines.append(f"    // {slave.name} adapter (crossbar → external slave)")
            lines.append(f"    {slave.name}_adapter u_{slave.name}_adapter (")
            lines.append("        .aclk(aclk),")
            lines.append("        .aresetn(aresetn),")
            lines.append("")
            lines.append("        // Crossbar interface (internal signals)")

            # Crossbar-facing signals (xbar_{slave}_axi_*)
            xbar_prefix = f"xbar_{slave.name}_axi_"
            for channel in channels:
                if channel not in AXI4_MASTER_SIGNALS:
                    continue
                for sig_info in AXI4_MASTER_SIGNALS[channel]:
                    sig_name = f"{xbar_prefix}{channel.value}{sig_info.name}"
                    lines.append(f"        .{xbar_prefix}{channel.value}{sig_info.name}({sig_name}),")

            lines.append("")
            lines.append("        // External slave interface")

            # External-facing signals (slave.prefix)
            ext_prefix = slave.prefix
            signal_list = []
            for channel in channels:
                if channel not in AXI4_MASTER_SIGNALS:
                    continue
                for sig_info in AXI4_MASTER_SIGNALS[channel]:
                    sig_name = f"{ext_prefix}{channel.value}{sig_info.name}"
                    signal_list.append(sig_name)

            # Generate connections with proper comma handling
            for idx, sig_name in enumerate(signal_list):
                # Not the last anymore - bridge_id signals come after
                lines.append(f"        .{ext_prefix}{sig_name.replace(ext_prefix, '')}({sig_name}),")

            # Bridge ID tracking signals (always present for slave adapters)
            lines.append("")
            lines.append("        // Bridge ID tracking")
            if has_write:
                lines.append(f"        .xbar_bridge_id_aw({slave.name}_axi_bridge_id_aw),")
                lines.append(f"        .bid_bridge_id({slave.name}_axi_bid_bridge_id),")
                lines.append(f"        .bid_valid({slave.name}_axi_bid_valid){'' if not has_read else ','}")
            if has_read:
                if has_write:
                    lines.append("")
                lines.append(f"        .xbar_bridge_id_ar({slave.name}_axi_bridge_id_ar),")
                lines.append(f"        .rid_bridge_id({slave.name}_axi_rid_bridge_id),")
                lines.append(f"        .rid_valid({slave.name}_axi_rid_valid)")

            lines.append("    );")
            lines.append("")

        return lines

    def _generate_apb_shims(self) -> List[str]:
        """
        Generate axi4_to_apb_shim instantiations for APB slaves.

        Converts crossbar AXI4 slave outputs to external APB ports.
        """
        lines = []

        # Filter for APB slaves only
        apb_slaves = [s for s in self.slaves if s.protocol == 'apb']

        if not apb_slaves:
            return lines

        lines.append("    // ================================================================")
        lines.append("    // APB Shim Instantiations")
        lines.append("    // Converts crossbar AXI4 outputs to APB protocol")
        lines.append("    // ================================================================")
        lines.append("")

        for slave in apb_slaves:
            # Crossbar AXI4 output prefix (matches crossbar-generated signals)
            axi_prefix = f"xbar_{slave.name}_axi_"
            # External APB port prefix (from slave config)
            apb_prefix = slave.prefix if hasattr(slave, 'prefix') and slave.prefix else f"{slave.name}_"
            if apb_prefix.endswith('_'):
                apb_prefix = apb_prefix[:-1]

            # APB slave native widths
            apb_data_width = slave.data_width
            apb_addr_width = 32  # Use global 32-bit address width

            # AXI4 interface widths (must match _generate_internal_signals() logic)
            # All slaves (including APB) use their native data width at crossbar interface
            # Width adaptation happens in master adapter, not at crossbar/APB converter
            axi_addr_width = 32  # Global 32-bit address width
            axi_data_width = slave.data_width  # APB slave's native width

            lines.append(f"    // APB Shim: {slave.name}")
            lines.append(f"    // Crossbar AXI4 ({axi_addr_width}b addr, {axi_data_width}b data) → External APB ({apb_addr_width}b addr, {apb_data_width}b data)")
            lines.append(f"    axi4_to_apb_shim #(")
            lines.append(f"        .DEPTH_AW(2),")
            lines.append(f"        .DEPTH_W(4),")
            lines.append(f"        .DEPTH_B(2),")
            lines.append(f"        .DEPTH_AR(2),")
            lines.append(f"        .DEPTH_R(4),")
            lines.append(f"        .SIDE_DEPTH(4),")
            lines.append(f"        .APB_CMD_DEPTH(4),")
            lines.append(f"        .APB_RSP_DEPTH(4),")
            lines.append(f"        .AXI_ID_WIDTH(4),")  # Standard 4-bit ID
            lines.append(f"        .AXI_ADDR_WIDTH({axi_addr_width}),")
            lines.append(f"        .AXI_DATA_WIDTH({axi_data_width}),")
            lines.append(f"        .AXI_USER_WIDTH(1),")
            lines.append(f"        .APB_ADDR_WIDTH({apb_addr_width}),")
            lines.append(f"        .APB_DATA_WIDTH({apb_data_width})")
            lines.append(f"    ) u_apb_shim_{slave.name} (")
            lines.append(f"        .aclk(aclk),")
            lines.append(f"        .aresetn(aresetn),")
            lines.append(f"        .pclk(aclk),")  # Same clock domain for now
            lines.append(f"        .presetn(aresetn),")
            lines.append(f"        ")
            lines.append(f"        // AXI4 Slave (from crossbar)")

            # Determine which channels to connect based on connecting masters
            connecting_masters = self._get_masters_connecting_to_slave(slave)
            has_write = any(m.channels in ["wr", "rw"] for m in connecting_masters)
            has_read = any(m.channels in ["rd", "rw"] for m in connecting_masters)

            # Get ID width from first connecting master
            id_width = connecting_masters[0].id_width if connecting_masters else 4

            # Write channels - connect or tie off
            if has_write:
                lines.append(f"        .s_axi_awid({axi_prefix}awid),")
                lines.append(f"        .s_axi_awaddr({axi_prefix}awaddr),")
                lines.append(f"        .s_axi_awlen({axi_prefix}awlen),")
                lines.append(f"        .s_axi_awsize({axi_prefix}awsize),")
                lines.append(f"        .s_axi_awburst({axi_prefix}awburst),")
                lines.append(f"        .s_axi_awlock({axi_prefix}awlock),")
                lines.append(f"        .s_axi_awcache({axi_prefix}awcache),")
                lines.append(f"        .s_axi_awprot({axi_prefix}awprot),")
                lines.append(f"        .s_axi_awqos(4'b0),")
                lines.append(f"        .s_axi_awregion(4'b0),")
                lines.append(f"        .s_axi_awuser(1'b0),")
                lines.append(f"        .s_axi_awvalid({axi_prefix}awvalid),")
                lines.append(f"        .s_axi_awready({axi_prefix}awready),")
                lines.append(f"        .s_axi_wdata({axi_prefix}wdata),")
                lines.append(f"        .s_axi_wstrb({axi_prefix}wstrb),")
                lines.append(f"        .s_axi_wlast({axi_prefix}wlast),")
                lines.append(f"        .s_axi_wuser(1'b0),")
                lines.append(f"        .s_axi_wvalid({axi_prefix}wvalid),")
                lines.append(f"        .s_axi_wready({axi_prefix}wready),")
                lines.append(f"        .s_axi_bid({axi_prefix}bid),")
                lines.append(f"        .s_axi_bresp({axi_prefix}bresp),")
                lines.append(f"        .s_axi_buser(),")
                lines.append(f"        .s_axi_bvalid({axi_prefix}bvalid),")
                lines.append(f"        .s_axi_bready({axi_prefix}bready),")
            else:
                # Tie off write channels for read-only bridge
                lines.append(f"        // Write channels tied off (read-only bridge)")
                lines.append(f"        .s_axi_awid({id_width}'b0),")
                lines.append(f"        .s_axi_awaddr(32'b0),")
                lines.append(f"        .s_axi_awlen(8'b0),")
                lines.append(f"        .s_axi_awsize(3'b0),")
                lines.append(f"        .s_axi_awburst(2'b0),")
                lines.append(f"        .s_axi_awlock(1'b0),")
                lines.append(f"        .s_axi_awcache(4'b0),")
                lines.append(f"        .s_axi_awprot(3'b0),")
                lines.append(f"        .s_axi_awqos(4'b0),")
                lines.append(f"        .s_axi_awregion(4'b0),")
                lines.append(f"        .s_axi_awuser(1'b0),")
                lines.append(f"        .s_axi_awvalid(1'b0),")
                lines.append(f"        .s_axi_awready(),  // Unconnected")
                # Use slave's AXI4 interface width (matches APB shim parameter)
                strb_width = axi_data_width // 8
                lines.append(f"        .s_axi_wdata({axi_data_width}'b0),")
                lines.append(f"        .s_axi_wstrb({strb_width}'b0),")
                lines.append(f"        .s_axi_wlast(1'b0),")
                lines.append(f"        .s_axi_wuser(1'b0),")
                lines.append(f"        .s_axi_wvalid(1'b0),")
                lines.append(f"        .s_axi_wready(),  // Unconnected")
                lines.append(f"        .s_axi_bid(),  // Unconnected")
                lines.append(f"        .s_axi_bresp(),  // Unconnected")
                lines.append(f"        .s_axi_buser(),  // Unconnected")
                lines.append(f"        .s_axi_bvalid(),  // Unconnected")
                lines.append(f"        .s_axi_bready(1'b0),")
            lines.append(f"        ")

            # Read channels - connect or tie off
            if has_read:
                lines.append(f"        .s_axi_arid({axi_prefix}arid),")
                lines.append(f"        .s_axi_araddr({axi_prefix}araddr),")
                lines.append(f"        .s_axi_arlen({axi_prefix}arlen),")
                lines.append(f"        .s_axi_arsize({axi_prefix}arsize),")
                lines.append(f"        .s_axi_arburst({axi_prefix}arburst),")
                lines.append(f"        .s_axi_arlock({axi_prefix}arlock),")
                lines.append(f"        .s_axi_arcache({axi_prefix}arcache),")
                lines.append(f"        .s_axi_arprot({axi_prefix}arprot),")
                lines.append(f"        .s_axi_arqos(4'b0),")
                lines.append(f"        .s_axi_arregion(4'b0),")
                lines.append(f"        .s_axi_aruser(1'b0),")
                lines.append(f"        .s_axi_arvalid({axi_prefix}arvalid),")
                lines.append(f"        .s_axi_arready({axi_prefix}arready),")
                lines.append(f"        .s_axi_rid({axi_prefix}rid),")
                lines.append(f"        .s_axi_rdata({axi_prefix}rdata),")
                lines.append(f"        .s_axi_rresp({axi_prefix}rresp),")
                lines.append(f"        .s_axi_rlast({axi_prefix}rlast),")
                lines.append(f"        .s_axi_ruser(),")
                lines.append(f"        .s_axi_rvalid({axi_prefix}rvalid),")
                lines.append(f"        .s_axi_rready({axi_prefix}rready),")
            else:
                # Tie off read channels for write-only bridge
                lines.append(f"        // Read channels tied off (write-only bridge)")
                lines.append(f"        .s_axi_arid({id_width}'b0),")
                lines.append(f"        .s_axi_araddr(32'b0),")
                lines.append(f"        .s_axi_arlen(8'b0),")
                lines.append(f"        .s_axi_arsize(3'b0),")
                lines.append(f"        .s_axi_arburst(2'b0),")
                lines.append(f"        .s_axi_arlock(1'b0),")
                lines.append(f"        .s_axi_arcache(4'b0),")
                lines.append(f"        .s_axi_arprot(3'b0),")
                lines.append(f"        .s_axi_arqos(4'b0),")
                lines.append(f"        .s_axi_arregion(4'b0),")
                lines.append(f"        .s_axi_aruser(1'b0),")
                lines.append(f"        .s_axi_arvalid(1'b0),")
                lines.append(f"        .s_axi_arready(),  // Unconnected")
                lines.append(f"        .s_axi_rid(),  // Unconnected")
                # Get data width from first connecting master
                data_width = connecting_masters[0].data_width if connecting_masters else 64
                lines.append(f"        .s_axi_rdata(),  // Unconnected")
                lines.append(f"        .s_axi_rresp(),  // Unconnected")
                lines.append(f"        .s_axi_rlast(),  // Unconnected")
                lines.append(f"        .s_axi_ruser(),  // Unconnected")
                lines.append(f"        .s_axi_rvalid(),  // Unconnected")
                lines.append(f"        .s_axi_rready(1'b0),")
            lines.append(f"        ")
            lines.append(f"        // APB Master (to external APB slave)")
            lines.append(f"        .m_apb_PSEL({apb_prefix}_PSEL),")
            lines.append(f"        .m_apb_PADDR({apb_prefix}_PADDR),")
            lines.append(f"        .m_apb_PENABLE({apb_prefix}_PENABLE),")
            lines.append(f"        .m_apb_PWRITE({apb_prefix}_PWRITE),")
            lines.append(f"        .m_apb_PWDATA({apb_prefix}_PWDATA),")
            lines.append(f"        .m_apb_PSTRB({apb_prefix}_PSTRB),")
            lines.append(f"        .m_apb_PPROT({apb_prefix}_PPROT),")
            lines.append(f"        .m_apb_PRDATA({apb_prefix}_PRDATA),")
            lines.append(f"        .m_apb_PREADY({apb_prefix}_PREADY),")
            lines.append(f"        .m_apb_PSLVERR({apb_prefix}_PSLVERR)")
            lines.append(f"    );")
            lines.append(f"")

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
