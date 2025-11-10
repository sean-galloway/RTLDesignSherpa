#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Channel Mux Component - Grant-based master-to-slave routing

from typing import List
from .slave_width_adapter import SlaveWidthAdapter


class ChannelMuxComponent:
    """
    Generate grant-based muxing logic from masters to slaves

    This component generates combinational logic that:
    1. Muxes winning master's signals to slave based on arbiter grant
    2. Routes slave ready/response signals back to winning master
    3. Handles all 5 AXI4 channels (AW, W, B, AR, R)
    4. Supports channel-specific masters (wr/rd/rw)

    Example Output (AW Channel):
        // AW Channel Mux to Slave 0
        always_comb begin
            ddr_s_axi_awaddr  = '0;
            ddr_s_axi_awvalid = 1'b0;
            ddr_s_axi_awid    = '0;
            // ... more signals

            case (aw_grant_s0)  // One-hot grant
                1'b1: begin  // Master 0 won
                    ddr_s_axi_awaddr  = xbar_m_awaddr[0];
                    ddr_s_axi_awvalid = xbar_m_awvalid[0];
                    ddr_s_axi_awid    = xbar_m_awid[0];
                    // ... more signals
                end
                default: begin
                    // No master granted - outputs stay at 0
                end
            endcase
        end

        // Route ready back to winning master
        always_comb begin
            xbar_m_awready = '0;
            case (aw_grant_s0)
                1'b1: xbar_m_awready[0] = ddr_s_axi_awready;
                default: xbar_m_awready = '0;
            endcase
        end
    """

    def __init__(self, masters: List, slaves: List,
                 data_width: int, addr_width: int, id_width: int, slave_id_width: int):
        """
        Initialize channel mux component

        Args:
            masters: List of PortSpec objects for masters
            slaves: List of PortSpec objects for slaves
            data_width: Crossbar data width
            addr_width: Crossbar address width
            id_width: Master-side ID width
            slave_id_width: Slave-side ID width (master ID + routing bits)
        """
        self.masters = masters
        self.slaves = slaves
        self.data_width = data_width
        self.addr_width = addr_width
        self.id_width = id_width
        self.slave_id_width = slave_id_width
        self.strb_width = data_width // 8

    def generate_aw_channel_mux(self, slave_idx: int, slave) -> List[str]:
        """Generate AW channel mux logic for one slave"""
        instructions = []

        if not slave.has_write_channels():
            return instructions  # Skip if slave doesn't support writes

        num_masters = len(self.masters)

        # Create slave width adapter to get correct signal prefix
        adapter = SlaveWidthAdapter(slave_idx, slave, self.data_width, self.slave_id_width, num_masters)
        prefix = adapter.get_aw_signal_prefix()
        id_width = adapter.get_id_width()  # Use slave's ID width or crossbar ID width

        # Calculate mb_id width based on number of masters
        # 1 master needs 0 bits (but enforce minimum of 1)
        # 2 masters need 1 bit, 4 masters need 2 bits, etc.
        mb_id_width = max(1, (num_masters - 1).bit_length() if num_masters > 1 else 0)

        instructions.append(f"// AW Channel Mux to Slave {slave_idx}: {slave.port_name}")
        if adapter.needs_conversion():
            instructions.append(f"// Routes to width converter ({self.data_width}b → {slave.data_width}b)")
        instructions.append("always_comb begin")
        instructions.append(f"    // Default: no master selected")
        instructions.append(f"    {prefix}awaddr  = {self.addr_width}'b0;")
        instructions.append(f"    {prefix}awid    = 8'b0;")  # HARD LIMIT: 8-bit ID for all agents
        instructions.append(f"    {prefix}awmb_id = {mb_id_width}'b0;")
        instructions.append(f"    {prefix}awlen   = 8'b0;")
        instructions.append(f"    {prefix}awsize  = 3'b0;")
        instructions.append(f"    {prefix}awburst = 2'b0;")
        instructions.append(f"    {prefix}awlock  = 1'b0;")
        instructions.append(f"    {prefix}awcache = 4'b0;")
        instructions.append(f"    {prefix}awprot  = 3'b0;")
        instructions.append(f"    {prefix}awvalid = 1'b0;")
        instructions.append("")
        instructions.append(f"    case (aw_grant_s{slave_idx})  // One-hot grant")

        # Generate case for each master
        for master_idx, master in enumerate(self.masters):
            if not master.has_write_channels():
                continue  # Skip read-only masters

            grant_bit = f"{num_masters}'b" + "0" * (num_masters - master_idx - 1) + "1" + "0" * master_idx

            instructions.append(f"        {grant_bit}: begin  // Master {master_idx}: {master.port_name}")
            instructions.append(f"            {prefix}awaddr  = xbar_m_awaddr[{master_idx}];")
            instructions.append(f"            {prefix}awid    = xbar_m_awid[{master_idx}];")
            instructions.append(f"            {prefix}awmb_id = {mb_id_width}'d{master_idx};")
            instructions.append(f"            {prefix}awlen   = xbar_m_awlen[{master_idx}];")
            instructions.append(f"            {prefix}awsize  = xbar_m_awsize[{master_idx}];")
            instructions.append(f"            {prefix}awburst = xbar_m_awburst[{master_idx}];")
            instructions.append(f"            {prefix}awlock  = xbar_m_awlock[{master_idx}];")
            instructions.append(f"            {prefix}awcache = xbar_m_awcache[{master_idx}];")
            instructions.append(f"            {prefix}awprot  = xbar_m_awprot[{master_idx}];")
            instructions.append(f"            {prefix}awvalid = xbar_m_awvalid[{master_idx}];")
            instructions.append(f"        end")

        instructions.append(f"        default: begin")
        instructions.append(f"            // No master granted - keep defaults")
        instructions.append(f"        end")
        instructions.append(f"    endcase")
        instructions.append("end")
        instructions.append("")

        # Route ready back
        instructions.append(f"// Route AW ready back to winning master for slave {slave_idx}")
        instructions.append("always_comb begin")
        instructions.append(f"    // Default: set all elements to 0 (unpacked array)")
        instructions.append(f"    for (int i = 0; i < {num_masters}; i++) begin")
        instructions.append(f"        xbar_m_awready[i] = 1'b0;")
        instructions.append(f"    end")
        instructions.append("")
        instructions.append(f"    case (aw_grant_s{slave_idx})")

        for master_idx, master in enumerate(self.masters):
            if not master.has_write_channels():
                continue

            grant_bit = f"{num_masters}'b" + "0" * (num_masters - master_idx - 1) + "1" + "0" * master_idx
            instructions.append(f"        {grant_bit}: xbar_m_awready[{master_idx}] = {prefix}awready;")

        instructions.append(f"        default: begin")
        instructions.append(f"            // Keep defaults")
        instructions.append(f"        end")
        instructions.append(f"    endcase")
        instructions.append("end")
        instructions.append("")

        return instructions

    def generate_w_channel_mux(self, slave_idx: int, slave) -> List[str]:
        """Generate W channel mux logic for one slave"""
        instructions = []

        if not slave.has_write_channels():
            return instructions

        num_masters = len(self.masters)

        # Create slave width adapter to get correct signal prefix
        adapter = SlaveWidthAdapter(slave_idx, slave, self.data_width, self.slave_id_width, num_masters)
        prefix = adapter.get_w_signal_prefix()

        # Determine target signal widths (slave width for direct/APB, crossbar width for converters)
        target_data_width = slave.data_width if not adapter.needs_conversion() else self.data_width
        target_strb_width = slave.data_width // 8 if not adapter.needs_conversion() else self.strb_width

        instructions.append(f"// W Channel Mux to Slave {slave_idx}: {slave.port_name}")
        instructions.append(f"// W follows AW grant (locked until WLAST)")
        if adapter.needs_conversion():
            instructions.append(f"// Routes to width converter ({self.data_width}b → {slave.data_width}b)")
        instructions.append("always_comb begin")
        instructions.append(f"    {prefix}wdata  = {target_data_width}'b0;")
        instructions.append(f"    {prefix}wstrb  = {target_strb_width}'b0;")
        instructions.append(f"    {prefix}wlast  = 1'b0;")
        instructions.append(f"    {prefix}wvalid = 1'b0;")
        instructions.append("")
        instructions.append(f"    case (aw_grant_s{slave_idx})  // W follows AW grant")

        for master_idx, master in enumerate(self.masters):
            if not master.has_write_channels():
                continue

            grant_bit = f"{num_masters}'b" + "0" * (num_masters - master_idx - 1) + "1" + "0" * master_idx

            instructions.append(f"        {grant_bit}: begin")
            # Width-aware assignment: truncate to slave width if direct connection
            if adapter.needs_conversion():
                instructions.append(f"            {prefix}wdata  = xbar_m_wdata[{master_idx}];")
                instructions.append(f"            {prefix}wstrb  = xbar_m_wstrb[{master_idx}];")
            else:
                instructions.append(f"            {prefix}wdata  = xbar_m_wdata[{master_idx}][{target_data_width-1}:0];  // Truncate to slave width")
                instructions.append(f"            {prefix}wstrb  = xbar_m_wstrb[{master_idx}][{target_strb_width-1}:0];  // Truncate to slave strb width")
            instructions.append(f"            {prefix}wlast  = xbar_m_wlast[{master_idx}];")
            instructions.append(f"            {prefix}wvalid = xbar_m_wvalid[{master_idx}];")
            instructions.append(f"        end")

        instructions.append(f"        default: begin")
        instructions.append(f"            // No grant")
        instructions.append(f"        end")
        instructions.append(f"    endcase")
        instructions.append("end")
        instructions.append("")

        # Route ready back
        instructions.append(f"// Route W ready back")
        instructions.append("always_comb begin")
        instructions.append(f"    // Default: set all elements to 0 (unpacked array)")
        instructions.append(f"    for (int i = 0; i < {num_masters}; i++) begin")
        instructions.append(f"        xbar_m_wready[i] = 1'b0;")
        instructions.append(f"    end")
        instructions.append("")
        instructions.append(f"    case (aw_grant_s{slave_idx})")

        for master_idx, master in enumerate(self.masters):
            if not master.has_write_channels():
                continue

            grant_bit = f"{num_masters}'b" + "0" * (num_masters - master_idx - 1) + "1" + "0" * master_idx
            instructions.append(f"        {grant_bit}: xbar_m_wready[{master_idx}] = {prefix}wready;")

        instructions.append(f"        default: begin")
        instructions.append(f"            // Keep defaults")
        instructions.append(f"        end")
        instructions.append(f"    endcase")
        instructions.append("end")
        instructions.append("")

        return instructions

    def generate_ar_channel_mux(self, slave_idx: int, slave) -> List[str]:
        """Generate AR channel mux logic for one slave"""
        instructions = []

        if not slave.has_read_channels():
            return instructions

        num_masters = len(self.masters)

        # Create slave width adapter to get correct signal prefix
        adapter = SlaveWidthAdapter(slave_idx, slave, self.data_width, self.slave_id_width, num_masters)
        prefix = adapter.get_ar_signal_prefix()
        id_width = adapter.get_id_width()  # Use slave's ID width or crossbar ID width

        # Calculate mb_id width based on number of masters
        # 1 master needs 0 bits (but enforce minimum of 1)
        # 2 masters need 1 bit, 4 masters need 2 bits, etc.
        mb_id_width = max(1, (num_masters - 1).bit_length() if num_masters > 1 else 0)

        instructions.append(f"// AR Channel Mux to Slave {slave_idx}: {slave.port_name}")
        if adapter.needs_conversion():
            instructions.append(f"// Routes to width converter ({self.data_width}b → {slave.data_width}b)")
        instructions.append("always_comb begin")
        instructions.append(f"    {prefix}araddr  = {self.addr_width}'b0;")
        instructions.append(f"    {prefix}arid    = 8'b0;")  # HARD LIMIT: 8-bit ID for all agents
        instructions.append(f"    {prefix}armb_id = {mb_id_width}'b0;")
        instructions.append(f"    {prefix}arlen   = 8'b0;")
        instructions.append(f"    {prefix}arsize  = 3'b0;")
        instructions.append(f"    {prefix}arburst = 2'b0;")
        instructions.append(f"    {prefix}arlock  = 1'b0;")
        instructions.append(f"    {prefix}arcache = 4'b0;")
        instructions.append(f"    {prefix}arprot  = 3'b0;")
        instructions.append(f"    {prefix}arvalid = 1'b0;")
        instructions.append("")
        instructions.append(f"    case (ar_grant_s{slave_idx})")

        for master_idx, master in enumerate(self.masters):
            if not master.has_read_channels():
                continue

            grant_bit = f"{num_masters}'b" + "0" * (num_masters - master_idx - 1) + "1" + "0" * master_idx

            instructions.append(f"        {grant_bit}: begin")
            instructions.append(f"            {prefix}araddr  = xbar_m_araddr[{master_idx}];")
            instructions.append(f"            {prefix}arid    = xbar_m_arid[{master_idx}];")
            instructions.append(f"            {prefix}armb_id = {mb_id_width}'d{master_idx};")
            instructions.append(f"            {prefix}arlen   = xbar_m_arlen[{master_idx}];")
            instructions.append(f"            {prefix}arsize  = xbar_m_arsize[{master_idx}];")
            instructions.append(f"            {prefix}arburst = xbar_m_arburst[{master_idx}];")
            instructions.append(f"            {prefix}arlock  = xbar_m_arlock[{master_idx}];")
            instructions.append(f"            {prefix}arcache = xbar_m_arcache[{master_idx}];")
            instructions.append(f"            {prefix}arprot  = xbar_m_arprot[{master_idx}];")
            instructions.append(f"            {prefix}arvalid = xbar_m_arvalid[{master_idx}];")
            instructions.append(f"        end")

        instructions.append(f"        default: begin")
        instructions.append(f"        end")
        instructions.append(f"    endcase")
        instructions.append("end")
        instructions.append("")

        # Route ready back
        instructions.append(f"// Route AR ready back")
        instructions.append("always_comb begin")
        instructions.append(f"    // Default: set all elements to 0 (unpacked array)")
        instructions.append(f"    for (int i = 0; i < {num_masters}; i++) begin")
        instructions.append(f"        xbar_m_arready[i] = 1'b0;")
        instructions.append(f"    end")
        instructions.append("")
        instructions.append(f"    case (ar_grant_s{slave_idx})")

        for master_idx, master in enumerate(self.masters):
            if not master.has_read_channels():
                continue

            grant_bit = f"{num_masters}'b" + "0" * (num_masters - master_idx - 1) + "1" + "0" * master_idx
            instructions.append(f"        {grant_bit}: xbar_m_arready[{master_idx}] = {prefix}arready;")

        instructions.append(f"        default: begin")
        instructions.append(f"            // Keep defaults")
        instructions.append(f"        end")
        instructions.append(f"    endcase")
        instructions.append("end")
        instructions.append("")

        return instructions

    def generate_all_slave_muxes(self) -> List[str]:
        """Generate mux logic for all slaves"""
        instructions = []

        for slave_idx, slave in enumerate(self.slaves):
            instructions.append(f"// {'='*70}")
            instructions.append(f"// Channel Muxes for Slave {slave_idx}: {slave.port_name}")
            instructions.append(f"// {'='*70}")
            instructions.append("")

            # AW channel mux
            instructions.extend(self.generate_aw_channel_mux(slave_idx, slave))

            # W channel mux
            instructions.extend(self.generate_w_channel_mux(slave_idx, slave))

            # AR channel mux
            instructions.extend(self.generate_ar_channel_mux(slave_idx, slave))

            instructions.append("")

        return instructions


# Example usage
if __name__ == '__main__':
    import sys
    import os
    sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../..'))
    from bridge_pkg.config import PortSpec

    print("=" * 70)
    print("ChannelMuxComponent Test")
    print("=" * 70)
    print()

    # Test configuration
    masters = [
        PortSpec('cpu', 'master', 'axi4', 'wr', 'cpu_m_axi_', 64, 32, 4)
    ]

    slaves = [
        PortSpec('ddr', 'slave', 'axi4', 'rw', 'ddr_s_axi_', 64, 32, 4, 0x80000000, 0x80000000)
    ]

    mux = ChannelMuxComponent(masters, slaves, 64, 32, 4, 4)

    # Generate AW channel mux
    print("AW Channel Mux Example:")
    aw_insts = mux.generate_aw_channel_mux(0, slaves[0])
    for inst in aw_insts[:20]:  # First 20 lines
        print(inst)

    print()
    print("=" * 70)
    print("✓ ChannelMuxComponent test complete!")
    print("=" * 70)
