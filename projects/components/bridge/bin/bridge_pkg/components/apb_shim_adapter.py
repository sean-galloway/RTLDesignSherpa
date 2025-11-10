#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# APB Shim Adapter Component - APB protocol conversion wrapper
#
# Generates APB shim instantiations for APB slaves
# Uses axi4_to_apb_shim from projects/components/converters/rtl/

from typing import List, Dict


class ApbShimAdapter:
    """
    Generate APB shim instantiation for APB slaves

    This component creates instantiations of axi4_to_apb_shim for each
    APB slave that a master connects to. The shim handles:
    - AXI4 to APB protocol conversion
    - Burst splitting (AXI burst → sequential APB transactions)
    - Clock domain crossing (aclk → pclk)
    - Response mapping (PSLVERR → BRESP/RRESP)

    Architecture:
        AXI4 Interface → axi4_slave_stub → axi4_to_apb_convert →
        CDC handshake → apb_master_stub → APB Interface

    Example:
        Master connects to: DDR (AXI4), UART (APB), GPIO (APB)
        Generated:
            - Direct AXI4 path to DDR
            - axi4_to_apb_shim instance for UART
            - axi4_to_apb_shim instance for GPIO
    """

    def __init__(self, master_config, all_slaves: List):
        """
        Initialize APB shim adapter for one master

        Args:
            master_config: MasterConfig object with master port info
            all_slaves: List of all SlaveInfo objects
        """
        self.master = master_config
        self.all_slaves = all_slaves

        # Filter to connected slaves based on master_config.slave_connections
        self.connected_slaves = [all_slaves[idx] for idx in self.master.slave_connections]

        # Further filter to APB slaves only
        self.apb_slaves = [s for s in self.connected_slaves if s.protocol == 'apb']

    def has_apb_slaves(self) -> bool:
        """Check if this master connects to any APB slaves"""
        return len(self.apb_slaves) > 0

    def generate_signals(self) -> List[str]:
        """
        Generate internal signal declarations for APB shim connections

        Returns:
            List of signal declaration strings
        """
        if not self.has_apb_slaves():
            return []

        signals = []
        signals.append(f"    // ================================================================")
        signals.append(f"    // APB Shim Signals for {self.master.name}")
        signals.append(f"    // ================================================================")
        signals.append(f"")

        for slave in self.apb_slaves:
            shim_prefix = f"{self.master.name}_{slave.name}_apb"
            apb_data_width = slave.data_width
            apb_addr_width = slave.addr_width
            apb_strb_width = apb_data_width // 8

            signals.append(f"    // APB shim signals for {slave.name}")
            signals.append(f"    logic                                  {shim_prefix}_psel;")
            signals.append(f"    logic [{apb_addr_width-1}:0]           {shim_prefix}_paddr;")
            signals.append(f"    logic                                  {shim_prefix}_penable;")
            signals.append(f"    logic                                  {shim_prefix}_pwrite;")
            signals.append(f"    logic [{apb_data_width-1}:0]           {shim_prefix}_pwdata;")
            signals.append(f"    logic [{apb_strb_width-1}:0]           {shim_prefix}_pstrb;")
            signals.append(f"    logic [2:0]                            {shim_prefix}_pprot;")
            signals.append(f"    logic [{apb_data_width-1}:0]           {shim_prefix}_prdata;")
            signals.append(f"    logic                                  {shim_prefix}_pready;")
            signals.append(f"    logic                                  {shim_prefix}_pslverr;")
            signals.append(f"")

        return signals

    def generate_shims(self) -> List[str]:
        """
        Generate APB shim instantiations

        Returns:
            List of RTL instantiation strings
        """
        if not self.has_apb_slaves():
            return []

        instructions = []
        instructions.append(f"    // ================================================================")
        instructions.append(f"    // APB Shim Instances for {self.master.name}")
        instructions.append(f"    // Converts AXI4 to APB protocol for APB slaves")
        instructions.append(f"    // ================================================================")
        instructions.append(f"")

        for slave in self.apb_slaves:
            shim_prefix = f"{self.master.name}_{slave.name}_apb"
            axi_data_width = self.master.data_width
            apb_data_width = slave.data_width
            apb_addr_width = slave.addr_width

            instructions.append(f"    // APB Shim: {self.master.name} → {slave.name}")
            instructions.append(f"    // AXI4({axi_data_width}b) → APB({apb_data_width}b)")
            instructions.append(f"    axi4_to_apb_shim #(")
            instructions.append(f"        .DEPTH_AW(2),")
            instructions.append(f"        .DEPTH_W(4),")
            instructions.append(f"        .DEPTH_B(2),")
            instructions.append(f"        .DEPTH_AR(2),")
            instructions.append(f"        .DEPTH_R(4),")
            instructions.append(f"        .SIDE_DEPTH(4),")
            instructions.append(f"        .APB_CMD_DEPTH(4),")
            instructions.append(f"        .APB_RSP_DEPTH(4),")
            instructions.append(f"        .AXI_ID_WIDTH({self.master.id_width}),")
            instructions.append(f"        .AXI_ADDR_WIDTH({self.master.addr_width}),")
            instructions.append(f"        .AXI_DATA_WIDTH({axi_data_width}),")
            instructions.append(f"        .AXI_USER_WIDTH(1),")
            instructions.append(f"        .APB_ADDR_WIDTH({apb_addr_width}),")
            instructions.append(f"        .APB_DATA_WIDTH({apb_data_width})")
            instructions.append(f"    ) u_apb_shim_{slave.name} (")
            instructions.append(f"        // Clocks and Resets")
            instructions.append(f"        .aclk(aclk),")
            instructions.append(f"        .aresetn(aresetn),")
            instructions.append(f"        .pclk(aclk),  // APB on same clock domain for now")
            instructions.append(f"        .presetn(aresetn),")
            instructions.append(f"        ")
            instructions.append(f"        // AXI4 Slave Interface (from wrapper output)")

            # AXI4 write channels (if master has write capability)
            if self.master.channels in ["wr", "rw"]:
                instructions.append(f"        // Write Address Channel")
                instructions.append(f"        .s_axi_awid(fub_axi_awid),")
                instructions.append(f"        .s_axi_awaddr(fub_axi_awaddr),")
                instructions.append(f"        .s_axi_awlen(fub_axi_awlen),")
                instructions.append(f"        .s_axi_awsize(fub_axi_awsize),")
                instructions.append(f"        .s_axi_awburst(fub_axi_awburst),")
                instructions.append(f"        .s_axi_awlock(fub_axi_awlock),")
                instructions.append(f"        .s_axi_awcache(fub_axi_awcache),")
                instructions.append(f"        .s_axi_awprot(fub_axi_awprot),")
                instructions.append(f"        .s_axi_awqos(4'b0),")
                instructions.append(f"        .s_axi_awregion(4'b0),")
                instructions.append(f"        .s_axi_awuser(1'b0),")
                instructions.append(f"        .s_axi_awvalid(fub_axi_awvalid),")
                instructions.append(f"        .s_axi_awready(fub_axi_awready),")
                instructions.append(f"        // Write Data Channel")
                instructions.append(f"        .s_axi_wdata(fub_axi_wdata),")
                instructions.append(f"        .s_axi_wstrb(fub_axi_wstrb),")
                instructions.append(f"        .s_axi_wlast(fub_axi_wlast),")
                instructions.append(f"        .s_axi_wuser(1'b0),")
                instructions.append(f"        .s_axi_wvalid(fub_axi_wvalid),")
                instructions.append(f"        .s_axi_wready(fub_axi_wready),")
                instructions.append(f"        // Write Response Channel")
                instructions.append(f"        .s_axi_bid(fub_axi_bid),")
                instructions.append(f"        .s_axi_bresp(fub_axi_bresp),")
                instructions.append(f"        .s_axi_buser(),")
                instructions.append(f"        .s_axi_bvalid(fub_axi_bvalid),")
                instructions.append(f"        .s_axi_bready(fub_axi_bready),")
            else:
                # Write channels tied off for read-only masters
                instructions.append(f"        // Write Address Channel (tied off)")
                instructions.append(f"        .s_axi_awid({self.master.id_width}'b0),")
                instructions.append(f"        .s_axi_awaddr({self.master.addr_width}'b0),")
                instructions.append(f"        .s_axi_awlen(8'b0),")
                instructions.append(f"        .s_axi_awsize(3'b0),")
                instructions.append(f"        .s_axi_awburst(2'b0),")
                instructions.append(f"        .s_axi_awlock(1'b0),")
                instructions.append(f"        .s_axi_awcache(4'b0),")
                instructions.append(f"        .s_axi_awprot(3'b0),")
                instructions.append(f"        .s_axi_awqos(4'b0),")
                instructions.append(f"        .s_axi_awregion(4'b0),")
                instructions.append(f"        .s_axi_awuser(1'b0),")
                instructions.append(f"        .s_axi_awvalid(1'b0),")
                instructions.append(f"        .s_axi_awready(),")
                instructions.append(f"        // Write Data Channel (tied off)")
                instructions.append(f"        .s_axi_wdata({axi_data_width}'b0),")
                instructions.append(f"        .s_axi_wstrb({axi_data_width//8}'b0),")
                instructions.append(f"        .s_axi_wlast(1'b0),")
                instructions.append(f"        .s_axi_wuser(1'b0),")
                instructions.append(f"        .s_axi_wvalid(1'b0),")
                instructions.append(f"        .s_axi_wready(),")
                instructions.append(f"        // Write Response Channel (tied off)")
                instructions.append(f"        .s_axi_bid(),")
                instructions.append(f"        .s_axi_bresp(),")
                instructions.append(f"        .s_axi_buser(),")
                instructions.append(f"        .s_axi_bvalid(),")
                instructions.append(f"        .s_axi_bready(1'b0),")

            # AXI4 read channels (if master has read capability)
            if self.master.channels in ["rd", "rw"]:
                instructions.append(f"        // Read Address Channel")
                instructions.append(f"        .s_axi_arid(fub_axi_arid),")
                instructions.append(f"        .s_axi_araddr(fub_axi_araddr),")
                instructions.append(f"        .s_axi_arlen(fub_axi_arlen),")
                instructions.append(f"        .s_axi_arsize(fub_axi_arsize),")
                instructions.append(f"        .s_axi_arburst(fub_axi_arburst),")
                instructions.append(f"        .s_axi_arlock(fub_axi_arlock),")
                instructions.append(f"        .s_axi_arcache(fub_axi_arcache),")
                instructions.append(f"        .s_axi_arprot(fub_axi_arprot),")
                instructions.append(f"        .s_axi_arqos(4'b0),")
                instructions.append(f"        .s_axi_arregion(4'b0),")
                instructions.append(f"        .s_axi_aruser(1'b0),")
                instructions.append(f"        .s_axi_arvalid(fub_axi_arvalid),")
                instructions.append(f"        .s_axi_arready(fub_axi_arready),")
                instructions.append(f"        // Read Data Channel")
                instructions.append(f"        .s_axi_rid(fub_axi_rid),")
                instructions.append(f"        .s_axi_rdata(fub_axi_rdata),")
                instructions.append(f"        .s_axi_rresp(fub_axi_rresp),")
                instructions.append(f"        .s_axi_rlast(fub_axi_rlast),")
                instructions.append(f"        .s_axi_ruser(),")
                instructions.append(f"        .s_axi_rvalid(fub_axi_rvalid),")
                instructions.append(f"        .s_axi_rready(fub_axi_rready),")
            else:
                # Read channels tied off for write-only masters
                instructions.append(f"        // Read Address Channel (tied off)")
                instructions.append(f"        .s_axi_arid({self.master.id_width}'b0),")
                instructions.append(f"        .s_axi_araddr({self.master.addr_width}'b0),")
                instructions.append(f"        .s_axi_arlen(8'b0),")
                instructions.append(f"        .s_axi_arsize(3'b0),")
                instructions.append(f"        .s_axi_arburst(2'b0),")
                instructions.append(f"        .s_axi_arlock(1'b0),")
                instructions.append(f"        .s_axi_arcache(4'b0),")
                instructions.append(f"        .s_axi_arprot(3'b0),")
                instructions.append(f"        .s_axi_arqos(4'b0),")
                instructions.append(f"        .s_axi_arregion(4'b0),")
                instructions.append(f"        .s_axi_aruser(1'b0),")
                instructions.append(f"        .s_axi_arvalid(1'b0),")
                instructions.append(f"        .s_axi_arready(),")
                instructions.append(f"        // Read Data Channel (tied off)")
                instructions.append(f"        .s_axi_rid(),")
                instructions.append(f"        .s_axi_rdata(),")
                instructions.append(f"        .s_axi_rresp(),")
                instructions.append(f"        .s_axi_rlast(),")
                instructions.append(f"        .s_axi_ruser(),")
                instructions.append(f"        .s_axi_rvalid(),")
                instructions.append(f"        .s_axi_rready(1'b0),")

            # APB Master Interface
            instructions.append(f"        ")
            instructions.append(f"        // APB Master Interface (to {slave.name})")
            instructions.append(f"        .m_apb_psel({shim_prefix}_psel),")
            instructions.append(f"        .m_apb_paddr({shim_prefix}_paddr),")
            instructions.append(f"        .m_apb_penable({shim_prefix}_penable),")
            instructions.append(f"        .m_apb_pwrite({shim_prefix}_pwrite),")
            instructions.append(f"        .m_apb_pwdata({shim_prefix}_pwdata),")
            instructions.append(f"        .m_apb_pstrb({shim_prefix}_pstrb),")
            instructions.append(f"        .m_apb_pprot({shim_prefix}_pprot),")
            instructions.append(f"        .m_apb_prdata({shim_prefix}_prdata),")
            instructions.append(f"        .m_apb_pready({shim_prefix}_pready),")
            instructions.append(f"        .m_apb_pslverr({shim_prefix}_pslverr)")
            instructions.append(f"    );")
            instructions.append(f"")

        return instructions

    def generate_apb_connections(self) -> List[str]:
        """
        Generate connections from APB shim outputs to external APB slave ports

        Returns:
            List of RTL assignment strings
        """
        if not self.has_apb_slaves():
            return []

        instructions = []
        instructions.append(f"    // ================================================================")
        instructions.append(f"    // APB Slave Connections for {self.master.name}")
        instructions.append(f"    // ================================================================")
        instructions.append(f"")

        for slave in self.apb_slaves:
            shim_prefix = f"{self.master.name}_{slave.name}_apb"
            # Note: SlaveInfo doesn't have prefix attribute, will use slave.name directly
            # External APB ports should use the slave's defined prefix

            instructions.append(f"    // {self.master.name} → {slave.name} (APB)")
            instructions.append(f"    // APB shim outputs → External APB slave ports")
            instructions.append(f"    // TODO: Connect to external {slave.name} APB ports")
            instructions.append(f"    // These connections are typically made at the bridge top level")
            instructions.append(f"")

        return instructions
