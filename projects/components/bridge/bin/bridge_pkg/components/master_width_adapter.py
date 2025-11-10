#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Master Width Adapter Component - Per-master width conversion wrapper
#
# Generates a wrapper module that:
# 1. Accepts master's native width AXI signals
# 2. Routes through appropriate width converters based on target slave
# 3. Outputs crossbar-width signals
# 4. Acts as pass-through when no conversion needed

from typing import List, Dict, Set


class MasterWidthAdapter:
    """
    Generate per-master width adapter module

    This component creates a wrapper that handles all width conversion
    for a single master port. It:
    - Determines which slaves the master connects to
    - Instantiates converters for each unique slave width
    - Muxes converter outputs based on address decode
    - Provides pass-through path when widths match

    Example:
        Master: 64b data, 4b ID
        Connects to slaves: 128b, 128b, 256b, 64b

        Generated module:
        - Instantiate 64→128 write converter
        - Instantiate 64→128 read converter
        - Instantiate 64→256 write converter
        - Instantiate 64→256 read converter
        - Pass-through path for 64b slave
        - Mux based on target slave
    """

    def __init__(self, master_idx: int, master, slaves: List,
                 connectivity: Dict[str, List[str]],
                 crossbar_data_width: int, crossbar_id_width: int):
        """
        Initialize adapter for one master

        Args:
            master_idx: Master index (0-based)
            master: PortSpec for the master
            slaves: List of all PortSpec slaves
            connectivity: Dict mapping master_name -> [slave_names]
            crossbar_data_width: Crossbar internal data width
            crossbar_id_width: Crossbar internal ID width

        Note:
            Interface wrappers (axi4_slave_rd/wr) are ALWAYS used.
            Converters always connect to fub_axi_* signals (wrapper outputs).
        """
        self.master_idx = master_idx
        self.master = master
        self.slaves = slaves
        self.connectivity = connectivity
        self.crossbar_data_width = crossbar_data_width
        self.crossbar_id_width = crossbar_id_width

        # Determine connected slaves and their widths
        self.connected_slaves = self._get_connected_slaves()
        self.unique_slave_widths = self._get_unique_slave_widths()

    def _get_connected_slaves(self) -> List:
        """Get list of slaves this master connects to"""
        slave_names = self.connectivity.get(self.master.port_name, [])
        return [s for s in self.slaves if s.port_name in slave_names]

    def _get_unique_slave_widths(self) -> Set[int]:
        """Get unique data widths of connected slaves"""
        return set(s.data_width for s in self.connected_slaves)

    def needs_conversion(self) -> bool:
        """Check if this master needs any width conversion"""
        # HARD LIMIT: All agents use 8-bit ID width (no ID width conversion)
        # Width converters only convert DATA width, not ID width
        # Need conversion only if data widths differ
        return self.master.data_width != self.crossbar_data_width

    def generate_signals(self) -> List[str]:
        """
        Generate internal signal declarations for converter paths

        Returns:
            List of signal declaration strings
        """
        if not self.needs_conversion():
            return []  # No conversion needed, direct pass-through

        signals = []
        signals.append(f"// Master {self.master_idx} ({self.master.port_name}) width adapter signals")

        # For fixed-width crossbar: always convert to crossbar width if needed
        # TODO: Future enhancement - per-slave-width routing with variable crossbar
        slave_width = self.crossbar_data_width
        for slave_width in [self.crossbar_data_width]:
            conv_suffix = f"m{self.master_idx}_to{slave_width}b"

            # Write path signals (if master has write channels)
            if self.master.has_write_channels():
                signals.append(f"")
                signals.append(f"// Write path: {self.master.data_width}b → {slave_width}b (ID: 8-bit fixed, Addr: 64-bit fixed)")
                signals.append(f"logic [7:0]                            conv_{conv_suffix}_awid;")
                signals.append(f"logic [63:0]                           conv_{conv_suffix}_awaddr;  // HARD LIMIT: 64-bit address")
                signals.append(f"logic [7:0]                            conv_{conv_suffix}_awlen;")
                signals.append(f"logic [2:0]                            conv_{conv_suffix}_awsize;")
                signals.append(f"logic [1:0]                            conv_{conv_suffix}_awburst;")
                signals.append(f"logic                                  conv_{conv_suffix}_awlock;")
                signals.append(f"logic [3:0]                            conv_{conv_suffix}_awcache;")
                signals.append(f"logic [2:0]                            conv_{conv_suffix}_awprot;")
                signals.append(f"logic                                  conv_{conv_suffix}_awvalid;")
                signals.append(f"logic                                  conv_{conv_suffix}_awready;")

                signals.append(f"logic [{slave_width-1}:0]              conv_{conv_suffix}_wdata;")
                signals.append(f"logic [{slave_width//8-1}:0]           conv_{conv_suffix}_wstrb;")
                signals.append(f"logic                                  conv_{conv_suffix}_wlast;")
                signals.append(f"logic                                  conv_{conv_suffix}_wvalid;")
                signals.append(f"logic                                  conv_{conv_suffix}_wready;")

                signals.append(f"logic [7:0]                            conv_{conv_suffix}_bid;")
                signals.append(f"logic [1:0]                            conv_{conv_suffix}_bresp;")
                signals.append(f"logic                                  conv_{conv_suffix}_bvalid;")
                signals.append(f"logic                                  conv_{conv_suffix}_bready;")

            # Read path signals (if master has read channels)
            if self.master.has_read_channels():
                signals.append(f"")
                signals.append(f"// Read path: {self.master.data_width}b → {slave_width}b (ID: 8-bit fixed, Addr: 64-bit fixed)")
                signals.append(f"logic [7:0]                            conv_{conv_suffix}_arid;")
                signals.append(f"logic [63:0]                           conv_{conv_suffix}_araddr;  // HARD LIMIT: 64-bit address")
                signals.append(f"logic [7:0]                            conv_{conv_suffix}_arlen;")
                signals.append(f"logic [2:0]                            conv_{conv_suffix}_arsize;")
                signals.append(f"logic [1:0]                            conv_{conv_suffix}_arburst;")
                signals.append(f"logic                                  conv_{conv_suffix}_arlock;")
                signals.append(f"logic [3:0]                            conv_{conv_suffix}_arcache;")
                signals.append(f"logic [2:0]                            conv_{conv_suffix}_arprot;")
                signals.append(f"logic                                  conv_{conv_suffix}_arvalid;")
                signals.append(f"logic                                  conv_{conv_suffix}_arready;")

                signals.append(f"logic [7:0]                            conv_{conv_suffix}_rid;")
                signals.append(f"logic [{slave_width-1}:0]              conv_{conv_suffix}_rdata;")
                signals.append(f"logic [1:0]                            conv_{conv_suffix}_rresp;")
                signals.append(f"logic                                  conv_{conv_suffix}_rlast;")
                signals.append(f"logic                                  conv_{conv_suffix}_rvalid;")
                signals.append(f"logic                                  conv_{conv_suffix}_rready;")

        return signals

    def generate_converters(self) -> List[str]:
        """
        Generate width converter instantiations

        Returns:
            List of RTL instantiation strings
        """
        if not self.needs_conversion():
            return []  # No conversion needed

        instructions = []
        instructions.append(f"")
        instructions.append(f"// Master {self.master_idx} ({self.master.port_name}) Width Converters")
        instructions.append(f"// Native width: {self.master.data_width}b, Crossbar width: {self.crossbar_data_width}b")
        instructions.append(f"// Converters connect to wrapper outputs (fub_axi_*)")

        # Converters ALWAYS connect to fub_axi_* signals (wrapper outputs)
        prefix = f"m{self.master_idx}_fub_axi_"

        # For fixed-width crossbar: always convert to crossbar width if needed
        # TODO: Future enhancement - per-slave-width routing with variable crossbar
        for slave_width in [self.crossbar_data_width]:
            conv_suffix = f"m{self.master_idx}_to{slave_width}b"

            # Write converter (if master has write channels)
            if self.master.has_write_channels():
                instructions.append(f"")
                instructions.append(f"// Write converter: {self.master.data_width}b → {slave_width}b (ID: 8-bit fixed)")
                instructions.append(f"axi4_dwidth_converter_wr #(")
                instructions.append(f"    .S_AXI_DATA_WIDTH({self.master.data_width}),")
                instructions.append(f"    .M_AXI_DATA_WIDTH({slave_width}),")
                instructions.append(f"    .AXI_ID_WIDTH(8),  // HARD LIMIT: 8-bit ID for all agents")
                instructions.append(f"    .AXI_ADDR_WIDTH(64),  // HARD LIMIT: 64-bit address for all agents")
                instructions.append(f"    .AXI_USER_WIDTH(1)")
                instructions.append(f") u_wr_conv_{conv_suffix} (")
                instructions.append(f"    .aclk(aclk),")
                instructions.append(f"    .aresetn(aresetn),")
                instructions.append(f"    // Slave side (from master port)")
                instructions.append(f"    .s_axi_awid({prefix}awid),")
                instructions.append(f"    .s_axi_awaddr({prefix}awaddr),")
                instructions.append(f"    .s_axi_awlen({prefix}awlen),")
                instructions.append(f"    .s_axi_awsize({prefix}awsize),")
                instructions.append(f"    .s_axi_awburst({prefix}awburst),")
                instructions.append(f"    .s_axi_awlock({prefix}awlock),")
                instructions.append(f"    .s_axi_awcache({prefix}awcache),")
                instructions.append(f"    .s_axi_awprot({prefix}awprot),")
                instructions.append(f"    .s_axi_awqos(4'b0),")
                instructions.append(f"    .s_axi_awregion(4'b0),")
                instructions.append(f"    .s_axi_awuser(1'b0),")
                instructions.append(f"    .s_axi_awvalid({prefix}awvalid),")
                instructions.append(f"    .s_axi_awready({prefix}awready),")
                instructions.append(f"    .s_axi_wdata({prefix}wdata),")
                instructions.append(f"    .s_axi_wstrb({prefix}wstrb),")
                instructions.append(f"    .s_axi_wlast({prefix}wlast),")
                instructions.append(f"    .s_axi_wuser(1'b0),")
                instructions.append(f"    .s_axi_wvalid({prefix}wvalid),")
                instructions.append(f"    .s_axi_wready({prefix}wready),")
                instructions.append(f"    .s_axi_bid({prefix}bid),")
                instructions.append(f"    .s_axi_bresp({prefix}bresp),")
                instructions.append(f"    .s_axi_buser(),")
                instructions.append(f"    .s_axi_bvalid({prefix}bvalid),")
                instructions.append(f"    .s_axi_bready({prefix}bready),")
                instructions.append(f"    // Master side (to converter signals)")
                instructions.append(f"    .m_axi_awid(conv_{conv_suffix}_awid),")
                instructions.append(f"    .m_axi_awaddr(conv_{conv_suffix}_awaddr),")
                instructions.append(f"    .m_axi_awlen(conv_{conv_suffix}_awlen),")
                instructions.append(f"    .m_axi_awsize(conv_{conv_suffix}_awsize),")
                instructions.append(f"    .m_axi_awburst(conv_{conv_suffix}_awburst),")
                instructions.append(f"    .m_axi_awlock(conv_{conv_suffix}_awlock),")
                instructions.append(f"    .m_axi_awcache(conv_{conv_suffix}_awcache),")
                instructions.append(f"    .m_axi_awprot(conv_{conv_suffix}_awprot),")
                instructions.append(f"    .m_axi_awqos(),")
                instructions.append(f"    .m_axi_awregion(),")
                instructions.append(f"    .m_axi_awuser(),")
                instructions.append(f"    .m_axi_awvalid(conv_{conv_suffix}_awvalid),")
                instructions.append(f"    .m_axi_awready(conv_{conv_suffix}_awready),")
                instructions.append(f"    .m_axi_wdata(conv_{conv_suffix}_wdata),")
                instructions.append(f"    .m_axi_wstrb(conv_{conv_suffix}_wstrb),")
                instructions.append(f"    .m_axi_wlast(conv_{conv_suffix}_wlast),")
                instructions.append(f"    .m_axi_wuser(),")
                instructions.append(f"    .m_axi_wvalid(conv_{conv_suffix}_wvalid),")
                instructions.append(f"    .m_axi_wready(conv_{conv_suffix}_wready),")
                instructions.append(f"    .m_axi_bid(conv_{conv_suffix}_bid),")
                instructions.append(f"    .m_axi_bresp(conv_{conv_suffix}_bresp),")
                instructions.append(f"    .m_axi_buser(1'b0),")
                instructions.append(f"    .m_axi_bvalid(conv_{conv_suffix}_bvalid),")
                instructions.append(f"    .m_axi_bready(conv_{conv_suffix}_bready)")
                instructions.append(f");")

            # Read converter (if master has read channels)
            if self.master.has_read_channels():
                instructions.append(f"")
                instructions.append(f"// Read converter: {self.master.data_width}b → {slave_width}b (ID: 8-bit fixed)")
                instructions.append(f"axi4_dwidth_converter_rd #(")
                instructions.append(f"    .S_AXI_DATA_WIDTH({self.master.data_width}),")
                instructions.append(f"    .M_AXI_DATA_WIDTH({slave_width}),")
                instructions.append(f"    .AXI_ID_WIDTH(8),  // HARD LIMIT: 8-bit ID for all agents")
                instructions.append(f"    .AXI_ADDR_WIDTH(64),  // HARD LIMIT: 64-bit address for all agents")
                instructions.append(f"    .AXI_USER_WIDTH(1)")
                instructions.append(f") u_rd_conv_{conv_suffix} (")
                instructions.append(f"    .aclk(aclk),")
                instructions.append(f"    .aresetn(aresetn),")
                instructions.append(f"    // Slave side (from master port)")
                instructions.append(f"    .s_axi_arid({prefix}arid),")
                instructions.append(f"    .s_axi_araddr({prefix}araddr),")
                instructions.append(f"    .s_axi_arlen({prefix}arlen),")
                instructions.append(f"    .s_axi_arsize({prefix}arsize),")
                instructions.append(f"    .s_axi_arburst({prefix}arburst),")
                instructions.append(f"    .s_axi_arlock({prefix}arlock),")
                instructions.append(f"    .s_axi_arcache({prefix}arcache),")
                instructions.append(f"    .s_axi_arprot({prefix}arprot),")
                instructions.append(f"    .s_axi_arqos(4'b0),")
                instructions.append(f"    .s_axi_arregion(4'b0),")
                instructions.append(f"    .s_axi_aruser(1'b0),")
                instructions.append(f"    .s_axi_arvalid({prefix}arvalid),")
                instructions.append(f"    .s_axi_arready({prefix}arready),")
                instructions.append(f"    .s_axi_rid({prefix}rid),")
                instructions.append(f"    .s_axi_rdata({prefix}rdata),")
                instructions.append(f"    .s_axi_rresp({prefix}rresp),")
                instructions.append(f"    .s_axi_rlast({prefix}rlast),")
                instructions.append(f"    .s_axi_ruser(),")
                instructions.append(f"    .s_axi_rvalid({prefix}rvalid),")
                instructions.append(f"    .s_axi_rready({prefix}rready),")
                instructions.append(f"    // Master side (to converter signals)")
                instructions.append(f"    .m_axi_arid(conv_{conv_suffix}_arid),")
                instructions.append(f"    .m_axi_araddr(conv_{conv_suffix}_araddr),")
                instructions.append(f"    .m_axi_arlen(conv_{conv_suffix}_arlen),")
                instructions.append(f"    .m_axi_arsize(conv_{conv_suffix}_arsize),")
                instructions.append(f"    .m_axi_arburst(conv_{conv_suffix}_arburst),")
                instructions.append(f"    .m_axi_arlock(conv_{conv_suffix}_arlock),")
                instructions.append(f"    .m_axi_arcache(conv_{conv_suffix}_arcache),")
                instructions.append(f"    .m_axi_arprot(conv_{conv_suffix}_arprot),")
                instructions.append(f"    .m_axi_arqos(),")
                instructions.append(f"    .m_axi_arregion(),")
                instructions.append(f"    .m_axi_aruser(),")
                instructions.append(f"    .m_axi_arvalid(conv_{conv_suffix}_arvalid),")
                instructions.append(f"    .m_axi_arready(conv_{conv_suffix}_arready),")
                instructions.append(f"    .m_axi_rid(conv_{conv_suffix}_rid),")
                instructions.append(f"    .m_axi_rdata(conv_{conv_suffix}_rdata),")
                instructions.append(f"    .m_axi_rresp(conv_{conv_suffix}_rresp),")
                instructions.append(f"    .m_axi_rlast(conv_{conv_suffix}_rlast),")
                instructions.append(f"    .m_axi_ruser(1'b0),")
                instructions.append(f"    .m_axi_rvalid(conv_{conv_suffix}_rvalid),")
                instructions.append(f"    .m_axi_rready(conv_{conv_suffix}_rready)")
                instructions.append(f");")

        return instructions

    def generate_routing(self, slave_addr_map: Dict[str, int]) -> List[str]:
        """
        Generate routing logic from converter outputs to crossbar

        Uses address decode to select which converter path (or pass-through)
        to route to crossbar arrays.

        Args:
            slave_addr_map: Dict mapping slave_name -> slave_index

        Returns:
            List of RTL instructions
        """
        if not self.needs_conversion():
            # No conversion - generate direct pass-through assignments
            return self._generate_direct_passthrough()

        # For fixed-width crossbar: route through converter to crossbar width
        # TODO: Future enhancement - per-slave-width routing with variable crossbar
        conv_suffix = f"m{self.master_idx}_to{self.crossbar_data_width}b"
        return self._generate_converter_routing(conv_suffix)

    def _generate_direct_passthrough(self) -> List[str]:
        """Generate direct signal assignments (no conversion)"""
        instructions = []

        # Direct connections ALWAYS use fub_axi_* signals (wrapper outputs)
        prefix = f"m{self.master_idx}_fub_axi_"
        m_idx = self.master_idx

        instructions.append(f"// Direct pass-through (no conversion needed)")
        instructions.append(f"// Connects wrapper outputs (fub_axi_*) to crossbar")

        if self.master.has_write_channels():
            instructions.append(f"assign xbar_m_awaddr[{m_idx}]  = {prefix}awaddr;")
            instructions.append(f"assign xbar_m_awid[{m_idx}]    = {prefix}awid;")
            instructions.append(f"assign xbar_m_awlen[{m_idx}]   = {prefix}awlen;")
            instructions.append(f"assign xbar_m_awsize[{m_idx}]  = {prefix}awsize;")
            instructions.append(f"assign xbar_m_awburst[{m_idx}] = {prefix}awburst;")
            instructions.append(f"assign xbar_m_awlock[{m_idx}]  = {prefix}awlock;")
            instructions.append(f"assign xbar_m_awcache[{m_idx}] = {prefix}awcache;")
            instructions.append(f"assign xbar_m_awprot[{m_idx}]  = {prefix}awprot;")
            instructions.append(f"assign xbar_m_awvalid[{m_idx}] = {prefix}awvalid;")
            instructions.append(f"assign {prefix}awready = xbar_m_awready[{m_idx}];")
            instructions.append(f"")
            instructions.append(f"assign xbar_m_wdata[{m_idx}]  = {prefix}wdata;")
            instructions.append(f"assign xbar_m_wstrb[{m_idx}]  = {prefix}wstrb;")
            instructions.append(f"assign xbar_m_wlast[{m_idx}]  = {prefix}wlast;")
            instructions.append(f"assign xbar_m_wvalid[{m_idx}] = {prefix}wvalid;")
            instructions.append(f"assign {prefix}wready = xbar_m_wready[{m_idx}];")
            instructions.append(f"")
            instructions.append(f"assign {prefix}bid    = xbar_m_bid[{m_idx}];")
            instructions.append(f"assign {prefix}bresp  = xbar_m_bresp[{m_idx}];")
            instructions.append(f"assign {prefix}bvalid = xbar_m_bvalid[{m_idx}];")
            instructions.append(f"assign xbar_m_bready[{m_idx}] = {prefix}bready;")
            instructions.append(f"")

        if self.master.has_read_channels():
            instructions.append(f"assign xbar_m_araddr[{m_idx}]  = {prefix}araddr;")
            instructions.append(f"assign xbar_m_arid[{m_idx}]    = {prefix}arid;")
            instructions.append(f"assign xbar_m_arlen[{m_idx}]   = {prefix}arlen;")
            instructions.append(f"assign xbar_m_arsize[{m_idx}]  = {prefix}arsize;")
            instructions.append(f"assign xbar_m_arburst[{m_idx}] = {prefix}arburst;")
            instructions.append(f"assign xbar_m_arlock[{m_idx}]  = {prefix}arlock;")
            instructions.append(f"assign xbar_m_arcache[{m_idx}] = {prefix}arcache;")
            instructions.append(f"assign xbar_m_arprot[{m_idx}]  = {prefix}arprot;")
            instructions.append(f"assign xbar_m_arvalid[{m_idx}] = {prefix}arvalid;")
            instructions.append(f"assign {prefix}arready = xbar_m_arready[{m_idx}];")
            instructions.append(f"")
            instructions.append(f"assign {prefix}rdata  = xbar_m_rdata[{m_idx}];")
            instructions.append(f"assign {prefix}rid    = xbar_m_rid[{m_idx}];")
            instructions.append(f"assign {prefix}rresp  = xbar_m_rresp[{m_idx}];")
            instructions.append(f"assign {prefix}rlast  = xbar_m_rlast[{m_idx}];")
            instructions.append(f"assign {prefix}rvalid = xbar_m_rvalid[{m_idx}];")
            instructions.append(f"assign xbar_m_rready[{m_idx}] = {prefix}rready;")
            instructions.append(f"")

        return instructions

    def _generate_converter_routing(self, conv_suffix: str) -> List[str]:
        """Generate routing through converter"""
        instructions = []
        m_idx = self.master_idx

        instructions.append(f"// Route through converter: {conv_suffix}")

        if self.master.has_write_channels():
            instructions.append(f"assign xbar_m_awaddr[{m_idx}]  = conv_{conv_suffix}_awaddr;")
            instructions.append(f"assign xbar_m_awid[{m_idx}]    = conv_{conv_suffix}_awid;")
            instructions.append(f"assign xbar_m_awlen[{m_idx}]   = conv_{conv_suffix}_awlen;")
            instructions.append(f"assign xbar_m_awsize[{m_idx}]  = conv_{conv_suffix}_awsize;")
            instructions.append(f"assign xbar_m_awburst[{m_idx}] = conv_{conv_suffix}_awburst;")
            instructions.append(f"assign xbar_m_awlock[{m_idx}]  = conv_{conv_suffix}_awlock;")
            instructions.append(f"assign xbar_m_awcache[{m_idx}] = conv_{conv_suffix}_awcache;")
            instructions.append(f"assign xbar_m_awprot[{m_idx}]  = conv_{conv_suffix}_awprot;")
            instructions.append(f"assign xbar_m_awvalid[{m_idx}] = conv_{conv_suffix}_awvalid;")
            instructions.append(f"assign conv_{conv_suffix}_awready = xbar_m_awready[{m_idx}];")
            instructions.append(f"")
            instructions.append(f"assign xbar_m_wdata[{m_idx}]  = conv_{conv_suffix}_wdata;")
            instructions.append(f"assign xbar_m_wstrb[{m_idx}]  = conv_{conv_suffix}_wstrb;")
            instructions.append(f"assign xbar_m_wlast[{m_idx}]  = conv_{conv_suffix}_wlast;")
            instructions.append(f"assign xbar_m_wvalid[{m_idx}] = conv_{conv_suffix}_wvalid;")
            instructions.append(f"assign conv_{conv_suffix}_wready = xbar_m_wready[{m_idx}];")
            instructions.append(f"")
            instructions.append(f"assign conv_{conv_suffix}_bid    = xbar_m_bid[{m_idx}];")
            instructions.append(f"assign conv_{conv_suffix}_bresp  = xbar_m_bresp[{m_idx}];")
            instructions.append(f"assign conv_{conv_suffix}_bvalid = xbar_m_bvalid[{m_idx}];")
            instructions.append(f"assign xbar_m_bready[{m_idx}] = conv_{conv_suffix}_bready;")
            instructions.append(f"")

        if self.master.has_read_channels():
            instructions.append(f"assign xbar_m_araddr[{m_idx}]  = conv_{conv_suffix}_araddr;")
            instructions.append(f"assign xbar_m_arid[{m_idx}]    = conv_{conv_suffix}_arid;")
            instructions.append(f"assign xbar_m_arlen[{m_idx}]   = conv_{conv_suffix}_arlen;")
            instructions.append(f"assign xbar_m_arsize[{m_idx}]  = conv_{conv_suffix}_arsize;")
            instructions.append(f"assign xbar_m_arburst[{m_idx}] = conv_{conv_suffix}_arburst;")
            instructions.append(f"assign xbar_m_arlock[{m_idx}]  = conv_{conv_suffix}_arlock;")
            instructions.append(f"assign xbar_m_arcache[{m_idx}] = conv_{conv_suffix}_arcache;")
            instructions.append(f"assign xbar_m_arprot[{m_idx}]  = conv_{conv_suffix}_arprot;")
            instructions.append(f"assign xbar_m_arvalid[{m_idx}] = conv_{conv_suffix}_arvalid;")
            instructions.append(f"assign conv_{conv_suffix}_arready = xbar_m_arready[{m_idx}];")
            instructions.append(f"")
            instructions.append(f"assign conv_{conv_suffix}_rdata  = xbar_m_rdata[{m_idx}];")
            instructions.append(f"assign conv_{conv_suffix}_rid    = xbar_m_rid[{m_idx}];")
            instructions.append(f"assign conv_{conv_suffix}_rresp  = xbar_m_rresp[{m_idx}];")
            instructions.append(f"assign conv_{conv_suffix}_rlast  = xbar_m_rlast[{m_idx}];")
            instructions.append(f"assign conv_{conv_suffix}_rvalid = xbar_m_rvalid[{m_idx}];")
            instructions.append(f"assign xbar_m_rready[{m_idx}] = conv_{conv_suffix}_rready;")
            instructions.append(f"")

        return instructions
