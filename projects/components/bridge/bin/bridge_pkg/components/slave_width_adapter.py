#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# Slave Width Adapter Component - Signal prefix helpers and width conversion
#
# ⚠️ DEPRECATION NOTICE:
#    The width conversion methods (generate_signals, generate_converters,
#    generate_mb_id_extraction) violate the approved bridge architecture
#    where ALL width conversion should occur on the MASTER side.
#
#    These methods are ONLY used by obsolete bridge_module.py.
#    Modern BridgeModuleGenerator does NOT use them.
#
#    The signal prefix helper methods (get_*_prefix) are architecturally
#    correct and actively used by crossbar routing logic.

from typing import List, Dict


class SlaveWidthAdapter:
    """
    Helper class for slave-side signal naming and routing.

    PRIMARY PURPOSE (Correct Architecture):
        - Provides signal prefix helpers for crossbar routing
        - Determines whether to route to slave port or converter output
        - Used by channel_mux_component.py for correct signal selection

    DEPRECATED PURPOSE (Violates Architecture):
        - Width conversion generation on slave side (architectural violation)
        - Only used by obsolete bridge_module.py
        - Modern generators do ALL conversion on master side

    Correct Architecture:
        Master → [Conversion] → Crossbar → [Direct] → Slave
                 ↑ ALL conversion here    ↑ No conversion

    Legacy Architecture (DEPRECATED):
        Master → [Upsize] → Crossbar → [Downsize] → Slave
                 ↑ Conversion 1      ↑ Conversion 2 (WASTEFUL!)

    For matching widths: Direct pass-through (no converter)
    For width mismatch in LEGACY code: Instantiate axi4_dwidth_converter_wr/rd
    """

    def __init__(self, slave_idx: int, slave,
                 crossbar_data_width: int, crossbar_id_width: int,
                 num_masters: int = 1, crossbar_addr_width: int = 32):
        """
        Initialize slave width adapter

        Args:
            slave_idx: Index of this slave in the slaves list
            slave: PortSpec object for this slave
            crossbar_data_width: Width of crossbar data bus
            crossbar_id_width: Width of crossbar ID (master ID + routing bits)
            num_masters: Number of masters (for mb_id width calculation)
            crossbar_addr_width: Width of crossbar address bus (default 32)
        """
        self.slave_idx = slave_idx
        self.slave = slave
        self.crossbar_data_width = crossbar_data_width
        self.crossbar_id_width = crossbar_id_width
        self.crossbar_addr_width = crossbar_addr_width
        self.num_masters = num_masters

        # Calculate mb_id width (master routing ID)
        self.mb_id_width = max(1, (num_masters - 1).bit_length() if num_masters > 1 else 0)

    def needs_conversion(self) -> bool:
        """
        Check if this slave needs width conversion

        Returns False if:
        - Slave is APB (needs AXI-to-APB converter, not width converter)
        - Data widths match (no conversion needed)
        - Slave has id_width=0 (invalid for AXI4 width converters)
        """
        # APB slaves need AXI-to-APB bridges, not width converters
        if self.slave.protocol.lower() == "apb":
            return False

        # AXI4 slaves with id_width=0 are invalid
        if self.slave.id_width == 0:
            return False

        # Only convert if data widths differ
        return self.slave.data_width != self.crossbar_data_width

    def generate_signals(self) -> List[str]:
        """
        DEPRECATED: Generate intermediate signal declarations for converter.

        ⚠️ ARCHITECTURAL VIOLATION:
           This method generates signals for SLAVE-SIDE width conversion,
           violating the approved architecture where ALL conversion occurs
           on the MASTER side.

        ONLY USED BY: Obsolete bridge_module.py
        DO NOT USE IN: New generators (use MasterWidthAdapter instead)

        Will be removed when bridge_module.py is deleted.
        """
        if not self.needs_conversion():
            return []

        signals = []
        signals.append(f"// Slave {self.slave_idx} ({self.slave.port_name}) width adapter signals")
        signals.append(f"// Crossbar: {self.crossbar_data_width}b → Slave: {self.slave.data_width}b")

        conv_suffix = f"s{self.slave_idx}_from{self.crossbar_data_width}b"

        # Crossbar-side signals (master side of converter) - at crossbar width
        # HARD LIMIT: All agents use 8-bit ID width
        if self.slave.has_write_channels():
            signals.append(f"// Write path (crossbar → converter) (ID: 8-bit fixed)")
            signals.append(f"logic [7:0]                              conv_{conv_suffix}_m_awid;")
            signals.append(f"logic [{self.mb_id_width-1}:0]           conv_{conv_suffix}_m_awmb_id;  // Master routing ID")
            signals.append(f"logic [{self.crossbar_addr_width-1}:0]   conv_{conv_suffix}_m_awaddr;")
            signals.append(f"logic [7:0]                              conv_{conv_suffix}_m_awlen;")
            signals.append(f"logic [2:0]                              conv_{conv_suffix}_m_awsize;")
            signals.append(f"logic [1:0]                              conv_{conv_suffix}_m_awburst;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_awlock;")
            signals.append(f"logic [3:0]                              conv_{conv_suffix}_m_awcache;")
            signals.append(f"logic [2:0]                              conv_{conv_suffix}_m_awprot;")
            signals.append(f"logic [3:0]                              conv_{conv_suffix}_m_awqos;")
            signals.append(f"logic [3:0]                              conv_{conv_suffix}_m_awregion;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_awuser;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_awvalid;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_awready;")

            signals.append(f"logic [{self.crossbar_data_width-1}:0]   conv_{conv_suffix}_m_wdata;")
            signals.append(f"logic [{self.crossbar_data_width//8-1}:0] conv_{conv_suffix}_m_wstrb;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_wlast;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_wuser;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_wvalid;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_wready;")

            signals.append(f"logic [7:0]                              conv_{conv_suffix}_m_bid;")
            signals.append(f"logic [{self.mb_id_width-1}:0]           conv_{conv_suffix}_m_bmb_id;  // Master routing ID (extracted from bid)")
            signals.append(f"logic [1:0]                              conv_{conv_suffix}_m_bresp;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_buser;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_bvalid;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_bready;")
            signals.append("")

        if self.slave.has_read_channels():
            signals.append(f"// Read path (crossbar → converter) (ID: 8-bit fixed)")
            signals.append(f"logic [7:0]                              conv_{conv_suffix}_m_arid;")
            signals.append(f"logic [{self.mb_id_width-1}:0]           conv_{conv_suffix}_m_armb_id;  // Master routing ID")
            signals.append(f"logic [{self.crossbar_addr_width-1}:0]   conv_{conv_suffix}_m_araddr;")
            signals.append(f"logic [7:0]                              conv_{conv_suffix}_m_arlen;")
            signals.append(f"logic [2:0]                              conv_{conv_suffix}_m_arsize;")
            signals.append(f"logic [1:0]                              conv_{conv_suffix}_m_arburst;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_arlock;")
            signals.append(f"logic [3:0]                              conv_{conv_suffix}_m_arcache;")
            signals.append(f"logic [2:0]                              conv_{conv_suffix}_m_arprot;")
            signals.append(f"logic [3:0]                              conv_{conv_suffix}_m_arqos;")
            signals.append(f"logic [3:0]                              conv_{conv_suffix}_m_arregion;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_aruser;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_arvalid;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_arready;")

            signals.append(f"logic [7:0]                              conv_{conv_suffix}_m_rid;")
            signals.append(f"logic [{self.mb_id_width-1}:0]           conv_{conv_suffix}_m_rmb_id;  // Master routing ID (extracted from rid)")
            signals.append(f"logic [{self.crossbar_data_width-1}:0]   conv_{conv_suffix}_m_rdata;")
            signals.append(f"logic [1:0]                              conv_{conv_suffix}_m_rresp;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_rlast;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_ruser;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_rvalid;")
            signals.append(f"logic                                    conv_{conv_suffix}_m_rready;")
            signals.append("")

        return signals

    def generate_mb_id_extraction(self) -> List[str]:
        """
        DEPRECATED: Generate mb_id extraction from BID/RID fields of converter responses.

        ⚠️ ARCHITECTURAL VIOLATION:
           This method supports SLAVE-SIDE width converters, which violate
           the approved architecture.

        ONLY USED BY: Obsolete bridge_module.py
        DO NOT USE IN: New generators

        Will be removed when bridge_module.py is deleted.
        """
        if not self.needs_conversion():
            return []

        extractions = []
        conv_suffix = f"s{self.slave_idx}_from{self.crossbar_data_width}b"

        extractions.append(f"// Slave {self.slave_idx} ({self.slave.port_name}) mb_id extraction from converter responses")
        extractions.append(f"// HARD LIMIT: 8-bit ID width for all agents")

        if self.slave.has_write_channels():
            # Extract mb_id from upper bits of BID
            # ID structure: {mb_id[mb_id_width-1:0], slave_id[...]}
            # Fixed 8-bit ID width
            upper_bit = 7  # 8-bit ID: bits [7:0]
            lower_bit = 8 - self.mb_id_width
            extractions.append(f"assign conv_{conv_suffix}_m_bmb_id = conv_{conv_suffix}_m_bid[{upper_bit}:{lower_bit}];")

        if self.slave.has_read_channels():
            # Extract mb_id from upper bits of RID
            # Fixed 8-bit ID width
            upper_bit = 7  # 8-bit ID: bits [7:0]
            lower_bit = 8 - self.mb_id_width
            extractions.append(f"assign conv_{conv_suffix}_m_rmb_id = conv_{conv_suffix}_m_rid[{upper_bit}:{lower_bit}];")

        extractions.append("")
        return extractions

    def generate_converters(self) -> List[str]:
        """
        DEPRECATED: Generate width converter instantiations on SLAVE side.

        ⚠️ ARCHITECTURAL VIOLATION:
           This method instantiates axi4_dwidth_converter_wr/rd on the SLAVE side,
           creating wasteful double-conversion for matching-width connections:

           Current (WRONG):
               Master(64b) → Upsize(64→512) → Crossbar → Downsize(512→64) → Slave(64b)
                                                           ↑ THIS CONVERTER (wasteful!)

           Correct Architecture:
               Master(64b) → Router → Direct → Slave(64b)
                             ↑ Zero conversions for matching widths

        ONLY USED BY: Obsolete bridge_module.py
        DO NOT USE IN: New generators (use MasterWidthAdapter instead)

        Will be removed when bridge_module.py is deleted.
        """
        if not self.needs_conversion():
            return []

        instructions = []
        prefix = self.slave.prefix
        conv_suffix = f"s{self.slave_idx}_from{self.crossbar_data_width}b"

        instructions.append(f"// Slave {self.slave_idx}: {self.slave.port_name} width converters")
        instructions.append(f"// Downsize: {self.crossbar_data_width}b → {self.slave.data_width}b")

        # Write converter (if slave supports writes)
        if self.slave.has_write_channels():
            instructions.append(f"axi4_dwidth_converter_wr #(")
            instructions.append(f"    .S_AXI_DATA_WIDTH({self.crossbar_data_width}),")
            instructions.append(f"    .M_AXI_DATA_WIDTH({self.slave.data_width}),")
            instructions.append(f"    .AXI_ID_WIDTH(8),  // HARD LIMIT: 8-bit ID for all agents")
            instructions.append(f"    .AXI_ADDR_WIDTH(64),  // HARD LIMIT: 64-bit address for all agents")
            instructions.append(f"    .AXI_USER_WIDTH(1)")
            instructions.append(f") u_wr_conv_{conv_suffix} (")
            instructions.append(f"    .aclk(aclk),")
            instructions.append(f"    .aresetn(aresetn),")
            instructions.append("")
            instructions.append(f"    // Slave side (from crossbar)")
            instructions.append(f"    .s_axi_awid(conv_{conv_suffix}_m_awid),")
            instructions.append(f"    .s_axi_awaddr(conv_{conv_suffix}_m_awaddr),")
            instructions.append(f"    .s_axi_awlen(conv_{conv_suffix}_m_awlen),")
            instructions.append(f"    .s_axi_awsize(conv_{conv_suffix}_m_awsize),")
            instructions.append(f"    .s_axi_awburst(conv_{conv_suffix}_m_awburst),")
            instructions.append(f"    .s_axi_awlock(conv_{conv_suffix}_m_awlock),")
            instructions.append(f"    .s_axi_awcache(conv_{conv_suffix}_m_awcache),")
            instructions.append(f"    .s_axi_awprot(conv_{conv_suffix}_m_awprot),")
            instructions.append(f"    .s_axi_awqos(conv_{conv_suffix}_m_awqos),")
            instructions.append(f"    .s_axi_awregion(conv_{conv_suffix}_m_awregion),")
            instructions.append(f"    .s_axi_awuser(conv_{conv_suffix}_m_awuser),")
            instructions.append(f"    .s_axi_awvalid(conv_{conv_suffix}_m_awvalid),")
            instructions.append(f"    .s_axi_awready(conv_{conv_suffix}_m_awready),")
            instructions.append("")
            instructions.append(f"    .s_axi_wdata(conv_{conv_suffix}_m_wdata),")
            instructions.append(f"    .s_axi_wstrb(conv_{conv_suffix}_m_wstrb),")
            instructions.append(f"    .s_axi_wlast(conv_{conv_suffix}_m_wlast),")
            instructions.append(f"    .s_axi_wuser(conv_{conv_suffix}_m_wuser),")
            instructions.append(f"    .s_axi_wvalid(conv_{conv_suffix}_m_wvalid),")
            instructions.append(f"    .s_axi_wready(conv_{conv_suffix}_m_wready),")
            instructions.append("")
            instructions.append(f"    .s_axi_bid(conv_{conv_suffix}_m_bid),")
            instructions.append(f"    .s_axi_bresp(conv_{conv_suffix}_m_bresp),")
            instructions.append(f"    .s_axi_buser(conv_{conv_suffix}_m_buser),")
            instructions.append(f"    .s_axi_bvalid(conv_{conv_suffix}_m_bvalid),")
            instructions.append(f"    .s_axi_bready(conv_{conv_suffix}_m_bready),")
            instructions.append("")
            instructions.append(f"    // Master side (to external slave)")
            instructions.append(f"    .m_axi_awid({prefix}awid),")
            instructions.append(f"    .m_axi_awaddr({prefix}awaddr),")
            instructions.append(f"    .m_axi_awlen({prefix}awlen),")
            instructions.append(f"    .m_axi_awsize({prefix}awsize),")
            instructions.append(f"    .m_axi_awburst({prefix}awburst),")
            instructions.append(f"    .m_axi_awlock({prefix}awlock),")
            instructions.append(f"    .m_axi_awcache({prefix}awcache),")
            instructions.append(f"    .m_axi_awprot({prefix}awprot),")
            instructions.append(f"    .m_axi_awqos({prefix}awqos),")
            instructions.append(f"    .m_axi_awregion({prefix}awregion),")
            instructions.append(f"    .m_axi_awuser({prefix}awuser),")
            instructions.append(f"    .m_axi_awvalid({prefix}awvalid),")
            instructions.append(f"    .m_axi_awready({prefix}awready),")
            instructions.append("")
            instructions.append(f"    .m_axi_wdata({prefix}wdata),")
            instructions.append(f"    .m_axi_wstrb({prefix}wstrb),")
            instructions.append(f"    .m_axi_wlast({prefix}wlast),")
            instructions.append(f"    .m_axi_wuser({prefix}wuser),")
            instructions.append(f"    .m_axi_wvalid({prefix}wvalid),")
            instructions.append(f"    .m_axi_wready({prefix}wready),")
            instructions.append("")
            instructions.append(f"    .m_axi_bid({prefix}bid),")
            instructions.append(f"    .m_axi_bresp({prefix}bresp),")
            instructions.append(f"    .m_axi_buser({prefix}buser),")
            instructions.append(f"    .m_axi_bvalid({prefix}bvalid),")
            instructions.append(f"    .m_axi_bready({prefix}bready)")
            instructions.append(f");")
            instructions.append("")

        # Read converter (if slave supports reads)
        if self.slave.has_read_channels():
            instructions.append(f"axi4_dwidth_converter_rd #(")
            instructions.append(f"    .S_AXI_DATA_WIDTH({self.crossbar_data_width}),")
            instructions.append(f"    .M_AXI_DATA_WIDTH({self.slave.data_width}),")
            instructions.append(f"    .AXI_ID_WIDTH(8),  // HARD LIMIT: 8-bit ID for all agents")
            instructions.append(f"    .AXI_ADDR_WIDTH(64),  // HARD LIMIT: 64-bit address for all agents")
            instructions.append(f"    .AXI_USER_WIDTH(1)")
            instructions.append(f") u_rd_conv_{conv_suffix} (")
            instructions.append(f"    .aclk(aclk),")
            instructions.append(f"    .aresetn(aresetn),")
            instructions.append("")
            instructions.append(f"    // Slave side (from crossbar)")
            instructions.append(f"    .s_axi_arid(conv_{conv_suffix}_m_arid),")
            instructions.append(f"    .s_axi_araddr(conv_{conv_suffix}_m_araddr),")
            instructions.append(f"    .s_axi_arlen(conv_{conv_suffix}_m_arlen),")
            instructions.append(f"    .s_axi_arsize(conv_{conv_suffix}_m_arsize),")
            instructions.append(f"    .s_axi_arburst(conv_{conv_suffix}_m_arburst),")
            instructions.append(f"    .s_axi_arlock(conv_{conv_suffix}_m_arlock),")
            instructions.append(f"    .s_axi_arcache(conv_{conv_suffix}_m_arcache),")
            instructions.append(f"    .s_axi_arprot(conv_{conv_suffix}_m_arprot),")
            instructions.append(f"    .s_axi_arqos(conv_{conv_suffix}_m_arqos),")
            instructions.append(f"    .s_axi_arregion(conv_{conv_suffix}_m_arregion),")
            instructions.append(f"    .s_axi_aruser(conv_{conv_suffix}_m_aruser),")
            instructions.append(f"    .s_axi_arvalid(conv_{conv_suffix}_m_arvalid),")
            instructions.append(f"    .s_axi_arready(conv_{conv_suffix}_m_arready),")
            instructions.append("")
            instructions.append(f"    .s_axi_rid(conv_{conv_suffix}_m_rid),")
            instructions.append(f"    .s_axi_rdata(conv_{conv_suffix}_m_rdata),")
            instructions.append(f"    .s_axi_rresp(conv_{conv_suffix}_m_rresp),")
            instructions.append(f"    .s_axi_rlast(conv_{conv_suffix}_m_rlast),")
            instructions.append(f"    .s_axi_ruser(conv_{conv_suffix}_m_ruser),")
            instructions.append(f"    .s_axi_rvalid(conv_{conv_suffix}_m_rvalid),")
            instructions.append(f"    .s_axi_rready(conv_{conv_suffix}_m_rready),")
            instructions.append("")
            instructions.append(f"    // Master side (to external slave)")
            instructions.append(f"    .m_axi_arid({prefix}arid),")
            instructions.append(f"    .m_axi_araddr({prefix}araddr),")
            instructions.append(f"    .m_axi_arlen({prefix}arlen),")
            instructions.append(f"    .m_axi_arsize({prefix}arsize),")
            instructions.append(f"    .m_axi_arburst({prefix}arburst),")
            instructions.append(f"    .m_axi_arlock({prefix}arlock),")
            instructions.append(f"    .m_axi_arcache({prefix}arcache),")
            instructions.append(f"    .m_axi_arprot({prefix}arprot),")
            instructions.append(f"    .m_axi_arqos({prefix}arqos),")
            instructions.append(f"    .m_axi_arregion({prefix}arregion),")
            instructions.append(f"    .m_axi_aruser({prefix}aruser),")
            instructions.append(f"    .m_axi_arvalid({prefix}arvalid),")
            instructions.append(f"    .m_axi_arready({prefix}arready),")
            instructions.append("")
            instructions.append(f"    .m_axi_rid({prefix}rid),")
            instructions.append(f"    .m_axi_rdata({prefix}rdata),")
            instructions.append(f"    .m_axi_rresp({prefix}rresp),")
            instructions.append(f"    .m_axi_rlast({prefix}rlast),")
            instructions.append(f"    .m_axi_ruser({prefix}ruser),")
            instructions.append(f"    .m_axi_rvalid({prefix}rvalid),")
            instructions.append(f"    .m_axi_rready({prefix}rready)")
            instructions.append(f");")
            instructions.append("")

        return instructions

    def get_aw_signal_prefix(self) -> str:
        """Get the prefix for AW channel signals to use in channel mux"""
        if not self.needs_conversion():
            return self.slave.prefix
        conv_suffix = f"s{self.slave_idx}_from{self.crossbar_data_width}b"
        return f"conv_{conv_suffix}_m_"

    def get_w_signal_prefix(self) -> str:
        """Get the prefix for W channel signals to use in channel mux"""
        if not self.needs_conversion():
            return self.slave.prefix
        conv_suffix = f"s{self.slave_idx}_from{self.crossbar_data_width}b"
        return f"conv_{conv_suffix}_m_"

    def get_b_signal_prefix(self) -> str:
        """Get the prefix for B channel signals to use in channel mux"""
        if not self.needs_conversion():
            return self.slave.prefix
        conv_suffix = f"s{self.slave_idx}_from{self.crossbar_data_width}b"
        return f"conv_{conv_suffix}_m_"

    def get_ar_signal_prefix(self) -> str:
        """Get the prefix for AR channel signals to use in channel mux"""
        if not self.needs_conversion():
            return self.slave.prefix
        conv_suffix = f"s{self.slave_idx}_from{self.crossbar_data_width}b"
        return f"conv_{conv_suffix}_m_"

    def get_r_signal_prefix(self) -> str:
        """Get the prefix for R channel signals to use in channel mux"""
        if not self.needs_conversion():
            return self.slave.prefix
        conv_suffix = f"s{self.slave_idx}_from{self.crossbar_data_width}b"
        return f"conv_{conv_suffix}_m_"

    def get_id_width(self) -> int:
        """Get the ID width to use in channel mux (uniform ID width per user directive)"""
        # Per user directive: "For now, only support all agents using the ID width of 8 or all the same size"
        # Always use slave's native ID width (uniform across all agents)
        return self.slave.id_width
