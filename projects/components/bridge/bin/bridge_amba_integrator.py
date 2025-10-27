#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BridgeAmbaIntegrator
# Purpose: AMBA AXI4 slave/master component integration for bridge crossbars
#
# Author: sean galloway
# Created: 2025-10-26

"""
AMBA Component Integration for Bridge Generator

Handles instantiation of axi4_slave_wr/rd and axi4_master_wr/rd components
for master-side and slave-side interfaces.

Provides skid buffers and proven flow control from rtl/amba/axi4/ modules.
"""

import sys
from pathlib import Path

# Import the framework
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / 'bin'))
from rtl_generators.verilog.module import Module


class BridgeAmbaIntegrator:
    """
    AMBA Component Integration for Bridge Crossbar

    Generates axi4_slave_wr/rd instances for master-side interfaces
    and axi4_master_wr/rd instances for slave-side interfaces.

    Signal Flow:
        External s_axi_* → axi4_slave_wr/rd → xbar_s_axi_* (crossbar input)
        xbar_m_axi_* (crossbar output) → axi4_master_wr/rd → External m_axi_*
    """

    def __init__(self, module: Module, config):
        """
        Initialize AMBA integrator

        Args:
            module: Module instance for RTL generation
            config: BridgeConfig with topology and skid depth settings
        """
        self.module = module
        self.cfg = config

    def generate_master_side_components(self):
        """
        Generate AMBA axi4_slave_wr and axi4_slave_rd instances for master-side interfaces

        One pair (wr + rd) per external master
        - External s_axi_* connects to axi4_slave components
        - axi4_slave outputs to xbar_s_axi_* (crossbar input)
        """
        self.module.comment("==========================================================================")
        self.module.comment("Master-Side AMBA Components (axi4_slave_wr and axi4_slave_rd)")
        self.module.comment("==========================================================================")
        self.module.comment("Accept connections from external masters with skid buffers and flow control")
        self.module.comment(f"Configuration: SKID_DEPTH_AW={self.cfg.skid_depth_aw}, W={self.cfg.skid_depth_w}, "
                     f"B={self.cfg.skid_depth_b}, AR={self.cfg.skid_depth_ar}, R={self.cfg.skid_depth_r}")
        self.module.comment("==========================================================================")
        self.module.instruction("")

        # Generate instances for each master
        self.module.instruction("generate")
        self.module.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_master_side_amba")
        self.module.instruction("")

        # axi4_slave_wr instance (AW, W, B channels)
        self.module.comment("        Write path: axi4_slave_wr for AW, W, B channels")
        self.module.instruction("        axi4_slave_wr #(")
        self.module.instruction("            .AXI_ID_WIDTH(ID_WIDTH),")
        self.module.instruction("            .AXI_ADDR_WIDTH(ADDR_WIDTH),")
        self.module.instruction("            .AXI_DATA_WIDTH(DATA_WIDTH),")
        self.module.instruction(f"            .SKID_DEPTH_AW({self.cfg.skid_depth_aw}),")
        self.module.instruction(f"            .SKID_DEPTH_W({self.cfg.skid_depth_w}),")
        self.module.instruction(f"            .SKID_DEPTH_B({self.cfg.skid_depth_b})")
        self.module.instruction("        ) u_master_wr (")
        self.module.instruction("            .aclk(aclk),")
        self.module.instruction("            .aresetn(aresetn),")
        self.module.instruction("")
        self.module.comment("            External master interface (s_axi_* from outside)")
        self.module.instruction("            .s_axi_awid(s_axi_awid[m]),")
        self.module.instruction("            .s_axi_awaddr(s_axi_awaddr[m]),")
        self.module.instruction("            .s_axi_awlen(s_axi_awlen[m]),")
        self.module.instruction("            .s_axi_awsize(s_axi_awsize[m]),")
        self.module.instruction("            .s_axi_awburst(s_axi_awburst[m]),")
        self.module.instruction("            .s_axi_awlock(s_axi_awlock[m]),")
        self.module.instruction("            .s_axi_awcache(s_axi_awcache[m]),")
        self.module.instruction("            .s_axi_awprot(s_axi_awprot[m]),")
        self.module.instruction("            .s_axi_awvalid(s_axi_awvalid[m]),")
        self.module.instruction("            .s_axi_awready(s_axi_awready[m]),")
        self.module.instruction("")
        self.module.instruction("            .s_axi_wdata(s_axi_wdata[m]),")
        self.module.instruction("            .s_axi_wstrb(s_axi_wstrb[m]),")
        self.module.instruction("            .s_axi_wlast(s_axi_wlast[m]),")
        self.module.instruction("            .s_axi_wvalid(s_axi_wvalid[m]),")
        self.module.instruction("            .s_axi_wready(s_axi_wready[m]),")
        self.module.instruction("")
        self.module.instruction("            .s_axi_bid(s_axi_bid[m]),")
        self.module.instruction("            .s_axi_bresp(s_axi_bresp[m]),")
        self.module.instruction("            .s_axi_bvalid(s_axi_bvalid[m]),")
        self.module.instruction("            .s_axi_bready(s_axi_bready[m]),")
        self.module.instruction("")
        self.module.comment("            Crossbar interface (xbar_s_axi_* to internal routing)")
        self.module.instruction("            .fub_axi_awid(xbar_s_axi_awid[m]),")
        self.module.instruction("            .fub_axi_awaddr(xbar_s_axi_awaddr[m]),")
        self.module.instruction("            .fub_axi_awlen(xbar_s_axi_awlen[m]),")
        self.module.instruction("            .fub_axi_awsize(xbar_s_axi_awsize[m]),")
        self.module.instruction("            .fub_axi_awburst(xbar_s_axi_awburst[m]),")
        self.module.instruction("            .fub_axi_awlock(xbar_s_axi_awlock[m]),")
        self.module.instruction("            .fub_axi_awcache(xbar_s_axi_awcache[m]),")
        self.module.instruction("            .fub_axi_awprot(xbar_s_axi_awprot[m]),")
        self.module.instruction("            .fub_axi_awvalid(xbar_s_axi_awvalid[m]),")
        self.module.instruction("            .fub_axi_awready(xbar_s_axi_awready[m]),")
        self.module.instruction("")
        self.module.instruction("            .fub_axi_wdata(xbar_s_axi_wdata[m]),")
        self.module.instruction("            .fub_axi_wstrb(xbar_s_axi_wstrb[m]),")
        self.module.instruction("            .fub_axi_wlast(xbar_s_axi_wlast[m]),")
        self.module.instruction("            .fub_axi_wvalid(xbar_s_axi_wvalid[m]),")
        self.module.instruction("            .fub_axi_wready(xbar_s_axi_wready[m]),")
        self.module.instruction("")
        self.module.instruction("            .fub_axi_bid(xbar_s_axi_bid[m]),")
        self.module.instruction("            .fub_axi_bresp(xbar_s_axi_bresp[m]),")
        self.module.instruction("            .fub_axi_bvalid(xbar_s_axi_bvalid[m]),")
        self.module.instruction("            .fub_axi_bready(xbar_s_axi_bready[m]),")
        self.module.instruction("")
        self.module.comment("            Extended AXI4 signals (QoS, Region, User) - tied to defaults")
        self.module.instruction("            .s_axi_awqos(4'b0000),      // QoS: lowest priority")
        self.module.instruction("            .s_axi_awregion(4'b0000),   // Region: unused")
        self.module.instruction("            .s_axi_awuser(1'b0),        // User: default")
        self.module.instruction("            .s_axi_wuser(1'b0),         // User: default")
        self.module.instruction("            .s_axi_buser(),             // User: unconnected output")
        self.module.instruction("            .fub_axi_awqos(),           // QoS: unconnected output")
        self.module.instruction("            .fub_axi_awregion(),        // Region: unconnected output")
        self.module.instruction("            .fub_axi_awuser(),          // User: unconnected output")
        self.module.instruction("            .fub_axi_wuser(),           // User: unconnected output")
        self.module.instruction("            .fub_axi_buser(1'b0),       // User: tie to default")
        self.module.instruction("            .busy()                     // Status: unconnected (FPGA, no clock gating)")
        self.module.instruction("        );")
        self.module.instruction("")

        # axi4_slave_rd instance (AR, R channels)
        self.module.comment("        Read path: axi4_slave_rd for AR, R channels")
        self.module.instruction("        axi4_slave_rd #(")
        self.module.instruction("            .AXI_ID_WIDTH(ID_WIDTH),")
        self.module.instruction("            .AXI_ADDR_WIDTH(ADDR_WIDTH),")
        self.module.instruction("            .AXI_DATA_WIDTH(DATA_WIDTH),")
        self.module.instruction(f"            .SKID_DEPTH_AR({self.cfg.skid_depth_ar}),")
        self.module.instruction(f"            .SKID_DEPTH_R({self.cfg.skid_depth_r})")
        self.module.instruction("        ) u_master_rd (")
        self.module.instruction("            .aclk(aclk),")
        self.module.instruction("            .aresetn(aresetn),")
        self.module.instruction("")
        self.module.comment("            External master interface (s_axi_* from outside)")
        self.module.instruction("            .s_axi_arid(s_axi_arid[m]),")
        self.module.instruction("            .s_axi_araddr(s_axi_araddr[m]),")
        self.module.instruction("            .s_axi_arlen(s_axi_arlen[m]),")
        self.module.instruction("            .s_axi_arsize(s_axi_arsize[m]),")
        self.module.instruction("            .s_axi_arburst(s_axi_arburst[m]),")
        self.module.instruction("            .s_axi_arlock(s_axi_arlock[m]),")
        self.module.instruction("            .s_axi_arcache(s_axi_arcache[m]),")
        self.module.instruction("            .s_axi_arprot(s_axi_arprot[m]),")
        self.module.instruction("            .s_axi_arvalid(s_axi_arvalid[m]),")
        self.module.instruction("            .s_axi_arready(s_axi_arready[m]),")
        self.module.instruction("")
        self.module.instruction("            .s_axi_rid(s_axi_rid[m]),")
        self.module.instruction("            .s_axi_rdata(s_axi_rdata[m]),")
        self.module.instruction("            .s_axi_rresp(s_axi_rresp[m]),")
        self.module.instruction("            .s_axi_rlast(s_axi_rlast[m]),")
        self.module.instruction("            .s_axi_rvalid(s_axi_rvalid[m]),")
        self.module.instruction("            .s_axi_rready(s_axi_rready[m]),")
        self.module.instruction("")
        self.module.comment("            Crossbar interface (xbar_s_axi_* to internal routing)")
        self.module.instruction("            .fub_axi_arid(xbar_s_axi_arid[m]),")
        self.module.instruction("            .fub_axi_araddr(xbar_s_axi_araddr[m]),")
        self.module.instruction("            .fub_axi_arlen(xbar_s_axi_arlen[m]),")
        self.module.instruction("            .fub_axi_arsize(xbar_s_axi_arsize[m]),")
        self.module.instruction("            .fub_axi_arburst(xbar_s_axi_arburst[m]),")
        self.module.instruction("            .fub_axi_arlock(xbar_s_axi_arlock[m]),")
        self.module.instruction("            .fub_axi_arcache(xbar_s_axi_arcache[m]),")
        self.module.instruction("            .fub_axi_arprot(xbar_s_axi_arprot[m]),")
        self.module.instruction("            .fub_axi_arvalid(xbar_s_axi_arvalid[m]),")
        self.module.instruction("            .fub_axi_arready(xbar_s_axi_arready[m]),")
        self.module.instruction("")
        self.module.instruction("            .fub_axi_rid(xbar_s_axi_rid[m]),")
        self.module.instruction("            .fub_axi_rdata(xbar_s_axi_rdata[m]),")
        self.module.instruction("            .fub_axi_rresp(xbar_s_axi_rresp[m]),")
        self.module.instruction("            .fub_axi_rlast(xbar_s_axi_rlast[m]),")
        self.module.instruction("            .fub_axi_rvalid(xbar_s_axi_rvalid[m]),")
        self.module.instruction("            .fub_axi_rready(xbar_s_axi_rready[m]),")
        self.module.instruction("")
        self.module.comment("            Extended AXI4 signals (QoS, Region, User) - tied to defaults")
        self.module.instruction("            .s_axi_arqos(4'b0000),      // QoS: lowest priority")
        self.module.instruction("            .s_axi_arregion(4'b0000),   // Region: unused")
        self.module.instruction("            .s_axi_aruser(1'b0),        // User: default")
        self.module.instruction("            .s_axi_ruser(),             // User: unconnected output")
        self.module.instruction("            .fub_axi_arqos(),           // QoS: unconnected output")
        self.module.instruction("            .fub_axi_arregion(),        // Region: unconnected output")
        self.module.instruction("            .fub_axi_aruser(),          // User: unconnected output")
        self.module.instruction("            .fub_axi_ruser(1'b0),       // User: tie to default")
        self.module.instruction("            .busy()                     // Status: unconnected (FPGA, no clock gating)")
        self.module.instruction("        );")
        self.module.instruction("")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

    def generate_slave_side_components(self):
        """
        Generate AMBA axi4_master_wr and axi4_master_rd instances for slave-side interfaces

        One pair (wr + rd) per external slave
        - Crossbar xbar_m_axi_* connects to axi4_master input
        - axi4_master outputs to external m_axi_*
        """
        self.module.comment("==========================================================================")
        self.module.comment("Slave-Side AMBA Components (axi4_master_wr and axi4_master_rd)")
        self.module.comment("==========================================================================")
        self.module.comment("Connect to external slaves with skid buffers and flow control")
        self.module.comment(f"Configuration: SKID_DEPTH_AW={self.cfg.skid_depth_aw}, W={self.cfg.skid_depth_w}, "
                     f"B={self.cfg.skid_depth_b}, AR={self.cfg.skid_depth_ar}, R={self.cfg.skid_depth_r}")
        self.module.comment("==========================================================================")
        self.module.instruction("")

        # Generate instances for each slave
        self.module.instruction("generate")
        self.module.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_slave_side_amba")
        self.module.instruction("")

        # axi4_master_wr instance (AW, W, B channels)
        self.module.comment("        Write path: axi4_master_wr for AW, W, B channels")
        self.module.instruction("        axi4_master_wr #(")
        self.module.instruction("            .AXI_ID_WIDTH(ID_WIDTH),")
        self.module.instruction("            .AXI_ADDR_WIDTH(ADDR_WIDTH),")
        self.module.instruction("            .AXI_DATA_WIDTH(DATA_WIDTH),")
        self.module.instruction(f"            .SKID_DEPTH_AW({self.cfg.skid_depth_aw}),")
        self.module.instruction(f"            .SKID_DEPTH_W({self.cfg.skid_depth_w}),")
        self.module.instruction(f"            .SKID_DEPTH_B({self.cfg.skid_depth_b})")
        self.module.instruction("        ) u_slave_wr (")
        self.module.instruction("            .aclk(aclk),")
        self.module.instruction("            .aresetn(aresetn),")
        self.module.instruction("")
        self.module.comment("            Crossbar interface (xbar_m_axi_* from internal routing)")
        self.module.instruction("            .fub_axi_awid(xbar_m_axi_awid[s]),")
        self.module.instruction("            .fub_axi_awaddr(xbar_m_axi_awaddr[s]),")
        self.module.instruction("            .fub_axi_awlen(xbar_m_axi_awlen[s]),")
        self.module.instruction("            .fub_axi_awsize(xbar_m_axi_awsize[s]),")
        self.module.instruction("            .fub_axi_awburst(xbar_m_axi_awburst[s]),")
        self.module.instruction("            .fub_axi_awlock(xbar_m_axi_awlock[s]),")
        self.module.instruction("            .fub_axi_awcache(xbar_m_axi_awcache[s]),")
        self.module.instruction("            .fub_axi_awprot(xbar_m_axi_awprot[s]),")
        self.module.instruction("            .fub_axi_awvalid(xbar_m_axi_awvalid[s]),")
        self.module.instruction("            .fub_axi_awready(xbar_m_axi_awready[s]),")
        self.module.instruction("")
        self.module.instruction("            .fub_axi_wdata(xbar_m_axi_wdata[s]),")
        self.module.instruction("            .fub_axi_wstrb(xbar_m_axi_wstrb[s]),")
        self.module.instruction("            .fub_axi_wlast(xbar_m_axi_wlast[s]),")
        self.module.instruction("            .fub_axi_wvalid(xbar_m_axi_wvalid[s]),")
        self.module.instruction("            .fub_axi_wready(xbar_m_axi_wready[s]),")
        self.module.instruction("")
        self.module.instruction("            .fub_axi_bid(xbar_m_axi_bid[s]),")
        self.module.instruction("            .fub_axi_bresp(xbar_m_axi_bresp[s]),")
        self.module.instruction("            .fub_axi_bvalid(xbar_m_axi_bvalid[s]),")
        self.module.instruction("            .fub_axi_bready(xbar_m_axi_bready[s]),")
        self.module.instruction("")
        self.module.comment("            External slave interface (m_axi_* to outside)")
        self.module.instruction("            .m_axi_awid(m_axi_awid[s]),")
        self.module.instruction("            .m_axi_awaddr(m_axi_awaddr[s]),")
        self.module.instruction("            .m_axi_awlen(m_axi_awlen[s]),")
        self.module.instruction("            .m_axi_awsize(m_axi_awsize[s]),")
        self.module.instruction("            .m_axi_awburst(m_axi_awburst[s]),")
        self.module.instruction("            .m_axi_awlock(m_axi_awlock[s]),")
        self.module.instruction("            .m_axi_awcache(m_axi_awcache[s]),")
        self.module.instruction("            .m_axi_awprot(m_axi_awprot[s]),")
        self.module.instruction("            .m_axi_awvalid(m_axi_awvalid[s]),")
        self.module.instruction("            .m_axi_awready(m_axi_awready[s]),")
        self.module.instruction("")
        self.module.instruction("            .m_axi_wdata(m_axi_wdata[s]),")
        self.module.instruction("            .m_axi_wstrb(m_axi_wstrb[s]),")
        self.module.instruction("            .m_axi_wlast(m_axi_wlast[s]),")
        self.module.instruction("            .m_axi_wvalid(m_axi_wvalid[s]),")
        self.module.instruction("            .m_axi_wready(m_axi_wready[s]),")
        self.module.instruction("")
        self.module.instruction("            .m_axi_bid(m_axi_bid[s]),")
        self.module.instruction("            .m_axi_bresp(m_axi_bresp[s]),")
        self.module.instruction("            .m_axi_bvalid(m_axi_bvalid[s]),")
        self.module.instruction("            .m_axi_bready(m_axi_bready[s]),")
        self.module.instruction("")
        self.module.comment("            Extended AXI4 signals (QoS, Region, User) - tied to defaults")
        self.module.instruction("            .fub_axi_awqos(4'b0000),    // QoS: tie to default")
        self.module.instruction("            .fub_axi_awregion(4'b0000), // Region: tie to default")
        self.module.instruction("            .fub_axi_awuser(1'b0),      // User: tie to default")
        self.module.instruction("            .fub_axi_wuser(1'b0),       // User: tie to default")
        self.module.instruction("            .fub_axi_buser(),           // User: unconnected input")
        self.module.instruction("            .m_axi_awqos(),             // QoS: unconnected output")
        self.module.instruction("            .m_axi_awregion(),          // Region: unconnected output")
        self.module.instruction("            .m_axi_awuser(),            // User: unconnected output")
        self.module.instruction("            .m_axi_wuser(),             // User: unconnected output")
        self.module.instruction("            .m_axi_buser(1'b0),         // User: tie input to default")
        self.module.instruction("            .busy()                     // Status: unconnected (FPGA, no clock gating)")
        self.module.instruction("        );")
        self.module.instruction("")

        # axi4_master_rd instance (AR, R channels)
        self.module.comment("        Read path: axi4_master_rd for AR, R channels")
        self.module.instruction("        axi4_master_rd #(")
        self.module.instruction("            .AXI_ID_WIDTH(ID_WIDTH),")
        self.module.instruction("            .AXI_ADDR_WIDTH(ADDR_WIDTH),")
        self.module.instruction("            .AXI_DATA_WIDTH(DATA_WIDTH),")
        self.module.instruction(f"            .SKID_DEPTH_AR({self.cfg.skid_depth_ar}),")
        self.module.instruction(f"            .SKID_DEPTH_R({self.cfg.skid_depth_r})")
        self.module.instruction("        ) u_slave_rd (")
        self.module.instruction("            .aclk(aclk),")
        self.module.instruction("            .aresetn(aresetn),")
        self.module.instruction("")
        self.module.comment("            Crossbar interface (xbar_m_axi_* from internal routing)")
        self.module.instruction("            .fub_axi_arid(xbar_m_axi_arid[s]),")
        self.module.instruction("            .fub_axi_araddr(xbar_m_axi_araddr[s]),")
        self.module.instruction("            .fub_axi_arlen(xbar_m_axi_arlen[s]),")
        self.module.instruction("            .fub_axi_arsize(xbar_m_axi_arsize[s]),")
        self.module.instruction("            .fub_axi_arburst(xbar_m_axi_arburst[s]),")
        self.module.instruction("            .fub_axi_arlock(xbar_m_axi_arlock[s]),")
        self.module.instruction("            .fub_axi_arcache(xbar_m_axi_arcache[s]),")
        self.module.instruction("            .fub_axi_arprot(xbar_m_axi_arprot[s]),")
        self.module.instruction("            .fub_axi_arvalid(xbar_m_axi_arvalid[s]),")
        self.module.instruction("            .fub_axi_arready(xbar_m_axi_arready[s]),")
        self.module.instruction("")
        self.module.instruction("            .fub_axi_rid(xbar_m_axi_rid[s]),")
        self.module.instruction("            .fub_axi_rdata(xbar_m_axi_rdata[s]),")
        self.module.instruction("            .fub_axi_rresp(xbar_m_axi_rresp[s]),")
        self.module.instruction("            .fub_axi_rlast(xbar_m_axi_rlast[s]),")
        self.module.instruction("            .fub_axi_rvalid(xbar_m_axi_rvalid[s]),")
        self.module.instruction("            .fub_axi_rready(xbar_m_axi_rready[s]),")
        self.module.instruction("")
        self.module.comment("            External slave interface (m_axi_* to outside)")
        self.module.instruction("            .m_axi_arid(m_axi_arid[s]),")
        self.module.instruction("            .m_axi_araddr(m_axi_araddr[s]),")
        self.module.instruction("            .m_axi_arlen(m_axi_arlen[s]),")
        self.module.instruction("            .m_axi_arsize(m_axi_arsize[s]),")
        self.module.instruction("            .m_axi_arburst(m_axi_arburst[s]),")
        self.module.instruction("            .m_axi_arlock(m_axi_arlock[s]),")
        self.module.instruction("            .m_axi_arcache(m_axi_arcache[s]),")
        self.module.instruction("            .m_axi_arprot(m_axi_arprot[s]),")
        self.module.instruction("            .m_axi_arvalid(m_axi_arvalid[s]),")
        self.module.instruction("            .m_axi_arready(m_axi_arready[s]),")
        self.module.instruction("")
        self.module.instruction("            .m_axi_rid(m_axi_rid[s]),")
        self.module.instruction("            .m_axi_rdata(m_axi_rdata[s]),")
        self.module.instruction("            .m_axi_rresp(m_axi_rresp[s]),")
        self.module.instruction("            .m_axi_rlast(m_axi_rlast[s]),")
        self.module.instruction("            .m_axi_rvalid(m_axi_rvalid[s]),")
        self.module.instruction("            .m_axi_rready(m_axi_rready[s]),")
        self.module.instruction("")
        self.module.comment("            Extended AXI4 signals (QoS, Region, User) - tied to defaults")
        self.module.instruction("            .fub_axi_arqos(4'b0000),    // QoS: tie to default")
        self.module.instruction("            .fub_axi_arregion(4'b0000), // Region: tie to default")
        self.module.instruction("            .fub_axi_aruser(1'b0),      // User: tie to default")
        self.module.instruction("            .fub_axi_ruser(),           // User: unconnected input")
        self.module.instruction("            .m_axi_arqos(),             // QoS: unconnected output")
        self.module.instruction("            .m_axi_arregion(),          // Region: unconnected output")
        self.module.instruction("            .m_axi_aruser(),            // User: unconnected output")
        self.module.instruction("            .m_axi_ruser(1'b0),         // User: tie input to default")
        self.module.instruction("            .busy()                     // Status: unconnected (FPGA, no clock gating)")
        self.module.instruction("        );")
        self.module.instruction("")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")
