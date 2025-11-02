#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BridgeChannelRouter
# Purpose: Channel muxing logic for AW, W, and AR channels
#
# Author: sean galloway
# Created: 2025-10-26

"""
Channel Muxing for Bridge Generator

Handles:
- AW channel muxing (address write)
- W channel muxing with grant tracking
- AR channel muxing (address read)
"""

import sys
from pathlib import Path

# Import the framework
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / 'bin'))
from rtl_generators.verilog.module import Module


class BridgeChannelRouter:
    """
    Channel Muxing for Bridge Crossbar

    Routes granted master's signals to appropriate slave:
    - AW channel: Address write with grant-based muxing
    - W channel: Write data follows AW grant (burst-aware)
    - AR channel: Address read with grant-based muxing
    """

    def __init__(self, module: Module, config):
        """
        Initialize channel router

        Args:
            module: Module instance for RTL generation
            config: BridgeConfig with topology
        """
        self.module = module
        self.cfg = config

    def generate_aw_channel_mux(self):
        """
        Generate AW channel multiplexer

        Routes granted master's AW signals to slave.
        Includes all AW channel signals: addr, id, len, size, burst, lock, cache, prot.
        """
        self.module.comment("==========================================================================")
        self.module.comment("AW Channel Multiplexing")
        self.module.comment("==========================================================================")
        self.module.comment("Mux granted master's write address signals to slave")
        self.module.comment("Grant-based routing ensures only one master per slave at a time")
        self.module.comment("==========================================================================")
        self.module.instruction("")

        self.module.instruction("generate")
        self.module.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_aw_mux")
        self.module.instruction("        always_comb begin")
        self.module.instruction("            // Default: all zeros")
        self.module.instruction("            xbar_m_axi_awaddr[s]  = '0;")
        self.module.instruction("            xbar_m_axi_awid[s]    = '0;")
        self.module.instruction("            xbar_m_axi_awlen[s]   = '0;")
        self.module.instruction("            xbar_m_axi_awsize[s]  = '0;")
        self.module.instruction("            xbar_m_axi_awburst[s] = '0;")
        self.module.instruction("            xbar_m_axi_awlock[s]  = '0;")
        self.module.instruction("            xbar_m_axi_awcache[s] = '0;")
        self.module.instruction("            xbar_m_axi_awprot[s]  = '0;")
        self.module.instruction("            xbar_m_axi_awvalid[s] = 1'b0;")
        self.module.instruction("")
        self.module.instruction("            // Multiplex granted master to this slave")
        self.module.instruction("            for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.module.instruction("                if (aw_grant_matrix[s][m]) begin")
        self.module.instruction("                    xbar_m_axi_awaddr[s]  = xbar_s_axi_awaddr[m];")
        self.module.instruction("                    xbar_m_axi_awid[s]    = xbar_s_axi_awid[m];")
        self.module.instruction("                    xbar_m_axi_awlen[s]   = xbar_s_axi_awlen[m];")
        self.module.instruction("                    xbar_m_axi_awsize[s]  = xbar_s_axi_awsize[m];")
        self.module.instruction("                    xbar_m_axi_awburst[s] = xbar_s_axi_awburst[m];")
        self.module.instruction("                    xbar_m_axi_awlock[s]  = xbar_s_axi_awlock[m];")
        self.module.instruction("                    xbar_m_axi_awcache[s] = xbar_s_axi_awcache[m];")
        self.module.instruction("                    xbar_m_axi_awprot[s]  = xbar_s_axi_awprot[m];")
        self.module.instruction("                    xbar_m_axi_awvalid[s] = xbar_s_axi_awvalid[m];")
        self.module.instruction("                end")
        self.module.instruction("            end")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

        self.module.comment("AWREADY backpressure routing")
        self.module.instruction("generate")
        self.module.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_awready")
        self.module.instruction("        always_comb begin")
        self.module.instruction("            xbar_s_axi_awready[m] = 1'b0;")
        self.module.instruction("            for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.module.instruction("                if (aw_grant_matrix[s][m]) begin")
        self.module.instruction("                    xbar_s_axi_awready[m] = xbar_m_axi_awready[s];")
        self.module.instruction("                end")
        self.module.instruction("            end")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

    def generate_w_channel_mux(self):
        """
        Generate W channel multiplexer with grant tracking

        W data follows AW grant. Need to track which master has grant for W channel.
        Grant persists until WLAST seen.
        """
        self.module.comment("==========================================================================")
        self.module.comment("W Channel Multiplexing (Write Data)")
        self.module.comment("==========================================================================")
        self.module.comment("W channel follows AW grant (burst-aware)")
        self.module.comment("Grant tracking: W grant locked from AWVALID until WLAST")
        self.module.comment("==========================================================================")
        self.module.instruction("")

        # W grant tracking (which master owns W channel for each slave)
        self.module.instruction("// W grant tracking: which master currently owns W channel for each slave")
        self.module.instruction("logic [NUM_MASTERS-1:0] w_grant_matrix [NUM_SLAVES];")
        self.module.instruction("")

        # Track W grants based on AW handshakes
        self.module.instruction("generate")
        self.module.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_w_grant_track")
        self.module.instruction("        always_ff @(posedge aclk or negedge aresetn) begin")
        self.module.instruction("            if (!aresetn) begin")
        self.module.instruction("                w_grant_matrix[s] <= '0;")
        self.module.instruction("            end else begin")
        self.module.instruction("                // Capture AW grant when AW handshake completes")
        self.module.instruction("                if (xbar_m_axi_awvalid[s] && xbar_m_axi_awready[s]) begin")
        self.module.instruction("                    w_grant_matrix[s] <= aw_grant_matrix[s];")
        self.module.instruction("                end")
        self.module.instruction("                // Clear grant when W burst completes (WLAST)")
        self.module.instruction("                else if (xbar_m_axi_wvalid[s] && xbar_m_axi_wready[s] && xbar_m_axi_wlast[s]) begin")
        self.module.instruction("                    w_grant_matrix[s] <= '0;")
        self.module.instruction("                end")
        self.module.instruction("            end")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

        # Mux W data based on W grant
        self.module.instruction("generate")
        self.module.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_w_mux")
        self.module.instruction("        always_comb begin")
        self.module.instruction("            // Default: all zeros")
        self.module.instruction("            xbar_m_axi_wdata[s]  = '0;")
        self.module.instruction("            xbar_m_axi_wstrb[s]  = '0;")
        self.module.instruction("            xbar_m_axi_wlast[s]  = 1'b0;")
        self.module.instruction("            xbar_m_axi_wvalid[s] = 1'b0;")
        self.module.instruction("")
        self.module.instruction("            // Multiplex W data from granted master")
        self.module.instruction("            for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.module.instruction("                if (w_grant_matrix[s][m]) begin")
        self.module.instruction("                    xbar_m_axi_wdata[s]  = xbar_s_axi_wdata[m];")
        self.module.instruction("                    xbar_m_axi_wstrb[s]  = xbar_s_axi_wstrb[m];")
        self.module.instruction("                    xbar_m_axi_wlast[s]  = xbar_s_axi_wlast[m];")
        self.module.instruction("                    xbar_m_axi_wvalid[s] = xbar_s_axi_wvalid[m];")
        self.module.instruction("                end")
        self.module.instruction("            end")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

        self.module.comment("WREADY backpressure routing")
        self.module.instruction("generate")
        self.module.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_wready")
        self.module.instruction("        always_comb begin")
        self.module.instruction("            xbar_s_axi_wready[m] = 1'b0;")
        self.module.instruction("            for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.module.instruction("                if (w_grant_matrix[s][m]) begin")
        self.module.instruction("                    xbar_s_axi_wready[m] = xbar_m_axi_wready[s];")
        self.module.instruction("                end")
        self.module.instruction("            end")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

    def generate_ar_channel_mux(self):
        """
        Generate AR channel multiplexer

        Routes granted master's AR signals to slave.
        Independent from AW channel (separate read/write paths).
        """
        self.module.comment("==========================================================================")
        self.module.comment("AR Channel Multiplexing")
        self.module.comment("==========================================================================")
        self.module.comment("Mux granted master's read address signals to slave")
        self.module.comment("Independent from AW channel (separate read/write paths)")
        self.module.comment("==========================================================================")
        self.module.instruction("")

        self.module.instruction("generate")
        self.module.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_ar_mux")
        self.module.instruction("        always_comb begin")
        self.module.instruction("            // Default: all zeros")
        self.module.instruction("            xbar_m_axi_araddr[s]  = '0;")
        self.module.instruction("            xbar_m_axi_arid[s]    = '0;")
        self.module.instruction("            xbar_m_axi_arlen[s]   = '0;")
        self.module.instruction("            xbar_m_axi_arsize[s]  = '0;")
        self.module.instruction("            xbar_m_axi_arburst[s] = '0;")
        self.module.instruction("            xbar_m_axi_arlock[s]  = '0;")
        self.module.instruction("            xbar_m_axi_arcache[s] = '0;")
        self.module.instruction("            xbar_m_axi_arprot[s]  = '0;")
        self.module.instruction("            xbar_m_axi_arvalid[s] = 1'b0;")
        self.module.instruction("")
        self.module.instruction("            // Multiplex granted master to this slave")
        self.module.instruction("            for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.module.instruction("                if (ar_grant_matrix[s][m]) begin")
        self.module.instruction("                    xbar_m_axi_araddr[s]  = xbar_s_axi_araddr[m];")
        self.module.instruction("                    xbar_m_axi_arid[s]    = xbar_s_axi_arid[m];")
        self.module.instruction("                    xbar_m_axi_arlen[s]   = xbar_s_axi_arlen[m];")
        self.module.instruction("                    xbar_m_axi_arsize[s]  = xbar_s_axi_arsize[m];")
        self.module.instruction("                    xbar_m_axi_arburst[s] = xbar_s_axi_arburst[m];")
        self.module.instruction("                    xbar_m_axi_arlock[s]  = xbar_s_axi_arlock[m];")
        self.module.instruction("                    xbar_m_axi_arcache[s] = xbar_s_axi_arcache[m];")
        self.module.instruction("                    xbar_m_axi_arprot[s]  = xbar_s_axi_arprot[m];")
        self.module.instruction("                    xbar_m_axi_arvalid[s] = xbar_s_axi_arvalid[m];")
        self.module.instruction("                end")
        self.module.instruction("            end")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")

        self.module.comment("ARREADY backpressure routing")
        self.module.instruction("generate")
        self.module.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_arready")
        self.module.instruction("        always_comb begin")
        self.module.instruction("            xbar_s_axi_arready[m] = 1'b0;")
        self.module.instruction("            for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.module.instruction("                if (ar_grant_matrix[s][m]) begin")
        self.module.instruction("                    xbar_s_axi_arready[m] = xbar_m_axi_arready[s];")
        self.module.instruction("                end")
        self.module.instruction("            end")
        self.module.instruction("        end")
        self.module.instruction("    end")
        self.module.instruction("endgenerate")
        self.module.instruction("")
