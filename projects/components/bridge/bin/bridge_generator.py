#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: BridgeConfig
# Purpose: Bridge: AXI4 Full Crossbar Generator (Framework Version)
#
# Documentation: projects/components/bridge/PRD.md
# Subsystem: bridge
#
# Author: sean galloway
# Created: 2025-10-18

"""
Bridge: AXI4 Full Crossbar Generator (Framework Version)
Generates parameterized AXI4 crossbars using the unified verilog framework

Bridge connects masters and slaves across the divide, enabling high-performance
memory-mapped interconnects with out-of-order transaction support.

Author: RTL Design Sherpa
Project: Bridge (AXI4 Full Crossbar Generator)
Version: 1.0 (Framework-based, skeleton)
"""

import argparse
import sys
import os
import math
from dataclasses import dataclass
from typing import Tuple, Dict
from pathlib import Path

# Import the framework
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / 'bin'))
from rtl_generators.verilog.module import Module


@dataclass
class BridgeConfig:
    """Configuration for AXI4 crossbar generation"""
    num_masters: int        # Number of master interfaces
    num_slaves: int         # Number of slave interfaces
    data_width: int         # Data bus width in bits
    addr_width: int         # Address bus width in bits
    id_width: int           # Transaction ID width in bits
    address_map: Dict[int, Dict]  # Address ranges per slave
    pipeline_outputs: bool = True  # Register slave outputs
    enable_counters: bool = True   # Performance counters


class BridgeFlatCrossbar(Module):
    """
    AXI4 Full Crossbar Generator using Module framework

    Key Differences from Delta (AXIS):
    1. 5 independent channels (AW, W, B, AR, R) vs 1 channel
    2. Address range decode vs TDEST decode
    3. ID-based response routing (B, R channels)
    4. Transaction tracking tables for out-of-order support
    5. Separate read/write arbitration
    """

    def __init__(self, config: BridgeConfig):
        self.cfg = config
        self.module_str = f'bridge_axi4_flat_{config.num_masters}x{config.num_slaves}'

        # Initialize Module base class
        Module.__init__(self, module_name=self.module_str)

        # Define parameters
        param_str = f'''
            parameter int NUM_MASTERS = {config.num_masters},
            parameter int NUM_SLAVES  = {config.num_slaves},
            parameter int DATA_WIDTH  = {config.data_width},
            parameter int ADDR_WIDTH  = {config.addr_width},
            parameter int ID_WIDTH    = {config.id_width},
            parameter int STRB_WIDTH  = {config.data_width // 8}
        '''
        self.params.add_param_string(param_str)

        # Define ports (all 5 AXI4 channels for M masters and S slaves)
        port_str = f'''
            input  logic aclk,
            input  logic aresetn,

            // Master Interfaces - Write Address Channel (AW)
            input  logic [ADDR_WIDTH-1:0]   s_axi_awaddr  [NUM_MASTERS],
            input  logic [ID_WIDTH-1:0]     s_axi_awid    [NUM_MASTERS],
            input  logic [7:0]              s_axi_awlen   [NUM_MASTERS],
            input  logic [2:0]              s_axi_awsize  [NUM_MASTERS],
            input  logic [1:0]              s_axi_awburst [NUM_MASTERS],
            input  logic                    s_axi_awlock  [NUM_MASTERS],
            input  logic [3:0]              s_axi_awcache [NUM_MASTERS],
            input  logic [2:0]              s_axi_awprot  [NUM_MASTERS],
            input  logic                    s_axi_awvalid [NUM_MASTERS],
            output logic                    s_axi_awready [NUM_MASTERS],

            // Master Interfaces - Write Data Channel (W)
            input  logic [DATA_WIDTH-1:0]   s_axi_wdata  [NUM_MASTERS],
            input  logic [STRB_WIDTH-1:0]   s_axi_wstrb  [NUM_MASTERS],
            input  logic                    s_axi_wlast  [NUM_MASTERS],
            input  logic                    s_axi_wvalid [NUM_MASTERS],
            output logic                    s_axi_wready [NUM_MASTERS],

            // Master Interfaces - Write Response Channel (B)
            output logic [ID_WIDTH-1:0]     s_axi_bid    [NUM_MASTERS],
            output logic [1:0]              s_axi_bresp  [NUM_MASTERS],
            output logic                    s_axi_bvalid [NUM_MASTERS],
            input  logic                    s_axi_bready [NUM_MASTERS],

            // Master Interfaces - Read Address Channel (AR)
            input  logic [ADDR_WIDTH-1:0]   s_axi_araddr  [NUM_MASTERS],
            input  logic [ID_WIDTH-1:0]     s_axi_arid    [NUM_MASTERS],
            input  logic [7:0]              s_axi_arlen   [NUM_MASTERS],
            input  logic [2:0]              s_axi_arsize  [NUM_MASTERS],
            input  logic [1:0]              s_axi_arburst [NUM_MASTERS],
            input  logic                    s_axi_arlock  [NUM_MASTERS],
            input  logic [3:0]              s_axi_arcache [NUM_MASTERS],
            input  logic [2:0]              s_axi_arprot  [NUM_MASTERS],
            input  logic                    s_axi_arvalid [NUM_MASTERS],
            output logic                    s_axi_arready [NUM_MASTERS],

            // Master Interfaces - Read Data Channel (R)
            output logic [DATA_WIDTH-1:0]   s_axi_rdata  [NUM_MASTERS],
            output logic [ID_WIDTH-1:0]     s_axi_rid    [NUM_MASTERS],
            output logic [1:0]              s_axi_rresp  [NUM_MASTERS],
            output logic                    s_axi_rlast  [NUM_MASTERS],
            output logic                    s_axi_rvalid [NUM_MASTERS],
            input  logic                    s_axi_rready [NUM_MASTERS],

            // Slave Interfaces - Write Address Channel (AW)
            output logic [ADDR_WIDTH-1:0]   m_axi_awaddr  [NUM_SLAVES],
            output logic [ID_WIDTH-1:0]     m_axi_awid    [NUM_SLAVES],
            output logic [7:0]              m_axi_awlen   [NUM_SLAVES],
            output logic [2:0]              m_axi_awsize  [NUM_SLAVES],
            output logic [1:0]              m_axi_awburst [NUM_SLAVES],
            output logic                    m_axi_awlock  [NUM_SLAVES],
            output logic [3:0]              m_axi_awcache [NUM_SLAVES],
            output logic [2:0]              m_axi_awprot  [NUM_SLAVES],
            output logic                    m_axi_awvalid [NUM_SLAVES],
            input  logic                    m_axi_awready [NUM_SLAVES],

            // Slave Interfaces - Write Data Channel (W)
            output logic [DATA_WIDTH-1:0]   m_axi_wdata  [NUM_SLAVES],
            output logic [STRB_WIDTH-1:0]   m_axi_wstrb  [NUM_SLAVES],
            output logic                    m_axi_wlast  [NUM_SLAVES],
            output logic                    m_axi_wvalid [NUM_SLAVES],
            input  logic                    m_axi_wready [NUM_SLAVES],

            // Slave Interfaces - Write Response Channel (B)
            input  logic [ID_WIDTH-1:0]     m_axi_bid    [NUM_SLAVES],
            input  logic [1:0]              m_axi_bresp  [NUM_SLAVES],
            input  logic                    m_axi_bvalid [NUM_SLAVES],
            output logic                    m_axi_bready [NUM_SLAVES],

            // Slave Interfaces - Read Address Channel (AR)
            output logic [ADDR_WIDTH-1:0]   m_axi_araddr  [NUM_SLAVES],
            output logic [ID_WIDTH-1:0]     m_axi_arid    [NUM_SLAVES],
            output logic [7:0]              m_axi_arlen   [NUM_SLAVES],
            output logic [2:0]              m_axi_arsize  [NUM_SLAVES],
            output logic [1:0]              m_axi_arburst [NUM_SLAVES],
            output logic                    m_axi_arlock  [NUM_SLAVES],
            output logic [3:0]              m_axi_arcache [NUM_SLAVES],
            output logic [2:0]              m_axi_arprot  [NUM_SLAVES],
            output logic                    m_axi_arvalid [NUM_SLAVES],
            input  logic                    m_axi_arready [NUM_SLAVES],

            // Slave Interfaces - Read Data Channel (R)
            input  logic [DATA_WIDTH-1:0]   m_axi_rdata  [NUM_SLAVES],
            input  logic [ID_WIDTH-1:0]     m_axi_rid    [NUM_SLAVES],
            input  logic [1:0]              m_axi_rresp  [NUM_SLAVES],
            input  logic                    m_axi_rlast  [NUM_SLAVES],
            input  logic                    m_axi_rvalid [NUM_SLAVES],
            output logic                    m_axi_rready [NUM_SLAVES]
        '''
        self.ports.add_port_string(port_str)

    def generate_header_comment(self):
        """Generate Bridge-specific header comment"""
        self.comment("==============================================================================")
        self.comment(f"Module: {self.module_str}")
        self.comment("Project: Bridge - AXI4 Full Crossbar Generator")
        self.comment("==============================================================================")
        self.comment(f"Description: AXI4 {self.cfg.num_masters}×{self.cfg.num_slaves} Full Crossbar")
        self.comment("")
        self.comment("Bridge: Connecting masters and slaves across the divide")
        self.comment("")
        self.comment("Generated by: bridge_generator.py (framework version)")
        self.comment("Configuration:")
        self.comment(f"  - Masters: {self.cfg.num_masters}")
        self.comment(f"  - Slaves: {self.cfg.num_slaves}")
        self.comment(f"  - Data Width: {self.cfg.data_width} bits")
        self.comment(f"  - Address Width: {self.cfg.addr_width} bits")
        self.comment(f"  - ID Width: {self.cfg.id_width} bits")
        self.comment("")
        self.comment("Features:")
        self.comment("  - Full 5-channel AXI4 protocol (AW, W, B, AR, R)")
        self.comment("  - Out-of-order transaction support (ID-based routing)")
        self.comment("  - Separate read/write arbitration (no head-of-line blocking)")
        self.comment("  - Burst transfer optimization (grant locking until xlast)")
        self.comment("")
        self.comment("==============================================================================")
        self.instruction("")

    def generate_address_decode(self):
        """
        Generate address range decode logic

        KEY DIFFERENCE from Delta:
        - Delta: Direct TDEST decode (tdest is slave ID)
        - Bridge: Address range checking (like APB but for 2 channels: AW, AR)
        """
        self.comment("==========================================================================")
        self.comment("Write Address Decode (AW channel)")
        self.comment("==========================================================================")
        self.comment("Check each master's AWADDR against all slave address ranges")
        self.comment("Similar to APB crossbar but separate decode for write address channel")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("logic [NUM_MASTERS-1:0] aw_request_matrix [NUM_SLAVES];")
        self.instruction("")

        self.instruction("always_comb begin")
        self.instruction("    // Initialize all write address requests to zero")
        self.instruction("    for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.instruction("        aw_request_matrix[s] = '0;")
        self.instruction("    end")
        self.instruction("")
        self.instruction("    // Decode AWADDR to slave for each master")
        self.instruction("    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("        if (s_axi_awvalid[m]) begin")

        # Generate address range checks for each slave
        for slave_idx, slave_info in self.cfg.address_map.items():
            base = slave_info['base']
            size = slave_info['size']
            name = slave_info.get('name', f'Slave{slave_idx}')
            end = base + size

            self.instruction(f"            // Slave {slave_idx}: {name} (0x{base:08X} - 0x{end-1:08X})")
            # Skip redundant >= 0 check for unsigned addresses
            if base == 0:
                self.instruction(f"            if (s_axi_awaddr[m] < {self.cfg.addr_width}'h{end:X})")
            else:
                self.instruction(f"            if (s_axi_awaddr[m] >= {self.cfg.addr_width}'h{base:X} &&")
                self.instruction(f"                s_axi_awaddr[m] < {self.cfg.addr_width}'h{end:X})")
            self.instruction(f"                aw_request_matrix[{slave_idx}][m] = 1'b1;")
            self.instruction("")

        self.instruction("        end")
        self.instruction("    end")
        self.instruction("end")
        self.instruction("")

        # Similar decode for AR channel
        self.comment("==========================================================================")
        self.comment("Read Address Decode (AR channel)")
        self.comment("==========================================================================")
        self.comment("Separate decode for read address channel (independent from writes)")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("logic [NUM_MASTERS-1:0] ar_request_matrix [NUM_SLAVES];")
        self.instruction("")

        self.instruction("always_comb begin")
        self.instruction("    // Initialize all read address requests to zero")
        self.instruction("    for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.instruction("        ar_request_matrix[s] = '0;")
        self.instruction("    end")
        self.instruction("")
        self.instruction("    // Decode ARADDR to slave for each master")
        self.instruction("    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("        if (s_axi_arvalid[m]) begin")

        for slave_idx, slave_info in self.cfg.address_map.items():
            base = slave_info['base']
            size = slave_info['size']
            name = slave_info.get('name', f'Slave{slave_idx}')
            end = base + size

            self.instruction(f"            // Slave {slave_idx}: {name} (0x{base:08X} - 0x{end-1:08X})")
            # Skip redundant >= 0 check for unsigned addresses
            if base == 0:
                self.instruction(f"            if (s_axi_araddr[m] < {self.cfg.addr_width}'h{end:X})")
            else:
                self.instruction(f"            if (s_axi_araddr[m] >= {self.cfg.addr_width}'h{base:X} &&")
                self.instruction(f"                s_axi_araddr[m] < {self.cfg.addr_width}'h{end:X})")
            self.instruction(f"                ar_request_matrix[{slave_idx}][m] = 1'b1;")
            self.instruction("")

        self.instruction("        end")
        self.instruction("    end")
        self.instruction("end")
        self.instruction("")

    def generate_aw_arbiter(self):
        """
        Generate AW (Write Address) channel arbiter logic

        Similar to Delta arbiter but adapted for AXI4:
        - Round-robin arbitration among requesting masters
        - Grant held until AW handshake completes (AWVALID && AWREADY)
        - Transaction stored in ID table (Phase 2)
        """
        self.comment("==========================================================================")
        self.comment("AW Channel Arbitration (Write Address)")
        self.comment("==========================================================================")
        self.comment("Round-robin arbiter per slave for write address channel")
        self.comment("Similar to Delta but for memory-mapped addresses (not streaming)")
        self.comment("Grant held until AWVALID && AWREADY handshake completes")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("logic [NUM_MASTERS-1:0] aw_grant_matrix [NUM_SLAVES];")
        self.instruction("logic [$clog2(NUM_MASTERS)-1:0] aw_last_grant [NUM_SLAVES];")
        self.instruction("logic aw_grant_active [NUM_SLAVES];  // Grant in progress")
        self.instruction("")

        self.comment("AW Arbitration logic for each slave")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_aw_arbiter")
        self.instruction("        always_ff @(posedge aclk or negedge aresetn) begin")
        self.instruction("            if (!aresetn) begin")
        self.instruction("                aw_grant_matrix[s] <= '0;")
        self.instruction("                aw_last_grant[s] <= '0;")
        self.instruction("                aw_grant_active[s] <= 1'b0;")
        self.instruction("            end else begin")
        self.instruction("                if (aw_grant_active[s]) begin")
        self.instruction("                    // Hold grant until AW handshake completes")
        self.instruction("                    if (m_axi_awvalid[s] && m_axi_awready[s]) begin")
        self.instruction("                        aw_grant_active[s] <= 1'b0;")
        self.instruction("                        aw_grant_matrix[s] <= '0;")
        self.instruction("                        // TODO Phase 2: Store master ID in transaction table")
        self.instruction("                    end")
        self.instruction("                end else if (|aw_request_matrix[s]) begin")
        self.instruction("                    // Round-robin arbitration (same algorithm as Delta)")
        self.instruction("                    aw_grant_matrix[s] = '0;")
        self.instruction("                    for (int i = 0; i < NUM_MASTERS; i++) begin")
        self.instruction("                        int m;")
        self.instruction("                        m = (int'(aw_last_grant[s]) + 1 + i) % NUM_MASTERS;")
        self.instruction("                        if (aw_request_matrix[s][m] && aw_grant_matrix[s] == '0) begin")
        self.instruction("                            aw_grant_matrix[s][m] = 1'b1;")
        self.instruction("                            aw_last_grant[s] = m[$clog2(NUM_MASTERS)-1:0];")
        self.instruction("                            aw_grant_active[s] = 1'b1;")
        self.instruction("                        end")
        self.instruction("                    end")
        self.instruction("                end else begin")
        self.instruction("                    aw_grant_matrix[s] <= '0;")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_ar_arbiter(self):
        """
        Generate AR (Read Address) channel arbiter logic

        Independent from AW arbiter (separate read/write paths)
        Same round-robin algorithm
        """
        self.comment("==========================================================================")
        self.comment("AR Channel Arbitration (Read Address)")
        self.comment("==========================================================================")
        self.comment("Independent from write path - no head-of-line blocking")
        self.comment("Round-robin arbiter per slave for read address channel")
        self.comment("Grant held until ARVALID && ARREADY handshake completes")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("logic [NUM_MASTERS-1:0] ar_grant_matrix [NUM_SLAVES];")
        self.instruction("logic [$clog2(NUM_MASTERS)-1:0] ar_last_grant [NUM_SLAVES];")
        self.instruction("logic ar_grant_active [NUM_SLAVES];  // Grant in progress")
        self.instruction("")

        self.comment("AR Arbitration logic for each slave")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_ar_arbiter")
        self.instruction("        always_ff @(posedge aclk or negedge aresetn) begin")
        self.instruction("            if (!aresetn) begin")
        self.instruction("                ar_grant_matrix[s] <= '0;")
        self.instruction("                ar_last_grant[s] <= '0;")
        self.instruction("                ar_grant_active[s] <= 1'b0;")
        self.instruction("            end else begin")
        self.instruction("                if (ar_grant_active[s]) begin")
        self.instruction("                    // Hold grant until AR handshake completes")
        self.instruction("                    if (m_axi_arvalid[s] && m_axi_arready[s]) begin")
        self.instruction("                        ar_grant_active[s] <= 1'b0;")
        self.instruction("                        ar_grant_matrix[s] <= '0;")
        self.instruction("                        // TODO Phase 2: Store master ID in transaction table")
        self.instruction("                    end")
        self.instruction("                end else if (|ar_request_matrix[s]) begin")
        self.instruction("                    // Round-robin arbitration")
        self.instruction("                    ar_grant_matrix[s] = '0;")
        self.instruction("                    for (int i = 0; i < NUM_MASTERS; i++) begin")
        self.instruction("                        int m;")
        self.instruction("                        m = (int'(ar_last_grant[s]) + 1 + i) % NUM_MASTERS;")
        self.instruction("                        if (ar_request_matrix[s][m] && ar_grant_matrix[s] == '0) begin")
        self.instruction("                            ar_grant_matrix[s][m] = 1'b1;")
        self.instruction("                            ar_last_grant[s] = m[$clog2(NUM_MASTERS)-1:0];")
        self.instruction("                            ar_grant_active[s] = 1'b1;")
        self.instruction("                        end")
        self.instruction("                    end")
        self.instruction("                end else begin")
        self.instruction("                    ar_grant_matrix[s] <= '0;")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_aw_channel_mux(self):
        """
        Generate AW channel multiplexer
        Routes granted master's AW signals to slave
        """
        self.comment("==========================================================================")
        self.comment("AW Channel Multiplexing")
        self.comment("==========================================================================")
        self.comment("Mux granted master's write address signals to slave")
        self.comment("Similar to Delta data mux but for AW channel signals")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_aw_mux")
        self.instruction("        always_comb begin")
        self.instruction("            // Default: all zeros")
        self.instruction("            m_axi_awaddr[s]  = '0;")
        self.instruction("            m_axi_awid[s]    = '0;")
        self.instruction("            m_axi_awlen[s]   = '0;")
        self.instruction("            m_axi_awsize[s]  = '0;")
        self.instruction("            m_axi_awburst[s] = '0;")
        self.instruction("            m_axi_awlock[s]  = '0;")
        self.instruction("            m_axi_awcache[s] = '0;")
        self.instruction("            m_axi_awprot[s]  = '0;")
        self.instruction("            m_axi_awvalid[s] = 1'b0;")
        self.instruction("")
        self.instruction("            // Multiplex granted master to this slave")
        self.instruction("            for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("                if (aw_grant_matrix[s][m]) begin")
        self.instruction("                    m_axi_awaddr[s]  = s_axi_awaddr[m];")
        self.instruction("                    m_axi_awid[s]    = s_axi_awid[m];")
        self.instruction("                    m_axi_awlen[s]   = s_axi_awlen[m];")
        self.instruction("                    m_axi_awsize[s]  = s_axi_awsize[m];")
        self.instruction("                    m_axi_awburst[s] = s_axi_awburst[m];")
        self.instruction("                    m_axi_awlock[s]  = s_axi_awlock[m];")
        self.instruction("                    m_axi_awcache[s] = s_axi_awcache[m];")
        self.instruction("                    m_axi_awprot[s]  = s_axi_awprot[m];")
        self.instruction("                    m_axi_awvalid[s] = s_axi_awvalid[m];")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

        self.comment("AWREADY backpressure routing")
        self.instruction("generate")
        self.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_awready")
        self.instruction("        always_comb begin")
        self.instruction("            s_axi_awready[m] = 1'b0;")
        self.instruction("            for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.instruction("                if (aw_grant_matrix[s][m]) begin")
        self.instruction("                    s_axi_awready[m] = m_axi_awready[s];")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_w_channel_mux(self):
        """
        Generate W channel multiplexer

        W channel follows AW grant:
        - When AW handshake completes, W grant locks to that master
        - W grant held until WLAST && WVALID && WREADY
        - No independent arbitration (depends on AW)
        """
        self.comment("==========================================================================")
        self.comment("W Channel Multiplexing (Write Data)")
        self.comment("==========================================================================")
        self.comment("W channel follows AW grant (no independent arbitration)")
        self.comment("Grant locked to master until WLAST completes")
        self.comment("Similar to Delta but with burst support via WLAST")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("logic [NUM_MASTERS-1:0] w_grant_matrix [NUM_SLAVES];")
        self.instruction("logic w_burst_active [NUM_SLAVES];  // W burst in progress")
        self.instruction("")

        self.comment("W grant tracking - lock to master that won AW arbitration")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_w_grant")
        self.instruction("        always_ff @(posedge aclk or negedge aresetn) begin")
        self.instruction("            if (!aresetn) begin")
        self.instruction("                w_grant_matrix[s] <= '0;")
        self.instruction("                w_burst_active[s] <= 1'b0;")
        self.instruction("            end else begin")
        self.instruction("                if (w_burst_active[s]) begin")
        self.instruction("                    // Hold W grant until WLAST completes")
        self.instruction("                    if (m_axi_wvalid[s] && m_axi_wready[s] && m_axi_wlast[s]) begin")
        self.instruction("                        w_burst_active[s] <= 1'b0;")
        self.instruction("                        w_grant_matrix[s] <= '0;")
        self.instruction("                    end")
        self.instruction("                end else if (aw_grant_active[s] && m_axi_awvalid[s] && m_axi_awready[s]) begin")
        self.instruction("                    // AW completed - lock W to the same master")
        self.instruction("                    w_grant_matrix[s] <= aw_grant_matrix[s];")
        self.instruction("                    w_burst_active[s] <= 1'b1;")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

        self.comment("W data multiplexing")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_w_mux")
        self.instruction("        always_comb begin")
        self.instruction("            // Default: all zeros")
        self.instruction("            m_axi_wdata[s]  = '0;")
        self.instruction("            m_axi_wstrb[s]  = '0;")
        self.instruction("            m_axi_wlast[s]  = 1'b0;")
        self.instruction("            m_axi_wvalid[s] = 1'b0;")
        self.instruction("")
        self.instruction("            // Multiplex W signals from locked master")
        self.instruction("            for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("                if (w_grant_matrix[s][m]) begin")
        self.instruction("                    m_axi_wdata[s]  = s_axi_wdata[m];")
        self.instruction("                    m_axi_wstrb[s]  = s_axi_wstrb[m];")
        self.instruction("                    m_axi_wlast[s]  = s_axi_wlast[m];")
        self.instruction("                    m_axi_wvalid[s] = s_axi_wvalid[m];")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

        self.comment("WREADY backpressure routing")
        self.instruction("generate")
        self.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_wready")
        self.instruction("        always_comb begin")
        self.instruction("            s_axi_wready[m] = 1'b0;")
        self.instruction("            for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.instruction("                if (w_grant_matrix[s][m]) begin")
        self.instruction("                    s_axi_wready[m] = m_axi_wready[s];")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_id_tables(self):
        """
        Generate transaction ID tracking tables (Phase 2)

        Purpose: Map {slave_index, transaction_id} → master_index for response routing

        Implementation: Distributed RAM (simple, suitable for small ID_WIDTH)
        - write_id_table: Maps AW transactions to master for B response routing
        - read_id_table: Maps AR transactions to master for R response routing

        Table updates:
        - Written on AW/AR handshake completion
        - Read on B/R response arrival
        - Cleared implicitly on overwrite (ID reuse)

        Complexity: 2 slaves × 2 tables × 16 entries × 1 bit = 64 flip-flops (2x2, ID_WIDTH=4)
        """
        self.comment("==========================================================================")
        self.comment("Transaction ID Tracking Tables (Phase 2)")
        self.comment("==========================================================================")
        self.comment("Purpose: Enable ID-based response routing (out-of-order support)")
        self.comment("")
        self.comment("Structure: Distributed RAM")
        self.comment(f"  - {self.cfg.num_slaves} slaves × 2 tables (write, read)")
        self.comment(f"  - 2^{self.cfg.id_width} = {2**self.cfg.id_width} entries per table")
        self.comment(f"  - Each entry: $clog2({self.cfg.num_masters}) = {math.ceil(math.log2(self.cfg.num_masters))} bits (master index)")
        self.comment("")
        self.comment("Write ID Table: Stores master index for AW transactions → B routing")
        self.comment("Read ID Table:  Stores master index for AR transactions → R routing")
        self.comment("==========================================================================")
        self.instruction("")

        # Declare ID tables
        master_bits = f"$clog2(NUM_MASTERS)" if self.cfg.num_masters > 1 else "0"
        self.instruction(f"// Transaction ID tables: [slave][transaction_id] → master_index")
        self.instruction(f"logic [{master_bits}:0] write_id_table [NUM_SLAVES][2**ID_WIDTH];")
        self.instruction(f"logic [{master_bits}:0] read_id_table [NUM_SLAVES][2**ID_WIDTH];")
        self.instruction("")

        # Generate table write logic
        self.comment("ID Table Write Logic")
        self.comment("Store master index when AW/AR handshakes complete")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_id_table_write")
        self.instruction("        always_ff @(posedge aclk or negedge aresetn) begin")
        self.instruction("            if (!aresetn) begin")
        self.instruction("                // Tables don't need explicit reset (overwritten on use)")
        self.instruction("            end else begin")
        self.instruction("                // Write ID table: Record master for completed AW transactions")
        self.instruction("                if (m_axi_awvalid[s] && m_axi_awready[s]) begin")
        self.instruction("                    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("                        if (aw_grant_matrix[s][m]) begin")
        if self.cfg.num_masters > 1:
            self.instruction(f"                            write_id_table[s][m_axi_awid[s]] <= m[{master_bits}:0];")
        else:
            self.instruction("                            write_id_table[s][m_axi_awid[s]] <= 1'b0;  // Only 1 master")
        self.instruction("                        end")
        self.instruction("                    end")
        self.instruction("                end")
        self.instruction("")
        self.instruction("                // Read ID table: Record master for completed AR transactions")
        self.instruction("                if (m_axi_arvalid[s] && m_axi_arready[s]) begin")
        self.instruction("                    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("                        if (ar_grant_matrix[s][m]) begin")
        if self.cfg.num_masters > 1:
            self.instruction(f"                            read_id_table[s][m_axi_arid[s]] <= m[{master_bits}:0];")
        else:
            self.instruction("                            read_id_table[s][m_axi_arid[s]] <= 1'b0;  // Only 1 master")
        self.instruction("                        end")
        self.instruction("                    end")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_b_channel_demux(self):
        """
        Generate B channel demux (Phase 3 - Write Response)

        KEY CHALLENGE: ID-based routing, not grant-based
        - Lookup master ID from write_id_table using {slave, BID}
        - Route B response to correct master
        - Handle multiple simultaneous responses from different slaves

        Complexity: Each slave can send B responses to any master (out-of-order)
        """
        self.comment("==========================================================================")
        self.comment("B Channel Demux (Write Response) - Phase 3")
        self.comment("==========================================================================")
        self.comment("ID-based routing: Lookup master from write_id_table[slave][bid]")
        self.comment("KEY DIFFERENCE from grant-based: Responses can be out-of-order")
        self.comment("Multiple slaves can respond simultaneously to different masters")
        self.comment("==========================================================================")
        self.instruction("")

        # B channel signals to masters (combinational routing)
        self.instruction("// B channel response routing to masters")
        self.instruction("logic [ID_WIDTH-1:0]     b_routed_id    [NUM_MASTERS];")
        self.instruction("logic [1:0]              b_routed_resp  [NUM_MASTERS];")
        self.instruction("logic                    b_routed_valid [NUM_MASTERS];")
        self.instruction("")

        self.instruction("always_comb begin")
        self.instruction("    // Initialize all master B channels to idle")
        self.instruction("    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("        b_routed_id[m]    = '0;")
        self.instruction("        b_routed_resp[m]  = 2'b00;")
        self.instruction("        b_routed_valid[m] = 1'b0;")
        self.instruction("    end")
        self.instruction("")
        self.instruction("    // Route B responses from each slave to target master")
        self.instruction("    for (int s = 0; s < NUM_SLAVES; s++) begin")
        master_bits_expr = "$clog2(NUM_MASTERS)-1" if self.cfg.num_masters > 1 else "0"
        self.instruction(f"        int target_master;  // Master index for this B response")
        self.instruction("        if (m_axi_bvalid[s]) begin")
        self.instruction("            // Lookup which master this transaction belongs to")
        self.instruction(f"            target_master = int'(write_id_table[s][m_axi_bid[s]]);")
        self.instruction("")
        self.instruction("            // Route to target master (ID-based, not grant-based)")
        self.instruction("            b_routed_id[target_master]    = m_axi_bid[s];")
        self.instruction("            b_routed_resp[target_master]  = m_axi_bresp[s];")
        self.instruction("            b_routed_valid[target_master] = 1'b1;")
        self.instruction("        end else begin")
        self.instruction("            target_master = 0;  // Default when no valid")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("end")
        self.instruction("")

        # Assign to output ports
        self.instruction("// Assign routed B signals to master output ports")
        self.instruction("generate")
        self.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_b_output")
        self.instruction("        assign s_axi_bid[m]    = b_routed_id[m];")
        self.instruction("        assign s_axi_bresp[m]  = b_routed_resp[m];")
        self.instruction("        assign s_axi_bvalid[m] = b_routed_valid[m];")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

        # B channel backpressure routing (BREADY)
        self.comment("B channel backpressure: Route master's BREADY to slave")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_b_ready")
        self.instruction("        always_comb begin")
        self.instruction("            int target_master;")
        self.instruction("            m_axi_bready[s] = 1'b0;")
        self.instruction("            if (m_axi_bvalid[s]) begin")
        self.instruction("                // Find which master this B response goes to")
        self.instruction(f"                target_master = int'(write_id_table[s][m_axi_bid[s]]);")
        self.instruction("                m_axi_bready[s] = s_axi_bready[target_master];")
        self.instruction("            end else begin")
        self.instruction("                target_master = 0;  // Default when no valid")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_r_channel_demux(self):
        """
        Generate R channel demux (Phase 3 - Read Data/Response)

        Similar to B channel but with burst handling:
        - Lookup master ID from read_id_table using {slave, RID}
        - Route R data/response to correct master
        - Handle RLAST (last beat of read burst)
        - Multiple R beats per transaction, all routed to same master

        Complexity: Burst transactions mean multiple R beats with same RID
        """
        self.comment("==========================================================================")
        self.comment("R Channel Demux (Read Data/Response) - Phase 3")
        self.comment("==========================================================================")
        self.comment("ID-based routing: Lookup master from read_id_table[slave][rid]")
        self.comment("Burst support: Multiple R beats (RLAST indicates last beat)")
        self.comment("Similar to B channel but with DATA_WIDTH data payload")
        self.comment("==========================================================================")
        self.instruction("")

        # R channel signals to masters (combinational routing)
        self.instruction("// R channel response routing to masters")
        self.instruction("logic [DATA_WIDTH-1:0]   r_routed_data  [NUM_MASTERS];")
        self.instruction("logic [ID_WIDTH-1:0]     r_routed_id    [NUM_MASTERS];")
        self.instruction("logic [1:0]              r_routed_resp  [NUM_MASTERS];")
        self.instruction("logic                    r_routed_last  [NUM_MASTERS];")
        self.instruction("logic                    r_routed_valid [NUM_MASTERS];")
        self.instruction("")

        self.instruction("always_comb begin")
        self.instruction("    // Initialize all master R channels to idle")
        self.instruction("    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("        r_routed_data[m]  = '0;")
        self.instruction("        r_routed_id[m]    = '0;")
        self.instruction("        r_routed_resp[m]  = 2'b00;")
        self.instruction("        r_routed_last[m]  = 1'b0;")
        self.instruction("        r_routed_valid[m] = 1'b0;")
        self.instruction("    end")
        self.instruction("")
        self.instruction("    // Route R responses from each slave to target master")
        self.instruction("    for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.instruction(f"        int target_master;  // Master index for this R response")
        self.instruction("        if (m_axi_rvalid[s]) begin")
        self.instruction("            // Lookup which master this transaction belongs to")
        self.instruction(f"            target_master = int'(read_id_table[s][m_axi_rid[s]]);")
        self.instruction("")
        self.instruction("            // Route to target master (ID-based, burst-aware)")
        self.instruction("            r_routed_data[target_master]  = m_axi_rdata[s];")
        self.instruction("            r_routed_id[target_master]    = m_axi_rid[s];")
        self.instruction("            r_routed_resp[target_master]  = m_axi_rresp[s];")
        self.instruction("            r_routed_last[target_master]  = m_axi_rlast[s];")
        self.instruction("            r_routed_valid[target_master] = 1'b1;")
        self.instruction("        end else begin")
        self.instruction("            target_master = 0;  // Default when no valid")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("end")
        self.instruction("")

        # Assign to output ports
        self.instruction("// Assign routed R signals to master output ports")
        self.instruction("generate")
        self.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_r_output")
        self.instruction("        assign s_axi_rdata[m]  = r_routed_data[m];")
        self.instruction("        assign s_axi_rid[m]    = r_routed_id[m];")
        self.instruction("        assign s_axi_rresp[m]  = r_routed_resp[m];")
        self.instruction("        assign s_axi_rlast[m]  = r_routed_last[m];")
        self.instruction("        assign s_axi_rvalid[m] = r_routed_valid[m];")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

        # R channel backpressure routing (RREADY)
        self.comment("R channel backpressure: Route master's RREADY to slave")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_r_ready")
        self.instruction("        always_comb begin")
        self.instruction("            int target_master;")
        self.instruction("            m_axi_rready[s] = 1'b0;")
        self.instruction("            if (m_axi_rvalid[s]) begin")
        self.instruction("                // Find which master this R response goes to")
        self.instruction(f"                target_master = int'(read_id_table[s][m_axi_rid[s]]);")
        self.instruction("                m_axi_rready[s] = s_axi_rready[target_master];")
        self.instruction("            end else begin")
        self.instruction("                target_master = 0;  // Default when no valid")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_ar_channel_mux(self):
        """
        Generate AR channel multiplexer
        Routes granted master's AR signals to slave
        """
        self.comment("==========================================================================")
        self.comment("AR Channel Multiplexing")
        self.comment("==========================================================================")
        self.comment("Mux granted master's read address signals to slave")
        self.comment("Independent from AW channel (separate read/write paths)")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_ar_mux")
        self.instruction("        always_comb begin")
        self.instruction("            // Default: all zeros")
        self.instruction("            m_axi_araddr[s]  = '0;")
        self.instruction("            m_axi_arid[s]    = '0;")
        self.instruction("            m_axi_arlen[s]   = '0;")
        self.instruction("            m_axi_arsize[s]  = '0;")
        self.instruction("            m_axi_arburst[s] = '0;")
        self.instruction("            m_axi_arlock[s]  = '0;")
        self.instruction("            m_axi_arcache[s] = '0;")
        self.instruction("            m_axi_arprot[s]  = '0;")
        self.instruction("            m_axi_arvalid[s] = 1'b0;")
        self.instruction("")
        self.instruction("            // Multiplex granted master to this slave")
        self.instruction("            for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("                if (ar_grant_matrix[s][m]) begin")
        self.instruction("                    m_axi_araddr[s]  = s_axi_araddr[m];")
        self.instruction("                    m_axi_arid[s]    = s_axi_arid[m];")
        self.instruction("                    m_axi_arlen[s]   = s_axi_arlen[m];")
        self.instruction("                    m_axi_arsize[s]  = s_axi_arsize[m];")
        self.instruction("                    m_axi_arburst[s] = s_axi_arburst[m];")
        self.instruction("                    m_axi_arlock[s]  = s_axi_arlock[m];")
        self.instruction("                    m_axi_arcache[s] = s_axi_arcache[m];")
        self.instruction("                    m_axi_arprot[s]  = s_axi_arprot[m];")
        self.instruction("                    m_axi_arvalid[s] = s_axi_arvalid[m];")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

        self.comment("ARREADY backpressure routing")
        self.instruction("generate")
        self.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_arready")
        self.instruction("        always_comb begin")
        self.instruction("            s_axi_arready[m] = 1'b0;")
        self.instruction("            for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.instruction("                if (ar_grant_matrix[s][m]) begin")
        self.instruction("                    s_axi_arready[m] = m_axi_arready[s];")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def verilog(self, file_path):
        """Generate complete RTL (main entry point)"""
        # Generate header comment
        self.generate_header_comment()

        # Generate address decode
        self.generate_address_decode()

        # Generate write path (AW + W channels)
        self.generate_aw_arbiter()
        self.generate_aw_channel_mux()
        self.generate_w_channel_mux()  # Full implementation

        # Generate read path (AR + R channels)
        self.generate_ar_arbiter()
        self.generate_ar_channel_mux()

        # Phase 2: Transaction ID tracking tables
        self.generate_id_tables()

        # Phase 3: Generate response channels (B, R)
        self.generate_b_channel_demux()  # Phase 3: Full B channel implementation
        self.generate_r_channel_demux()  # Phase 3: Full R channel implementation with bursts

        # Module framework handles module header/footer
        self.start()  # Auto-generates module header with ports/params
        self.end()    # Auto-generates endmodule

        # Write to file
        self.write(file_path, f'{self.module_name}.sv')


def main():
    parser = argparse.ArgumentParser(
        description="Bridge: AXI4 Full Crossbar Generator (Framework Version)",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )

    parser.add_argument("--masters", type=int, required=True, help="Number of master interfaces")
    parser.add_argument("--slaves", type=int, required=True, help="Number of slave interfaces")
    parser.add_argument("--data-width", type=int, default=512, help="Data bus width in bits")
    parser.add_argument("--addr-width", type=int, default=64, help="Address bus width in bits")
    parser.add_argument("--id-width", type=int, default=4, help="Transaction ID width in bits")
    parser.add_argument("--output-dir", type=str, default="../rtl", help="Output directory")
    parser.add_argument("--no-pipeline", action="store_true", help="Disable output registers")
    parser.add_argument("--no-counters", action="store_true", help="Disable performance counters")

    args = parser.parse_args()

    # Simple default address map (TODO: make configurable from file)
    address_map = {}
    base_addr = 0x00000000
    size_per_slave = 0x10000000  # 256MB per slave

    for s in range(args.slaves):
        address_map[s] = {
            'base': base_addr,
            'size': size_per_slave,
            'name': f'Slave{s}'
        }
        base_addr += size_per_slave

    config = BridgeConfig(
        num_masters=args.masters,
        num_slaves=args.slaves,
        data_width=args.data_width,
        addr_width=args.addr_width,
        id_width=args.id_width,
        address_map=address_map,
        pipeline_outputs=not args.no_pipeline,
        enable_counters=not args.no_counters
    )

    os.makedirs(args.output_dir, exist_ok=True)

    generator = BridgeFlatCrossbar(config)
    generator.verilog(args.output_dir)
    print(f"✓ Generated skeleton: {args.output_dir}/bridge_axi4_flat_{args.masters}x{args.slaves}.sv")
    print(f"")
    print(f"⚠ NOTE: This is a SKELETON implementation demonstrating framework usage.")
    print(f"  Full implementation requires:")
    print(f"  - 5 arbiters per slave (AW, W, B, AR, R)")
    print(f"  - ID tracking tables for out-of-order support")
    print(f"  - Response demux logic (B, R channels)")
    print(f"  - Burst handling with grant locking")
    print(f"")
    print(f"{'='*70}")
    print(f"✓ Bridge skeleton generation complete (framework version)!")
    print(f"{'='*70}")


if __name__ == "__main__":
    main()
