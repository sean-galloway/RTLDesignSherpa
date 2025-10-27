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
Version: 2.0 (Hierarchical architecture with AMBA components)
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

# Import hierarchical bridge modules
from bridge_amba_integrator import BridgeAmbaIntegrator
from bridge_address_arbiter import BridgeAddressArbiter
from bridge_channel_router import BridgeChannelRouter
from bridge_response_router import BridgeResponseRouter


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
    # AMBA component skid buffer depths
    skid_depth_aw: int = 2  # Address Write channel skid depth
    skid_depth_w: int = 4   # Write data channel skid depth (larger for data)
    skid_depth_b: int = 2   # Write response channel skid depth
    skid_depth_ar: int = 2  # Address Read channel skid depth
    skid_depth_r: int = 4   # Read data channel skid depth (larger for data)


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

        # Instantiate hierarchical modules (pass self as module instance)
        self.amba_integrator = BridgeAmbaIntegrator(self, config)
        self.address_arbiter = BridgeAddressArbiter(self, config)
        self.channel_router = BridgeChannelRouter(self, config)
        self.response_router = BridgeResponseRouter(self, config)

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
        self.comment("Architecture:")
        self.comment("  - AMBA axi4_slave_wr/rd components on master-side interfaces")
        self.comment("  - Internal crossbar routing with standard arbitration")
        self.comment("  - AMBA axi4_master_wr/rd components on slave-side interfaces")
        self.comment("")
        self.comment("Features:")
        self.comment("  - Full 5-channel AXI4 protocol (AW, W, B, AR, R)")
        self.comment("  - Out-of-order transaction support (ID-based routing)")
        self.comment("  - Separate read/write arbitration (no head-of-line blocking)")
        self.comment("  - Burst transfer optimization (grant locking until xlast)")
        self.comment(f"  - Configurable skid buffers (AW={self.cfg.skid_depth_aw}, W={self.cfg.skid_depth_w}, "
                     f"B={self.cfg.skid_depth_b}, AR={self.cfg.skid_depth_ar}, R={self.cfg.skid_depth_r})")
        self.comment("")
        self.comment("==============================================================================")
        self.instruction("")

    def generate_internal_signals(self):
        """
        Generate internal crossbar signal declarations

        Signal flow:
        s_axi_* (external) → [axi4_slave_wr/rd] → xbar_s_axi_* → [crossbar routing]
                          → xbar_m_axi_* → [axi4_master_wr/rd] → m_axi_* (external)
        """
        self.comment("==========================================================================")
        self.comment("Internal Crossbar Signals")
        self.comment("==========================================================================")
        self.comment("Master-side AMBA components (axi4_slave_wr/rd) output to xbar_s_axi_*")
        self.comment("Crossbar routes xbar_s_axi_* to xbar_m_axi_*")
        self.comment("Slave-side AMBA components (axi4_master_wr/rd) input from xbar_m_axi_*")
        self.comment("==========================================================================")
        self.instruction("")

        # Master-side signals (from axi4_slave components to crossbar)
        self.comment("Signals from axi4_slave_wr/rd to crossbar (NUM_MASTERS sets)")
        self.instruction("// Write address channel")
        self.instruction("logic [ADDR_WIDTH-1:0]   xbar_s_axi_awaddr  [NUM_MASTERS];")
        self.instruction("logic [ID_WIDTH-1:0]     xbar_s_axi_awid    [NUM_MASTERS];")
        self.instruction("logic [7:0]              xbar_s_axi_awlen   [NUM_MASTERS];")
        self.instruction("logic [2:0]              xbar_s_axi_awsize  [NUM_MASTERS];")
        self.instruction("logic [1:0]              xbar_s_axi_awburst [NUM_MASTERS];")
        self.instruction("logic                    xbar_s_axi_awlock  [NUM_MASTERS];")
        self.instruction("logic [3:0]              xbar_s_axi_awcache [NUM_MASTERS];")
        self.instruction("logic [2:0]              xbar_s_axi_awprot  [NUM_MASTERS];")
        self.instruction("logic [3:0]              xbar_s_axi_awqos   [NUM_MASTERS];")
        self.instruction("logic [3:0]              xbar_s_axi_awregion [NUM_MASTERS];")
        self.instruction("logic                    xbar_s_axi_awvalid [NUM_MASTERS];")
        self.instruction("logic                    xbar_s_axi_awready [NUM_MASTERS];")
        self.instruction("")
        self.instruction("// Write data channel")
        self.instruction("logic [DATA_WIDTH-1:0]   xbar_s_axi_wdata  [NUM_MASTERS];")
        self.instruction("logic [STRB_WIDTH-1:0]   xbar_s_axi_wstrb  [NUM_MASTERS];")
        self.instruction("logic                    xbar_s_axi_wlast  [NUM_MASTERS];")
        self.instruction("logic                    xbar_s_axi_wvalid [NUM_MASTERS];")
        self.instruction("logic                    xbar_s_axi_wready [NUM_MASTERS];")
        self.instruction("")
        self.instruction("// Write response channel")
        self.instruction("logic [ID_WIDTH-1:0]     xbar_s_axi_bid    [NUM_MASTERS];")
        self.instruction("logic [1:0]              xbar_s_axi_bresp  [NUM_MASTERS];")
        self.instruction("logic                    xbar_s_axi_bvalid [NUM_MASTERS];")
        self.instruction("logic                    xbar_s_axi_bready [NUM_MASTERS];")
        self.instruction("")
        self.instruction("// Read address channel")
        self.instruction("logic [ADDR_WIDTH-1:0]   xbar_s_axi_araddr  [NUM_MASTERS];")
        self.instruction("logic [ID_WIDTH-1:0]     xbar_s_axi_arid    [NUM_MASTERS];")
        self.instruction("logic [7:0]              xbar_s_axi_arlen   [NUM_MASTERS];")
        self.instruction("logic [2:0]              xbar_s_axi_arsize  [NUM_MASTERS];")
        self.instruction("logic [1:0]              xbar_s_axi_arburst [NUM_MASTERS];")
        self.instruction("logic                    xbar_s_axi_arlock  [NUM_MASTERS];")
        self.instruction("logic [3:0]              xbar_s_axi_arcache [NUM_MASTERS];")
        self.instruction("logic [2:0]              xbar_s_axi_arprot  [NUM_MASTERS];")
        self.instruction("logic [3:0]              xbar_s_axi_arqos   [NUM_MASTERS];")
        self.instruction("logic [3:0]              xbar_s_axi_arregion [NUM_MASTERS];")
        self.instruction("logic                    xbar_s_axi_arvalid [NUM_MASTERS];")
        self.instruction("logic                    xbar_s_axi_arready [NUM_MASTERS];")
        self.instruction("")
        self.instruction("// Read data channel")
        self.instruction("logic [DATA_WIDTH-1:0]   xbar_s_axi_rdata  [NUM_MASTERS];")
        self.instruction("logic [ID_WIDTH-1:0]     xbar_s_axi_rid    [NUM_MASTERS];")
        self.instruction("logic [1:0]              xbar_s_axi_rresp  [NUM_MASTERS];")
        self.instruction("logic                    xbar_s_axi_rlast  [NUM_MASTERS];")
        self.instruction("logic                    xbar_s_axi_rvalid [NUM_MASTERS];")
        self.instruction("logic                    xbar_s_axi_rready [NUM_MASTERS];")
        self.instruction("")

        # Slave-side signals (from crossbar to axi4_master components)
        self.comment("Signals from crossbar to axi4_master_wr/rd (NUM_SLAVES sets)")
        self.instruction("// Write address channel")
        self.instruction("logic [ADDR_WIDTH-1:0]   xbar_m_axi_awaddr  [NUM_SLAVES];")
        self.instruction("logic [ID_WIDTH-1:0]     xbar_m_axi_awid    [NUM_SLAVES];")
        self.instruction("logic [7:0]              xbar_m_axi_awlen   [NUM_SLAVES];")
        self.instruction("logic [2:0]              xbar_m_axi_awsize  [NUM_SLAVES];")
        self.instruction("logic [1:0]              xbar_m_axi_awburst [NUM_SLAVES];")
        self.instruction("logic                    xbar_m_axi_awlock  [NUM_SLAVES];")
        self.instruction("logic [3:0]              xbar_m_axi_awcache [NUM_SLAVES];")
        self.instruction("logic [2:0]              xbar_m_axi_awprot  [NUM_SLAVES];")
        self.instruction("logic [3:0]              xbar_m_axi_awqos   [NUM_SLAVES];")
        self.instruction("logic [3:0]              xbar_m_axi_awregion [NUM_SLAVES];")
        self.instruction("logic                    xbar_m_axi_awvalid [NUM_SLAVES];")
        self.instruction("logic                    xbar_m_axi_awready [NUM_SLAVES];")
        self.instruction("")
        self.instruction("// Write data channel")
        self.instruction("logic [DATA_WIDTH-1:0]   xbar_m_axi_wdata  [NUM_SLAVES];")
        self.instruction("logic [STRB_WIDTH-1:0]   xbar_m_axi_wstrb  [NUM_SLAVES];")
        self.instruction("logic                    xbar_m_axi_wlast  [NUM_SLAVES];")
        self.instruction("logic                    xbar_m_axi_wvalid [NUM_SLAVES];")
        self.instruction("logic                    xbar_m_axi_wready [NUM_SLAVES];")
        self.instruction("")
        self.instruction("// Write response channel")
        self.instruction("logic [ID_WIDTH-1:0]     xbar_m_axi_bid    [NUM_SLAVES];")
        self.instruction("logic [1:0]              xbar_m_axi_bresp  [NUM_SLAVES];")
        self.instruction("logic                    xbar_m_axi_bvalid [NUM_SLAVES];")
        self.instruction("logic                    xbar_m_axi_bready [NUM_SLAVES];")
        self.instruction("")
        self.instruction("// Read address channel")
        self.instruction("logic [ADDR_WIDTH-1:0]   xbar_m_axi_araddr  [NUM_SLAVES];")
        self.instruction("logic [ID_WIDTH-1:0]     xbar_m_axi_arid    [NUM_SLAVES];")
        self.instruction("logic [7:0]              xbar_m_axi_arlen   [NUM_SLAVES];")
        self.instruction("logic [2:0]              xbar_m_axi_arsize  [NUM_SLAVES];")
        self.instruction("logic [1:0]              xbar_m_axi_arburst [NUM_SLAVES];")
        self.instruction("logic                    xbar_m_axi_arlock  [NUM_SLAVES];")
        self.instruction("logic [3:0]              xbar_m_axi_arcache [NUM_SLAVES];")
        self.instruction("logic [2:0]              xbar_m_axi_arprot  [NUM_SLAVES];")
        self.instruction("logic [3:0]              xbar_m_axi_arqos   [NUM_SLAVES];")
        self.instruction("logic [3:0]              xbar_m_axi_arregion [NUM_SLAVES];")
        self.instruction("logic                    xbar_m_axi_arvalid [NUM_SLAVES];")
        self.instruction("logic                    xbar_m_axi_arready [NUM_SLAVES];")
        self.instruction("")
        self.instruction("// Read data channel")
        self.instruction("logic [DATA_WIDTH-1:0]   xbar_m_axi_rdata  [NUM_SLAVES];")
        self.instruction("logic [ID_WIDTH-1:0]     xbar_m_axi_rid    [NUM_SLAVES];")
        self.instruction("logic [1:0]              xbar_m_axi_rresp  [NUM_SLAVES];")
        self.instruction("logic                    xbar_m_axi_rlast  [NUM_SLAVES];")
        self.instruction("logic                    xbar_m_axi_rvalid [NUM_SLAVES];")
        self.instruction("logic                    xbar_m_axi_rready [NUM_SLAVES];")
        self.instruction("")

    def generate_address_decode(self):
        """
        Generate address range decode logic

        KEY DIFFERENCE from Delta:
        - Delta: Direct TDEST decode (tdest is slave ID)
        - Bridge: Address range checking (like APB but for 2 channels: AW, AR)

        Uses xbar_s_axi_* signals from axi4_slave components
        """
        self.comment("==========================================================================")
        self.comment("Write Address Decode (AW channel)")
        self.comment("==========================================================================")
        self.comment("Check each master's AWADDR against all slave address ranges")
        self.comment("Operates on xbar_s_axi_* signals from axi4_slave_wr components")
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
        self.instruction("        if (xbar_s_axi_awvalid[m]) begin")

        # Generate address range checks for each slave
        for slave_idx, slave_info in self.cfg.address_map.items():
            base = slave_info['base']
            size = slave_info['size']
            name = slave_info.get('name', f'Slave{slave_idx}')
            end = base + size

            self.instruction(f"            // Slave {slave_idx}: {name} (0x{base:08X} - 0x{end-1:08X})")
            # Skip redundant >= 0 check for unsigned addresses
            if base == 0:
                self.instruction(f"            if (xbar_s_axi_awaddr[m] < {self.cfg.addr_width}'h{end:X})")
            else:
                self.instruction(f"            if (xbar_s_axi_awaddr[m] >= {self.cfg.addr_width}'h{base:X} &&")
                self.instruction(f"                xbar_s_axi_awaddr[m] < {self.cfg.addr_width}'h{end:X})")
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
        self.comment("Operates on xbar_s_axi_* signals from axi4_slave_rd components")
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
        self.instruction("        if (xbar_s_axi_arvalid[m]) begin")

        for slave_idx, slave_info in self.cfg.address_map.items():
            base = slave_info['base']
            size = slave_info['size']
            name = slave_info.get('name', f'Slave{slave_idx}')
            end = base + size

            self.instruction(f"            // Slave {slave_idx}: {name} (0x{base:08X} - 0x{end-1:08X})")
            # Skip redundant >= 0 check for unsigned addresses
            if base == 0:
                self.instruction(f"            if (xbar_s_axi_araddr[m] < {self.cfg.addr_width}'h{end:X})")
            else:
                self.instruction(f"            if (xbar_s_axi_araddr[m] >= {self.cfg.addr_width}'h{base:X} &&")
                self.instruction(f"                xbar_s_axi_araddr[m] < {self.cfg.addr_width}'h{end:X})")
            self.instruction(f"                ar_request_matrix[{slave_idx}][m] = 1'b1;")
            self.instruction("")

        self.instruction("        end")
        self.instruction("    end")
        self.instruction("end")
        self.instruction("")

    def generate_aw_arbiter(self):
        """
        Generate AW (Write Address) channel arbiter logic using standard components

        Uses arbiter_round_robin from rtl/common/ with WAIT_GNT_ACK=1:
        - Round-robin arbitration among requesting masters
        - Grant held until AW handshake completes (AWVALID && AWREADY)
        - Proven component (95% test coverage)
        - Easy QoS migration path (use arbiter_round_robin_weighted)
        """
        self.comment("==========================================================================")
        self.comment("AW Channel Arbitration (Write Address) - Using Standard Components")
        self.comment("==========================================================================")
        self.comment("Uses arbiter_round_robin.sv from rtl/common/ with WAIT_GNT_ACK=1")
        self.comment("Grant persistence: Held until AWVALID && AWREADY handshake completes")
        self.comment("Benefits: Proven component, QoS upgrade path, consistent with repo standards")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("logic [NUM_MASTERS-1:0] aw_grant_matrix [NUM_SLAVES];")
        self.instruction("logic aw_grant_active [NUM_SLAVES];  // Grant valid signal")
        self.instruction("logic [NUM_MASTERS-1:0] aw_grant_ack [NUM_SLAVES];  // Grant acknowledgment")
        self.instruction("")

        self.comment("Generate grant_ack signals: Handshake completion triggers ACK")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_aw_grant_ack")
        self.instruction("        always_comb begin")
        self.instruction("            aw_grant_ack[s] = '0;")
        self.instruction("            for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("                if (aw_grant_matrix[s][m] && xbar_m_axi_awvalid[s] && xbar_m_axi_awready[s]) begin")
        self.instruction("                    aw_grant_ack[s][m] = 1'b1;")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

        self.comment("AW Arbiter instances (one per slave)")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_aw_arbiter")
        self.instruction("")
        self.instruction("        arbiter_round_robin #(")
        self.instruction("            .CLIENTS(NUM_MASTERS),")
        self.instruction("            .WAIT_GNT_ACK(1)  // Hold grant until acknowledgment")
        self.instruction("        ) u_aw_arbiter (")
        self.instruction("            .clk         (aclk),")
        self.instruction("            .rst_n       (aresetn),")
        self.instruction("            .block_arb   (1'b0),  // Future: can connect to flow control")
        self.instruction("            .request     (aw_request_matrix[s]),")
        self.instruction("            .grant_ack   (aw_grant_ack[s]),")
        self.instruction("            .grant_valid (aw_grant_active[s]),")
        self.instruction("            .grant       (aw_grant_matrix[s]),")
        self.instruction("            .grant_id    (),  // Optional: can use for debug")
        self.instruction("            .last_grant  ()   // Optional: debug visibility")
        self.instruction("        );")
        self.instruction("")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_ar_arbiter(self):
        """
        Generate AR (Read Address) channel arbiter logic using standard components

        Uses arbiter_round_robin from rtl/common/ with WAIT_GNT_ACK=1:
        - Independent from write path (separate read/write arbitration)
        - Round-robin arbitration among requesting masters
        - Grant held until AR handshake completes (ARVALID && ARREADY)
        - Same proven component as AW arbiter
        """
        self.comment("==========================================================================")
        self.comment("AR Channel Arbitration (Read Address) - Using Standard Components")
        self.comment("==========================================================================")
        self.comment("Uses arbiter_round_robin.sv from rtl/common/ with WAIT_GNT_ACK=1")
        self.comment("Independent from write path - no head-of-line blocking")
        self.comment("Grant persistence: Held until ARVALID && ARREADY handshake completes")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("logic [NUM_MASTERS-1:0] ar_grant_matrix [NUM_SLAVES];")
        self.instruction("logic ar_grant_active [NUM_SLAVES];  // Grant valid signal")
        self.instruction("logic [NUM_MASTERS-1:0] ar_grant_ack [NUM_SLAVES];  // Grant acknowledgment")
        self.instruction("")

        self.comment("Generate grant_ack signals: Handshake completion triggers ACK")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_ar_grant_ack")
        self.instruction("        always_comb begin")
        self.instruction("            ar_grant_ack[s] = '0;")
        self.instruction("            for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("                if (ar_grant_matrix[s][m] && xbar_m_axi_arvalid[s] && xbar_m_axi_arready[s]) begin")
        self.instruction("                    ar_grant_ack[s][m] = 1'b1;")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

        self.comment("AR Arbiter instances (one per slave)")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_ar_arbiter")
        self.instruction("")
        self.instruction("        arbiter_round_robin #(")
        self.instruction("            .CLIENTS(NUM_MASTERS),")
        self.instruction("            .WAIT_GNT_ACK(1)  // Hold grant until acknowledgment")
        self.instruction("        ) u_ar_arbiter (")
        self.instruction("            .clk         (aclk),")
        self.instruction("            .rst_n       (aresetn),")
        self.instruction("            .block_arb   (1'b0),  // Future: can connect to flow control")
        self.instruction("            .request     (ar_request_matrix[s]),")
        self.instruction("            .grant_ack   (ar_grant_ack[s]),")
        self.instruction("            .grant_valid (ar_grant_active[s]),")
        self.instruction("            .grant       (ar_grant_matrix[s]),")
        self.instruction("            .grant_id    (),  // Optional: can use for debug")
        self.instruction("            .last_grant  ()   // Optional: debug visibility")
        self.instruction("        );")
        self.instruction("")
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
        self.comment("Operates on xbar_* internal crossbar signals")
        self.comment("==========================================================================")
        self.instruction("")

        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_aw_mux")
        self.instruction("        always_comb begin")
        self.instruction("            // Default: all zeros")
        self.instruction("            xbar_m_axi_awaddr[s]  = '0;")
        self.instruction("            xbar_m_axi_awid[s]    = '0;")
        self.instruction("            xbar_m_axi_awlen[s]   = '0;")
        self.instruction("            xbar_m_axi_awsize[s]  = '0;")
        self.instruction("            xbar_m_axi_awburst[s] = '0;")
        self.instruction("            xbar_m_axi_awlock[s]  = '0;")
        self.instruction("            xbar_m_axi_awcache[s] = '0;")
        self.instruction("            xbar_m_axi_awprot[s]  = '0;")
        self.instruction("            xbar_m_axi_awqos[s]   = '0;")
        self.instruction("            xbar_m_axi_awregion[s] = '0;")
        self.instruction("            xbar_m_axi_awvalid[s] = 1'b0;")
        self.instruction("")
        self.instruction("            // Multiplex granted master to this slave")
        self.instruction("            for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("                if (aw_grant_matrix[s][m]) begin")
        self.instruction("                    xbar_m_axi_awaddr[s]  = xbar_s_axi_awaddr[m];")
        self.instruction("                    xbar_m_axi_awid[s]    = xbar_s_axi_awid[m];")
        self.instruction("                    xbar_m_axi_awlen[s]   = xbar_s_axi_awlen[m];")
        self.instruction("                    xbar_m_axi_awsize[s]  = xbar_s_axi_awsize[m];")
        self.instruction("                    xbar_m_axi_awburst[s] = xbar_s_axi_awburst[m];")
        self.instruction("                    xbar_m_axi_awlock[s]  = xbar_s_axi_awlock[m];")
        self.instruction("                    xbar_m_axi_awcache[s] = xbar_s_axi_awcache[m];")
        self.instruction("                    xbar_m_axi_awprot[s]  = xbar_s_axi_awprot[m];")
        self.instruction("                    xbar_m_axi_awqos[s]   = xbar_s_axi_awqos[m];")
        self.instruction("                    xbar_m_axi_awregion[s] = xbar_s_axi_awregion[m];")
        self.instruction("                    xbar_m_axi_awvalid[s] = xbar_s_axi_awvalid[m];")
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
        self.instruction("            xbar_s_axi_awready[m] = 1'b0;")
        self.instruction("            for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.instruction("                if (aw_grant_matrix[s][m]) begin")
        self.instruction("                    xbar_s_axi_awready[m] = xbar_m_axi_awready[s];")
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
        self.comment("Operates on xbar_* internal crossbar signals")
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
        self.instruction("                    if (xbar_m_axi_wvalid[s] && xbar_m_axi_wready[s] && xbar_m_axi_wlast[s]) begin")
        self.instruction("                        w_burst_active[s] <= 1'b0;")
        self.instruction("                        w_grant_matrix[s] <= '0;")
        self.instruction("                    end")
        self.instruction("                end else if (aw_grant_active[s] && xbar_m_axi_awvalid[s] && xbar_m_axi_awready[s]) begin")
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
        self.instruction("            xbar_m_axi_wdata[s]  = '0;")
        self.instruction("            xbar_m_axi_wstrb[s]  = '0;")
        self.instruction("            xbar_m_axi_wlast[s]  = 1'b0;")
        self.instruction("            xbar_m_axi_wvalid[s] = 1'b0;")
        self.instruction("")
        self.instruction("            // Multiplex W signals from locked master")
        self.instruction("            for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("                if (w_grant_matrix[s][m]) begin")
        self.instruction("                    xbar_m_axi_wdata[s]  = xbar_s_axi_wdata[m];")
        self.instruction("                    xbar_m_axi_wstrb[s]  = xbar_s_axi_wstrb[m];")
        self.instruction("                    xbar_m_axi_wlast[s]  = xbar_s_axi_wlast[m];")
        self.instruction("                    xbar_m_axi_wvalid[s] = xbar_s_axi_wvalid[m];")
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
        self.instruction("            xbar_s_axi_wready[m] = 1'b0;")
        self.instruction("            for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.instruction("                if (w_grant_matrix[s][m]) begin")
        self.instruction("                    xbar_s_axi_wready[m] = xbar_m_axi_wready[s];")
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
        self.instruction("                if (xbar_m_axi_awvalid[s] && xbar_m_axi_awready[s]) begin")
        self.instruction("                    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("                        if (aw_grant_matrix[s][m]) begin")
        if self.cfg.num_masters > 1:
            self.instruction(f"                            write_id_table[s][xbar_m_axi_awid[s]] <= m[{master_bits}:0];")
        else:
            self.instruction("                            write_id_table[s][xbar_m_axi_awid[s]] <= 1'b0;  // Only 1 master")
        self.instruction("                        end")
        self.instruction("                    end")
        self.instruction("                end")
        self.instruction("")
        self.instruction("                // Read ID table: Record master for completed AR transactions")
        self.instruction("                if (xbar_m_axi_arvalid[s] && xbar_m_axi_arready[s]) begin")
        self.instruction("                    for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("                        if (ar_grant_matrix[s][m]) begin")
        if self.cfg.num_masters > 1:
            self.instruction(f"                            read_id_table[s][xbar_m_axi_arid[s]] <= m[{master_bits}:0];")
        else:
            self.instruction("                            read_id_table[s][xbar_m_axi_arid[s]] <= 1'b0;  // Only 1 master")
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
        self.instruction("        if (xbar_m_axi_bvalid[s]) begin")
        self.instruction("            // Lookup which master this transaction belongs to")
        self.instruction(f"            target_master = int'(write_id_table[s][xbar_m_axi_bid[s]]);")
        self.instruction("")
        self.instruction("            // Route to target master (ID-based, not grant-based)")
        self.instruction("            b_routed_id[target_master]    = xbar_m_axi_bid[s];")
        self.instruction("            b_routed_resp[target_master]  = xbar_m_axi_bresp[s];")
        self.instruction("            b_routed_valid[target_master] = 1'b1;")
        self.instruction("        end else begin")
        self.instruction("            target_master = 0;  // Default when no valid")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("end")
        self.instruction("")

        # Assign to output ports
        self.instruction("// Assign routed B signals to crossbar output")
        self.instruction("generate")
        self.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_b_output")
        self.instruction("        assign xbar_s_axi_bid[m]    = b_routed_id[m];")
        self.instruction("        assign xbar_s_axi_bresp[m]  = b_routed_resp[m];")
        self.instruction("        assign xbar_s_axi_bvalid[m] = b_routed_valid[m];")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

        # B channel backpressure routing (BREADY)
        self.comment("B channel backpressure: Route master's BREADY to slave")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_b_ready")
        self.instruction("        always_comb begin")
        self.instruction("            int target_master;")
        self.instruction("            xbar_m_axi_bready[s] = 1'b0;")
        self.instruction("            if (xbar_m_axi_bvalid[s]) begin")
        self.instruction("                // Find which master this B response goes to")
        self.instruction(f"                target_master = int'(write_id_table[s][xbar_m_axi_bid[s]]);")
        self.instruction("                xbar_m_axi_bready[s] = xbar_s_axi_bready[target_master];")
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
        self.instruction("        if (xbar_m_axi_rvalid[s]) begin")
        self.instruction("            // Lookup which master this transaction belongs to")
        self.instruction(f"            target_master = int'(read_id_table[s][xbar_m_axi_rid[s]]);")
        self.instruction("")
        self.instruction("            // Route to target master (ID-based, burst-aware)")
        self.instruction("            r_routed_data[target_master]  = xbar_m_axi_rdata[s];")
        self.instruction("            r_routed_id[target_master]    = xbar_m_axi_rid[s];")
        self.instruction("            r_routed_resp[target_master]  = xbar_m_axi_rresp[s];")
        self.instruction("            r_routed_last[target_master]  = xbar_m_axi_rlast[s];")
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
        self.instruction("        assign xbar_s_axi_rdata[m]  = r_routed_data[m];")
        self.instruction("        assign xbar_s_axi_rid[m]    = r_routed_id[m];")
        self.instruction("        assign xbar_s_axi_rresp[m]  = r_routed_resp[m];")
        self.instruction("        assign xbar_s_axi_rlast[m]  = r_routed_last[m];")
        self.instruction("        assign xbar_s_axi_rvalid[m] = r_routed_valid[m];")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

        # R channel backpressure routing (RREADY)
        self.comment("R channel backpressure: Route master's RREADY to slave")
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_r_ready")
        self.instruction("        always_comb begin")
        self.instruction("            int target_master;")
        self.instruction("            xbar_m_axi_rready[s] = 1'b0;")
        self.instruction("            if (xbar_m_axi_rvalid[s]) begin")
        self.instruction("                // Find which master this R response goes to")
        self.instruction(f"                target_master = int'(read_id_table[s][xbar_m_axi_rid[s]]);")
        self.instruction("                xbar_m_axi_rready[s] = xbar_s_axi_rready[target_master];")
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
        self.instruction("            xbar_m_axi_araddr[s]  = '0;")
        self.instruction("            xbar_m_axi_arid[s]    = '0;")
        self.instruction("            xbar_m_axi_arlen[s]   = '0;")
        self.instruction("            xbar_m_axi_arsize[s]  = '0;")
        self.instruction("            xbar_m_axi_arburst[s] = '0;")
        self.instruction("            xbar_m_axi_arlock[s]  = '0;")
        self.instruction("            xbar_m_axi_arcache[s] = '0;")
        self.instruction("            xbar_m_axi_arprot[s]  = '0;")
        self.instruction("            xbar_m_axi_arvalid[s] = 1'b0;")
        self.instruction("")
        self.instruction("            // Multiplex granted master to this slave")
        self.instruction("            for (int m = 0; m < NUM_MASTERS; m++) begin")
        self.instruction("                if (ar_grant_matrix[s][m]) begin")
        self.instruction("                    xbar_m_axi_araddr[s]  = xbar_s_axi_araddr[m];")
        self.instruction("                    xbar_m_axi_arid[s]    = xbar_s_axi_arid[m];")
        self.instruction("                    xbar_m_axi_arlen[s]   = xbar_s_axi_arlen[m];")
        self.instruction("                    xbar_m_axi_arsize[s]  = xbar_s_axi_arsize[m];")
        self.instruction("                    xbar_m_axi_arburst[s] = xbar_s_axi_arburst[m];")
        self.instruction("                    xbar_m_axi_arlock[s]  = xbar_s_axi_arlock[m];")
        self.instruction("                    xbar_m_axi_arcache[s] = xbar_s_axi_arcache[m];")
        self.instruction("                    xbar_m_axi_arprot[s]  = xbar_s_axi_arprot[m];")
        self.instruction("                    xbar_m_axi_arvalid[s] = xbar_s_axi_arvalid[m];")
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
        self.instruction("            xbar_s_axi_arready[m] = 1'b0;")
        self.instruction("            for (int s = 0; s < NUM_SLAVES; s++) begin")
        self.instruction("                if (ar_grant_matrix[s][m]) begin")
        self.instruction("                    xbar_s_axi_arready[m] = xbar_m_axi_arready[s];")
        self.instruction("                end")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_master_side_components(self):
        """
        Generate AMBA axi4_slave_wr and axi4_slave_rd instances for master-side interfaces

        One pair (wr + rd) per external master
        - External s_axi_* connects to axi4_slave components
        - axi4_slave outputs to xbar_s_axi_* (crossbar input)
        """
        self.comment("==========================================================================")
        self.comment("Master-Side AMBA Components (axi4_slave_wr and axi4_slave_rd)")
        self.comment("==========================================================================")
        self.comment("Accept connections from external masters with skid buffers and flow control")
        self.comment(f"Configuration: SKID_DEPTH_AW={self.cfg.skid_depth_aw}, W={self.cfg.skid_depth_w}, "
                     f"B={self.cfg.skid_depth_b}, AR={self.cfg.skid_depth_ar}, R={self.cfg.skid_depth_r}")
        self.comment("==========================================================================")
        self.instruction("")

        # Generate instances for each master
        self.instruction("generate")
        self.instruction("    for (genvar m = 0; m < NUM_MASTERS; m++) begin : gen_master_side_amba")
        self.instruction("")

        # Write path component (axi4_slave_wr)
        self.comment("Write path: AW, W, B channels")
        self.instruction("        axi4_slave_wr #(")
        self.instruction(f"            .SKID_DEPTH_AW({self.cfg.skid_depth_aw}),")
        self.instruction(f"            .SKID_DEPTH_W({self.cfg.skid_depth_w}),")
        self.instruction(f"            .SKID_DEPTH_B({self.cfg.skid_depth_b}),")
        self.instruction("            .AXI_ID_WIDTH(ID_WIDTH),")
        self.instruction("            .AXI_ADDR_WIDTH(ADDR_WIDTH),")
        self.instruction("            .AXI_DATA_WIDTH(DATA_WIDTH)")
        self.instruction("        ) u_master_wr (")
        self.instruction("            .aclk           (aclk),")
        self.instruction("            .aresetn        (aresetn),")
        self.instruction("            // External slave interface (from external master)")
        self.instruction("            .s_axi_awid     (s_axi_awid[m]),")
        self.instruction("            .s_axi_awaddr   (s_axi_awaddr[m]),")
        self.instruction("            .s_axi_awlen    (s_axi_awlen[m]),")
        self.instruction("            .s_axi_awsize   (s_axi_awsize[m]),")
        self.instruction("            .s_axi_awburst  (s_axi_awburst[m]),")
        self.instruction("            .s_axi_awlock   (s_axi_awlock[m]),")
        self.instruction("            .s_axi_awcache  (s_axi_awcache[m]),")
        self.instruction("            .s_axi_awprot   (s_axi_awprot[m]),")
        self.instruction("            .s_axi_awqos    (4'h0),  // Not used")
        self.instruction("            .s_axi_awregion (4'h0),  // Not used")
        self.instruction("            .s_axi_awuser   (1'b0),  // Not used")
        self.instruction("            .s_axi_awvalid  (s_axi_awvalid[m]),")
        self.instruction("            .s_axi_awready  (s_axi_awready[m]),")
        self.instruction("            .s_axi_wdata    (s_axi_wdata[m]),")
        self.instruction("            .s_axi_wstrb    (s_axi_wstrb[m]),")
        self.instruction("            .s_axi_wlast    (s_axi_wlast[m]),")
        self.instruction("            .s_axi_wuser    (1'b0),  // Not used")
        self.instruction("            .s_axi_wvalid   (s_axi_wvalid[m]),")
        self.instruction("            .s_axi_wready   (s_axi_wready[m]),")
        self.instruction("            .s_axi_bid      (s_axi_bid[m]),")
        self.instruction("            .s_axi_bresp    (s_axi_bresp[m]),")
        self.instruction("            .s_axi_buser    (),  // Not used")
        self.instruction("            .s_axi_bvalid   (s_axi_bvalid[m]),")
        self.instruction("            .s_axi_bready   (s_axi_bready[m]),")
        self.instruction("            // Crossbar interface (to crossbar routing)")
        self.instruction("            .fub_axi_awid     (xbar_s_axi_awid[m]),")
        self.instruction("            .fub_axi_awaddr   (xbar_s_axi_awaddr[m]),")
        self.instruction("            .fub_axi_awlen    (xbar_s_axi_awlen[m]),")
        self.instruction("            .fub_axi_awsize   (xbar_s_axi_awsize[m]),")
        self.instruction("            .fub_axi_awburst  (xbar_s_axi_awburst[m]),")
        self.instruction("            .fub_axi_awlock   (xbar_s_axi_awlock[m]),")
        self.instruction("            .fub_axi_awcache  (xbar_s_axi_awcache[m]),")
        self.instruction("            .fub_axi_awprot   (xbar_s_axi_awprot[m]),")
        self.instruction("            .fub_axi_awqos    (xbar_s_axi_awqos[m]),")
        self.instruction("            .fub_axi_awregion (xbar_s_axi_awregion[m]),")
        self.instruction("            .fub_axi_awuser   (),  // Not used")
        self.instruction("            .fub_axi_awvalid  (xbar_s_axi_awvalid[m]),")
        self.instruction("            .fub_axi_awready  (xbar_s_axi_awready[m]),")
        self.instruction("            .fub_axi_wdata    (xbar_s_axi_wdata[m]),")
        self.instruction("            .fub_axi_wstrb    (xbar_s_axi_wstrb[m]),")
        self.instruction("            .fub_axi_wlast    (xbar_s_axi_wlast[m]),")
        self.instruction("            .fub_axi_wuser    (),  // Not used")
        self.instruction("            .fub_axi_wvalid   (xbar_s_axi_wvalid[m]),")
        self.instruction("            .fub_axi_wready   (xbar_s_axi_wready[m]),")
        self.instruction("            .fub_axi_bid      (xbar_s_axi_bid[m]),")
        self.instruction("            .fub_axi_bresp    (xbar_s_axi_bresp[m]),")
        self.instruction("            .fub_axi_buser    (1'b0),  // Not used")
        self.instruction("            .fub_axi_bvalid   (xbar_s_axi_bvalid[m]),")
        self.instruction("            .fub_axi_bready   (xbar_s_axi_bready[m]),")
        self.instruction("            .busy             ()  // Optional monitoring")
        self.instruction("        );")
        self.instruction("")

        # Read path component (axi4_slave_rd)
        self.comment("Read path: AR, R channels")
        self.instruction("        axi4_slave_rd #(")
        self.instruction(f"            .SKID_DEPTH_AR({self.cfg.skid_depth_ar}),")
        self.instruction(f"            .SKID_DEPTH_R({self.cfg.skid_depth_r}),")
        self.instruction("            .AXI_ID_WIDTH(ID_WIDTH),")
        self.instruction("            .AXI_ADDR_WIDTH(ADDR_WIDTH),")
        self.instruction("            .AXI_DATA_WIDTH(DATA_WIDTH)")
        self.instruction("        ) u_master_rd (")
        self.instruction("            .aclk           (aclk),")
        self.instruction("            .aresetn        (aresetn),")
        self.instruction("            // External slave interface (from external master)")
        self.instruction("            .s_axi_arid     (s_axi_arid[m]),")
        self.instruction("            .s_axi_araddr   (s_axi_araddr[m]),")
        self.instruction("            .s_axi_arlen    (s_axi_arlen[m]),")
        self.instruction("            .s_axi_arsize   (s_axi_arsize[m]),")
        self.instruction("            .s_axi_arburst  (s_axi_arburst[m]),")
        self.instruction("            .s_axi_arlock   (s_axi_arlock[m]),")
        self.instruction("            .s_axi_arcache  (s_axi_arcache[m]),")
        self.instruction("            .s_axi_arprot   (s_axi_arprot[m]),")
        self.instruction("            .s_axi_arqos    (4'h0),  // Not used")
        self.instruction("            .s_axi_arregion (4'h0),  // Not used")
        self.instruction("            .s_axi_aruser   (1'b0),  // Not used")
        self.instruction("            .s_axi_arvalid  (s_axi_arvalid[m]),")
        self.instruction("            .s_axi_arready  (s_axi_arready[m]),")
        self.instruction("            .s_axi_rid      (s_axi_rid[m]),")
        self.instruction("            .s_axi_rdata    (s_axi_rdata[m]),")
        self.instruction("            .s_axi_rresp    (s_axi_rresp[m]),")
        self.instruction("            .s_axi_rlast    (s_axi_rlast[m]),")
        self.instruction("            .s_axi_ruser    (),  // Not used")
        self.instruction("            .s_axi_rvalid   (s_axi_rvalid[m]),")
        self.instruction("            .s_axi_rready   (s_axi_rready[m]),")
        self.instruction("            // Crossbar interface (to crossbar routing)")
        self.instruction("            .fub_axi_arid     (xbar_s_axi_arid[m]),")
        self.instruction("            .fub_axi_araddr   (xbar_s_axi_araddr[m]),")
        self.instruction("            .fub_axi_arlen    (xbar_s_axi_arlen[m]),")
        self.instruction("            .fub_axi_arsize   (xbar_s_axi_arsize[m]),")
        self.instruction("            .fub_axi_arburst  (xbar_s_axi_arburst[m]),")
        self.instruction("            .fub_axi_arlock   (xbar_s_axi_arlock[m]),")
        self.instruction("            .fub_axi_arcache  (xbar_s_axi_arcache[m]),")
        self.instruction("            .fub_axi_arprot   (xbar_s_axi_arprot[m]),")
        self.instruction("            .fub_axi_arqos    (xbar_s_axi_arqos[m]),")
        self.instruction("            .fub_axi_arregion (xbar_s_axi_arregion[m]),")
        self.instruction("            .fub_axi_aruser   (),  // Not used")
        self.instruction("            .fub_axi_arvalid  (xbar_s_axi_arvalid[m]),")
        self.instruction("            .fub_axi_arready  (xbar_s_axi_arready[m]),")
        self.instruction("            .fub_axi_rid      (xbar_s_axi_rid[m]),")
        self.instruction("            .fub_axi_rdata    (xbar_s_axi_rdata[m]),")
        self.instruction("            .fub_axi_rresp    (xbar_s_axi_rresp[m]),")
        self.instruction("            .fub_axi_rlast    (xbar_s_axi_rlast[m]),")
        self.instruction("            .fub_axi_ruser    (1'b0),  // Not used")
        self.instruction("            .fub_axi_rvalid   (xbar_s_axi_rvalid[m]),")
        self.instruction("            .fub_axi_rready   (xbar_s_axi_rready[m]),")
        self.instruction("            .busy             ()  // Optional monitoring")
        self.instruction("        );")
        self.instruction("")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def generate_slave_side_components(self):
        """
        Generate AMBA axi4_master_wr and axi4_master_rd instances for slave-side interfaces

        One pair (wr + rd) per external slave
        - Crossbar xbar_m_axi_* connects to axi4_master input
        - axi4_master outputs to external m_axi_*
        """
        self.comment("==========================================================================")
        self.comment("Slave-Side AMBA Components (axi4_master_wr and axi4_master_rd)")
        self.comment("==========================================================================")
        self.comment("Connect to external slaves with skid buffers and flow control")
        self.comment(f"Configuration: SKID_DEPTH_AW={self.cfg.skid_depth_aw}, W={self.cfg.skid_depth_w}, "
                     f"B={self.cfg.skid_depth_b}, AR={self.cfg.skid_depth_ar}, R={self.cfg.skid_depth_r}")
        self.comment("==========================================================================")
        self.instruction("")

        # Generate instances for each slave
        self.instruction("generate")
        self.instruction("    for (genvar s = 0; s < NUM_SLAVES; s++) begin : gen_slave_side_amba")
        self.instruction("")

        # Write path component (axi4_master_wr)
        self.comment("Write path: AW, W, B channels")
        self.instruction("        axi4_master_wr #(")
        self.instruction(f"            .SKID_DEPTH_AW({self.cfg.skid_depth_aw}),")
        self.instruction(f"            .SKID_DEPTH_W({self.cfg.skid_depth_w}),")
        self.instruction(f"            .SKID_DEPTH_B({self.cfg.skid_depth_b}),")
        self.instruction("            .AXI_ID_WIDTH(ID_WIDTH),")
        self.instruction("            .AXI_ADDR_WIDTH(ADDR_WIDTH),")
        self.instruction("            .AXI_DATA_WIDTH(DATA_WIDTH)")
        self.instruction("        ) u_slave_wr (")
        self.instruction("            .aclk           (aclk),")
        self.instruction("            .aresetn        (aresetn),")
        self.instruction("            // Crossbar interface (from crossbar routing)")
        self.instruction("            .fub_axi_awid     (xbar_m_axi_awid[s]),")
        self.instruction("            .fub_axi_awaddr   (xbar_m_axi_awaddr[s]),")
        self.instruction("            .fub_axi_awlen    (xbar_m_axi_awlen[s]),")
        self.instruction("            .fub_axi_awsize   (xbar_m_axi_awsize[s]),")
        self.instruction("            .fub_axi_awburst  (xbar_m_axi_awburst[s]),")
        self.instruction("            .fub_axi_awlock   (xbar_m_axi_awlock[s]),")
        self.instruction("            .fub_axi_awcache  (xbar_m_axi_awcache[s]),")
        self.instruction("            .fub_axi_awprot   (xbar_m_axi_awprot[s]),")
        self.instruction("            .fub_axi_awqos    (xbar_m_axi_awqos[s]),")
        self.instruction("            .fub_axi_awregion (xbar_m_axi_awregion[s]),")
        self.instruction("            .fub_axi_awuser   (1'b0),  // Not used")
        self.instruction("            .fub_axi_awvalid  (xbar_m_axi_awvalid[s]),")
        self.instruction("            .fub_axi_awready  (xbar_m_axi_awready[s]),")
        self.instruction("            .fub_axi_wdata    (xbar_m_axi_wdata[s]),")
        self.instruction("            .fub_axi_wstrb    (xbar_m_axi_wstrb[s]),")
        self.instruction("            .fub_axi_wlast    (xbar_m_axi_wlast[s]),")
        self.instruction("            .fub_axi_wuser    (1'b0),  // Not used")
        self.instruction("            .fub_axi_wvalid   (xbar_m_axi_wvalid[s]),")
        self.instruction("            .fub_axi_wready   (xbar_m_axi_wready[s]),")
        self.instruction("            .fub_axi_bid      (xbar_m_axi_bid[s]),")
        self.instruction("            .fub_axi_bresp    (xbar_m_axi_bresp[s]),")
        self.instruction("            .fub_axi_buser    (),  // Not used")
        self.instruction("            .fub_axi_bvalid   (xbar_m_axi_bvalid[s]),")
        self.instruction("            .fub_axi_bready   (xbar_m_axi_bready[s]),")
        self.instruction("            // External master interface (to external slave)")
        self.instruction("            .m_axi_awid     (m_axi_awid[s]),")
        self.instruction("            .m_axi_awaddr   (m_axi_awaddr[s]),")
        self.instruction("            .m_axi_awlen    (m_axi_awlen[s]),")
        self.instruction("            .m_axi_awsize   (m_axi_awsize[s]),")
        self.instruction("            .m_axi_awburst  (m_axi_awburst[s]),")
        self.instruction("            .m_axi_awlock   (m_axi_awlock[s]),")
        self.instruction("            .m_axi_awcache  (m_axi_awcache[s]),")
        self.instruction("            .m_axi_awprot   (m_axi_awprot[s]),")
        self.instruction("            .m_axi_awqos    (),  // Not used")
        self.instruction("            .m_axi_awregion (),  // Not used")
        self.instruction("            .m_axi_awuser   (),  // Not used")
        self.instruction("            .m_axi_awvalid  (m_axi_awvalid[s]),")
        self.instruction("            .m_axi_awready  (m_axi_awready[s]),")
        self.instruction("            .m_axi_wdata    (m_axi_wdata[s]),")
        self.instruction("            .m_axi_wstrb    (m_axi_wstrb[s]),")
        self.instruction("            .m_axi_wlast    (m_axi_wlast[s]),")
        self.instruction("            .m_axi_wuser    (),  // Not used")
        self.instruction("            .m_axi_wvalid   (m_axi_wvalid[s]),")
        self.instruction("            .m_axi_wready   (m_axi_wready[s]),")
        self.instruction("            .m_axi_bid      (m_axi_bid[s]),")
        self.instruction("            .m_axi_bresp    (m_axi_bresp[s]),")
        self.instruction("            .m_axi_buser    (1'b0),  // Not used")
        self.instruction("            .m_axi_bvalid   (m_axi_bvalid[s]),")
        self.instruction("            .m_axi_bready   (m_axi_bready[s]),")
        self.instruction("            .busy           ()  // Optional monitoring")
        self.instruction("        );")
        self.instruction("")

        # Read path component (axi4_master_rd)
        self.comment("Read path: AR, R channels")
        self.instruction("        axi4_master_rd #(")
        self.instruction(f"            .SKID_DEPTH_AR({self.cfg.skid_depth_ar}),")
        self.instruction(f"            .SKID_DEPTH_R({self.cfg.skid_depth_r}),")
        self.instruction("            .AXI_ID_WIDTH(ID_WIDTH),")
        self.instruction("            .AXI_ADDR_WIDTH(ADDR_WIDTH),")
        self.instruction("            .AXI_DATA_WIDTH(DATA_WIDTH)")
        self.instruction("        ) u_slave_rd (")
        self.instruction("            .aclk           (aclk),")
        self.instruction("            .aresetn        (aresetn),")
        self.instruction("            // Crossbar interface (from crossbar routing)")
        self.instruction("            .fub_axi_arid     (xbar_m_axi_arid[s]),")
        self.instruction("            .fub_axi_araddr   (xbar_m_axi_araddr[s]),")
        self.instruction("            .fub_axi_arlen    (xbar_m_axi_arlen[s]),")
        self.instruction("            .fub_axi_arsize   (xbar_m_axi_arsize[s]),")
        self.instruction("            .fub_axi_arburst  (xbar_m_axi_arburst[s]),")
        self.instruction("            .fub_axi_arlock   (xbar_m_axi_arlock[s]),")
        self.instruction("            .fub_axi_arcache  (xbar_m_axi_arcache[s]),")
        self.instruction("            .fub_axi_arprot   (xbar_m_axi_arprot[s]),")
        self.instruction("            .fub_axi_arqos    (xbar_m_axi_arqos[s]),")
        self.instruction("            .fub_axi_arregion (xbar_m_axi_arregion[s]),")
        self.instruction("            .fub_axi_aruser   (1'b0),  // Not used")
        self.instruction("            .fub_axi_arvalid  (xbar_m_axi_arvalid[s]),")
        self.instruction("            .fub_axi_arready  (xbar_m_axi_arready[s]),")
        self.instruction("            .fub_axi_rid      (xbar_m_axi_rid[s]),")
        self.instruction("            .fub_axi_rdata    (xbar_m_axi_rdata[s]),")
        self.instruction("            .fub_axi_rresp    (xbar_m_axi_rresp[s]),")
        self.instruction("            .fub_axi_rlast    (xbar_m_axi_rlast[s]),")
        self.instruction("            .fub_axi_ruser    (),  // Not used")
        self.instruction("            .fub_axi_rvalid   (xbar_m_axi_rvalid[s]),")
        self.instruction("            .fub_axi_rready   (xbar_m_axi_rready[s]),")
        self.instruction("            // External master interface (to external slave)")
        self.instruction("            .m_axi_arid     (m_axi_arid[s]),")
        self.instruction("            .m_axi_araddr   (m_axi_araddr[s]),")
        self.instruction("            .m_axi_arlen    (m_axi_arlen[s]),")
        self.instruction("            .m_axi_arsize   (m_axi_arsize[s]),")
        self.instruction("            .m_axi_arburst  (m_axi_arburst[s]),")
        self.instruction("            .m_axi_arlock   (m_axi_arlock[s]),")
        self.instruction("            .m_axi_arcache  (m_axi_arcache[s]),")
        self.instruction("            .m_axi_arprot   (m_axi_arprot[s]),")
        self.instruction("            .m_axi_arqos    (),  // Not used")
        self.instruction("            .m_axi_arregion (),  // Not used")
        self.instruction("            .m_axi_aruser   (),  // Not used")
        self.instruction("            .m_axi_arvalid  (m_axi_arvalid[s]),")
        self.instruction("            .m_axi_arready  (m_axi_arready[s]),")
        self.instruction("            .m_axi_rid      (m_axi_rid[s]),")
        self.instruction("            .m_axi_rdata    (m_axi_rdata[s]),")
        self.instruction("            .m_axi_rresp    (m_axi_rresp[s]),")
        self.instruction("            .m_axi_rlast    (m_axi_rlast[s]),")
        self.instruction("            .m_axi_ruser    (1'b0),  // Not used")
        self.instruction("            .m_axi_rvalid   (m_axi_rvalid[s]),")
        self.instruction("            .m_axi_rready   (m_axi_rready[s]),")
        self.instruction("            .busy           ()  // Optional monitoring")
        self.instruction("        );")
        self.instruction("")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    def verilog(self, file_path):
        """
        Generate complete RTL (main entry point)

        Uses hierarchical modules for clean organization:
        - BridgeAmbaIntegrator: AMBA component instantiation
        - BridgeAddressArbiter: Address decode and arbitration
        - BridgeChannelRouter: Channel muxing (AW, W, AR)
        - BridgeResponseRouter: ID tracking and response routing (B, R)
        """
        # Generate header comment
        self.generate_header_comment()

        # Generate internal crossbar signals (xbar_s_axi_* and xbar_m_axi_*)
        self.generate_internal_signals()

        # ===================================================================
        # Master-Side AMBA Components
        # ===================================================================
        # axi4_slave_wr/rd instances: External s_axi_* → xbar_s_axi_*
        self.amba_integrator.generate_master_side_components()

        # ===================================================================
        # Address Decode and Arbitration
        # ===================================================================
        # Decode addresses and arbitrate between masters for each slave
        self.address_arbiter.generate_address_decode()
        self.address_arbiter.generate_aw_arbiter()
        self.address_arbiter.generate_ar_arbiter()

        # ===================================================================
        # Channel Routing (AW, W, AR)
        # ===================================================================
        # Mux granted master's signals to slaves
        self.channel_router.generate_aw_channel_mux()
        self.channel_router.generate_w_channel_mux()
        self.channel_router.generate_ar_channel_mux()

        # ===================================================================
        # Response Routing (ID Tables, B, R)
        # ===================================================================
        # Track transactions and route responses back to masters
        self.response_router.generate_id_tables()
        self.response_router.generate_b_channel_demux()
        self.response_router.generate_r_channel_demux()

        # ===================================================================
        # Slave-Side AMBA Components
        # ===================================================================
        # axi4_master_wr/rd instances: xbar_m_axi_* → External m_axi_*
        self.amba_integrator.generate_slave_side_components()

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

    # Address map - use topology-specific defaults or sequential fallback
    address_map = {}

    if args.masters == 5 and args.slaves == 3:
        # OOO Bridge topology (bridge_ooo_with_arbiter.sv)
        # Non-overlapping address ranges with proper decode
        address_map = {
            0: {'base': 0x80000000, 'size': 0x80000000, 'name': 'DDR'},      # 2GB
            1: {'base': 0x40000000, 'size': 0x10000000, 'name': 'SRAM'},     # 256MB
            2: {'base': 0x00000000, 'size': 0x00010000, 'name': 'APB'},      # 64KB
        }
    else:
        # Default: sequential address map
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
