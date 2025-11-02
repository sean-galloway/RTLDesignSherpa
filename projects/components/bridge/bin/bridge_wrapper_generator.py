#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: Bridge Wrapper Generator
# Purpose: Generate Verilator-compatible wrapper with individual signals
#
# Verilator VPI doesn't support array port indexing, so we need individual
# signals for cocotb testbenches.

"""
Bridge Wrapper Generator

Creates a thin wrapper that:
1. Exposes individual signals (s0_axi_awvalid, s1_axi_awvalid) for Verilator/cocotb
2. Instantiates the core bridge with array ports internally
3. Connects individual signals to array elements via assign statements

This preserves the clean array-based bridge implementation while providing
Verilator VPI compatibility for testing.
"""

import sys
from pathlib import Path

# Import the framework
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / 'bin'))
from rtl_generators.verilog.module import Module


def generate_bridge_wrapper(num_masters, num_slaves, data_width, addr_width, id_width, output_path):
    """
    Generate Verilator-compatible wrapper for bridge crossbar.

    Args:
        num_masters: Number of master interfaces
        num_slaves: Number of slave interfaces
        data_width: Data bus width
        addr_width: Address bus width
        id_width: Transaction ID width
        output_path: Output file path
    """

    strb_width = data_width // 8
    wrapper_name = f"bridge_wrapper_{num_masters}x{num_slaves}"
    core_name = f"bridge_axi4_flat_{num_masters}x{num_slaves}"

    m = Module(module_name=wrapper_name)

    # Parameters
    param_str = f'''
        parameter int NUM_MASTERS = {num_masters},
        parameter int NUM_SLAVES  = {num_slaves},
        parameter int DATA_WIDTH  = {data_width},
        parameter int ADDR_WIDTH  = {addr_width},
        parameter int ID_WIDTH    = {id_width},
        parameter int STRB_WIDTH  = {strb_width}
    '''
    m.params.add_param_string(param_str)

    # Clock and reset
    port_str = "input  logic aclk,\n    input  logic aresetn"

    # Generate individual ports for each master
    for i in range(num_masters):
        port_str += f",\n\n    // Master {i} - Write Address Channel"
        port_str += f",\n    input  logic [ADDR_WIDTH-1:0]   s{i}_axi_awaddr"
        port_str += f",\n    input  logic [ID_WIDTH-1:0]     s{i}_axi_awid"
        port_str += f",\n    input  logic [7:0]              s{i}_axi_awlen"
        port_str += f",\n    input  logic [2:0]              s{i}_axi_awsize"
        port_str += f",\n    input  logic [1:0]              s{i}_axi_awburst"
        port_str += f",\n    input  logic                    s{i}_axi_awlock"
        port_str += f",\n    input  logic [3:0]              s{i}_axi_awcache"
        port_str += f",\n    input  logic [2:0]              s{i}_axi_awprot"
        port_str += f",\n    input  logic                    s{i}_axi_awvalid"
        port_str += f",\n    output logic                    s{i}_axi_awready"

        port_str += f",\n\n    // Master {i} - Write Data Channel"
        port_str += f",\n    input  logic [DATA_WIDTH-1:0]   s{i}_axi_wdata"
        port_str += f",\n    input  logic [STRB_WIDTH-1:0]   s{i}_axi_wstrb"
        port_str += f",\n    input  logic                    s{i}_axi_wlast"
        port_str += f",\n    input  logic                    s{i}_axi_wvalid"
        port_str += f",\n    output logic                    s{i}_axi_wready"

        port_str += f",\n\n    // Master {i} - Write Response Channel"
        port_str += f",\n    output logic [ID_WIDTH-1:0]     s{i}_axi_bid"
        port_str += f",\n    output logic [1:0]              s{i}_axi_bresp"
        port_str += f",\n    output logic                    s{i}_axi_bvalid"
        port_str += f",\n    input  logic                    s{i}_axi_bready"

        port_str += f",\n\n    // Master {i} - Read Address Channel"
        port_str += f",\n    input  logic [ADDR_WIDTH-1:0]   s{i}_axi_araddr"
        port_str += f",\n    input  logic [ID_WIDTH-1:0]     s{i}_axi_arid"
        port_str += f",\n    input  logic [7:0]              s{i}_axi_arlen"
        port_str += f",\n    input  logic [2:0]              s{i}_axi_arsize"
        port_str += f",\n    input  logic [1:0]              s{i}_axi_arburst"
        port_str += f",\n    input  logic                    s{i}_axi_arlock"
        port_str += f",\n    input  logic [3:0]              s{i}_axi_arcache"
        port_str += f",\n    input  logic [2:0]              s{i}_axi_arprot"
        port_str += f",\n    input  logic                    s{i}_axi_arvalid"
        port_str += f",\n    output logic                    s{i}_axi_arready"

        port_str += f",\n\n    // Master {i} - Read Data Channel"
        port_str += f",\n    output logic [DATA_WIDTH-1:0]   s{i}_axi_rdata"
        port_str += f",\n    output logic [ID_WIDTH-1:0]     s{i}_axi_rid"
        port_str += f",\n    output logic [1:0]              s{i}_axi_rresp"
        port_str += f",\n    output logic                    s{i}_axi_rlast"
        port_str += f",\n    output logic                    s{i}_axi_rvalid"
        port_str += f",\n    input  logic                    s{i}_axi_rready"

    # Generate individual ports for each slave
    for i in range(num_slaves):
        port_str += f",\n\n    // Slave {i} - Write Address Channel"
        port_str += f",\n    output logic [ADDR_WIDTH-1:0]   m{i}_axi_awaddr"
        port_str += f",\n    output logic [ID_WIDTH-1:0]     m{i}_axi_awid"
        port_str += f",\n    output logic [7:0]              m{i}_axi_awlen"
        port_str += f",\n    output logic [2:0]              m{i}_axi_awsize"
        port_str += f",\n    output logic [1:0]              m{i}_axi_awburst"
        port_str += f",\n    output logic                    m{i}_axi_awlock"
        port_str += f",\n    output logic [3:0]              m{i}_axi_awcache"
        port_str += f",\n    output logic [2:0]              m{i}_axi_awprot"
        port_str += f",\n    output logic                    m{i}_axi_awvalid"
        port_str += f",\n    input  logic                    m{i}_axi_awready"

        port_str += f",\n\n    // Slave {i} - Write Data Channel"
        port_str += f",\n    output logic [DATA_WIDTH-1:0]   m{i}_axi_wdata"
        port_str += f",\n    output logic [STRB_WIDTH-1:0]   m{i}_axi_wstrb"
        port_str += f",\n    output logic                    m{i}_axi_wlast"
        port_str += f",\n    output logic                    m{i}_axi_wvalid"
        port_str += f",\n    input  logic                    m{i}_axi_wready"

        port_str += f",\n\n    // Slave {i} - Write Response Channel"
        port_str += f",\n    input  logic [ID_WIDTH-1:0]     m{i}_axi_bid"
        port_str += f",\n    input  logic [1:0]              m{i}_axi_bresp"
        port_str += f",\n    input  logic                    m{i}_axi_bvalid"
        port_str += f",\n    output logic                    m{i}_axi_bready"

        port_str += f",\n\n    // Slave {i} - Read Address Channel"
        port_str += f",\n    output logic [ADDR_WIDTH-1:0]   m{i}_axi_araddr"
        port_str += f",\n    output logic [ID_WIDTH-1:0]     m{i}_axi_arid"
        port_str += f",\n    output logic [7:0]              m{i}_axi_arlen"
        port_str += f",\n    output logic [2:0]              m{i}_axi_arsize"
        port_str += f",\n    output logic [1:0]              m{i}_axi_arburst"
        port_str += f",\n    output logic                    m{i}_axi_arlock"
        port_str += f",\n    output logic [3:0]              m{i}_axi_arcache"
        port_str += f",\n    output logic [2:0]              m{i}_axi_arprot"
        port_str += f",\n    output logic                    m{i}_axi_arvalid"
        port_str += f",\n    input  logic                    m{i}_axi_arready"

        port_str += f",\n\n    // Slave {i} - Read Data Channel"
        port_str += f",\n    input  logic [DATA_WIDTH-1:0]   m{i}_axi_rdata"
        port_str += f",\n    input  logic [ID_WIDTH-1:0]     m{i}_axi_rid"
        port_str += f",\n    input  logic [1:0]              m{i}_axi_rresp"
        port_str += f",\n    input  logic                    m{i}_axi_rlast"
        port_str += f",\n    input  logic                    m{i}_axi_rvalid"
        port_str += f",\n    output logic                    m{i}_axi_rready"

    m.ports.add_port_string(port_str)

    # Generate module header (timescale, module declaration, parameters, ports)
    m.start()

    # Header comment
    m.comment("=" * 78)
    m.comment(f"Module: {wrapper_name}")
    m.comment("Purpose: Verilator-compatible wrapper for AXI4 bridge crossbar")
    m.comment("=" * 78)
    m.comment("")
    m.comment("This wrapper expands array ports into individual signals for")
    m.comment("Verilator VPI compatibility. The core bridge uses arrays internally.")
    m.comment("")
    m.comment(f"Configuration: {num_masters}x{num_slaves}, DW={data_width}, AW={addr_width}, ID={id_width}")
    m.comment("")

    # Internal array signals that connect to core
    m.comment("Internal array signals for core bridge")
    m.instruction(f"logic [ADDR_WIDTH-1:0]   core_s_axi_awaddr  [NUM_MASTERS];")
    m.instruction(f"logic [ID_WIDTH-1:0]     core_s_axi_awid    [NUM_MASTERS];")
    m.instruction(f"logic [7:0]              core_s_axi_awlen   [NUM_MASTERS];")
    m.instruction(f"logic [2:0]              core_s_axi_awsize  [NUM_MASTERS];")
    m.instruction(f"logic [1:0]              core_s_axi_awburst [NUM_MASTERS];")
    m.instruction(f"logic                    core_s_axi_awlock  [NUM_MASTERS];")
    m.instruction(f"logic [3:0]              core_s_axi_awcache [NUM_MASTERS];")
    m.instruction(f"logic [2:0]              core_s_axi_awprot  [NUM_MASTERS];")
    m.instruction(f"logic                    core_s_axi_awvalid [NUM_MASTERS];")
    m.instruction(f"logic                    core_s_axi_awready [NUM_MASTERS];")
    m.comment("")

    m.instruction(f"logic [DATA_WIDTH-1:0]   core_s_axi_wdata  [NUM_MASTERS];")
    m.instruction(f"logic [STRB_WIDTH-1:0]   core_s_axi_wstrb  [NUM_MASTERS];")
    m.instruction(f"logic                    core_s_axi_wlast  [NUM_MASTERS];")
    m.instruction(f"logic                    core_s_axi_wvalid [NUM_MASTERS];")
    m.instruction(f"logic                    core_s_axi_wready [NUM_MASTERS];")
    m.comment("")

    m.instruction(f"logic [ID_WIDTH-1:0]     core_s_axi_bid    [NUM_MASTERS];")
    m.instruction(f"logic [1:0]              core_s_axi_bresp  [NUM_MASTERS];")
    m.instruction(f"logic                    core_s_axi_bvalid [NUM_MASTERS];")
    m.instruction(f"logic                    core_s_axi_bready [NUM_MASTERS];")
    m.comment("")

    m.instruction(f"logic [ADDR_WIDTH-1:0]   core_s_axi_araddr  [NUM_MASTERS];")
    m.instruction(f"logic [ID_WIDTH-1:0]     core_s_axi_arid    [NUM_MASTERS];")
    m.instruction(f"logic [7:0]              core_s_axi_arlen   [NUM_MASTERS];")
    m.instruction(f"logic [2:0]              core_s_axi_arsize  [NUM_MASTERS];")
    m.instruction(f"logic [1:0]              core_s_axi_arburst [NUM_MASTERS];")
    m.instruction(f"logic                    core_s_axi_arlock  [NUM_MASTERS];")
    m.instruction(f"logic [3:0]              core_s_axi_arcache [NUM_MASTERS];")
    m.instruction(f"logic [2:0]              core_s_axi_arprot  [NUM_MASTERS];")
    m.instruction(f"logic                    core_s_axi_arvalid [NUM_MASTERS];")
    m.instruction(f"logic                    core_s_axi_arready [NUM_MASTERS];")
    m.comment("")

    m.instruction(f"logic [DATA_WIDTH-1:0]   core_s_axi_rdata  [NUM_MASTERS];")
    m.instruction(f"logic [ID_WIDTH-1:0]     core_s_axi_rid    [NUM_MASTERS];")
    m.instruction(f"logic [1:0]              core_s_axi_rresp  [NUM_MASTERS];")
    m.instruction(f"logic                    core_s_axi_rlast  [NUM_MASTERS];")
    m.instruction(f"logic                    core_s_axi_rvalid [NUM_MASTERS];")
    m.instruction(f"logic                    core_s_axi_rready [NUM_MASTERS];")
    m.comment("")

    # Slave arrays
    m.instruction(f"logic [ADDR_WIDTH-1:0]   core_m_axi_awaddr  [NUM_SLAVES];")
    m.instruction(f"logic [ID_WIDTH-1:0]     core_m_axi_awid    [NUM_SLAVES];")
    m.instruction(f"logic [7:0]              core_m_axi_awlen   [NUM_SLAVES];")
    m.instruction(f"logic [2:0]              core_m_axi_awsize  [NUM_SLAVES];")
    m.instruction(f"logic [1:0]              core_m_axi_awburst [NUM_SLAVES];")
    m.instruction(f"logic                    core_m_axi_awlock  [NUM_SLAVES];")
    m.instruction(f"logic [3:0]              core_m_axi_awcache [NUM_SLAVES];")
    m.instruction(f"logic [2:0]              core_m_axi_awprot  [NUM_SLAVES];")
    m.instruction(f"logic                    core_m_axi_awvalid [NUM_SLAVES];")
    m.instruction(f"logic                    core_m_axi_awready [NUM_SLAVES];")
    m.comment("")

    m.instruction(f"logic [DATA_WIDTH-1:0]   core_m_axi_wdata  [NUM_SLAVES];")
    m.instruction(f"logic [STRB_WIDTH-1:0]   core_m_axi_wstrb  [NUM_SLAVES];")
    m.instruction(f"logic                    core_m_axi_wlast  [NUM_SLAVES];")
    m.instruction(f"logic                    core_m_axi_wvalid [NUM_SLAVES];")
    m.instruction(f"logic                    core_m_axi_wready [NUM_SLAVES];")
    m.comment("")

    m.instruction(f"logic [ID_WIDTH-1:0]     core_m_axi_bid    [NUM_SLAVES];")
    m.instruction(f"logic [1:0]              core_m_axi_bresp  [NUM_SLAVES];")
    m.instruction(f"logic                    core_m_axi_bvalid [NUM_SLAVES];")
    m.instruction(f"logic                    core_m_axi_bready [NUM_SLAVES];")
    m.comment("")

    m.instruction(f"logic [ADDR_WIDTH-1:0]   core_m_axi_araddr  [NUM_SLAVES];")
    m.instruction(f"logic [ID_WIDTH-1:0]     core_m_axi_arid    [NUM_SLAVES];")
    m.instruction(f"logic [7:0]              core_m_axi_arlen   [NUM_SLAVES];")
    m.instruction(f"logic [2:0]              core_m_axi_arsize  [NUM_SLAVES];")
    m.instruction(f"logic [1:0]              core_m_axi_arburst [NUM_SLAVES];")
    m.instruction(f"logic                    core_m_axi_arlock  [NUM_SLAVES];")
    m.instruction(f"logic [3:0]              core_m_axi_arcache [NUM_SLAVES];")
    m.instruction(f"logic [2:0]              core_m_axi_arprot  [NUM_SLAVES];")
    m.instruction(f"logic                    core_m_axi_arvalid [NUM_SLAVES];")
    m.instruction(f"logic                    core_m_axi_arready [NUM_SLAVES];")
    m.comment("")

    m.instruction(f"logic [DATA_WIDTH-1:0]   core_m_axi_rdata  [NUM_SLAVES];")
    m.instruction(f"logic [ID_WIDTH-1:0]     core_m_axi_rid    [NUM_SLAVES];")
    m.instruction(f"logic [1:0]              core_m_axi_rresp  [NUM_SLAVES];")
    m.instruction(f"logic                    core_m_axi_rlast  [NUM_SLAVES];")
    m.instruction(f"logic                    core_m_axi_rvalid [NUM_SLAVES];")
    m.instruction(f"logic                    core_m_axi_rready [NUM_SLAVES];")
    m.comment("")

    # Connection assigns for masters
    m.comment("Connect individual master signals to internal arrays")
    for i in range(num_masters):
        m.comment(f"Master {i} connections")
        # AW channel
        m.instruction(f"assign core_s_axi_awaddr[{i}]  = s{i}_axi_awaddr;")
        m.instruction(f"assign core_s_axi_awid[{i}]    = s{i}_axi_awid;")
        m.instruction(f"assign core_s_axi_awlen[{i}]   = s{i}_axi_awlen;")
        m.instruction(f"assign core_s_axi_awsize[{i}]  = s{i}_axi_awsize;")
        m.instruction(f"assign core_s_axi_awburst[{i}] = s{i}_axi_awburst;")
        m.instruction(f"assign core_s_axi_awlock[{i}]  = s{i}_axi_awlock;")
        m.instruction(f"assign core_s_axi_awcache[{i}] = s{i}_axi_awcache;")
        m.instruction(f"assign core_s_axi_awprot[{i}]  = s{i}_axi_awprot;")
        m.instruction(f"assign core_s_axi_awvalid[{i}] = s{i}_axi_awvalid;")
        m.instruction(f"assign s{i}_axi_awready = core_s_axi_awready[{i}];")
        m.comment("")

        # W channel
        m.instruction(f"assign core_s_axi_wdata[{i}]  = s{i}_axi_wdata;")
        m.instruction(f"assign core_s_axi_wstrb[{i}]  = s{i}_axi_wstrb;")
        m.instruction(f"assign core_s_axi_wlast[{i}]  = s{i}_axi_wlast;")
        m.instruction(f"assign core_s_axi_wvalid[{i}] = s{i}_axi_wvalid;")
        m.instruction(f"assign s{i}_axi_wready = core_s_axi_wready[{i}];")
        m.comment("")

        # B channel
        m.instruction(f"assign s{i}_axi_bid   = core_s_axi_bid[{i}];")
        m.instruction(f"assign s{i}_axi_bresp = core_s_axi_bresp[{i}];")
        m.instruction(f"assign s{i}_axi_bvalid = core_s_axi_bvalid[{i}];")
        m.instruction(f"assign core_s_axi_bready[{i}] = s{i}_axi_bready;")
        m.comment("")

        # AR channel
        m.instruction(f"assign core_s_axi_araddr[{i}]  = s{i}_axi_araddr;")
        m.instruction(f"assign core_s_axi_arid[{i}]    = s{i}_axi_arid;")
        m.instruction(f"assign core_s_axi_arlen[{i}]   = s{i}_axi_arlen;")
        m.instruction(f"assign core_s_axi_arsize[{i}]  = s{i}_axi_arsize;")
        m.instruction(f"assign core_s_axi_arburst[{i}] = s{i}_axi_arburst;")
        m.instruction(f"assign core_s_axi_arlock[{i}]  = s{i}_axi_arlock;")
        m.instruction(f"assign core_s_axi_arcache[{i}] = s{i}_axi_arcache;")
        m.instruction(f"assign core_s_axi_arprot[{i}]  = s{i}_axi_arprot;")
        m.instruction(f"assign core_s_axi_arvalid[{i}] = s{i}_axi_arvalid;")
        m.instruction(f"assign s{i}_axi_arready = core_s_axi_arready[{i}];")
        m.comment("")

        # R channel
        m.instruction(f"assign s{i}_axi_rdata  = core_s_axi_rdata[{i}];")
        m.instruction(f"assign s{i}_axi_rid    = core_s_axi_rid[{i}];")
        m.instruction(f"assign s{i}_axi_rresp  = core_s_axi_rresp[{i}];")
        m.instruction(f"assign s{i}_axi_rlast  = core_s_axi_rlast[{i}];")
        m.instruction(f"assign s{i}_axi_rvalid = core_s_axi_rvalid[{i}];")
        m.instruction(f"assign core_s_axi_rready[{i}] = s{i}_axi_rready;")
        m.comment("")

    # Connection assigns for slaves
    m.comment("Connect individual slave signals to internal arrays")
    for i in range(num_slaves):
        m.comment(f"Slave {i} connections")
        # AW channel
        m.instruction(f"assign m{i}_axi_awaddr  = core_m_axi_awaddr[{i}];")
        m.instruction(f"assign m{i}_axi_awid    = core_m_axi_awid[{i}];")
        m.instruction(f"assign m{i}_axi_awlen   = core_m_axi_awlen[{i}];")
        m.instruction(f"assign m{i}_axi_awsize  = core_m_axi_awsize[{i}];")
        m.instruction(f"assign m{i}_axi_awburst = core_m_axi_awburst[{i}];")
        m.instruction(f"assign m{i}_axi_awlock  = core_m_axi_awlock[{i}];")
        m.instruction(f"assign m{i}_axi_awcache = core_m_axi_awcache[{i}];")
        m.instruction(f"assign m{i}_axi_awprot  = core_m_axi_awprot[{i}];")
        m.instruction(f"assign m{i}_axi_awvalid = core_m_axi_awvalid[{i}];")
        m.instruction(f"assign core_m_axi_awready[{i}] = m{i}_axi_awready;")
        m.comment("")

        # W channel
        m.instruction(f"assign m{i}_axi_wdata  = core_m_axi_wdata[{i}];")
        m.instruction(f"assign m{i}_axi_wstrb  = core_m_axi_wstrb[{i}];")
        m.instruction(f"assign m{i}_axi_wlast  = core_m_axi_wlast[{i}];")
        m.instruction(f"assign m{i}_axi_wvalid = core_m_axi_wvalid[{i}];")
        m.instruction(f"assign core_m_axi_wready[{i}] = m{i}_axi_wready;")
        m.comment("")

        # B channel
        m.instruction(f"assign core_m_axi_bid[{i}]   = m{i}_axi_bid;")
        m.instruction(f"assign core_m_axi_bresp[{i}] = m{i}_axi_bresp;")
        m.instruction(f"assign core_m_axi_bvalid[{i}] = m{i}_axi_bvalid;")
        m.instruction(f"assign m{i}_axi_bready = core_m_axi_bready[{i}];")
        m.comment("")

        # AR channel
        m.instruction(f"assign m{i}_axi_araddr  = core_m_axi_araddr[{i}];")
        m.instruction(f"assign m{i}_axi_arid    = core_m_axi_arid[{i}];")
        m.instruction(f"assign m{i}_axi_arlen   = core_m_axi_arlen[{i}];")
        m.instruction(f"assign m{i}_axi_arsize  = core_m_axi_arsize[{i}];")
        m.instruction(f"assign m{i}_axi_arburst = core_m_axi_arburst[{i}];")
        m.instruction(f"assign m{i}_axi_arlock  = core_m_axi_arlock[{i}];")
        m.instruction(f"assign m{i}_axi_arcache = core_m_axi_arcache[{i}];")
        m.instruction(f"assign m{i}_axi_arprot  = core_m_axi_arprot[{i}];")
        m.instruction(f"assign m{i}_axi_arvalid = core_m_axi_arvalid[{i}];")
        m.instruction(f"assign core_m_axi_arready[{i}] = m{i}_axi_arready;")
        m.comment("")

        # R channel
        m.instruction(f"assign core_m_axi_rdata[{i}]  = m{i}_axi_rdata;")
        m.instruction(f"assign core_m_axi_rid[{i}]    = m{i}_axi_rid;")
        m.instruction(f"assign core_m_axi_rresp[{i}]  = m{i}_axi_rresp;")
        m.instruction(f"assign core_m_axi_rlast[{i}]  = m{i}_axi_rlast;")
        m.instruction(f"assign core_m_axi_rvalid[{i}] = m{i}_axi_rvalid;")
        m.instruction(f"assign m{i}_axi_rready = core_m_axi_rready[{i}];")
        m.comment("")

    # Instantiate core bridge
    m.comment("=" * 78)
    m.comment("Core Bridge Instantiation")
    m.comment("=" * 78)
    m.comment("")
    m.instruction(f"{core_name} #(")
    m.instruction(f"    .NUM_MASTERS (NUM_MASTERS),")
    m.instruction(f"    .NUM_SLAVES  (NUM_SLAVES),")
    m.instruction(f"    .DATA_WIDTH  (DATA_WIDTH),")
    m.instruction(f"    .ADDR_WIDTH  (ADDR_WIDTH),")
    m.instruction(f"    .ID_WIDTH    (ID_WIDTH)")
    m.instruction(f") u_core (")
    m.instruction(f"    .aclk    (aclk),")
    m.instruction(f"    .aresetn (aresetn),")
    m.comment("")
    m.instruction(f"    // Master interfaces (arrays)")
    m.instruction(f"    .s_axi_awaddr  (core_s_axi_awaddr),")
    m.instruction(f"    .s_axi_awid    (core_s_axi_awid),")
    m.instruction(f"    .s_axi_awlen   (core_s_axi_awlen),")
    m.instruction(f"    .s_axi_awsize  (core_s_axi_awsize),")
    m.instruction(f"    .s_axi_awburst (core_s_axi_awburst),")
    m.instruction(f"    .s_axi_awlock  (core_s_axi_awlock),")
    m.instruction(f"    .s_axi_awcache (core_s_axi_awcache),")
    m.instruction(f"    .s_axi_awprot  (core_s_axi_awprot),")
    m.instruction(f"    .s_axi_awvalid (core_s_axi_awvalid),")
    m.instruction(f"    .s_axi_awready (core_s_axi_awready),")
    m.comment("")
    m.instruction(f"    .s_axi_wdata  (core_s_axi_wdata),")
    m.instruction(f"    .s_axi_wstrb  (core_s_axi_wstrb),")
    m.instruction(f"    .s_axi_wlast  (core_s_axi_wlast),")
    m.instruction(f"    .s_axi_wvalid (core_s_axi_wvalid),")
    m.instruction(f"    .s_axi_wready (core_s_axi_wready),")
    m.comment("")
    m.instruction(f"    .s_axi_bid    (core_s_axi_bid),")
    m.instruction(f"    .s_axi_bresp  (core_s_axi_bresp),")
    m.instruction(f"    .s_axi_bvalid (core_s_axi_bvalid),")
    m.instruction(f"    .s_axi_bready (core_s_axi_bready),")
    m.comment("")
    m.instruction(f"    .s_axi_araddr  (core_s_axi_araddr),")
    m.instruction(f"    .s_axi_arid    (core_s_axi_arid),")
    m.instruction(f"    .s_axi_arlen   (core_s_axi_arlen),")
    m.instruction(f"    .s_axi_arsize  (core_s_axi_arsize),")
    m.instruction(f"    .s_axi_arburst (core_s_axi_arburst),")
    m.instruction(f"    .s_axi_arlock  (core_s_axi_arlock),")
    m.instruction(f"    .s_axi_arcache (core_s_axi_arcache),")
    m.instruction(f"    .s_axi_arprot  (core_s_axi_arprot),")
    m.instruction(f"    .s_axi_arvalid (core_s_axi_arvalid),")
    m.instruction(f"    .s_axi_arready (core_s_axi_arready),")
    m.comment("")
    m.instruction(f"    .s_axi_rdata  (core_s_axi_rdata),")
    m.instruction(f"    .s_axi_rid    (core_s_axi_rid),")
    m.instruction(f"    .s_axi_rresp  (core_s_axi_rresp),")
    m.instruction(f"    .s_axi_rlast  (core_s_axi_rlast),")
    m.instruction(f"    .s_axi_rvalid (core_s_axi_rvalid),")
    m.instruction(f"    .s_axi_rready (core_s_axi_rready),")
    m.comment("")
    m.instruction(f"    // Slave interfaces (arrays)")
    m.instruction(f"    .m_axi_awaddr  (core_m_axi_awaddr),")
    m.instruction(f"    .m_axi_awid    (core_m_axi_awid),")
    m.instruction(f"    .m_axi_awlen   (core_m_axi_awlen),")
    m.instruction(f"    .m_axi_awsize  (core_m_axi_awsize),")
    m.instruction(f"    .m_axi_awburst (core_m_axi_awburst),")
    m.instruction(f"    .m_axi_awlock  (core_m_axi_awlock),")
    m.instruction(f"    .m_axi_awcache (core_m_axi_awcache),")
    m.instruction(f"    .m_axi_awprot  (core_m_axi_awprot),")
    m.instruction(f"    .m_axi_awvalid (core_m_axi_awvalid),")
    m.instruction(f"    .m_axi_awready (core_m_axi_awready),")
    m.comment("")
    m.instruction(f"    .m_axi_wdata  (core_m_axi_wdata),")
    m.instruction(f"    .m_axi_wstrb  (core_m_axi_wstrb),")
    m.instruction(f"    .m_axi_wlast  (core_m_axi_wlast),")
    m.instruction(f"    .m_axi_wvalid (core_m_axi_wvalid),")
    m.instruction(f"    .m_axi_wready (core_m_axi_wready),")
    m.comment("")
    m.instruction(f"    .m_axi_bid    (core_m_axi_bid),")
    m.instruction(f"    .m_axi_bresp  (core_m_axi_bresp),")
    m.instruction(f"    .m_axi_bvalid (core_m_axi_bvalid),")
    m.instruction(f"    .m_axi_bready (core_m_axi_bready),")
    m.comment("")
    m.instruction(f"    .m_axi_araddr  (core_m_axi_araddr),")
    m.instruction(f"    .m_axi_arid    (core_m_axi_arid),")
    m.instruction(f"    .m_axi_arlen   (core_m_axi_arlen),")
    m.instruction(f"    .m_axi_arsize  (core_m_axi_arsize),")
    m.instruction(f"    .m_axi_arburst (core_m_axi_arburst),")
    m.instruction(f"    .m_axi_arlock  (core_m_axi_arlock),")
    m.instruction(f"    .m_axi_arcache (core_m_axi_arcache),")
    m.instruction(f"    .m_axi_arprot  (core_m_axi_arprot),")
    m.instruction(f"    .m_axi_arvalid (core_m_axi_arvalid),")
    m.instruction(f"    .m_axi_arready (core_m_axi_arready),")
    m.comment("")
    m.instruction(f"    .m_axi_rdata  (core_m_axi_rdata),")
    m.instruction(f"    .m_axi_rid    (core_m_axi_rid),")
    m.instruction(f"    .m_axi_rresp  (core_m_axi_rresp),")
    m.instruction(f"    .m_axi_rlast  (core_m_axi_rlast),")
    m.instruction(f"    .m_axi_rvalid (core_m_axi_rvalid),")
    m.instruction(f"    .m_axi_rready (core_m_axi_rready)")
    m.instruction(f");")
    m.comment("")

    # Generate module footer (endmodule)
    m.end()

    # Write output file
    from pathlib import Path
    output = Path(output_path)
    m.write(str(output.parent), output.name)
    print(f"Generated wrapper: {output_path}")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Generate Verilator-compatible AXI4 bridge wrapper")
    parser.add_argument("--masters", type=int, default=2, help="Number of masters")
    parser.add_argument("--slaves", type=int, default=2, help="Number of slaves")
    parser.add_argument("--data-width", type=int, default=32, help="Data width in bits")
    parser.add_argument("--addr-width", type=int, default=32, help="Address width in bits")
    parser.add_argument("--id-width", type=int, default=4, help="ID width in bits")
    parser.add_argument("--output", type=str, required=True, help="Output file path")

    args = parser.parse_args()

    generate_bridge_wrapper(
        args.masters,
        args.slaves,
        args.data_width,
        args.addr_width,
        args.id_width,
        args.output
    )
