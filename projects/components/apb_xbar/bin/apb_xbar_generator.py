#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: apb_xbar_generator
# Purpose: APB Crossbar Generator
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""
APB Crossbar Generator

Generates parameterized APB crossbars (M masters to N slaves) using the proven
apb_slave and apb_master module architecture.

Architecture:
- apb_slave modules on master side convert APB -> cmd/rsp
- apb_master modules on slave side convert cmd/rsp -> APB
- Independent round-robin arbitration per slave
- Address decoding for slave selection
- FIFOs for datapath isolation

Usage:
    python apb_xbar_generator.py --masters 2 --slaves 4 --output apb_xbar_2to4.sv
    python apb_xbar_generator.py --masters 1 --slaves 1 --output apb_xbar_1to1.sv

Author: Generated code for RTL Design Sherpa
Date: 2025-10-14
"""

import argparse
import sys
from pathlib import Path


def generate_apb_xbar(num_masters, num_slaves, base_addr=0x10000000,
                      addr_width=32, data_width=32, output_file=None):
    """
    Generate an M-to-N APB crossbar module.

    Args:
        num_masters: Number of master interfaces (1-16)
        num_slaves: Number of slave interfaces (1-16)
        base_addr: Base address for slave address map
        addr_width: Address bus width (default 32)
        data_width: Data bus width (default 32)
        output_file: Output filename (default apb_xbar_MtoN.sv)

    Returns:
        SystemVerilog code as string
    """

    M = num_masters
    N = num_slaves

    if M < 1 or M > 16:
        raise ValueError(f"Number of masters must be 1-16, got {M}")
    if N < 1 or N > 16:
        raise ValueError(f"Number of slaves must be 1-16, got {N}")

    # Calculate address bits needed for slave selection
    import math
    slave_addr_bits = max(1, math.ceil(math.log2(N)))

    strb_width = data_width // 8

    if output_file is None:
        output_file = f"apb_xbar_{M}to{N}.sv"

    module_name = f"apb_xbar_{M}to{N}"

    # Generate header
    code = f"""`timescale 1ns / 1ps

// {M}-to-{N} APB crossbar with address decoding and arbitration
// {M} master{'s' if M > 1 else ''} to {N} slave{'s' if N > 1 else ''} using apb_slave and apb_master modules
//
// Address Map (same for all masters):
"""

    # Document address map
    for s in range(N):
        addr_offset = s * 0x10000
        addr_start = base_addr + addr_offset
        addr_end = addr_start + 0xFFFF
        code += f"//   Slave {s}: [0x{addr_start:08X}, 0x{addr_end:08X}]\n"

    code += f"""
module {module_name} #(
    parameter int ADDR_WIDTH = {addr_width},
    parameter int DATA_WIDTH = {data_width},
    parameter int STRB_WIDTH = DATA_WIDTH / 8,
    parameter logic [ADDR_WIDTH-1:0] BASE_ADDR = {addr_width}'h{base_addr:08X}
) (
    // Clock and Reset
    input  logic                  pclk,
    input  logic                  presetn,

"""

    # Generate master interfaces
    for m in range(M):
        code += f"    // Master {m} APB interface (from external master {m})\n"
        code += f"    input  logic                  m{m}_apb_PSEL,\n"
        code += f"    input  logic                  m{m}_apb_PENABLE,\n"
        code += f"    input  logic [ADDR_WIDTH-1:0] m{m}_apb_PADDR,\n"
        code += f"    input  logic                  m{m}_apb_PWRITE,\n"
        code += f"    input  logic [DATA_WIDTH-1:0] m{m}_apb_PWDATA,\n"
        code += f"    input  logic [STRB_WIDTH-1:0] m{m}_apb_PSTRB,\n"
        code += f"    input  logic [2:0]            m{m}_apb_PPROT,\n"
        code += f"    output logic [DATA_WIDTH-1:0] m{m}_apb_PRDATA,\n"
        code += f"    output logic                  m{m}_apb_PSLVERR,\n"
        code += f"    output logic                  m{m}_apb_PREADY"
        code += ",\n\n" if m < M-1 or N > 0 else "\n"

    # Generate slave interfaces
    for s in range(N):
        code += f"    // Slave {s} APB interface (to external slave {s})\n"
        code += f"    output logic                  s{s}_apb_PSEL,\n"
        code += f"    output logic                  s{s}_apb_PENABLE,\n"
        code += f"    output logic [ADDR_WIDTH-1:0] s{s}_apb_PADDR,\n"
        code += f"    output logic                  s{s}_apb_PWRITE,\n"
        code += f"    output logic [DATA_WIDTH-1:0] s{s}_apb_PWDATA,\n"
        code += f"    output logic [STRB_WIDTH-1:0] s{s}_apb_PSTRB,\n"
        code += f"    output logic [2:0]            s{s}_apb_PPROT,\n"
        code += f"    input  logic [DATA_WIDTH-1:0] s{s}_apb_PRDATA,\n"
        code += f"    input  logic                  s{s}_apb_PSLVERR,\n"
        code += f"    input  logic                  s{s}_apb_PREADY"
        code += ",\n\n" if s < N-1 else "\n"

    code += ");\n\n"

    # Generate master-side apb_slave cmd/rsp interfaces
    for m in range(M):
        code += f"    // Command/Response interfaces for master {m} apb_slave\n"
        code += f"    logic                  m{m}_cmd_valid;\n"
        code += f"    logic                  m{m}_cmd_ready;\n"
        code += f"    logic                  m{m}_cmd_pwrite;\n"
        code += f"    logic [ADDR_WIDTH-1:0] m{m}_cmd_paddr;\n"
        code += f"    logic [DATA_WIDTH-1:0] m{m}_cmd_pwdata;\n"
        code += f"    logic [STRB_WIDTH-1:0] m{m}_cmd_pstrb;\n"
        code += f"    logic [2:0]            m{m}_cmd_pprot;\n"
        code += f"    logic                  m{m}_rsp_valid;\n"
        code += f"    logic                  m{m}_rsp_ready;\n"
        code += f"    logic [DATA_WIDTH-1:0] m{m}_rsp_prdata;\n"
        code += f"    logic                  m{m}_rsp_pslverr;\n\n"

    # Generate slave-side apb_master cmd/rsp interfaces
    code += "    // Command/Response interfaces for slave apb_masters\n"
    code += "    logic                  "
    for s in range(N):
        code += f"s{s}_cmd_valid"
        code += ", " if s < N-1 else ";\n"

    code += "    logic                  "
    for s in range(N):
        code += f"s{s}_cmd_ready"
        code += ", " if s < N-1 else ";\n"

    code += "    logic                  "
    for s in range(N):
        code += f"s{s}_cmd_pwrite"
        code += ", " if s < N-1 else ";\n"

    code += "    logic [ADDR_WIDTH-1:0] "
    for s in range(N):
        code += f"s{s}_cmd_paddr"
        code += ", " if s < N-1 else ";\n"

    code += "    logic [DATA_WIDTH-1:0] "
    for s in range(N):
        code += f"s{s}_cmd_pwdata"
        code += ", " if s < N-1 else ";\n"

    code += "    logic [STRB_WIDTH-1:0] "
    for s in range(N):
        code += f"s{s}_cmd_pstrb"
        code += ", " if s < N-1 else ";\n"

    code += "    logic [2:0]            "
    for s in range(N):
        code += f"s{s}_cmd_pprot"
        code += ", " if s < N-1 else ";\n"

    code += "    logic                  "
    for s in range(N):
        code += f"s{s}_rsp_valid"
        code += ", " if s < N-1 else ";\n"

    code += "    logic                  "
    for s in range(N):
        code += f"s{s}_rsp_ready"
        code += ", " if s < N-1 else ";\n"

    code += "    logic [DATA_WIDTH-1:0] "
    for s in range(N):
        code += f"s{s}_rsp_prdata"
        code += ", " if s < N-1 else ";\n"

    code += "    logic                  "
    for s in range(N):
        code += f"s{s}_rsp_pslverr"
        code += ", " if s < N-1 else ";\n\n"

    # Instantiate apb_slave modules for each master
    for m in range(M):
        code += f"    // APB Slave {m} - converts master {m} APB to cmd/rsp\n"
        code += f"    apb_slave #(\n"
        code += f"        .ADDR_WIDTH (ADDR_WIDTH),\n"
        code += f"        .DATA_WIDTH (DATA_WIDTH),\n"
        code += f"        .STRB_WIDTH (STRB_WIDTH),\n"
        code += f"        .PROT_WIDTH (3)\n"
        code += f"    ) u_apb_slave_m{m} (\n"
        code += f"        .pclk           (pclk),\n"
        code += f"        .presetn        (presetn),\n"
        code += f"        .s_apb_PSEL     (m{m}_apb_PSEL),\n"
        code += f"        .s_apb_PENABLE  (m{m}_apb_PENABLE),\n"
        code += f"        .s_apb_PREADY   (m{m}_apb_PREADY),\n"
        code += f"        .s_apb_PADDR    (m{m}_apb_PADDR),\n"
        code += f"        .s_apb_PWRITE   (m{m}_apb_PWRITE),\n"
        code += f"        .s_apb_PWDATA   (m{m}_apb_PWDATA),\n"
        code += f"        .s_apb_PSTRB    (m{m}_apb_PSTRB),\n"
        code += f"        .s_apb_PPROT    (m{m}_apb_PPROT),\n"
        code += f"        .s_apb_PRDATA   (m{m}_apb_PRDATA),\n"
        code += f"        .s_apb_PSLVERR  (m{m}_apb_PSLVERR),\n"
        code += f"        .cmd_valid      (m{m}_cmd_valid),\n"
        code += f"        .cmd_ready      (m{m}_cmd_ready),\n"
        code += f"        .cmd_pwrite     (m{m}_cmd_pwrite),\n"
        code += f"        .cmd_paddr      (m{m}_cmd_paddr),\n"
        code += f"        .cmd_pwdata     (m{m}_cmd_pwdata),\n"
        code += f"        .cmd_pstrb      (m{m}_cmd_pstrb),\n"
        code += f"        .cmd_pprot      (m{m}_cmd_pprot),\n"
        code += f"        .rsp_valid      (m{m}_rsp_valid),\n"
        code += f"        .rsp_ready      (m{m}_rsp_ready),\n"
        code += f"        .rsp_prdata     (m{m}_rsp_prdata),\n"
        code += f"        .rsp_pslverr    (m{m}_rsp_pslverr)\n"
        code += f"    );\n\n"

    # Generate address decode logic for each master
    if N > 1:
        slave_sel_width = slave_addr_bits
        code += "    // Address decode for each master\n"
        for m in range(M):
            code += f"    logic [{slave_sel_width-1}:0] m{m}_slave_sel;\n"
            code += f"    logic m{m}_addr_in_range;\n"
            code += f"    logic [{slave_sel_width-1}:0] r_m{m}_slave_sel;  // Registered for response routing\n"

        code += "\n    always_comb begin\n"
        for m in range(M):
            addr_range_size = N * 0x10000
            code += f"        m{m}_addr_in_range = (m{m}_cmd_paddr >= BASE_ADDR) &&\n"
            code += f"                          (m{m}_cmd_paddr < (BASE_ADDR + {addr_width}'h{addr_range_size:08X}));\n"
            code += f"        m{m}_slave_sel = m{m}_cmd_paddr[{16+slave_sel_width-1}:16];\n\n"
        code += "    end\n\n"

        code += "    // Register slave selection for each master when command accepted\n"
        code += "    always_ff @(posedge pclk or negedge presetn) begin\n"
        code += "        if (!presetn) begin\n"
        for m in range(M):
            code += f"            r_m{m}_slave_sel <= {slave_sel_width}'d0;\n"
        code += "        end else begin\n"
        for m in range(M):
            code += f"            if (m{m}_cmd_valid && m{m}_cmd_ready) begin\n"
            code += f"                r_m{m}_slave_sel <= m{m}_slave_sel;\n"
            code += f"            end\n"
        code += "        end\n"
        code += "    end\n\n"

    # Generate arbitration and routing logic for each slave
    if M > 1:
        code += "    // Arbitration and command routing for each slave\n"
        code += "    // Each slave has independent round-robin arbitration between the masters\n"
        code += "    // Uses proven arbiter_round_robin module from rtl/common/\n\n"

        for s in range(N):
            code += f"    // Slave {s} arbitration signals\n"
            code += f"    logic [{M-1}:0] s{s}_arb_request;\n"
            code += f"    logic [{M-1}:0] s{s}_arb_grant;\n"
            code += f"    logic [{M-1}:0] s{s}_arb_grant_ack;\n\n"

            # Build request vector
            code += f"    // Build request vector for slave {s}\n"
            code += f"    always_comb begin\n"
            for m in range(M):
                if N > 1:
                    code += f"        s{s}_arb_request[{m}] = m{m}_cmd_valid && m{m}_addr_in_range && m{m}_slave_sel == {slave_sel_width}'d{s};\n"
                else:
                    code += f"        s{s}_arb_request[{m}] = m{m}_cmd_valid;\n"
            code += f"    end\n\n"

            # Build grant_ack vector (transaction complete)
            code += f"    // Build grant_ack vector for slave {s} (transaction complete)\n"
            code += f"    always_comb begin\n"
            for m in range(M):
                code += f"        s{s}_arb_grant_ack[{m}] = s{s}_arb_grant[{m}] && s{s}_rsp_valid && s{s}_rsp_ready;\n"
            code += f"    end\n\n"

            # Instantiate arbiter
            code += f"    // Round-robin arbiter for slave {s}\n"
            code += f"    arbiter_round_robin #(\n"
            code += f"        .CLIENTS({M}),\n"
            code += f"        .WAIT_GNT_ACK(1)  // Lock grant until transaction completes\n"
            code += f"    ) u_s{s}_arbiter (\n"
            code += f"        .clk        (pclk),\n"
            code += f"        .rst_n      (presetn),\n"
            code += f"        .block_arb  (1'b0),\n"
            code += f"        .request    (s{s}_arb_request),\n"
            code += f"        .grant_ack  (s{s}_arb_grant_ack),\n"
            code += f"        .grant_valid(),  // Not used\n"
            code += f"        .grant      (s{s}_arb_grant),\n"
            code += f"        .grant_id   (),  // Not used\n"
            code += f"        .last_grant ()   // Not used\n"
            code += f"    );\n\n"

            # Command routing to slave
            code += f"    // Command routing to slave {s}\n"
            code += f"    always_comb begin\n"
            code += f"        s{s}_cmd_valid = 1'b0;\n"
            code += f"        s{s}_cmd_pwrite = 1'b0;\n"
            code += f"        s{s}_cmd_paddr = '0;\n"
            code += f"        s{s}_cmd_pwdata = '0;\n"
            code += f"        s{s}_cmd_pstrb = '0;\n"
            code += f"        s{s}_cmd_pprot = '0;\n"
            code += f"        case (1'b1)\n"
            for m in range(M):
                code += f"            s{s}_arb_grant[{m}]: begin\n"
                code += f"                s{s}_cmd_valid = m{m}_cmd_valid"
                if N > 1:
                    code += f" && m{m}_addr_in_range && (m{m}_slave_sel == {slave_sel_width}'d{s})"
                code += ";\n"
                code += f"                s{s}_cmd_pwrite = m{m}_cmd_pwrite;\n"
                code += f"                s{s}_cmd_paddr = m{m}_cmd_paddr;\n"
                code += f"                s{s}_cmd_pwdata = m{m}_cmd_pwdata;\n"
                code += f"                s{s}_cmd_pstrb = m{m}_cmd_pstrb;\n"
                code += f"                s{s}_cmd_pprot = m{m}_cmd_pprot;\n"
                code += f"            end\n"
            code += f"        endcase\n"
            code += f"    end\n\n"

        # Master cmd_ready signals
        code += "    // Master cmd_ready signals\n"
        for m in range(M):
            code += f"    always_comb begin\n"
            code += f"        m{m}_cmd_ready = 1'b0;\n"
            if N > 1:
                code += f"        if (m{m}_cmd_valid && m{m}_addr_in_range) begin\n"
                code += f"            case (m{m}_slave_sel)\n"
                for s in range(N):
                    code += f"                {slave_sel_width}'d{s}: m{m}_cmd_ready = s{s}_arb_grant[{m}] && s{s}_cmd_ready;\n"
                code += f"            endcase\n"
                code += f"        end\n"
            else:
                code += f"        m{m}_cmd_ready = s0_arb_grant[{m}] && s0_cmd_ready;\n"
            code += f"    end\n\n"

        # Response routing
        code += "    // Response routing from slaves to masters\n"
        for m in range(M):
            code += f"    always_comb begin\n"
            code += f"        m{m}_rsp_valid = 1'b0;\n"
            code += f"        m{m}_rsp_prdata = '0;\n"
            code += f"        m{m}_rsp_pslverr = 1'b0;\n"
            if N > 1:
                code += f"        case (r_m{m}_slave_sel)\n"
                for s in range(N):
                    code += f"            {slave_sel_width}'d{s}: begin\n"
                    code += f"                if (s{s}_arb_grant[{m}]) begin\n"
                    code += f"                    m{m}_rsp_valid = s{s}_rsp_valid;\n"
                    code += f"                    m{m}_rsp_prdata = s{s}_rsp_prdata;\n"
                    code += f"                    m{m}_rsp_pslverr = s{s}_rsp_pslverr;\n"
                    code += f"                end\n"
                    code += f"            end\n"
                code += f"        endcase\n"
            else:
                code += f"        if (s0_arb_grant[{m}]) begin\n"
                code += f"            m{m}_rsp_valid = s0_rsp_valid;\n"
                code += f"            m{m}_rsp_prdata = s0_rsp_prdata;\n"
                code += f"            m{m}_rsp_pslverr = s0_rsp_pslverr;\n"
                code += f"        end\n"
            code += f"    end\n\n"

        # Slave rsp_ready signals
        for s in range(N):
            code += f"    // Slave {s} rsp_ready\n"
            code += f"    always_comb begin\n"
            code += f"        s{s}_rsp_ready = 1'b0;\n"
            for m in range(M):
                code += f"        if (s{s}_arb_grant[{m}]"
                if N > 1:
                    code += f" && r_m{m}_slave_sel == {slave_sel_width}'d{s}"
                code += f") s{s}_rsp_ready = m{m}_rsp_ready;\n"
            code += f"    end\n\n"

    else:  # M == 1 (single master)
        # Simple pass-through for single master case
        if N > 1:
            code += "    // Single master - command routing based on address decode\n"
            for s in range(N):
                code += f"    assign s{s}_cmd_valid = m0_cmd_valid && m0_addr_in_range && (m0_slave_sel == {slave_sel_width}'d{s});\n"
                code += f"    assign s{s}_cmd_pwrite = m0_cmd_pwrite;\n"
                code += f"    assign s{s}_cmd_paddr = m0_cmd_paddr;\n"
                code += f"    assign s{s}_cmd_pwdata = m0_cmd_pwdata;\n"
                code += f"    assign s{s}_cmd_pstrb = m0_cmd_pstrb;\n"
                code += f"    assign s{s}_cmd_pprot = m0_cmd_pprot;\n\n"

            code += "    // Master ready when selected slave is ready\n"
            code += "    always_comb begin\n"
            code += "        m0_cmd_ready = 1'b0;\n"
            code += "        if (m0_cmd_valid && m0_addr_in_range) begin\n"
            code += "            case (m0_slave_sel)\n"
            for s in range(N):
                code += f"                {slave_sel_width}'d{s}: m0_cmd_ready = s{s}_cmd_ready;\n"
            code += "            endcase\n"
            code += "        end\n"
            code += "    end\n\n"

            code += "    // Response routing based on registered slave selection\n"
            code += "    always_comb begin\n"
            code += "        m0_rsp_valid = 1'b0;\n"
            code += "        m0_rsp_prdata = '0;\n"
            code += "        m0_rsp_pslverr = 1'b0;\n"
            code += "        case (r_m0_slave_sel)\n"
            for s in range(N):
                code += f"            {slave_sel_width}'d{s}: begin\n"
                code += f"                m0_rsp_valid = s{s}_rsp_valid;\n"
                code += f"                m0_rsp_prdata = s{s}_rsp_prdata;\n"
                code += f"                m0_rsp_pslverr = s{s}_rsp_pslverr;\n"
                code += f"            end\n"
            code += "        endcase\n"
            code += "    end\n\n"

            for s in range(N):
                code += f"    assign s{s}_rsp_ready = (r_m0_slave_sel == {slave_sel_width}'d{s}) ? m0_rsp_ready : 1'b0;\n"

        else:  # M == 1, N == 1 (simple passthrough)
            code += "    // Simple 1-to-1 passthrough\n"
            code += "    assign s0_cmd_valid = m0_cmd_valid;\n"
            code += "    assign s0_cmd_pwrite = m0_cmd_pwrite;\n"
            code += "    assign s0_cmd_paddr = m0_cmd_paddr;\n"
            code += "    assign s0_cmd_pwdata = m0_cmd_pwdata;\n"
            code += "    assign s0_cmd_pstrb = m0_cmd_pstrb;\n"
            code += "    assign s0_cmd_pprot = m0_cmd_pprot;\n"
            code += "    assign m0_cmd_ready = s0_cmd_ready;\n\n"

            code += "    assign m0_rsp_valid = s0_rsp_valid;\n"
            code += "    assign m0_rsp_prdata = s0_rsp_prdata;\n"
            code += "    assign m0_rsp_pslverr = s0_rsp_pslverr;\n"
            code += "    assign s0_rsp_ready = m0_rsp_ready;\n\n"

    # Instantiate apb_master modules for each slave
    for s in range(N):
        code += f"    // APB Master {s} - converts cmd/rsp to slave {s} APB\n"
        code += f"    apb_master #(\n"
        code += f"        .ADDR_WIDTH (ADDR_WIDTH),\n"
        code += f"        .DATA_WIDTH (DATA_WIDTH),\n"
        code += f"        .STRB_WIDTH (STRB_WIDTH),\n"
        code += f"        .PROT_WIDTH (3)\n"
        code += f"    ) u_apb_master_s{s} (\n"
        code += f"        .pclk           (pclk),\n"
        code += f"        .presetn        (presetn),\n"
        code += f"        .m_apb_PSEL     (s{s}_apb_PSEL),\n"
        code += f"        .m_apb_PENABLE  (s{s}_apb_PENABLE),\n"
        code += f"        .m_apb_PREADY   (s{s}_apb_PREADY),\n"
        code += f"        .m_apb_PADDR    (s{s}_apb_PADDR),\n"
        code += f"        .m_apb_PWRITE   (s{s}_apb_PWRITE),\n"
        code += f"        .m_apb_PWDATA   (s{s}_apb_PWDATA),\n"
        code += f"        .m_apb_PSTRB    (s{s}_apb_PSTRB),\n"
        code += f"        .m_apb_PPROT    (s{s}_apb_PPROT),\n"
        code += f"        .m_apb_PRDATA   (s{s}_apb_PRDATA),\n"
        code += f"        .m_apb_PSLVERR  (s{s}_apb_PSLVERR),\n"
        code += f"        .cmd_valid      (s{s}_cmd_valid),\n"
        code += f"        .cmd_ready      (s{s}_cmd_ready),\n"
        code += f"        .cmd_pwrite     (s{s}_cmd_pwrite),\n"
        code += f"        .cmd_paddr      (s{s}_cmd_paddr),\n"
        code += f"        .cmd_pwdata     (s{s}_cmd_pwdata),\n"
        code += f"        .cmd_pstrb      (s{s}_cmd_pstrb),\n"
        code += f"        .cmd_pprot      (s{s}_cmd_pprot),\n"
        code += f"        .rsp_valid      (s{s}_rsp_valid),\n"
        code += f"        .rsp_ready      (s{s}_rsp_ready),\n"
        code += f"        .rsp_prdata     (s{s}_rsp_prdata),\n"
        code += f"        .rsp_pslverr    (s{s}_rsp_pslverr)\n"
        code += f"    );\n\n"

    code += f"endmodule : {module_name}\n"

    return code


def main():
    parser = argparse.ArgumentParser(
        description='Generate APB crossbar modules',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  Generate 2-to-4 crossbar:
    %(prog)s --masters 2 --slaves 4 --output rtl/amba/apb/xbar/apb_xbar_2to4.sv

  Generate 1-to-1 passthrough:
    %(prog)s --masters 1 --slaves 1 --output rtl/amba/apb/xbar/apb_xbar_1to1.sv

  Generate 4-to-8 crossbar with custom base address:
    %(prog)s --masters 4 --slaves 8 --base-addr 0x80000000 --output apb_xbar_4to8.sv
        """
    )

    parser.add_argument('--masters', '-m', type=int, required=True,
                        help='Number of master interfaces (1-16)')
    parser.add_argument('--slaves', '-s', type=int, required=True,
                        help='Number of slave interfaces (1-16)')
    parser.add_argument('--base-addr', '-b', type=lambda x: int(x, 0),
                        default=0x10000000,
                        help='Base address for slave address map (default 0x10000000)')
    parser.add_argument('--addr-width', '-a', type=int, default=32,
                        help='Address bus width (default 32)')
    parser.add_argument('--data-width', '-d', type=int, default=32,
                        help='Data bus width (default 32)')
    parser.add_argument('--output', '-o', type=str,
                        help='Output filename (default apb_xbar_MtoN.sv)')

    args = parser.parse_args()

    try:
        code = generate_apb_xbar(
            num_masters=args.masters,
            num_slaves=args.slaves,
            base_addr=args.base_addr,
            addr_width=args.addr_width,
            data_width=args.data_width,
            output_file=args.output
        )

        output_file = args.output if args.output else f"apb_xbar_{args.masters}to{args.slaves}.sv"

        with open(output_file, 'w') as f:
            f.write(code)

        print(f"✅ Generated {output_file}")
        print(f"   Masters: {args.masters}, Slaves: {args.slaves}")
        print(f"   Base Address: 0x{args.base_addr:08X}")

    except Exception as e:
        print(f"❌ Error: {e}", file=sys.stderr)
        return 1

    return 0


if __name__ == '__main__':
    sys.exit(main())
