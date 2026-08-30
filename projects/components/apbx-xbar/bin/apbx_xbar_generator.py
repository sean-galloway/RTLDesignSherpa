#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: apbx_xbar_generator
# Purpose: APB Crossbar Generator
#
# Documentation: docs/markdown/rtl-common/index.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""
APB Crossbar Generator

Generates parameterized APB crossbars (M masters to N slaves) using the proven
apb4_slave and apb4_master module architecture.

Architecture:
- apb4_slave modules on master side convert APB -> cmd/rsp
- apb4_master modules on slave side convert cmd/rsp -> APB
- Independent round-robin arbitration per slave
- Address decoding for slave selection
- FIFOs for datapath isolation

Usage:
    python apbx_xbar_generator.py --masters 2 --slaves 4 --output apbx_xbar_2to4.sv
    python apbx_xbar_generator.py --masters 1 --slaves 1 --output apbx_xbar_1to1.sv

Author: Generated code for RTL Design Sherpa
Date: 2025-10-14
"""

import argparse
import sys
from pathlib import Path


def generate_apbx_xbar(num_masters, num_slaves, base_addr=0x10000000,
                      addr_width=32, data_width=32, output_file=None, slave_size=0x1000,
                      master_versions=None, slave_versions=None, name_suffix="",
                      enable_parity=False):
    """
    Generate an M-to-N APB crossbar module.

    Args:
        num_masters: Number of master interfaces (1-16)
        num_slaves: Number of slave interfaces (1-16)
        base_addr: Base address for slave address map
        addr_width: Address bus width (default 32)
        data_width: Data bus width (default 32)
        output_file: Output filename (default apbx_xbar_MtoN.sv)
        slave_size: Address space per slave (default 0x1000 = 4KB)
                    Common values: 0x1000 (4KB), 0x10000 (64KB)
        enable_parity: Carry APB5 parity on APB5 ports (APBX-003).
                    A generated variant CHECKS parity at the
                    boundary and REGENERATES it on the far side -- the
                    boundary IP deconstructs the transfer into cmd/rsp
                    and the parity bits do not cross that interface.
                    The cmd/rsp fabric between the two is therefore
                    outside the protected domain, so each port exposes
                    its own parity_error_* outputs; a check whose result
                    goes nowhere is not protection. A mixed pairing has
                    no parity at all, per the version masks.

    Returns:
        SystemVerilog code as string
    """

    M = num_masters
    N = num_slaves

    # APBX-001: per-port protocol versions ('apb4' | 'apb5'). Default all
    # apb4 keeps every legacy config byte-compatible. apb5 ports swap in
    # the apb5_slave / apb5_master boundary IP; the cmd/rsp fabric grows
    # the sideband fields only where a versioned port needs them.
    master_versions = master_versions or ['apb4'] * M
    slave_versions = slave_versions or ['apb4'] * N
    if len(master_versions) != M or len(slave_versions) != N:
        raise ValueError("version list length mismatch")
    for v in list(master_versions) + list(slave_versions):
        if v not in ('apb4', 'apb5'):
            raise ValueError(f"unknown port version {v!r}")
    m5 = [v == 'apb5' for v in master_versions]
    s5 = [v == 'apb5' for v in slave_versions]

    if M < 1 or M > 16:
        raise ValueError(f"Number of masters must be 1-16, got {M}")
    if N < 1 or N > 16:
        raise ValueError(f"Number of slaves must be 1-16, got {N}")

    # Validate slave_size is power of 2
    if slave_size & (slave_size - 1) != 0 or slave_size < 0x100:
        raise ValueError(f"slave_size must be power of 2 and >= 256 bytes, got 0x{slave_size:X}")

    # Calculate address bits needed for slave selection
    import math
    slave_addr_bits = max(1, math.ceil(math.log2(N)))

    strb_width = data_width // 8

    if output_file is None:
        output_file = f"apbx_xbar_{M}to{N}{name_suffix}.sv"

    module_name = f"apbx_xbar_{M}to{N}{name_suffix}"

    # Generate header
    # House banner + reset_defs include: the generator emits the FINAL
    # form — regeneration must never need post-processing (APBX-001).
    def _title(name):
        return ' '.join(w.capitalize() for w in name.split('_'))
    version_note = ""
    if any(m5) or any(s5):
        mv = ', '.join(f"m{i}={v}" for i, v in enumerate(master_versions))
        sv = ', '.join(f"s{i}={v}" for i, v in enumerate(slave_versions))
        version_note = (f"//          Mixed-version ports (APBX-001): {mv}; {sv}.\n")
    code = f"""// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: {module_name}
// Purpose: {_title(module_name)} module
{version_note}//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

// {M}-to-{N} APB crossbar with address decoding and arbitration
// {M} master{'s' if M > 1 else ''} to {N} slave{'s' if N > 1 else ''} using apb4_slave and apb4_master modules
//
// Address Map (same for all masters):
"""

    # Document address map
    for s in range(N):
        addr_offset = s * slave_size
        addr_start = base_addr + addr_offset
        addr_end = addr_start + (slave_size - 1)
        code += f"//   Slave {s}: [0x{addr_start:08X}, 0x{addr_end:08X}] ({slave_size//1024}KB)\n"

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
        if m5[m]:
            code += ",\n"
            code += f"    // APB5 sideband (master {m} is apb5)\n"
            code += f"    input  logic                  m{m}_apb_PAUSER,\n"
            code += f"    input  logic                  m{m}_apb_PWUSER,\n"
            code += f"    output logic                  m{m}_apb_PWAKEUP,\n"
            code += f"    output logic                  m{m}_apb_PRUSER,\n"
            code += f"    output logic                  m{m}_apb_PBUSER"
            if enable_parity:
                code += ",\n"
                code += f"    // APB5 parity (checked here, regenerated on the far side)\n"
                code += f"    input  logic [STRB_WIDTH-1:0] m{m}_apb_PWDATAPARITY,\n"
                code += f"    input  logic                  m{m}_apb_PADDRPARITY,\n"
                code += f"    input  logic                  m{m}_apb_PCTRLPARITY,\n"
                code += f"    output logic [STRB_WIDTH-1:0] m{m}_apb_PRDATAPARITY,\n"
                code += f"    output logic                  m{m}_apb_PREADYPARITY,\n"
                code += f"    output logic                  m{m}_apb_PSLVERRPARITY,\n"
                code += f"    // Per-port fault report. Deliberately NOT folded into\n"
                code += f"    // PSLVERR: that would make a fabric fault look like the\n"
                code += f"    // slave's own error response, which is the distinction\n"
                code += f"    // parity exists to draw.\n"
                code += f"    output logic                  m{m}_parity_error_wdata,\n"
                code += f"    output logic                  m{m}_parity_error_ctrl"
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
        if s5[s]:
            code += ",\n"
            code += f"    // APB5 sideband (slave {s} is apb5)\n"
            code += f"    output logic                  s{s}_apb_PAUSER,\n"
            code += f"    output logic                  s{s}_apb_PWUSER,\n"
            code += f"    input  logic                  s{s}_apb_PWAKEUP,\n"
            code += f"    input  logic                  s{s}_apb_PRUSER,\n"
            code += f"    input  logic                  s{s}_apb_PBUSER"
            if enable_parity:
                code += ",\n"
                code += f"    // APB5 parity (regenerated here from the cmd/rsp path)\n"
                code += f"    output logic [STRB_WIDTH-1:0] s{s}_apb_PWDATAPARITY,\n"
                code += f"    output logic                  s{s}_apb_PADDRPARITY,\n"
                code += f"    output logic                  s{s}_apb_PCTRLPARITY,\n"
                code += f"    input  logic [STRB_WIDTH-1:0] s{s}_apb_PRDATAPARITY,\n"
                code += f"    input  logic                  s{s}_apb_PREADYPARITY,\n"
                code += f"    input  logic                  s{s}_apb_PSLVERRPARITY,\n"
                code += f"    output logic                  s{s}_parity_error_rdata,\n"
                code += f"    output logic                  s{s}_parity_error_ctrl"
        code += ",\n\n" if s < N-1 else "\n"

    code += ");\n\n"

    # Generate master-side apb4_slave cmd/rsp interfaces
    for m in range(M):
        code += f"    // Command/Response interfaces for master {m} apb4_slave\n"
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
        code += f"    logic                  m{m}_rsp_pslverr;\n"
        if m5[m]:
            code += f"    logic                  m{m}_cmd_pauser;\n"
            code += f"    logic                  m{m}_cmd_pwuser;\n"
            code += f"    logic                  m{m}_rsp_pruser;\n"
            code += f"    logic                  m{m}_rsp_pbuser;\n"
        code += "\n"

    # Generate slave-side apb4_master cmd/rsp interfaces
    code += "    // Command/Response interfaces for slave apb4_masters\n"
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
        code += ", " if s < N-1 else ";\n"
    for s in range(N):
        if s5[s]:
            code += f"    logic                  s{s}_cmd_pauser;\n"
            code += f"    logic                  s{s}_cmd_pwuser;\n"
            code += f"    logic                  s{s}_rsp_pruser;\n"
            code += f"    logic                  s{s}_rsp_pbuser;\n"
    code += "\n"

    # Instantiate apb4_slave / apb5_slave modules for each master
    for m in range(M):
        proto = 'apb5' if m5[m] else 'apb4'
        code += f"    // APB Slave {m} - converts master {m} {proto.upper()} to cmd/rsp\n"
        code += f"    {proto}_slave #(\n"
        code += f"        .ADDR_WIDTH (ADDR_WIDTH),\n"
        code += f"        .DATA_WIDTH (DATA_WIDTH),\n"
        code += f"        .STRB_WIDTH (STRB_WIDTH),\n"
        if m5[m]:
            # 1-bit user signals on the xbar surface; parity stays off
            # (ENABLE_PARITY=0 default) with its pins tied below.
            code += f"        .PROT_WIDTH (3),\n"
            code += f"        .AUSER_WIDTH (1),\n"
            code += f"        .WUSER_WIDTH (1),\n"
            code += f"        .RUSER_WIDTH (1),\n"
            if enable_parity:
                code += f"        .BUSER_WIDTH (1),\n"
                code += f"        .ENABLE_PARITY (1)\n"
            else:
                code += f"        .BUSER_WIDTH (1)\n"
        else:
            code += f"        .PROT_WIDTH (3)\n"
        code += f"    ) u_{proto}_slave_m{m} (\n"
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
        if m5[m]:
            code += f"        .rsp_pslverr    (m{m}_rsp_pslverr),\n"
            code += f"        .s_apb_PAUSER   (m{m}_apb_PAUSER),\n"
            code += f"        .s_apb_PWUSER   (m{m}_apb_PWUSER),\n"
            code += f"        .s_apb_PWAKEUP  (m{m}_apb_PWAKEUP),\n"
            code += f"        .s_apb_PRUSER   (m{m}_apb_PRUSER),\n"
            code += f"        .s_apb_PBUSER   (m{m}_apb_PBUSER),\n"
            code += f"        .cmd_pauser     (m{m}_cmd_pauser),\n"
            code += f"        .cmd_pwuser     (m{m}_cmd_pwuser),\n"
            code += f"        .rsp_pruser     (m{m}_rsp_pruser),\n"
            code += f"        .rsp_pbuser     (m{m}_rsp_pbuser),\n"
            if enable_parity:
                code += f"        // parity checked here; regenerated on the far side\n"
                code += f"        .s_apb_PWDATAPARITY (m{m}_apb_PWDATAPARITY),\n"
                code += f"        .s_apb_PADDRPARITY  (m{m}_apb_PADDRPARITY),\n"
                code += f"        .s_apb_PCTRLPARITY  (m{m}_apb_PCTRLPARITY),\n"
                code += f"        .s_apb_PRDATAPARITY (m{m}_apb_PRDATAPARITY),\n"
                code += f"        .s_apb_PREADYPARITY (m{m}_apb_PREADYPARITY),\n"
                code += f"        .s_apb_PSLVERRPARITY(m{m}_apb_PSLVERRPARITY),\n"
                code += f"        .parity_error_wdata (m{m}_parity_error_wdata),\n"
                code += f"        .parity_error_ctrl  (m{m}_parity_error_ctrl),\n"
            else:
                code += f"        // parity feature unused (ENABLE_PARITY=0)\n"
                code += f"        .s_apb_PWDATAPARITY ('0),\n"
                code += f"        .s_apb_PADDRPARITY  ('0),\n"
                code += f"        .s_apb_PCTRLPARITY  ('0),\n"
                code += f"        .s_apb_PRDATAPARITY (),\n"
                code += f"        .s_apb_PREADYPARITY (),\n"
                code += f"        .s_apb_PSLVERRPARITY(),\n"
                code += f"        .parity_error_wdata (),\n"
                code += f"        .parity_error_ctrl  (),\n"
            code += f"        // wakeup handled inside the boundary IP\n"
            code += f"        .wakeup_request     ('0)\n"
        else:
            code += f"        .rsp_pslverr    (m{m}_rsp_pslverr)\n"
        code += f"    );\n\n"

    # Generate address decode logic for each master
    if N > 1:
        slave_sel_width = slave_addr_bits
        code += "    // Address decode for each master. The slave index comes from the\n"
        code += "    // OFFSET (PADDR - BASE_ADDR), not raw PADDR bits: with raw bits a\n"
        code += "    // BASE_ADDR whose select bits are nonzero silently rotated the\n"
        code += "    // whole slave map relative to the documented address map. The\n"
        code += "    // subtraction folds to constants at elaboration (BASE_ADDR is a\n"
        code += "    // parameter), so this costs nothing.\n"
        for m in range(M):
            code += f"    logic [ADDR_WIDTH-1:0] m{m}_cmd_offset;\n"
            code += f"    logic [{slave_sel_width-1}:0] m{m}_slave_sel;\n"
            code += f"    logic m{m}_addr_in_range;\n"
            code += f"    logic [{slave_sel_width-1}:0] r_m{m}_slave_sel;  // Registered for response routing\n"

        code += "\n    always_comb begin\n"
        for m in range(M):
            addr_range_size = N * slave_size
            # Calculate bit positions for slave select based on slave_size
            # For slave_size = 0x1000 (4KB), lower 12 bits are offset, next bits select slave
            # For slave_size = 0x10000 (64KB), lower 16 bits are offset, next bits select slave
            import math
            slave_offset_bits = int(math.log2(slave_size))
            slave_sel_high = slave_offset_bits + slave_sel_width - 1
            slave_sel_low = slave_offset_bits
            # APBX-004: the slave index comes from the OFFSET (PADDR - BASE_ADDR),
            # not from raw PADDR. Slicing raw PADDR rotates the whole slave map
            # whenever BASE_ADDR is not span-aligned -- e.g. with BASE_ADDR
            # 0x10010000 and 64KB slaves, an access to slave 0 decoded as slave 1.
            # Emitting the raw-PADDR form here is what put that bug in every
            # generated variant in the first place.
            code += f"        m{m}_cmd_offset    = m{m}_cmd_paddr - BASE_ADDR;\n"
            code += f"        m{m}_addr_in_range = (m{m}_cmd_paddr >= BASE_ADDR) &&\n"
            code += f"                          (m{m}_cmd_paddr < (BASE_ADDR + {addr_width}'h{addr_range_size:08X}));\n"
            code += f"        m{m}_slave_sel = m{m}_cmd_offset[{slave_sel_high}:{slave_sel_low}];\n\n"
        code += "    end\n\n"

        code += "    // Register slave selection for each master when command accepted\n"
        code += "    `ALWAYS_FF_RST(pclk, presetn,\n"
        code += "        if (`RST_ASSERTED(presetn)) begin\n"
        for m in range(M):
            code += f"            r_m{m}_slave_sel <= {slave_sel_width}'d0;\n"
        code += "        end else begin\n"
        for m in range(M):
            code += f"            if (m{m}_cmd_valid && m{m}_cmd_ready && m{m}_addr_in_range) begin\n"
            code += f"                r_m{m}_slave_sel <= m{m}_slave_sel;\n"
            code += f"            end\n"
        code += "        end\n"
        code += "    )\n\n"

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
            if s5[s]:
                code += f"        s{s}_cmd_pauser = 1'b0;\n"
                code += f"        s{s}_cmd_pwuser = 1'b0;\n"
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
                if s5[s] and m5[m]:
                    code += f"                s{s}_cmd_pauser = m{m}_cmd_pauser;\n"
                    code += f"                s{s}_cmd_pwuser = m{m}_cmd_pwuser;\n"
                code += f"            end\n"
            code += f"        endcase\n"
            code += f"    end\n\n"

        # Master cmd_ready signals
        code += "    // Master cmd_ready signals\n"
        # APBX-005 for the multi-master path. Same rule as the 1toN branch: an
        # out-of-range access must COMPLETE with PSLVERR rather than hold
        # cmd_ready low forever and wedge that master with no timeout.
        if N > 1:
            for m in range(M):
                code += f"    // Decode miss on master {m}: complete locally with PSLVERR\n"
                code += f"    // rather than leaving cmd_ready low forever, which wedged the\n"
                code += f"    // external master in ACCESS with no error signature.\n"
                code += f"    logic r_m{m}_decerr_pending;\n"
                code += f"    `ALWAYS_FF_RST(pclk, presetn,\n"
                code += f"        if (`RST_ASSERTED(presetn)) begin\n"
                code += f"            r_m{m}_decerr_pending <= 1'b0;\n"
                code += f"        end else begin\n"
                code += f"            if (m{m}_cmd_valid && m{m}_cmd_ready && !m{m}_addr_in_range) begin\n"
                code += f"                r_m{m}_decerr_pending <= 1'b1;\n"
                code += f"            end else if (r_m{m}_decerr_pending && m{m}_rsp_ready) begin\n"
                code += f"                r_m{m}_decerr_pending <= 1'b0;\n"
                code += f"            end\n"
                code += f"        end\n"
                code += f"    )\n\n"

        for m in range(M):
            code += f"    always_comb begin\n"
            code += f"        m{m}_cmd_ready = 1'b0;\n"
            if N > 1:
                code += f"        if (m{m}_cmd_valid) begin\n"
                code += f"            if (!m{m}_addr_in_range) begin\n"
                code += f"                m{m}_cmd_ready = !r_m{m}_decerr_pending;\n"
                code += f"            end else begin\n"
                code += f"                case (m{m}_slave_sel)\n"
                for s in range(N):
                    code += f"                    {slave_sel_width}'d{s}: m{m}_cmd_ready = s{s}_arb_grant[{m}] && s{s}_cmd_ready;\n"
                code += f"                endcase\n"
                code += f"            end\n"
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
            if m5[m]:
                code += f"        m{m}_rsp_pruser = 1'b0;\n"
                code += f"        m{m}_rsp_pbuser = 1'b0;\n"
            if N > 1:
                code += f"        if (r_m{m}_decerr_pending) begin\n"
                code += f"            m{m}_rsp_valid = 1'b1;\n"
                code += f"            m{m}_rsp_pslverr = 1'b1;\n"
                code += f"        end else case (r_m{m}_slave_sel)\n"
                for s in range(N):
                    code += f"            {slave_sel_width}'d{s}: begin\n"
                    code += f"                if (s{s}_arb_grant[{m}]) begin\n"
                    code += f"                    m{m}_rsp_valid = s{s}_rsp_valid;\n"
                    code += f"                    m{m}_rsp_prdata = s{s}_rsp_prdata;\n"
                    code += f"                    m{m}_rsp_pslverr = s{s}_rsp_pslverr;\n"
                    if m5[m] and s5[s]:
                        code += f"                    m{m}_rsp_pruser = s{s}_rsp_pruser;\n"
                        code += f"                    m{m}_rsp_pbuser = s{s}_rsp_pbuser;\n"
                    code += f"                end\n"
                    code += f"            end\n"
                code += f"        endcase\n"
            else:
                code += f"        if (s0_arb_grant[{m}]) begin\n"
                code += f"            m{m}_rsp_valid = s0_rsp_valid;\n"
                code += f"            m{m}_rsp_prdata = s0_rsp_prdata;\n"
                code += f"            m{m}_rsp_pslverr = s0_rsp_pslverr;\n"
                if m5[m] and s5[0]:
                    code += f"            m{m}_rsp_pruser = s0_rsp_pruser;\n"
                    code += f"            m{m}_rsp_pbuser = s0_rsp_pbuser;\n"
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
                    code += f" && !r_m{m}_decerr_pending && r_m{m}_slave_sel == {slave_sel_width}'d{s}"
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
                code += f"    assign s{s}_cmd_pprot = m0_cmd_pprot;\n"
                if s5[s]:
                    if m5[0]:
                        code += f"    assign s{s}_cmd_pauser = m0_cmd_pauser;\n"
                        code += f"    assign s{s}_cmd_pwuser = m0_cmd_pwuser;\n"
                    else:
                        code += f"    assign s{s}_cmd_pauser = 1'b0;\n"
                        code += f"    assign s{s}_cmd_pwuser = 1'b0;\n"
                code += "\n"


            # APBX-005: an out-of-range address must COMPLETE with PSLVERR.
            # Leaving cmd_ready low forever wedged the external master in
            # ACCESS with PREADY low, no error signature and no timeout --
            # recoverable only by reset. Emitting the decode without this is
            # what shipped that bug in every decoding variant.
            code += "    // Decode miss: an out-of-range address must COMPLETE with PSLVERR,\n"
            code += "    // not leave cmd_ready low forever (which wedged the external master\n"
            code += "    // in ACCESS with PREADY low and no error signature). The apb4_slave\n"
            code += "    // runs one transaction at a time, so a single pending flag serves:\n"
            code += "    // accept the miss, hold a local error response until taken.\n"
            code += "    logic r_m0_decerr_pending;\n"
            code += "    `ALWAYS_FF_RST(pclk, presetn,\n"
            code += "        if (`RST_ASSERTED(presetn)) begin\n"
            code += "            r_m0_decerr_pending <= 1'b0;\n"
            code += "        end else begin\n"
            code += "            if (m0_cmd_valid && m0_cmd_ready && !m0_addr_in_range) begin\n"
            code += "                r_m0_decerr_pending <= 1'b1;\n"
            code += "            end else if (r_m0_decerr_pending && m0_rsp_ready) begin\n"
            code += "                r_m0_decerr_pending <= 1'b0;\n"
            code += "            end\n"
            code += "        end\n"
            code += "    )\n\n"

            code += "    // Master ready when selected slave is ready; a decode miss is\n"
            code += "    // accepted immediately (one at a time) and answered locally.\n"
            code += "    always_comb begin\n"
            code += "        m0_cmd_ready = 1'b0;\n"
            code += "        if (m0_cmd_valid) begin\n"
            code += "            if (!m0_addr_in_range) begin\n"
            code += "                m0_cmd_ready = !r_m0_decerr_pending;\n"
            code += "            end else begin\n"
            code += "                case (m0_slave_sel)\n"
            for s in range(N):
                code += f"                    {slave_sel_width}'d{s}: m0_cmd_ready = s{s}_cmd_ready;\n"
            code += "                endcase\n"
            code += "            end\n"
            code += "        end\n"
            code += "    end\n\n"

            code += "    // Response routing based on registered slave selection\n"
            code += "    always_comb begin\n"
            code += "        m0_rsp_valid = 1'b0;\n"
            code += "        m0_rsp_prdata = '0;\n"
            code += "        m0_rsp_pslverr = 1'b0;\n"
            if m5[0]:
                code += "        m0_rsp_pruser = 1'b0;\n"
                code += "        m0_rsp_pbuser = 1'b0;\n"
            code += "        if (r_m0_decerr_pending) begin\n"
            code += "            m0_rsp_valid = 1'b1;\n"
            code += "            m0_rsp_pslverr = 1'b1;\n"
            code += "        end else case (r_m0_slave_sel)\n"
            for s in range(N):
                code += f"            {slave_sel_width}'d{s}: begin\n"
                code += f"                m0_rsp_valid = s{s}_rsp_valid;\n"
                code += f"                m0_rsp_prdata = s{s}_rsp_prdata;\n"
                code += f"                m0_rsp_pslverr = s{s}_rsp_pslverr;\n"
                if m5[0] and s5[s]:
                    code += f"                m0_rsp_pruser = s{s}_rsp_pruser;\n"
                    code += f"                m0_rsp_pbuser = s{s}_rsp_pbuser;\n"
                code += f"            end\n"
            code += "        endcase\n"
            code += "    end\n\n"

            for s in range(N):
                code += f"    assign s{s}_rsp_ready = (!r_m0_decerr_pending && r_m0_slave_sel == {slave_sel_width}'d{s}) ? m0_rsp_ready : 1'b0;\n"

        else:  # M == 1, N == 1 (simple passthrough)
            code += "    // Simple 1-to-1 passthrough\n"
            code += "    assign s0_cmd_valid = m0_cmd_valid;\n"
            code += "    assign s0_cmd_pwrite = m0_cmd_pwrite;\n"
            code += "    assign s0_cmd_paddr = m0_cmd_paddr;\n"
            code += "    assign s0_cmd_pwdata = m0_cmd_pwdata;\n"
            code += "    assign s0_cmd_pstrb = m0_cmd_pstrb;\n"
            code += "    assign s0_cmd_pprot = m0_cmd_pprot;\n"
            if s5[0]:
                code += ("    assign s0_cmd_pauser = m0_cmd_pauser;\n"
                         if m5[0] else "    assign s0_cmd_pauser = 1'b0;\n")
                code += ("    assign s0_cmd_pwuser = m0_cmd_pwuser;\n"
                         if m5[0] else "    assign s0_cmd_pwuser = 1'b0;\n")
            code += "    assign m0_cmd_ready = s0_cmd_ready;\n\n"

            code += "    assign m0_rsp_valid = s0_rsp_valid;\n"
            code += "    assign m0_rsp_prdata = s0_rsp_prdata;\n"
            code += "    assign m0_rsp_pslverr = s0_rsp_pslverr;\n"
            if m5[0]:
                code += ("    assign m0_rsp_pruser = s0_rsp_pruser;\n"
                         if s5[0] else "    assign m0_rsp_pruser = 1'b0;\n")
                code += ("    assign m0_rsp_pbuser = s0_rsp_pbuser;\n"
                         if s5[0] else "    assign m0_rsp_pbuser = 1'b0;\n")
            code += "    assign s0_rsp_ready = m0_rsp_ready;\n\n"

    # Instantiate apb4_master / apb5_master modules for each slave
    for s in range(N):
        proto = 'apb5' if s5[s] else 'apb4'
        code += f"    // APB Master {s} - converts cmd/rsp to slave {s} {proto.upper()}\n"
        code += f"    {proto}_master #(\n"
        code += f"        .ADDR_WIDTH (ADDR_WIDTH),\n"
        code += f"        .DATA_WIDTH (DATA_WIDTH),\n"
        code += f"        .STRB_WIDTH (STRB_WIDTH),\n"
        if s5[s]:
            code += f"        .PROT_WIDTH (3),\n"
            code += f"        .AUSER_WIDTH (1),\n"
            code += f"        .WUSER_WIDTH (1),\n"
            code += f"        .RUSER_WIDTH (1),\n"
            if enable_parity:
                code += f"        .BUSER_WIDTH (1),\n"
                code += f"        .ENABLE_PARITY (1)\n"
            else:
                code += f"        .BUSER_WIDTH (1)\n"
        else:
            code += f"        .PROT_WIDTH (3)\n"
        code += f"    ) u_{proto}_master_s{s} (\n"
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
        if s5[s]:
            code += f"        .rsp_pslverr    (s{s}_rsp_pslverr),\n"
            code += f"        .m_apb_PAUSER   (s{s}_apb_PAUSER),\n"
            code += f"        .m_apb_PWUSER   (s{s}_apb_PWUSER),\n"
            code += f"        .m_apb_PWAKEUP  (s{s}_apb_PWAKEUP),\n"
            code += f"        .m_apb_PRUSER   (s{s}_apb_PRUSER),\n"
            code += f"        .m_apb_PBUSER   (s{s}_apb_PBUSER),\n"
            code += f"        .cmd_pauser     (s{s}_cmd_pauser),\n"
            code += f"        .cmd_pwuser     (s{s}_cmd_pwuser),\n"
            # rsp_pwakeup is regenerated by the master-side apb5_slave's
            # own wakeup logic; the completer's PWAKEUP terminates here.
            code += f"        .rsp_pwakeup    (),\n"
            code += f"        .rsp_pruser     (s{s}_rsp_pruser),\n"
            code += f"        .rsp_pbuser     (s{s}_rsp_pbuser),\n"
            if enable_parity:
                code += f"        // parity regenerated here from the cmd/rsp path\n"
                code += f"        .m_apb_PWDATAPARITY (s{s}_apb_PWDATAPARITY),\n"
                code += f"        .m_apb_PADDRPARITY  (s{s}_apb_PADDRPARITY),\n"
                code += f"        .m_apb_PCTRLPARITY  (s{s}_apb_PCTRLPARITY),\n"
                code += f"        .m_apb_PRDATAPARITY (s{s}_apb_PRDATAPARITY),\n"
                code += f"        .m_apb_PREADYPARITY (s{s}_apb_PREADYPARITY),\n"
                code += f"        .m_apb_PSLVERRPARITY(s{s}_apb_PSLVERRPARITY),\n"
                code += f"        .parity_error_rdata (s{s}_parity_error_rdata),\n"
                code += f"        .parity_error_ctrl  (s{s}_parity_error_ctrl),\n"
            else:
                code += f"        // parity feature unused (ENABLE_PARITY=0)\n"
                code += f"        .m_apb_PWDATAPARITY (),\n"
                code += f"        .m_apb_PADDRPARITY  (),\n"
                code += f"        .m_apb_PCTRLPARITY  (),\n"
                code += f"        .m_apb_PRDATAPARITY ('0),\n"
                code += f"        .m_apb_PREADYPARITY ('0),\n"
                code += f"        .m_apb_PSLVERRPARITY('0),\n"
                code += f"        .parity_error_rdata (),\n"
                code += f"        .parity_error_ctrl  (),\n"
            code += f"        .wakeup_pending     ()\n"
        else:
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
    %(prog)s --masters 2 --slaves 4 --output rtl/amba/apb4/xbar/apbx_xbar_2to4.sv

  Generate 1-to-1 passthrough:
    %(prog)s --masters 1 --slaves 1 --output rtl/amba/apb4/xbar/apbx_xbar_1to1.sv

  Generate 4-to-8 crossbar with custom base address:
    %(prog)s --masters 4 --slaves 8 --base-addr 0x80000000 --output apbx_xbar_4to8.sv
        """
    )

    parser.add_argument('--masters', '-m', type=int, required=True,
                        help='Number of master interfaces (1-16)')
    parser.add_argument('--slaves', '-s', type=int, required=True,
                        help='Number of slave interfaces (1-16)')
    parser.add_argument('--base-addr', '-b', type=lambda x: int(x, 0),
                        default=0x10000000,
                        help='Base address for slave address map (default 0x10000000)')
    parser.add_argument('--slave-size', type=lambda x: int(x, 0),
                        default=0x1000,
                        help='Address space per slave: 0x1000=4KB, 0x10000=64KB (default 0x1000)')
    parser.add_argument('--addr-width', '-a', type=int, default=32,
                        help='Address bus width (default 32)')
    parser.add_argument('--data-width', '-d', type=int, default=32,
                        help='Data bus width (default 32)')
    parser.add_argument('--output', '-o', type=str,
                        help='Output filename (default apbx_xbar_MtoN.sv)')

    args = parser.parse_args()

    try:
        code = generate_apbx_xbar(
            num_masters=args.masters,
            num_slaves=args.slaves,
            base_addr=args.base_addr,
            addr_width=args.addr_width,
            data_width=args.data_width,
            output_file=args.output,
            slave_size=args.slave_size
        )

        output_file = args.output if args.output else f"apbx_xbar_{args.masters}to{args.slaves}.sv"

        with open(output_file, 'w') as f:
            f.write(code)

        print(f"✅ Generated {output_file}")
        print(f"   Masters: {args.masters}, Slaves: {args.slaves}")
        print(f"   Base Address: 0x{args.base_addr:08X}")
        print(f"   Slave Size: 0x{args.slave_size:X} ({args.slave_size//1024}KB per slave)")

    except Exception as e:
        print(f"❌ Error: {e}", file=sys.stderr)
        return 1

    return 0


if __name__ == '__main__':
    sys.exit(main())
