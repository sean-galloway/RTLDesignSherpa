// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Package: bch_loop_cfg_pkg
// Purpose:
//   The ONE source of the BCH loop harness's geometry. The board top, the
//   harness and the cosim all elaborate from these values; a literal in any of
//   them is the bug (handbook: fpga/cmn-infra/one-source-config).
//
//   Profile: BCH(4224,4120) over GF(2^13), t = 8, first_root = 1, primitive
//   polynomial 0x201B. The message length does not fill the final 32-bit beat,
//   so the final recovered beat carries 24 valid bits (3 bytes); the pattern
//   checker is therefore instantiated in byte-granular (BYTE_CRC=1) mode.
//
// Documentation: projects/fpga-systems/Genesys2/ecc-ip/bch/README.md
// Subsystem: bch (NexysA7 harness)
//
// Author: sean galloway
// Created: 2026-10-04

`timescale 1ns / 1ps

package bch_loop_cfg_pkg;

    // the code
    localparam int CFG_FIELD_DIM  = 13;
    localparam int CFG_PRIM_POLY  = 'h201B;
    localparam int CFG_T_BITS     = 8;
    localparam int CFG_N_BITS     = 4224;
    localparam int CFG_K_BITS     = 4120;   // CFG_N_BITS - degree(g(x))
    localparam int CFG_FIRST_ROOT = 1;

    // the bus: 32-bit AXI-Stream, 32 bits per beat
    localparam int CFG_DATA_WIDTH = 32;
    localparam int CFG_K_BEATS    = 129;    // ceil(CFG_K_BITS / CFG_DATA_WIDTH)
    localparam int CFG_CW_BEATS   = 132;    // ceil(CFG_N_BITS / CFG_DATA_WIDTH)
    localparam int CFG_K_TAIL     = CFG_K_BITS % CFG_DATA_WIDTH;  // 24 bits = 3 bytes

    // the board
    localparam int          CFG_SYS_CLK_HZ = 100_000_000;
    localparam int          CFG_UART_BAUD  = 115_200;
    localparam logic [31:0] CFG_BUILD_ID   = 32'h4243_4850;   // "BCHP"

    // AXI4 datapath geometry
    localparam int unsigned CFG_AXI4_MEM_DEPTH = 4096;
    localparam logic [7:0]  CFG_AXI4_BURST_LEN = 8'd64;
    localparam int unsigned CFG_AXI4_MAX_BLOCKS = CFG_AXI4_MEM_DEPTH / CFG_CW_BEATS;

    localparam string       CFG_KES = "RIBM";

endpackage : bch_loop_cfg_pkg
