// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Package: rs_loop_cfg_pkg
// Purpose:
//   The ONE source of the Reed-Solomon loop harness's geometry. The board top,
//   the harness and the cosim all elaborate from these values; a literal in
//   any of them is the bug (handbook: fpga/cmn-infra/one-source-config).
//
//   Profile: RS(252,236) over GF(2^8), t = 8, first root 0 -- the reference
//   RS(255,239) shortened by three symbols so that n and k are multiples of
//   the 4-symbol (32-bit) beat. That keeps every beat full, which the shared
//   AXI-Stream pattern checker requires (it compares whole 32-bit words).
//
// Documentation: projects/fpga-systems/NexysA7/reed-solomon/README.md
// Subsystem: reed-solomon (NexysA7 harness)
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps

package rs_loop_cfg_pkg;

    // the code
    localparam int CFG_SYMBOL_WIDTH = 8;
    localparam int CFG_PRIM_POLY    = 'h11D;
    localparam int CFG_T_SYMBOLS    = 8;
    localparam int CFG_N_SYMBOLS    = 252;
    localparam int CFG_K_SYMBOLS    = CFG_N_SYMBOLS - 2 * CFG_T_SYMBOLS;   // 236
    localparam int CFG_FIRST_ROOT   = 0;

    // the bus: 32-bit AXI-Stream, 4 symbols per beat
    localparam int CFG_DATA_WIDTH   = 32;
    localparam int CFG_SPB          = CFG_DATA_WIDTH / CFG_SYMBOL_WIDTH;    // 4
    localparam int CFG_K_BEATS      = CFG_K_SYMBOLS / CFG_SPB;              // 59
    localparam int CFG_N_BEATS      = CFG_N_SYMBOLS / CFG_SPB;              // 63

    // the board
    localparam int          CFG_SYS_CLK_HZ = 100_000_000;
    localparam int          CFG_UART_BAUD  = 115_200;
    localparam logic [31:0] CFG_BUILD_ID   = 32'h5253_4C50;   // "RSLP"

    // the two decoders under test
    // AXI4 datapath geometry. Each of the four memories holds the largest
    // region any one stage uses -- a codeword region is blocks * CFG_N_BEATS
    // words -- so the depth caps the blocks a single AXI4 run can carry. 4096
    // words at 32 bits is 16 KB per memory, 4 block RAMs, and the part has
    // 135 with none otherwise used. Burst length is a round 16 beats: long
    // enough that AW/AR overhead is small against a 63-beat codeword, short
    // enough to stay well inside a 4 KB boundary at 4 bytes a beat.
    localparam int unsigned CFG_AXI4_MEM_DEPTH = 4096;
    localparam logic [7:0]  CFG_AXI4_BURST_LEN = 8'd16;
    localparam int unsigned CFG_AXI4_MAX_BLOCKS = CFG_AXI4_MEM_DEPTH / CFG_N_BEATS;

    localparam string       CFG_KES_A = "RIBM";
    localparam string       CFG_KES_B = "EUCLID";

endpackage : rs_loop_cfg_pkg
