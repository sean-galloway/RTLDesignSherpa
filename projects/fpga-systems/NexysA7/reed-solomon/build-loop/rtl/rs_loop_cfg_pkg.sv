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
    // 135 with none otherwise used.
    localparam int unsigned CFG_AXI4_MEM_DEPTH = 4096;

    // Burst length, in beats. 64 beats is 256 bytes.
    //
    // MUST BE A POWER OF TWO. The engines issue bursts back to back from the
    // job base, so each burst is aligned to its own size, and a size that
    // divides 4096 then cannot cross AXI4's 4 KB boundary. One burst per
    // codeword would be the obvious choice and is NOT available: 63 beats is
    // 252 bytes, 4096 is not a multiple of it, and such a burst would
    // eventually straddle the boundary.
    //
    // It was 16, which cost ~8 cycles a block. Measured with the codeword
    // meters gated to the encode and decode passes, the cost is in the MEMORY
    // SLAVE rather than the engines: the encoder's W channel showed 501 cycles
    // of BACKPRESSURE against 11 of starvation, and the decoder's R channel
    // 394 of starvation against zero backpressure -- about 2.0 and 1.6 cycles
    // per burst. Both divide by the burst COUNT, so quartering the count is
    // the fixture-side mitigation. The slave's own per-burst gap is in shared
    // AMBA RTL and is not this file's to fix.
    localparam logic [7:0]  CFG_AXI4_BURST_LEN = 8'd64;
    localparam int unsigned CFG_AXI4_MAX_BLOCKS = CFG_AXI4_MEM_DEPTH / CFG_N_BEATS;

    localparam string       CFG_KES_A = "RIBM";
    localparam string       CFG_KES_B = "EUCLID";

endpackage : rs_loop_cfg_pkg
