// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Package: bch_loop_cfg_pkg
// Purpose:
//   The ONE source of the BCH loop harness's geometry. The board top, the
//   harness and the cosim all elaborate from these values; a literal in any of
//   them is the bug (handbook: fpga/cmn-infra/one-source-config).
//
//   Selection: define BCH_LOOP_SMALL on the command line / filelist to build the
//   small Nexys A7-100T profile; leave it undefined for the original board
//   profile. Both profiles share the same 32-bit AXI-Stream interface.
//
//   Profiles:
//     board (default, BCHP 0x4243_4850):
//       BCH(4224,4120) over GF(2^13), t = 8, first_root = 1, primitive poly 0x201B.
//       k does not fill the final 32-bit beat: tail = 24 bits (3 bytes), so the
//       pattern checker runs in byte-granular (BYTE_CRC=1) mode.
//
//     small (BCHS 0x4243_4853):
//       BCH(248,224) t = 3, shortened from BCH(255,231) over GF(2^8),
//       primitive poly 0x11D, first_root = 1. k = 224 = 7 beats exactly and
//       n = 248 = 8 codeword beats, so the final beat is byte-aligned (tail = 0)
//       and the byte-granular checker sees 31 bytes per codeword.
//
// Documentation: projects/fpga-systems/Genesys2/ecc-ip/bch/README.md
// Subsystem: bch (NexysA7 harness)
//
// Author: sean galloway
// Created: 2026-10-04

`timescale 1ns / 1ps

package bch_loop_cfg_pkg;

`ifdef BCH_LOOP_SMALL

    // the code: BCH(248,224) t=3, shortened from BCH(255,231) over GF(2^8)
    localparam int CFG_FIELD_DIM  = 8;
    localparam int CFG_PRIM_POLY  = 'h11D;
    localparam int CFG_T_BITS     = 3;
    localparam int CFG_N_BITS     = 248;
    localparam int CFG_K_BITS     = 224;    // CFG_N_BITS - degree(g(x))
    localparam int CFG_FIRST_ROOT = 1;

    // the bus: 32-bit AXI-Stream, 32 bits per beat
    localparam int CFG_DATA_WIDTH = 32;
    localparam int CFG_K_BEATS    = 7;      // ceil(CFG_K_BITS / CFG_DATA_WIDTH)
    localparam int CFG_CW_BEATS   = 8;      // ceil(CFG_N_BITS / CFG_DATA_WIDTH)
    localparam int CFG_K_TAIL     = CFG_K_BITS % CFG_DATA_WIDTH;  // 0 bits (full last beat)

    // the board
    localparam int          CFG_SYS_CLK_HZ = 50_000_000;   // 50 MHz: fabric divide-by-2 in bch_loop_top (`ifdef BCH_LOOP_SMALL)
    localparam int          CFG_UART_BAUD  = 115_200;
    localparam logic [31:0] CFG_BUILD_ID   = 32'h4243_4853;   // "BCHS"

`else

    // the code: BCH(4224,4120) over GF(2^13), t = 8, first_root = 1, primitive poly 0x201B
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

`endif

    // AXI4 datapath geometry
    localparam int unsigned CFG_AXI4_MEM_DEPTH = 4096;
    localparam logic [7:0]  CFG_AXI4_BURST_LEN = 8'd64;
    localparam int unsigned CFG_AXI4_MAX_BLOCKS = CFG_AXI4_MEM_DEPTH / CFG_CW_BEATS;

    localparam string       CFG_KES = "RIBM";

endpackage : bch_loop_cfg_pkg
