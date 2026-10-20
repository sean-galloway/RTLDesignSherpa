// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cell_pkg
// Purpose: Shared types and constants for the compute cell
//
// Documentation: projects/components/compute-eng-ip/cell/docs/PRD.md
// Subsystem: cell
//
// Author: sean galloway
// Created: 2026-10-18
//
// NOTE: The tile packet header is defined in TILE_SPEC §11.5.  Because the
//       delta node the cell instantiates currently exposes a 64-bit TUSER
//       AXI4-Stream interface, slice 1 compacts the header fields the cell
//       actually uses into 64 bits.  This is a pragmatic slice-1 packing; it
//       will be revisited when delta's TUSER width grows or CXS transport
//       lands.  See cell_rx.sv for the field layout.

`ifndef CELL_PKG_SV
`define CELL_PKG_SV

package cell_pkg;

    // -------------------------------------------------------------------------
    // Coordinate and slice-1 compact header field widths
    // -------------------------------------------------------------------------
    localparam int COORD_W       = 4;
    localparam int COORD_BITS    = 1 + 3 * COORD_W + 2;      // {ext, level, X, Y, Z}

    // The delta node reads TUSER[13:12] as its QoS class and consumes any
    // head beat with QoS=0 addressed to its own coordinate.  Cell traffic must
    // therefore place a non-zero QoS value at TUSER[13:12].  Slice 1 reserves
    // those bits explicitly and places the destination X/Y/Z below them.
    localparam int PTYPE_W       = 3;
    localparam int OP_W          = 1;
    localparam int LENGTH_W      = 16;                       // compacted from 32
    localparam int TARGET_ADDR_W = 10;                       // compacted from 49
    localparam int TAG_W         = 4;

    // -------------------------------------------------------------------------
    // Slice-1 compact header field offsets in TUSER (head beat only)
    //
    // Layout:
    //   [11:0]    dst {X[3:0], Y[3:0], Z[3:0]}     COORD_W=4
    //   [13:12]   qos (must be 2'b01 for cell traffic so delta does not consume)
    //   [14]      dst ext bit (unused by cell match in slice 1)
    //   [29:15]   src_coord {ext, level, X, Y, Z}
    //   [32:30]   ptype
    //   [33]      op
    //   [49:34]   length
    //   [59:50]   target_addr
    //   [63:60]   tag
    // -------------------------------------------------------------------------
    localparam int HDR_DST_XYZ_LO  = 0;
    localparam int HDR_QOS_LO      = 12;
    localparam int HDR_DST_EXT_LO  = 14;
    localparam int HDR_SRC_LO      = 15;
    localparam int HDR_PTYPE_LO    = HDR_SRC_LO + COORD_BITS;
    localparam int HDR_OP_LO       = HDR_PTYPE_LO + PTYPE_W;
    localparam int HDR_LENGTH_LO   = HDR_OP_LO + OP_W;
    localparam int HDR_TARGET_LO   = HDR_LENGTH_LO + LENGTH_W;
    localparam int HDR_TAG_LO      = HDR_TARGET_LO + TARGET_ADDR_W;
    localparam int HDR_TOTAL_W     = HDR_TAG_LO + TAG_W;

    // -------------------------------------------------------------------------
    // Coordinate sub-field offsets inside the 15-bit coordinate word
    // -------------------------------------------------------------------------
    localparam int COORD_Z_LO      = 0;
    localparam int COORD_Y_LO      = COORD_W;
    localparam int COORD_X_LO      = 2 * COORD_W;
    localparam int COORD_LEVEL_LO  = 3 * COORD_W;
    localparam int COORD_EXT_LO    = 3 * COORD_W + 2;

    // -------------------------------------------------------------------------
    // Payload types (TILE_SPEC §11.2)
    // -------------------------------------------------------------------------
    localparam logic [PTYPE_W-1:0] PTYPE_CFG    = 3'd0;
    localparam logic [PTYPE_W-1:0] PTYPE_PROG   = 3'd1;
    localparam logic [PTYPE_W-1:0] PTYPE_MEM    = 3'd2;
    localparam logic [PTYPE_W-1:0] PTYPE_CREDIT = 3'd3;
    localparam logic [PTYPE_W-1:0] PTYPE_DESC   = 3'd4;

    // -------------------------------------------------------------------------
    // Config register offsets (PRD §7)
    // -------------------------------------------------------------------------
    localparam logic [7:0] REG_CTRL           = 8'h00;
    localparam logic [7:0] REG_STATUS         = 8'h04;
    localparam logic [7:0] REG_FUNC_SEL       = 8'h08;
    localparam logic [7:0] REG_OP_LINES       = 8'h0C;
    localparam logic [7:0] REG_EMIT_BATCH_X   = 8'h10;
    localparam logic [7:0] REG_CREDIT_BATCH_N = 8'h14;
    localparam logic [7:0] REG_IRQ_EN         = 8'h18;
    localparam logic [7:0] REG_IRQ_STATUS     = 8'h1C;
    localparam logic [7:0] REG_A              = 8'h20;
    localparam logic [7:0] REG_B              = 8'h24;
    localparam logic [7:0] REG_C              = 8'h28;
    localparam logic [7:0] REG_D              = 8'h2C;
    localparam logic [7:0] REG_T              = 8'h30;
    localparam logic [7:0] REG_OP_SRC         = 8'h34;
    localparam logic [7:0] REG_DEST           = 8'h38;
    localparam logic [7:0] REG_IP             = 8'h3C;
    localparam logic [7:0] REG_OP             = 8'h40;
    localparam logic [7:0] REG_CNT_LINES_IN   = 8'h44;
    localparam logic [7:0] REG_CNT_LINES_OUT  = 8'h48;
    localparam logic [7:0] REG_CNT_CREDITS    = 8'h4C;
    localparam logic [7:0] REG_CNT_PKTS       = 8'h50;

    localparam logic [7:0] REG_MAX            = 8'h53;

    // -------------------------------------------------------------------------
    // CTRL / STATUS bit definitions
    // -------------------------------------------------------------------------
    localparam int CTRL_EN_BIT          = 0;
    localparam int CTRL_SOFT_RST_BIT    = 1;
    localparam int CTRL_FLUSH_BIT       = 2;

    localparam int STATUS_BUSY_BIT          = 0;
    localparam int STATUS_INPUT_EMPTY_BIT   = 1;
    localparam int STATUS_RESULT_NONEMPTY_BIT = 2;
    localparam int STATUS_GRANT_NONZERO_BIT = 3;

    localparam int IRQ_DONE_BIT         = 0;
    localparam int IRQ_ERROR_BIT        = 1;
    localparam int IRQ_GRANT_STARVED_BIT = 2;
    localparam int IRQ_CREDIT_TIMEOUT_BIT = 3;

endpackage : cell_pkg

`endif // CELL_PKG_SV
