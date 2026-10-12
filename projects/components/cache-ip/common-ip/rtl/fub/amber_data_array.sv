// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_data_array
// Purpose:
//   Per-way cache-line data store for the amber MESI L1. One line is
//   LINE_BYTES bytes split into FILL_BEATS beats of BUS_WIDTH bits; the
//   beat address is {set, beat}. Byte-write enables support CPU write
//   merge on a hit; fills write whole beats. No reset port.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/03_tag_data_arrays.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-06

`timescale 1ns / 1ps

//==============================================================================
// Module: amber_data_array
//==============================================================================
// Description:
//   Storage organization per MAS ch02_blocks/03: depth SETS * FILL_BEATS,
//   width BUS_WIDTH, one flat array per way, index
//     way * (SETS * FILL_BEATS) + {set, beat}.
//
//   Port A reads one beat of one way (the tag lookup has already selected
//   the way) for the CPU hit / replay path. Port B does the same for the
//   snoop data transfer, which walks beats of the matching way. The write
//   port installs fill beats (all byte enables) or merges CPU write data
//   (per-byte enables) into the hit way.
//
//   Not a shared sdpram_core instance for the same reason as
//   amber_tag_array: a per-beat AXI burst slave is the wrong shape for a
//   single-beat random-access readout. Inferred RAM, house FIFO idiom,
//   GLOBAL_REQUIREMENTS 1.2 attributes; block RAM is the expected mapping
//   at the default geometry (4 ways x 128 sets x 8 beats x 64 bit).
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SETS:
//     Description: Number of sets (power of two)
//     Type: int
//     Range: 16 to 512
//     Default: amber_pkg.AMBER_SETS (128)
//
//   WAYS:
//     Description: Associativity
//     Type: int
//     Range: 2 to 8
//     Default: amber_pkg.AMBER_WAYS (4)
//
//   LINE_BYTES:
//     Description: Cache line size in bytes (power of two)
//     Type: int
//     Range: 32 to 64
//     Default: amber_pkg.AMBER_LINE_BYTES (64)
//
//   BUS_WIDTH:
//     Description: CPU/fabric data width in bits
//     Type: int
//     Range: 32 to 128, multiple of 8
//     Default: amber_pkg.AMBER_BUS_WIDTH (64)
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - No reset port (GLOBAL_REQUIREMENTS 1.4).
//   - wr_be is per-byte: a fill asserts all bits; a CPU write hit asserts
//     the bytes the transaction selects and the merge preserves the rest
//     of the beat.
//   - Read data is combinational; like the tag array, a write is visible
//     to a lookup after the clock edge.
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - Instantiated by: amber_core (amber_control drives the ports)
//   - Package: amber_pkg (geometry defaults)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/fub/test_amber_data_array.py
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/fub/test_amber_data_array.py -v
//
//==============================================================================

module amber_data_array
    import amber_pkg::*;
#(
    parameter int SETS       = AMBER_SETS,
    parameter int WAYS       = AMBER_WAYS,
    parameter int LINE_BYTES = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH  = AMBER_BUS_WIDTH,
    localparam int STRB_W          = BUS_WIDTH / 8,
    localparam int FILL_BEATS      = LINE_BYTES / STRB_W,
    localparam int SET_INDEX_WIDTH = $clog2(SETS),
    localparam int BEAT_INDEX_WIDTH= $clog2(FILL_BEATS),
    localparam int WAY_INDEX_WIDTH = $clog2(WAYS),
    localparam int MEM_ADDR_WIDTH  = SET_INDEX_WIDTH + BEAT_INDEX_WIDTH
)(
    input  logic                          clk,

    // Read port A: CPU hit / replay data
    input  logic [MEM_ADDR_WIDTH-1:0]     a_addr,   // {set, beat}
    input  logic [WAY_INDEX_WIDTH-1:0]    a_way,
    output logic [BUS_WIDTH-1:0]          a_rdata,

    // Read port B: snoop data transfer
    input  logic [MEM_ADDR_WIDTH-1:0]     b_addr,   // {set, beat}
    input  logic [WAY_INDEX_WIDTH-1:0]    b_way,
    output logic [BUS_WIDTH-1:0]          b_rdata,

    // Write port: fill beats (full wr_be) or CPU write merge (partial wr_be)
    input  logic                          wr_en,
    input  logic [WAYS-1:0]               wr_way_onehot,
    input  logic [MEM_ADDR_WIDTH-1:0]     wr_addr,  // {set, beat}
    input  logic [BUS_WIDTH-1:0]          wr_wdata,
    input  logic [STRB_W-1:0]             wr_be
);

    // Elaboration-time geometry checks.
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("amber_data_array: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("amber_data_array: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
            $error("amber_data_array: LINE_BYTES / BUS_WIDTH*8 must be a power of two");
        if ((BUS_WIDTH % 8) != 0)
            $error("amber_data_array: BUS_WIDTH must be a multiple of 8");
        if (WAYS < 2)
            $error("amber_data_array: WAYS must be >= 2");
    end

    // Flat storage (GLOBAL_REQUIREMENTS 1.3); index
    // way * (SETS * FILL_BEATS) + {set, beat} -- the {set, beat} address
    // is already the intra-way offset by construction.
`ifdef XILINX
    (* ram_style = "auto" *)
`elsif SYNTH_PRAGMA
    /* synthesis ramstyle = "AUTO" */
`endif
    logic [BUS_WIDTH-1:0] mem [SETS * FILL_BEATS * WAYS];

    always_ff @(posedge clk) begin
        if (wr_en) begin
            for (int w = 0; w < WAYS; w++) begin
                if (wr_way_onehot[w]) begin
                    for (int b = 0; b < STRB_W; b++) begin
                        if (wr_be[b]) begin
                            mem[w * SETS * FILL_BEATS + 32'(wr_addr)][8*b +: 8]
                                <= wr_wdata[8*b +: 8];
                        end
                    end
                end
            end
        end
    end

    always_comb begin
        a_rdata = mem[32'(a_way) * SETS * FILL_BEATS + 32'(a_addr)];
        b_rdata = mem[32'(b_way) * SETS * FILL_BEATS + 32'(b_addr)];
    end

endmodule : amber_data_array
