// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: l1_data_array
// Purpose:
//   Per-way cache-line data store for the cache-ip shared MESI L1. One line is
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
// Module: l1_data_array
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
//   l1_tag_array: a per-beat AXI burst slave is the wrong shape for a
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
//     Default: l1_pkg.AMBER_SETS (128)
//
//   WAYS:
//     Description: Associativity
//     Type: int
//     Range: 2 to 8
//     Default: l1_pkg.AMBER_WAYS (4)
//
//   LINE_BYTES:
//     Description: Cache line size in bytes (power of two)
//     Type: int
//     Range: 32 to 64
//     Default: l1_pkg.AMBER_LINE_BYTES (64)
//
//   BUS_WIDTH:
//     Description: CPU/fabric data width in bits
//     Type: int
//     Range: 32 to 128, multiple of 8
//     Default: l1_pkg.AMBER_BUS_WIDTH (64)
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
//   - Instantiated by: l1_core (l1_control drives the ports)
//   - Package: l1_pkg (geometry defaults)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/fub/test_amber_data_array.py
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/fub/test_amber_data_array.py -v
//
//==============================================================================

module l1_data_array
    import l1_pkg::*;
#(
    parameter int SETS       = AMBER_SETS,
    parameter int WAYS       = AMBER_WAYS,
    parameter int LINE_BYTES = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH  = AMBER_BUS_WIDTH,
    // 0: combinational read (distributed RAM; the original contract).
    // 1: registered read -- *_rdata is the word at the address presented
    //    the PREVIOUS cycle; the way select stays after the register so
    //    *_way may arrive with the data. This is the block-RAM shape: on
    //    the Kintex-7 pair rig the combinational form is 16k LUTRAM +
    //    8.7k F7/F8 muxes per core, the registered form 16 RAMB36 +
    //    ~140 LUT (FPGA review 2026-11-07). Read-before-write: a read of
    //    the address written at the same edge returns the OLD word; the
    //    controller never consumes that word (l1_control DATA_SYNC_READ).
    parameter bit SYNC_READ  = 1'b0,
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
            $error("l1_data_array: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("l1_data_array: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
            $error("l1_data_array: LINE_BYTES / BUS_WIDTH*8 must be a power of two");
        if ((BUS_WIDTH % 8) != 0)
            $error("l1_data_array: BUS_WIDTH must be a multiple of 8");
        if (WAYS < 2)
            $error("l1_data_array: WAYS must be >= 2");
    end

    // Per-way storage (GLOBAL_REQUIREMENTS 1.3).  Each way is a separate
    // inferred dual-port array so synthesis sees exactly one write address
    // per process; the one-hot way select picks the array, and the byte
    // enables pick the lanes within the beat.  This is the same logical
    // layout as the old flat index (way * (SETS * FILL_BEATS) + {set,beat}).
    // SYNC_READ=0: the combinational read maps to distributed RAM.
    // SYNC_READ=1: the registered read maps to block RAM (two copies, one
    // per read port). Either way the restructure avoids the "multiple
    // writes in one process" pattern that made Vivado dissolve the flat
    // array.
    logic [BUS_WIDTH-1:0] a_rdata_per_way [WAYS];
    logic [BUS_WIDTH-1:0] b_rdata_per_way [WAYS];

    generate
        for (genvar w = 0; w < WAYS; w++) begin : g_way
            (* ram_style = "auto" *)
            /* synthesis ramstyle = "AUTO" */
            logic [BUS_WIDTH-1:0] mem [SETS * FILL_BEATS];

            always_ff @(posedge clk) begin
                if (wr_en && wr_way_onehot[w]) begin
                    for (int b = 0; b < STRB_W; b++) begin
                        if (wr_be[b]) begin
                            mem[wr_addr][8*b +: 8] <= wr_wdata[8*b +: 8];
                        end
                    end
                end
            end

            if (SYNC_READ) begin : g_sync
                always_ff @(posedge clk) begin
                    a_rdata_per_way[w] <= mem[a_addr];
                    b_rdata_per_way[w] <= mem[b_addr];
                end
            end else begin : g_comb
                always_comb begin
                    a_rdata_per_way[w] = mem[a_addr];
                    b_rdata_per_way[w] = mem[b_addr];
                end
            end
        end
    endgenerate

    always_comb begin
        a_rdata = a_rdata_per_way[a_way];
        b_rdata = b_rdata_per_way[b_way];
    end

endmodule : l1_data_array
