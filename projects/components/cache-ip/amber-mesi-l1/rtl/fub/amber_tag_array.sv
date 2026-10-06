// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_tag_array
// Purpose:
//   Per-way tag+state store for the amber MESI L1. Two combinational
//   lookup ports (CPU/fill on A, snoop on B) and one synchronous write
//   port with one-hot way select. No reset port: line validity after
//   reset is amber_control's init walk (STATE_I to every way).
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/03_tag_data_arrays.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-06

`timescale 1ns / 1ps

//==============================================================================
// Module: amber_tag_array
//==============================================================================
// Description:
//   Storage word per way is {tag[TAG_WIDTH-1:0], state[2:0]} packed in
//   TAG_STATE_WIDTH bits. All ways of a set are read in parallel on each
//   lookup port and the hit/miss decision is a combinational compare
//   across the WAY outputs (MAS ch02_blocks/03) -- the critical hit path
//   stays inside one cycle.
//
//   Address into the storage is the set index; ways are decoded on writes
//   by wr_way_onehot. The flat storage index is way * SETS + set.
//
//   The storage is NOT a shared sdpram_core instance: sdpram_core is a
//   FUB/AXI burst slave (rtl/amba/shared), the wrong shape for a
//   multi-way parallel lookup. The inferred distributed-RAM array below
//   is the same idiom the house FIFOs use internally, with the
//   GLOBAL_REQUIREMENTS 1.2 attributes. Combinational read maps to LUT
//   RAM; per-way physical banking (MAS) is a synthesis-time consequence
//   of the flat index, not a generate structure.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH:
//     Description: Address width; determines the tag width
//     Type: int
//     Range: >= SET_INDEX_WIDTH + LINE_OFFSET_WIDTH
//     Default: amber_pkg.AMBER_ADDR_WIDTH (32)
//
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
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - No reset port (GLOBAL_REQUIREMENTS 1.4: SRAM contents are not
//     reset). amber_control treats all lines as Invalid after aresetn
//     deassertion; its init walk writes STATE_I to every way (MAS
//     ch02_blocks/03, "Reset Behavior").
//   - Writes are synchronous; lookups are combinational. A write followed
//     by a lookup to the same set sees the new data after the clock edge.
//   - wr_way_onehot must be one-hot; the TB drives exactly one way.
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - Instantiated by: amber_core (amber_control drives the ports)
//   - Package: amber_pkg (state encodings, geometry defaults)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/fub/test_amber_tag_array.py
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/fub/test_amber_tag_array.py -v
//
//==============================================================================

module amber_tag_array
    import amber_pkg::*;
#(
    parameter int ADDR_WIDTH = AMBER_ADDR_WIDTH,
    parameter int SETS       = AMBER_SETS,
    parameter int WAYS       = AMBER_WAYS,
    parameter int LINE_BYTES = AMBER_LINE_BYTES,
    localparam int SET_INDEX_WIDTH = $clog2(SETS),
    localparam int TAG_WIDTH       = ADDR_WIDTH - SET_INDEX_WIDTH - $clog2(LINE_BYTES),
    localparam int TAG_STATE_WIDTH = TAG_WIDTH + 3
)(
    input  logic                                 clk,

    // Lookup port A: CPU request / fill lookup
    input  logic [SET_INDEX_WIDTH-1:0]           a_set,
    output logic [WAYS-1:0][TAG_STATE_WIDTH-1:0] a_tag_state,

    // Lookup port B: snoop lookup
    input  logic [SET_INDEX_WIDTH-1:0]           b_set,
    output logic [WAYS-1:0][TAG_STATE_WIDTH-1:0] b_tag_state,

    // Write port: fill install or hit state update
    input  logic                                 wr_en,
    input  logic [WAYS-1:0]                      wr_way_onehot,
    input  logic [SET_INDEX_WIDTH-1:0]           wr_set,
    input  logic [TAG_STATE_WIDTH-1:0]           wr_tag_state
);

    // Elaboration-time geometry checks (HAS Table 5.0 ranges + the
    // power-of-two requirements the address math depends on).
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("amber_tag_array: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("amber_tag_array: LINE_BYTES must be a power of two");
        if (WAYS < 2)
            $error("amber_tag_array: WAYS must be >= 2");
        if (TAG_WIDTH < 1)
            $error("amber_tag_array: ADDR_WIDTH too small for SETS/LINE_BYTES");
    end

    // Per-way storage, flattened to one dimension (GLOBAL_REQUIREMENTS
    // 1.3); index way * SETS + set. Combinational read => distributed RAM.
`ifdef XILINX
    (* ram_style = "distributed" *)
`elsif SYNTH_PRAGMA
    /* synthesis ramstyle = "MLAB" */
`endif
    logic [TAG_STATE_WIDTH-1:0] mem [SETS * WAYS];

    always_ff @(posedge clk) begin
        if (wr_en) begin
            for (int w = 0; w < WAYS; w++) begin
                if (wr_way_onehot[w]) begin
                    mem[w * SETS + 32'(wr_set)] <= wr_tag_state;
                end
            end
        end
    end

    always_comb begin
        for (int w = 0; w < WAYS; w++) begin
            a_tag_state[w] = mem[w * SETS + 32'(a_set)];
            b_tag_state[w] = mem[w * SETS + 32'(b_set)];
        end
    end

endmodule : amber_tag_array
