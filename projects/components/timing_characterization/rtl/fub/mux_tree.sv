// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mux_tree
// Purpose: Binary Mux Tree for Timing Characterization
//
// Description:
//   Parameterizable binary tree of 2:1 multiplexers between input and
//   output flip-flops. Used to measure mux-tree propagation delay, which
//   tests routing fabric and LUT usage differently than logic gates.
//
//   The tree structure mirrors nand_chain but uses 2:1 muxes. Each mux
//   selects between its two child outputs based on a select bit from
//   a registered select vector.
//
//   Tree structure (LEVELS=3):
//     data[0] --\
//                MUX(sel[0]) --\
//     data[1] --/               \
//                                MUX(sel[4]) --\
//     data[2] --\               /               \
//                MUX(sel[1]) --/                  MUX(sel[6]) --> r_out_flop
//                                                /
//     data[3] --\                               /
//                MUX(sel[2]) --\               /
//     data[4] --/               \             /
//                                MUX(sel[5])-/
//     data[5] --\               /
//                MUX(sel[3]) --/
//     data[6] --/
//
//   Note: leaf muxes use 2 data inputs + 1 select, so we need
//   NUM_LEAVES data inputs and NUM_MUXES select bits.
//
// Parameters:
//   LEVELS    - Depth of the mux tree (critical path = LEVELS mux delays)
//               Valid range: 1 to 64
//   NUM_FLOPS - Number of physical input data flops (default: 256)
//
// Notes:
//   - Synthesis preservation attributes prevent optimization
//   - NUM_LEAVES = 2^LEVELS data inputs (with modulo flop reuse)
//   - NUM_MUXES = 2^LEVELS - 1 select bits
//   - Critical path = LEVELS mux delays
//
// Documentation: projects/components/timing_characterization/README.md
// Subsystem: timing_characterization
//
// Author: sean galloway
// Created: 2026-03-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module mux_tree #(
    parameter int LEVELS    = 3,
    parameter int NUM_FLOPS = 256,

    // Derived parameters (do not override)
    parameter int NUM_LEAVES    = 2**LEVELS,
    parameter int NUM_MUXES     = NUM_LEAVES - 1,
    parameter int ACTUAL_FLOPS  = (NUM_LEAVES < NUM_FLOPS) ? NUM_LEAVES : NUM_FLOPS,
    parameter int ACTUAL_SEL    = (NUM_MUXES < NUM_FLOPS)  ? NUM_MUXES  : NUM_FLOPS
) (
    // Clock and Reset
    input  logic                     clk,
    input  logic                     rst_n,

    //=========================================================================
    // Data Interface
    //=========================================================================
    input  logic [ACTUAL_FLOPS-1:0]  i_data,
    input  logic [ACTUAL_SEL-1:0]    i_sel,
    output logic                     o_data
);

    //=========================================================================
    // Input Flip-Flops (Data)
    //=========================================================================

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic [ACTUAL_FLOPS-1:0] r_data_flops;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_data_flops <= '0;
        end else begin
            r_data_flops <= i_data;
        end
    )

    //=========================================================================
    // Input Flip-Flops (Select)
    //=========================================================================

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic [ACTUAL_SEL-1:0] r_sel_flops;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_sel_flops <= '0;
        end else begin
            r_sel_flops <= i_sel;
        end
    )

    //=========================================================================
    // Mux Tree (Combinational)
    //=========================================================================
    // Binary tree of 2:1 muxes using heap-style indexing.
    // Leaf muxes select between data flop pairs.
    // Internal muxes select between child mux outputs.

    genvar g;
    generate
        for (g = 0; g < NUM_MUXES; g++) begin : gen_mux_tree

            localparam int LEFT_CHILD  = 2 * g + 1;
            localparam int RIGHT_CHILD = 2 * g + 2;
            localparam int SEL_IDX     = g % ACTUAL_SEL;

            `ifdef XILINX
                (* dont_touch = "true" *)
            `elsif INTEL
                /* synthesis preserve */
            `endif
            logic w_node;

            if (LEFT_CHILD >= NUM_MUXES) begin : gen_leaf_mux
                // Leaf mux: inputs from data flops (modulo wrapped)
                localparam int LOGICAL_BASE = (g - (NUM_LEAVES / 2 - 1)) * 2;
                localparam int FLOP_A = LOGICAL_BASE % ACTUAL_FLOPS;
                localparam int FLOP_B = (LOGICAL_BASE + 1) % ACTUAL_FLOPS;

                assign w_node = r_sel_flops[SEL_IDX]
                              ? r_data_flops[FLOP_B]
                              : r_data_flops[FLOP_A];

            end else begin : gen_internal_mux
                // Internal mux: inputs from child mux outputs
                assign w_node = r_sel_flops[SEL_IDX]
                              ? gen_mux_tree[RIGHT_CHILD].w_node
                              : gen_mux_tree[LEFT_CHILD].w_node;
            end

        end
    endgenerate

    //=========================================================================
    // Output Flip-Flop (Tree Root)
    //=========================================================================

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic r_out_flop;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_out_flop <= 1'b0;
        end else begin
            r_out_flop <= gen_mux_tree[0].w_node;
        end
    )

    assign o_data = r_out_flop;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    initial begin
        assert (LEVELS >= 1) else $fatal(1, "LEVELS must be >= 1");
        assert (LEVELS <= 64) else $fatal(1, "LEVELS must be <= 64");
        assert (NUM_FLOPS >= 2) else $fatal(1, "NUM_FLOPS must be >= 2");
    end
    `endif

endmodule : mux_tree
