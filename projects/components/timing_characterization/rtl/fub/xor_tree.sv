// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: xor_tree
// Purpose: XOR Gate Binary Tree for Timing Characterization
//
// Description:
//   Parameterizable binary tree of XOR gates between input and output
//   flip-flops. Used to measure combinational logic delay with XOR gates
//   which stress LUT packing differently than NAND gates on FPGA fabrics.
//
//   Same tree structure as nand_chain but with XOR gates. The tree is
//   built bottom-up using heap-style indexing:
//     LEVELS=1: 2 leaf pairs -> 1 XOR  -> 1 output flop
//     LEVELS=N: 2^N leaf pairs -> (2^N - 1) XORs -> 1 output flop
//
//   Input flops are reused via modulo wrapping when 2^LEVELS > NUM_FLOPS.
//
// Parameters:
//   LEVELS    - Depth of the XOR tree (critical path = LEVELS XOR delays)
//               Valid range: 1 to 64
//   NUM_FLOPS - Number of physical input flops (default: 256)
//
// Notes:
//   - Synthesis preservation attributes prevent optimization
//   - Critical path = LEVELS XOR gate delays
//   - XOR gates test LUT usage differently than NAND on FPGAs
//
// Documentation: projects/components/timing_characterization/README.md
// Subsystem: timing_characterization
//
// Author: sean galloway
// Created: 2026-03-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module xor_tree #(
    parameter int LEVELS    = 3,
    parameter int NUM_FLOPS = 256,

    // Derived parameters (do not override)
    parameter int NUM_LEAVES   = 2**LEVELS,
    parameter int NUM_XORS     = NUM_LEAVES - 1,
    parameter int ACTUAL_FLOPS = (NUM_LEAVES < NUM_FLOPS) ? NUM_LEAVES : NUM_FLOPS
) (
    // Clock and Reset
    input  logic                    clk,
    input  logic                    rst_n,

    //=========================================================================
    // Data Interface
    //=========================================================================
    input  logic [ACTUAL_FLOPS-1:0] i_data,
    output logic                    o_data
);

    //=========================================================================
    // Input Flip-Flops
    //=========================================================================

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic [ACTUAL_FLOPS-1:0] r_input_flops;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_input_flops <= '0;
        end else begin
            r_input_flops <= i_data;
        end
    )

    //=========================================================================
    // XOR Gate Tree (Combinational)
    //=========================================================================
    // Binary tree of XOR gates using heap-style indexing.
    // Same structure as nand_chain but with XOR operation.

    genvar g;
    generate
        for (g = 0; g < NUM_XORS; g++) begin : gen_xor_tree

            localparam int LEFT_CHILD  = 2 * g + 1;
            localparam int RIGHT_CHILD = 2 * g + 2;

            `ifdef XILINX
                (* dont_touch = "true" *)
            `elsif INTEL
                /* synthesis preserve */
            `endif
            logic w_node;

            if (LEFT_CHILD >= NUM_XORS) begin : gen_leaf_xor
                localparam int LOGICAL_BASE = (g - (NUM_LEAVES / 2 - 1)) * 2;
                localparam int FLOP_A = LOGICAL_BASE % ACTUAL_FLOPS;
                localparam int FLOP_B = (LOGICAL_BASE + 1) % ACTUAL_FLOPS;

                assign w_node = r_input_flops[FLOP_A] ^ r_input_flops[FLOP_B];

            end else begin : gen_internal_xor
                assign w_node = gen_xor_tree[LEFT_CHILD].w_node ^
                                gen_xor_tree[RIGHT_CHILD].w_node;
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
            r_out_flop <= gen_xor_tree[0].w_node;
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

endmodule : xor_tree
