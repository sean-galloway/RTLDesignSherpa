// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: nand_chain
// Purpose: NAND Gate Binary Tree for Timing Characterization
//
// Description:
//   Parameterizable binary tree of NAND gates between input and output
//   flip-flops. Used to measure combinational logic delay at various
//   frequencies and across different technology targets.
//
//   The tree structure is determined by the LEVELS parameter:
//     LEVELS=1: 2 leaf pairs -> 1 NAND -> 1 output flop
//     LEVELS=2: 4 leaf pairs -> 3 NANDs (tree) -> 1 output flop
//     LEVELS=3: 8 leaf pairs -> 7 NANDs (tree) -> 1 output flop
//     LEVELS=N: 2^N leaf pairs -> (2^N - 1) NANDs -> 1 output flop
//
//   For large LEVELS values, the number of leaf pairs (2^LEVELS) would
//   require an impractical number of physical flops. The NUM_FLOPS
//   parameter caps the actual flop count; leaf NANDs wrap around and
//   reuse flops via modulo indexing. This preserves the full NAND tree
//   depth (and thus the critical path) while keeping resource usage
//   bounded.
//
//   The critical path is LEVELS NAND gate delays from any leaf NAND
//   to the output flop.
//
// Tree Structure (LEVELS=3 example, NUM_FLOPS >= 8):
//
//   r_input_flops[0] --\
//                       NAND --\
//   r_input_flops[1] --/        \
//                                NAND --\
//   r_input_flops[2] --\        /       \
//                       NAND --/         \
//   r_input_flops[3] --/                  NAND --> r_out_flop
//                                        /
//   r_input_flops[4] --\                /
//                       NAND --\       /
//   r_input_flops[5] --/        \     /
//                                NAND-/
//   r_input_flops[6] --\        /
//                       NAND --/
//   r_input_flops[7] --/
//
// Parameters:
//   LEVELS    - Depth of the NAND tree (number of NAND gate delays on critical path)
//               Valid range: 1 to 64
//   NUM_FLOPS - Number of physical input flops. Leaf NANDs reuse flops via
//               modulo indexing when 2^LEVELS > NUM_FLOPS. Default: 256.
//
// Notes:
//   - Synthesis preservation attributes prevent optimization of the NAND tree
//   - Logical leaf count = 2^LEVELS (tree leaf nodes)
//   - Physical input flops = min(2^LEVELS, NUM_FLOPS)
//   - NAND gate count = 2^LEVELS - 1 (all internal nodes)
//   - Critical path = LEVELS NAND gate delays
//   - All flops use reset macros per repository standards
//
// Documentation: projects/components/timing_characterization/README.md
// Subsystem: timing_characterization
//
// Author: sean galloway
// Created: 2026-03-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module nand_chain #(
    // Primary parameters
    parameter int LEVELS    = 3,                       // Depth of NAND tree (critical path = LEVELS NAND delays)
    parameter int NUM_FLOPS = 256,                     // Physical input flop count (leaf pairs wrap via modulo)

    // Derived parameters (do not override)
    parameter int NUM_LEAVES   = 2**LEVELS,            // Logical leaf count (tree leaf nodes)
    parameter int NUM_NANDS    = NUM_LEAVES - 1,       // Total NAND gates in tree
    parameter int ACTUAL_FLOPS = (NUM_LEAVES < NUM_FLOPS) ? NUM_LEAVES : NUM_FLOPS
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // Data Interface
    //=========================================================================
    input  logic [ACTUAL_FLOPS-1:0]     i_data,        // Input data (one bit per physical flop)
    output logic                        o_data         // Output data (single bit from tree root)
);

    //=========================================================================
    // Input Flip-Flops
    //=========================================================================
    // Physical flop pool. When LEVELS is large (e.g., 64), there are 2^64
    // logical leaf pairs but only ACTUAL_FLOPS physical flops. Leaf NANDs
    // index into this pool using modulo wrapping.

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
    // NAND Gate Tree (Combinational)
    //=========================================================================
    // Binary tree of NAND gates. The tree is built bottom-up:
    //   - Leaf NANDs: inputs from r_input_flops (with modulo wrapping)
    //   - Internal NANDs: inputs from child NAND outputs
    //   - Root: single NAND output feeds r_out_flop
    //
    // Tree node indexing (heap-style):
    //   gen_nand_tree[0].w_node             = root (feeds output flop)
    //   gen_nand_tree[1..2].w_node          = level 1
    //   gen_nand_tree[3..6].w_node          = level 2
    //   gen_nand_tree[2^(L-1)-1..2^L-2]     = level L-1 (leaf NANDs)
    //
    // For a node at index i:
    //   Left child  = 2*i + 1
    //   Right child = 2*i + 2
    //   Parent      = (i - 1) / 2
    //
    // Each node declares its own w_node wire inside the generate block
    // to avoid Verilator UNOPTFLAT warnings on packed vector self-reference.

    // Build the tree using generate - each node has its own wire
    genvar g;
    generate
        for (g = 0; g < NUM_NANDS; g++) begin : gen_nand_tree

            localparam int LEFT_CHILD  = 2 * g + 1;
            localparam int RIGHT_CHILD = 2 * g + 2;

            // Per-node output wire with synthesis preservation
            `ifdef XILINX
                (* dont_touch = "true" *)
            `elsif INTEL
                /* synthesis preserve */
            `endif
            logic w_node;

            // Leaf NAND: children are input flops (with modulo wrapping)
            // Internal NAND: children are other NAND outputs
            //
            // A node is a leaf NAND if its children index >= NUM_NANDS
            // Leaf NANDs connect to input flop pairs:
            //   leaf NAND at heap index g connects to logical flop indices
            //   (g - (NUM_LEAVES/2 - 1))*2 and *2+1, wrapped by ACTUAL_FLOPS

            if (LEFT_CHILD >= NUM_NANDS) begin : gen_leaf_nand
                // Leaf NAND - inputs come from flops (modulo wrapped)
                localparam int LOGICAL_BASE = (g - (NUM_LEAVES / 2 - 1)) * 2;
                localparam int FLOP_A = LOGICAL_BASE % ACTUAL_FLOPS;
                localparam int FLOP_B = (LOGICAL_BASE + 1) % ACTUAL_FLOPS;

                assign w_node = ~(r_input_flops[FLOP_A] & r_input_flops[FLOP_B]);

            end else begin : gen_internal_nand
                // Internal NAND - inputs come from child NAND outputs

                assign w_node = ~(gen_nand_tree[LEFT_CHILD].w_node &
                                    gen_nand_tree[RIGHT_CHILD].w_node);

            end
        end
    endgenerate

    //=========================================================================
    // Output Flip-Flop (Tree Root)
    //=========================================================================
    // Captures the output of the NAND tree root (gen_nand_tree[0].w_node)

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
            r_out_flop <= gen_nand_tree[0].w_node;
        end
    )

    assign o_data = r_out_flop;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    // Parameter sanity checks
    initial begin
        assert (LEVELS >= 1) else $fatal(1, "LEVELS must be >= 1");
        assert (LEVELS <= 64) else $fatal(1, "LEVELS must be <= 64");
        assert (NUM_FLOPS >= 2) else $fatal(1, "NUM_FLOPS must be >= 2");
    end
    `endif

endmodule : nand_chain
