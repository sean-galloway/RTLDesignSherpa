// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_bf16_max_tree
// Purpose: Tree-based reduction to find maximum magnitude BF16 value
//
// Documentation: BF16_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-12-25
//

`timescale 1ns / 1ps

//==============================================================================
// Module: math_bf16_max_tree
//==============================================================================
// Description:
//   Finds the maximum magnitude BF16 value from an array of N inputs using
//   a tree-based reduction structure. Each level of the tree uses
//   math_bf16_comparator modules to compare pairs and propagate winners.
//
// Features:
//   - Parameterized input count (must be power of 2)
//   - O(log2(N)) levels of comparison
//   - Combinational (single-cycle) operation
//   - Proper NaN handling (NaN propagates as "largest")
//   - Returns both max value and its index
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   NUM_INPUTS:
//     Description: Number of BF16 inputs to compare
//     Type: int
//     Range: 2, 4, 8, 16, 32, 64, 128, 256, 512 (powers of 2)
//     Default: 8
//     Constraints: Must be power of 2
//
//------------------------------------------------------------------------------
// Ports:
//------------------------------------------------------------------------------
//   Inputs:
//     i_values[NUM_INPUTS-1:0][15:0]: Array of BF16 values to compare
//
//   Outputs:
//     ow_max[15:0]:          BF16 value with largest magnitude
//     ow_max_index[$clog2(NUM_INPUTS)-1:0]: Index of the max value
//     ow_all_zero:           1 if all inputs are zero
//
//------------------------------------------------------------------------------
// Architecture:
//------------------------------------------------------------------------------
//   For NUM_INPUTS=8, the tree has 3 levels:
//
//   Level 0: [0] [1] [2] [3] [4] [5] [6] [7]   (8 inputs)
//              \ /     \ /     \ /     \ /
//   Level 1:   [0]     [1]     [2]     [3]     (4 intermediate)
//                \     /         \     /
//   Level 2:       [0]             [1]         (2 intermediate)
//                    \             /
//   Level 3:            [max]                  (1 output)
//
//   Each comparison node also tracks the index of the winning value.
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/common/test_math_bf16_max_tree.py
//   Run: pytest val/common/test_math_bf16_max_tree.py -v
//
//==============================================================================
module math_bf16_max_tree #(
    parameter int NUM_INPUTS = 8
) (
    input  logic [NUM_INPUTS*16-1:0]    i_values_flat,  // Flattened: {val[N-1], ..., val[1], val[0]}
    output logic [15:0]                 ow_max,
    output logic [$clog2(NUM_INPUTS)-1:0] ow_max_index,
    output logic                        ow_all_zero
);

// Unpack flattened input into array for internal use
logic [NUM_INPUTS-1:0][15:0] i_values;
generate
    for (genvar i = 0; i < NUM_INPUTS; i++) begin : gen_unpack
        assign i_values[i] = i_values_flat[i*16 +: 16];
    end
endgenerate

// Number of tree levels
localparam int NUM_LEVELS = $clog2(NUM_INPUTS);
localparam int IDX_WIDTH = $clog2(NUM_INPUTS);

// Total number of comparator nodes = NUM_INPUTS - 1
// Flat array to store all intermediate values and indices
// Node numbering: first NUM_INPUTS/2 nodes are level 0, next NUM_INPUTS/4 are level 1, etc.
localparam int TOTAL_NODES = NUM_INPUTS - 1;

// Flat wires for all tree nodes
// Note: Verilator warns about UNOPTFLAT because it sees array indices
// being read and written in the same generate block. This is a false positive
// since each level only reads from lower-indexed nodes and writes to higher-indexed nodes.
/* verilator lint_off UNOPTFLAT */
logic [TOTAL_NODES-1:0][15:0] node_values;
logic [TOTAL_NODES-1:0][IDX_WIDTH-1:0] node_indices;
logic [TOTAL_NODES-1:0] node_a_greater;
/* verilator lint_on UNOPTFLAT */

// Zero detection for all inputs
logic [NUM_INPUTS-1:0] input_is_zero;
generate
    for (genvar i = 0; i < NUM_INPUTS; i++) begin : gen_zero_detect
        // Zero: exp=0 (including subnormals treated as zero)
        assign input_is_zero[i] = (i_values[i][14:7] == 8'h00);
    end
endgenerate
assign ow_all_zero = &input_is_zero;

// Generate the tree structure with explicit node indices
// Level 0: nodes 0 to NUM_INPUTS/2-1 (compare inputs pairwise)
// Level 1: nodes NUM_INPUTS/2 to NUM_INPUTS/2+NUM_INPUTS/4-1
// etc.

generate
    // Level 0: compare adjacent inputs
    for (genvar n = 0; n < NUM_INPUTS/2; n++) begin : gen_level0
        math_bf16_comparator u_cmp (
            .i_a(i_values[2*n]),
            .i_b(i_values[2*n + 1]),
            .ow_max(node_values[n]),
            .ow_a_greater(node_a_greater[n]),
            .ow_equal()
        );
        assign node_indices[n] = node_a_greater[n] ? IDX_WIDTH'(2*n) : IDX_WIDTH'(2*n + 1);
    end

    // Level 1 and beyond
    if (NUM_INPUTS >= 4) begin : gen_level1_plus
        // Level 1: nodes NUM_INPUTS/2 to NUM_INPUTS/2 + NUM_INPUTS/4 - 1
        localparam int L1_START = NUM_INPUTS/2;
        localparam int L1_COUNT = NUM_INPUTS/4;

        for (genvar n = 0; n < L1_COUNT; n++) begin : gen_level1
            localparam int SRC_BASE = 0;  // Level 0 starts at node 0
            math_bf16_comparator u_cmp (
                .i_a(node_values[SRC_BASE + 2*n]),
                .i_b(node_values[SRC_BASE + 2*n + 1]),
                .ow_max(node_values[L1_START + n]),
                .ow_a_greater(node_a_greater[L1_START + n]),
                .ow_equal()
            );
            assign node_indices[L1_START + n] = node_a_greater[L1_START + n] ?
                node_indices[SRC_BASE + 2*n] : node_indices[SRC_BASE + 2*n + 1];
        end
    end

    if (NUM_INPUTS >= 8) begin : gen_level2_plus
        // Level 2: nodes start after level 1
        localparam int L2_START = NUM_INPUTS/2 + NUM_INPUTS/4;
        localparam int L2_COUNT = NUM_INPUTS/8;
        localparam int L1_START = NUM_INPUTS/2;

        for (genvar n = 0; n < L2_COUNT; n++) begin : gen_level2
            math_bf16_comparator u_cmp (
                .i_a(node_values[L1_START + 2*n]),
                .i_b(node_values[L1_START + 2*n + 1]),
                .ow_max(node_values[L2_START + n]),
                .ow_a_greater(node_a_greater[L2_START + n]),
                .ow_equal()
            );
            assign node_indices[L2_START + n] = node_a_greater[L2_START + n] ?
                node_indices[L1_START + 2*n] : node_indices[L1_START + 2*n + 1];
        end
    end

    if (NUM_INPUTS >= 16) begin : gen_level3_plus
        localparam int L3_START = NUM_INPUTS/2 + NUM_INPUTS/4 + NUM_INPUTS/8;
        localparam int L3_COUNT = NUM_INPUTS/16;
        localparam int L2_START = NUM_INPUTS/2 + NUM_INPUTS/4;

        for (genvar n = 0; n < L3_COUNT; n++) begin : gen_level3
            math_bf16_comparator u_cmp (
                .i_a(node_values[L2_START + 2*n]),
                .i_b(node_values[L2_START + 2*n + 1]),
                .ow_max(node_values[L3_START + n]),
                .ow_a_greater(node_a_greater[L3_START + n]),
                .ow_equal()
            );
            assign node_indices[L3_START + n] = node_a_greater[L3_START + n] ?
                node_indices[L2_START + 2*n] : node_indices[L2_START + 2*n + 1];
        end
    end

    if (NUM_INPUTS >= 32) begin : gen_level4_plus
        localparam int L4_START = NUM_INPUTS/2 + NUM_INPUTS/4 + NUM_INPUTS/8 + NUM_INPUTS/16;
        localparam int L4_COUNT = NUM_INPUTS/32;
        localparam int L3_START = NUM_INPUTS/2 + NUM_INPUTS/4 + NUM_INPUTS/8;

        for (genvar n = 0; n < L4_COUNT; n++) begin : gen_level4
            math_bf16_comparator u_cmp (
                .i_a(node_values[L3_START + 2*n]),
                .i_b(node_values[L3_START + 2*n + 1]),
                .ow_max(node_values[L4_START + n]),
                .ow_a_greater(node_a_greater[L4_START + n]),
                .ow_equal()
            );
            assign node_indices[L4_START + n] = node_a_greater[L4_START + n] ?
                node_indices[L3_START + 2*n] : node_indices[L3_START + 2*n + 1];
        end
    end

    if (NUM_INPUTS >= 64) begin : gen_level5_plus
        localparam int L5_START = NUM_INPUTS - NUM_INPUTS/32 - 1;
        localparam int L5_COUNT = NUM_INPUTS/64;
        localparam int L4_START = NUM_INPUTS/2 + NUM_INPUTS/4 + NUM_INPUTS/8 + NUM_INPUTS/16;

        for (genvar n = 0; n < L5_COUNT; n++) begin : gen_level5
            math_bf16_comparator u_cmp (
                .i_a(node_values[L4_START + 2*n]),
                .i_b(node_values[L4_START + 2*n + 1]),
                .ow_max(node_values[L5_START + n]),
                .ow_a_greater(node_a_greater[L5_START + n]),
                .ow_equal()
            );
            assign node_indices[L5_START + n] = node_a_greater[L5_START + n] ?
                node_indices[L4_START + 2*n] : node_indices[L4_START + 2*n + 1];
        end
    end
endgenerate

// Output is the last node in the flat array
assign ow_max = node_values[TOTAL_NODES-1];
assign ow_max_index = node_indices[TOTAL_NODES-1];

endmodule : math_bf16_max_tree
