// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_min_tree_8
//
// Verifies:
//   - Output equals one of the 8 inputs
//   - Output <= all inputs (FP comparison, ignoring NaN)
//   - One-hot index points to a matching input

`timescale 1ns / 1ps

module formal_math_bf16_min_tree_8 (
    input logic clk
);

    // Free inputs
    (* anyconst *) logic [15:0] d0, d1, d2, d3, d4, d5, d6, d7;

    logic [15:0] data [8];
    assign data[0] = d0;
    assign data[1] = d1;
    assign data[2] = d2;
    assign data[3] = d3;
    assign data[4] = d4;
    assign data[5] = d5;
    assign data[6] = d6;
    assign data[7] = d7;

    // DUT
    logic [15:0] min_val;
    logic [7:0]  min_idx;

    math_bf16_min_tree_8 dut (
        .i_data    (data),
        .ow_min    (min_val),
        .ow_min_idx(min_idx)
    );

    // FP less-or-equal helper (a <= b)
    function automatic logic fp_le(input logic [15:0] a, input logic [15:0] b);
        logic a_nan, b_nan;
        a_nan = (a[14:7] == 8'hFF) & (a[6:0] != 7'h0);
        b_nan = (b[14:7] == 8'hFF) & (b[6:0] != 7'h0);
        if (a_nan | b_nan) return 1'b1;
        if (a[15] != b[15]) return a[15]; // neg <= pos
        if (a[15] == 1'b0) return (a[14:0] <= b[14:0]);
        else                return (a[14:0] >= b[14:0]);
    endfunction

    // Property 1: Output is one of the inputs
    always @(posedge clk) begin
        p_output_is_input: assert (
            min_val == d0 || min_val == d1 || min_val == d2 || min_val == d3 ||
            min_val == d4 || min_val == d5 || min_val == d6 || min_val == d7
        );
    end

    // Property 2: Output <= each input
    always @(posedge clk) begin
        p_le_d0: assert (fp_le(min_val, d0));
        p_le_d1: assert (fp_le(min_val, d1));
        p_le_d2: assert (fp_le(min_val, d2));
        p_le_d3: assert (fp_le(min_val, d3));
        p_le_d4: assert (fp_le(min_val, d4));
        p_le_d5: assert (fp_le(min_val, d5));
        p_le_d6: assert (fp_le(min_val, d6));
        p_le_d7: assert (fp_le(min_val, d7));
    end

    // Property 3: At least one index bit set
    always @(posedge clk) begin
        p_idx_nonzero: assert (min_idx != 8'h0);
    end

    // Property 4: Each set index bit matches min_val
    always @(posedge clk) begin
        if (min_idx[0]) begin p_idx0_match: assert (d0 == min_val); end
        if (min_idx[1]) begin p_idx1_match: assert (d1 == min_val); end
        if (min_idx[2]) begin p_idx2_match: assert (d2 == min_val); end
        if (min_idx[3]) begin p_idx3_match: assert (d3 == min_val); end
        if (min_idx[4]) begin p_idx4_match: assert (d4 == min_val); end
        if (min_idx[5]) begin p_idx5_match: assert (d5 == min_val); end
        if (min_idx[6]) begin p_idx6_match: assert (d6 == min_val); end
        if (min_idx[7]) begin p_idx7_match: assert (d7 == min_val); end
    end

    // Cover
    always @(posedge clk) begin
        c_all_same: cover (d0 == d1 && d1 == d2 && d2 == d3 &&
                           d3 == d4 && d4 == d5 && d5 == d6 && d6 == d7);
        c_unique_min: cover (min_idx == 8'h01);
    end

endmodule
