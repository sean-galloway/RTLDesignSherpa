// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_max_tree_8
//
// Verifies:
//   - Output equals one of the 8 inputs
//   - Output >= all inputs (FP comparison, ignoring NaN)
//   - One-hot index points to a matching input

`timescale 1ns / 1ps

module formal_math_bf16_max_tree_8 (
    input logic clk
);

    // Free inputs
    (* anyconst *) logic [15:0] d0, d1, d2, d3, d4, d5, d6, d7;

    // Wire into unpacked array
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
    logic [15:0] max_val;
    logic [7:0]  max_idx;

    math_bf16_max_tree_8 dut (
        .i_data    (data),
        .ow_max    (max_val),
        .ow_max_idx(max_idx)
    );

    // FP greater-or-equal helper (a >= b): true when a is not less than b
    // Negative < Positive; same sign: compare magnitudes
    function automatic logic fp_ge(input logic [15:0] a, input logic [15:0] b);
        logic a_nan, b_nan;
        a_nan = (a[14:7] == 8'hFF) & (a[6:0] != 7'h0);
        b_nan = (b[14:7] == 8'hFF) & (b[6:0] != 7'h0);
        if (a_nan | b_nan) return 1'b1; // NaN: skip comparison
        if (a[15] != b[15]) return ~a[15]; // pos >= neg
        if (a[15] == 1'b0) return (a[14:0] >= b[14:0]);
        else                return (a[14:0] <= b[14:0]);
    endfunction

    // Property 1: Output is one of the inputs
    always @(posedge clk) begin
        p_output_is_input: assert (
            max_val == d0 || max_val == d1 || max_val == d2 || max_val == d3 ||
            max_val == d4 || max_val == d5 || max_val == d6 || max_val == d7
        );
    end

    // Property 2: Output >= each input (FP semantics, NaN skipped)
    always @(posedge clk) begin
        p_ge_d0: assert (fp_ge(max_val, d0));
        p_ge_d1: assert (fp_ge(max_val, d1));
        p_ge_d2: assert (fp_ge(max_val, d2));
        p_ge_d3: assert (fp_ge(max_val, d3));
        p_ge_d4: assert (fp_ge(max_val, d4));
        p_ge_d5: assert (fp_ge(max_val, d5));
        p_ge_d6: assert (fp_ge(max_val, d6));
        p_ge_d7: assert (fp_ge(max_val, d7));
    end

    // Property 3: At least one index bit set
    always @(posedge clk) begin
        p_idx_nonzero: assert (max_idx != 8'h0);
    end

    // Property 4: Each set index bit corresponds to an input matching max_val
    always @(posedge clk) begin
        if (max_idx[0]) begin p_idx0_match: assert (d0 == max_val); end
        if (max_idx[1]) begin p_idx1_match: assert (d1 == max_val); end
        if (max_idx[2]) begin p_idx2_match: assert (d2 == max_val); end
        if (max_idx[3]) begin p_idx3_match: assert (d3 == max_val); end
        if (max_idx[4]) begin p_idx4_match: assert (d4 == max_val); end
        if (max_idx[5]) begin p_idx5_match: assert (d5 == max_val); end
        if (max_idx[6]) begin p_idx6_match: assert (d6 == max_val); end
        if (max_idx[7]) begin p_idx7_match: assert (d7 == max_val); end
    end

    // Cover
    always @(posedge clk) begin
        c_all_same: cover (d0 == d1 && d1 == d2 && d2 == d3 &&
                           d3 == d4 && d4 == d5 && d5 == d6 && d6 == d7);
        c_unique_max: cover (max_idx == 8'h01);
    end

endmodule
