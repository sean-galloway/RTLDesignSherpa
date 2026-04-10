// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp32_max_tree_8

`timescale 1ns / 1ps

module formal_math_fp32_max_tree_8 (
    input logic clk
);

    (* anyconst *) logic [31:0] d0, d1, d2, d3, d4, d5, d6, d7;

    logic [31:0] data [8];
    assign data[0] = d0; assign data[1] = d1;
    assign data[2] = d2; assign data[3] = d3;
    assign data[4] = d4; assign data[5] = d5;
    assign data[6] = d6; assign data[7] = d7;

    logic [31:0] max_val;
    logic [7:0]  max_idx;

    math_fp32_max_tree_8 dut (
        .i_data(data), .ow_max(max_val), .ow_max_idx(max_idx)
    );

    // FP32 ge helper
    function automatic logic fp_ge(input logic [31:0] a, input logic [31:0] b);
        logic a_nan, b_nan;
        a_nan = (a[30:23] == 8'hFF) & (a[22:0] != 23'h0);
        b_nan = (b[30:23] == 8'hFF) & (b[22:0] != 23'h0);
        if (a_nan | b_nan) return 1'b1;
        if (a[31] != b[31]) return ~a[31];
        if (a[31] == 1'b0) return (a[30:0] >= b[30:0]);
        else                return (a[30:0] <= b[30:0]);
    endfunction

    always @(posedge clk) begin
        p_output_is_input: assert (
            max_val == d0 || max_val == d1 || max_val == d2 || max_val == d3 ||
            max_val == d4 || max_val == d5 || max_val == d6 || max_val == d7);
    end

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

    always @(posedge clk) begin
        p_idx_nonzero: assert (max_idx != 8'h0);
    end

    always @(posedge clk) begin
        if (max_idx[0]) begin p_idx0: assert (d0 == max_val); end
        if (max_idx[1]) begin p_idx1: assert (d1 == max_val); end
        if (max_idx[2]) begin p_idx2: assert (d2 == max_val); end
        if (max_idx[3]) begin p_idx3: assert (d3 == max_val); end
        if (max_idx[4]) begin p_idx4: assert (d4 == max_val); end
        if (max_idx[5]) begin p_idx5: assert (d5 == max_val); end
        if (max_idx[6]) begin p_idx6: assert (d6 == max_val); end
        if (max_idx[7]) begin p_idx7: assert (d7 == max_val); end
    end

    always @(posedge clk) begin
        c_unique_max: cover (max_idx == 8'h01);
    end

endmodule
