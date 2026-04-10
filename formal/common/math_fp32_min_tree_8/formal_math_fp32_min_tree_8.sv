// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp32_min_tree_8

`timescale 1ns / 1ps

module formal_math_fp32_min_tree_8 (
    input logic clk
);

    (* anyconst *) logic [31:0] d0, d1, d2, d3, d4, d5, d6, d7;

    logic [31:0] data [8];
    assign data[0] = d0; assign data[1] = d1;
    assign data[2] = d2; assign data[3] = d3;
    assign data[4] = d4; assign data[5] = d5;
    assign data[6] = d6; assign data[7] = d7;

    logic [31:0] min_val;
    logic [7:0]  min_idx;

    math_fp32_min_tree_8 dut (
        .i_data(data), .ow_min(min_val), .ow_min_idx(min_idx)
    );

    // FP32 le helper
    function automatic logic fp_le(input logic [31:0] a, input logic [31:0] b);
        logic a_nan, b_nan;
        a_nan = (a[30:23] == 8'hFF) & (a[22:0] != 23'h0);
        b_nan = (b[30:23] == 8'hFF) & (b[22:0] != 23'h0);
        if (a_nan | b_nan) return 1'b1;
        if (a[31] != b[31]) return a[31];
        if (a[31] == 1'b0) return (a[30:0] <= b[30:0]);
        else                return (a[30:0] >= b[30:0]);
    endfunction

    always @(posedge clk) begin
        p_output_is_input: assert (
            min_val == d0 || min_val == d1 || min_val == d2 || min_val == d3 ||
            min_val == d4 || min_val == d5 || min_val == d6 || min_val == d7);
    end

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

    always @(posedge clk) begin
        p_idx_nonzero: assert (min_idx != 8'h0);
    end

    always @(posedge clk) begin
        if (min_idx[0]) begin p_idx0: assert (d0 == min_val); end
        if (min_idx[1]) begin p_idx1: assert (d1 == min_val); end
        if (min_idx[2]) begin p_idx2: assert (d2 == min_val); end
        if (min_idx[3]) begin p_idx3: assert (d3 == min_val); end
        if (min_idx[4]) begin p_idx4: assert (d4 == min_val); end
        if (min_idx[5]) begin p_idx5: assert (d5 == min_val); end
        if (min_idx[6]) begin p_idx6: assert (d6 == min_val); end
        if (min_idx[7]) begin p_idx7: assert (d7 == min_val); end
    end

    always @(posedge clk) begin
        c_unique_min: cover (min_idx == 8'h01);
    end

endmodule
