// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp32_max_tree_8

`timescale 1ns / 1ps

module formal_math_fp32_max_tree_8 (
    input logic clk
);

    (* anyconst *) logic [31:0] d0, d1, d2, d3, d4, d5, d6, d7;

    logic [31:0] max_val;
    logic [7:0]  max_idx;

    math_fp32_max_tree_8 dut (
        .i_data_0(d0), .i_data_1(d1), .i_data_2(d2), .i_data_3(d3),
        .i_data_4(d4), .i_data_5(d5), .i_data_6(d6), .i_data_7(d7),
        .ow_max(max_val), .ow_max_idx(max_idx)
    );

    // Inline FP comparison wires
    wire w_nan_d0 = (d0[30:23] == 8'hFF) & (d0[22:0] != 23'h0);
    wire w_nan_max_0 = (max_val[30:23] == 8'hFF) & (max_val[22:0] != 23'h0);
    wire w_ge_d0 = (w_nan_d0 | w_nan_max_0) ? 1'b1 :
        (max_val[31] != d0[31]) ? ~max_val[31] :
        (max_val[31] == 1'b0) ? (max_val[30:0] >= d0[30:0]) :
        (max_val[30:0] <= d0[30:0]);
    wire w_nan_d1 = (d1[30:23] == 8'hFF) & (d1[22:0] != 23'h0);
    wire w_nan_max_1 = (max_val[30:23] == 8'hFF) & (max_val[22:0] != 23'h0);
    wire w_ge_d1 = (w_nan_d1 | w_nan_max_1) ? 1'b1 :
        (max_val[31] != d1[31]) ? ~max_val[31] :
        (max_val[31] == 1'b0) ? (max_val[30:0] >= d1[30:0]) :
        (max_val[30:0] <= d1[30:0]);
    wire w_nan_d2 = (d2[30:23] == 8'hFF) & (d2[22:0] != 23'h0);
    wire w_nan_max_2 = (max_val[30:23] == 8'hFF) & (max_val[22:0] != 23'h0);
    wire w_ge_d2 = (w_nan_d2 | w_nan_max_2) ? 1'b1 :
        (max_val[31] != d2[31]) ? ~max_val[31] :
        (max_val[31] == 1'b0) ? (max_val[30:0] >= d2[30:0]) :
        (max_val[30:0] <= d2[30:0]);
    wire w_nan_d3 = (d3[30:23] == 8'hFF) & (d3[22:0] != 23'h0);
    wire w_nan_max_3 = (max_val[30:23] == 8'hFF) & (max_val[22:0] != 23'h0);
    wire w_ge_d3 = (w_nan_d3 | w_nan_max_3) ? 1'b1 :
        (max_val[31] != d3[31]) ? ~max_val[31] :
        (max_val[31] == 1'b0) ? (max_val[30:0] >= d3[30:0]) :
        (max_val[30:0] <= d3[30:0]);
    wire w_nan_d4 = (d4[30:23] == 8'hFF) & (d4[22:0] != 23'h0);
    wire w_nan_max_4 = (max_val[30:23] == 8'hFF) & (max_val[22:0] != 23'h0);
    wire w_ge_d4 = (w_nan_d4 | w_nan_max_4) ? 1'b1 :
        (max_val[31] != d4[31]) ? ~max_val[31] :
        (max_val[31] == 1'b0) ? (max_val[30:0] >= d4[30:0]) :
        (max_val[30:0] <= d4[30:0]);
    wire w_nan_d5 = (d5[30:23] == 8'hFF) & (d5[22:0] != 23'h0);
    wire w_nan_max_5 = (max_val[30:23] == 8'hFF) & (max_val[22:0] != 23'h0);
    wire w_ge_d5 = (w_nan_d5 | w_nan_max_5) ? 1'b1 :
        (max_val[31] != d5[31]) ? ~max_val[31] :
        (max_val[31] == 1'b0) ? (max_val[30:0] >= d5[30:0]) :
        (max_val[30:0] <= d5[30:0]);
    wire w_nan_d6 = (d6[30:23] == 8'hFF) & (d6[22:0] != 23'h0);
    wire w_nan_max_6 = (max_val[30:23] == 8'hFF) & (max_val[22:0] != 23'h0);
    wire w_ge_d6 = (w_nan_d6 | w_nan_max_6) ? 1'b1 :
        (max_val[31] != d6[31]) ? ~max_val[31] :
        (max_val[31] == 1'b0) ? (max_val[30:0] >= d6[30:0]) :
        (max_val[30:0] <= d6[30:0]);
    wire w_nan_d7 = (d7[30:23] == 8'hFF) & (d7[22:0] != 23'h0);
    wire w_nan_max_7 = (max_val[30:23] == 8'hFF) & (max_val[22:0] != 23'h0);
    wire w_ge_d7 = (w_nan_d7 | w_nan_max_7) ? 1'b1 :
        (max_val[31] != d7[31]) ? ~max_val[31] :
        (max_val[31] == 1'b0) ? (max_val[30:0] >= d7[30:0]) :
        (max_val[30:0] <= d7[30:0]);

    // Property 1: Output is one of the inputs
    always @(posedge clk) begin
        p_output_is_input: assert (
            max_val == d0 || max_val == d1 || max_val == d2 || max_val == d3 ||
            max_val == d4 || max_val == d5 || max_val == d6 || max_val == d7);
    end

    // Property 2: Output >= each input
    always @(posedge clk) begin
        p_ge_d0: assert (w_ge_d0);
        p_ge_d1: assert (w_ge_d1);
        p_ge_d2: assert (w_ge_d2);
        p_ge_d3: assert (w_ge_d3);
        p_ge_d4: assert (w_ge_d4);
        p_ge_d5: assert (w_ge_d5);
        p_ge_d6: assert (w_ge_d6);
        p_ge_d7: assert (w_ge_d7);
    end

    // Property 3: At least one index bit set
    always @(posedge clk) begin
        p_idx_nonzero: assert (max_idx != 8'h0);
    end

    // Property 4: Each set index bit matches max_val
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

    // Cover
    always @(posedge clk) begin
        c_unique: cover (max_idx == 8'h01);
    end

endmodule
