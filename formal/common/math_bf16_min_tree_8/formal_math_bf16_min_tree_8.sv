// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_min_tree_8

`timescale 1ns / 1ps

module formal_math_bf16_min_tree_8 (
    input logic clk
);

    (* anyconst *) logic [15:0] d0, d1, d2, d3, d4, d5, d6, d7;

    logic [15:0] min_val;
    logic [7:0]  min_idx;

    math_bf16_min_tree_8 dut (
        .i_data_0(d0), .i_data_1(d1), .i_data_2(d2), .i_data_3(d3),
        .i_data_4(d4), .i_data_5(d5), .i_data_6(d6), .i_data_7(d7),
        .ow_min(min_val), .ow_min_idx(min_idx)
    );

    // Inline FP comparison wires
    wire w_nan_d0 = (d0[14:7] == 8'hFF) & (d0[6:0] != 7'h0);
    wire w_nan_min_0 = (min_val[14:7] == 8'hFF) & (min_val[6:0] != 7'h0);
    wire w_le_d0 = (w_nan_d0 | w_nan_min_0) ? 1'b1 :
        (min_val[15] != d0[15]) ? min_val[15] :
        (min_val[15] == 1'b0) ? (min_val[14:0] <= d0[14:0]) :
        (min_val[14:0] >= d0[14:0]);
    wire w_nan_d1 = (d1[14:7] == 8'hFF) & (d1[6:0] != 7'h0);
    wire w_nan_min_1 = (min_val[14:7] == 8'hFF) & (min_val[6:0] != 7'h0);
    wire w_le_d1 = (w_nan_d1 | w_nan_min_1) ? 1'b1 :
        (min_val[15] != d1[15]) ? min_val[15] :
        (min_val[15] == 1'b0) ? (min_val[14:0] <= d1[14:0]) :
        (min_val[14:0] >= d1[14:0]);
    wire w_nan_d2 = (d2[14:7] == 8'hFF) & (d2[6:0] != 7'h0);
    wire w_nan_min_2 = (min_val[14:7] == 8'hFF) & (min_val[6:0] != 7'h0);
    wire w_le_d2 = (w_nan_d2 | w_nan_min_2) ? 1'b1 :
        (min_val[15] != d2[15]) ? min_val[15] :
        (min_val[15] == 1'b0) ? (min_val[14:0] <= d2[14:0]) :
        (min_val[14:0] >= d2[14:0]);
    wire w_nan_d3 = (d3[14:7] == 8'hFF) & (d3[6:0] != 7'h0);
    wire w_nan_min_3 = (min_val[14:7] == 8'hFF) & (min_val[6:0] != 7'h0);
    wire w_le_d3 = (w_nan_d3 | w_nan_min_3) ? 1'b1 :
        (min_val[15] != d3[15]) ? min_val[15] :
        (min_val[15] == 1'b0) ? (min_val[14:0] <= d3[14:0]) :
        (min_val[14:0] >= d3[14:0]);
    wire w_nan_d4 = (d4[14:7] == 8'hFF) & (d4[6:0] != 7'h0);
    wire w_nan_min_4 = (min_val[14:7] == 8'hFF) & (min_val[6:0] != 7'h0);
    wire w_le_d4 = (w_nan_d4 | w_nan_min_4) ? 1'b1 :
        (min_val[15] != d4[15]) ? min_val[15] :
        (min_val[15] == 1'b0) ? (min_val[14:0] <= d4[14:0]) :
        (min_val[14:0] >= d4[14:0]);
    wire w_nan_d5 = (d5[14:7] == 8'hFF) & (d5[6:0] != 7'h0);
    wire w_nan_min_5 = (min_val[14:7] == 8'hFF) & (min_val[6:0] != 7'h0);
    wire w_le_d5 = (w_nan_d5 | w_nan_min_5) ? 1'b1 :
        (min_val[15] != d5[15]) ? min_val[15] :
        (min_val[15] == 1'b0) ? (min_val[14:0] <= d5[14:0]) :
        (min_val[14:0] >= d5[14:0]);
    wire w_nan_d6 = (d6[14:7] == 8'hFF) & (d6[6:0] != 7'h0);
    wire w_nan_min_6 = (min_val[14:7] == 8'hFF) & (min_val[6:0] != 7'h0);
    wire w_le_d6 = (w_nan_d6 | w_nan_min_6) ? 1'b1 :
        (min_val[15] != d6[15]) ? min_val[15] :
        (min_val[15] == 1'b0) ? (min_val[14:0] <= d6[14:0]) :
        (min_val[14:0] >= d6[14:0]);
    wire w_nan_d7 = (d7[14:7] == 8'hFF) & (d7[6:0] != 7'h0);
    wire w_nan_min_7 = (min_val[14:7] == 8'hFF) & (min_val[6:0] != 7'h0);
    wire w_le_d7 = (w_nan_d7 | w_nan_min_7) ? 1'b1 :
        (min_val[15] != d7[15]) ? min_val[15] :
        (min_val[15] == 1'b0) ? (min_val[14:0] <= d7[14:0]) :
        (min_val[14:0] >= d7[14:0]);

    // Property 1: Output is one of the inputs
    always @(posedge clk) begin
        p_output_is_input: assert (
            min_val == d0 || min_val == d1 || min_val == d2 || min_val == d3 ||
            min_val == d4 || min_val == d5 || min_val == d6 || min_val == d7);
    end

    // Property 2: Output <= each input
    always @(posedge clk) begin
        p_le_d0: assert (w_le_d0);
        p_le_d1: assert (w_le_d1);
        p_le_d2: assert (w_le_d2);
        p_le_d3: assert (w_le_d3);
        p_le_d4: assert (w_le_d4);
        p_le_d5: assert (w_le_d5);
        p_le_d6: assert (w_le_d6);
        p_le_d7: assert (w_le_d7);
    end

    // Property 3: At least one index bit set
    always @(posedge clk) begin
        p_idx_nonzero: assert (min_idx != 8'h0);
    end

    // Property 4: Each set index bit matches min_val
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

    // Cover
    always @(posedge clk) begin
        c_unique: cover (min_idx == 8'h01);
    end

endmodule
