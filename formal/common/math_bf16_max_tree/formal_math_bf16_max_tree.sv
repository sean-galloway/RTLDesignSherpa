// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_max_tree
//
// Verifies with NUM_INPUTS=8 (default):
//   - Output equals one of the 8 inputs
//   - Output magnitude >= all input magnitudes (NaN propagates as largest)
//   - ow_max_index points to a valid input
//   - ow_all_zero correct when all inputs are zero

`timescale 1ns / 1ps

module formal_math_bf16_max_tree (
    input logic clk
);

    localparam int N = 8;
    localparam int IDX_W = $clog2(N);

    // Free inputs -- 8 x 16-bit BF16
    (* anyconst *) logic [15:0] d0, d1, d2, d3, d4, d5, d6, d7;

    // Build flat input
    wire [N*16-1:0] flat_in = {d7, d6, d5, d4, d3, d2, d1, d0};

    // DUT
    logic [15:0]      max_val;
    logic [IDX_W-1:0] max_index;
    logic              all_zero;

    math_bf16_max_tree #(.NUM_INPUTS(N)) dut (
        .i_values_flat (flat_in),
        .ow_max        (max_val),
        .ow_max_index  (max_index),
        .ow_all_zero   (all_zero)
    );

    // Extract individual values for assertions
    wire [15:0] vals [N];
    assign vals[0] = d0; assign vals[1] = d1;
    assign vals[2] = d2; assign vals[3] = d3;
    assign vals[4] = d4; assign vals[5] = d5;
    assign vals[6] = d6; assign vals[7] = d7;

    // Zero detection (matches DUT: exp==0x00 treated as zero)
    wire [N-1:0] is_zero;
    genvar gi;
    generate
        for (gi = 0; gi < N; gi++) begin : gen_zero
            assign is_zero[gi] = (vals[gi][14:7] == 8'h00);
        end
    endgenerate

    // Property 1: Output is one of the inputs
    always @(posedge clk) begin
        p_output_is_input: assert (
            max_val == d0 || max_val == d1 || max_val == d2 || max_val == d3 ||
            max_val == d4 || max_val == d5 || max_val == d6 || max_val == d7);
    end

    // Property 2: max_index is valid
    always @(posedge clk) begin
        p_idx_valid: assert (max_index < N);
    end

    // Property 3: The value at max_index matches the output
    always @(posedge clk) begin
        p_idx_matches: assert (vals[max_index] == max_val);
    end

    // Property 4: Output magnitude >= each input magnitude (ignoring sign)
    // NaN (exp=FF, mant!=0) has magnitude 0x7Fxx which is largest, so it
    // naturally wins magnitude comparison -- consistent with DUT behavior.
    always @(posedge clk) begin
        p_mag_d0: assert (max_val[14:0] >= d0[14:0]);
        p_mag_d1: assert (max_val[14:0] >= d1[14:0]);
        p_mag_d2: assert (max_val[14:0] >= d2[14:0]);
        p_mag_d3: assert (max_val[14:0] >= d3[14:0]);
        p_mag_d4: assert (max_val[14:0] >= d4[14:0]);
        p_mag_d5: assert (max_val[14:0] >= d5[14:0]);
        p_mag_d6: assert (max_val[14:0] >= d6[14:0]);
        p_mag_d7: assert (max_val[14:0] >= d7[14:0]);
    end

    // Property 5: all_zero flag
    always @(posedge clk) begin
        p_all_zero: assert (all_zero == &is_zero);
    end

    // Cover
    always @(posedge clk) begin
        c_all_zero: cover (all_zero);
        c_not_zero: cover (!all_zero);
        c_idx_0: cover (max_index == 0);
        c_idx_7: cover (max_index == 7);
    end

endmodule
