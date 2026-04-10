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

    // Free inputs -- 8 x 16-bit BF16
    (* anyconst *) logic [15:0] d0, d1, d2, d3, d4, d5, d6, d7;

    // Build flat input: {d7, d6, ..., d1, d0}
    wire [127:0] flat_in = {d7, d6, d5, d4, d3, d2, d1, d0};

    // DUT
    logic [15:0] max_val;
    logic [2:0]  max_index;
    logic        all_zero;

    math_bf16_max_tree #(.NUM_INPUTS(8)) dut (
        .i_values_flat (flat_in),
        .ow_max        (max_val),
        .ow_max_index  (max_index),
        .ow_all_zero   (all_zero)
    );

    // Zero detection (matches DUT: exp==0x00 treated as zero)
    wire z0 = (d0[14:7] == 8'h00);
    wire z1 = (d1[14:7] == 8'h00);
    wire z2 = (d2[14:7] == 8'h00);
    wire z3 = (d3[14:7] == 8'h00);
    wire z4 = (d4[14:7] == 8'h00);
    wire z5 = (d5[14:7] == 8'h00);
    wire z6 = (d6[14:7] == 8'h00);
    wire z7 = (d7[14:7] == 8'h00);
    wire all_z = z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7;

    // Mux for index -> value lookup
    wire [15:0] val_at_idx = (max_index == 3'd0) ? d0 :
                             (max_index == 3'd1) ? d1 :
                             (max_index == 3'd2) ? d2 :
                             (max_index == 3'd3) ? d3 :
                             (max_index == 3'd4) ? d4 :
                             (max_index == 3'd5) ? d5 :
                             (max_index == 3'd6) ? d6 : d7;

    // Property 1: Output is one of the inputs
    always @(posedge clk) begin
        p_output_is_input: assert (
            max_val == d0 || max_val == d1 || max_val == d2 || max_val == d3 ||
            max_val == d4 || max_val == d5 || max_val == d6 || max_val == d7);
    end

    // Property 2: max_index is valid (always true for 3-bit with 8 inputs)
    always @(posedge clk) begin
        p_idx_valid: assert (max_index < 8);
    end

    // Property 3: The value at max_index matches the output
    always @(posedge clk) begin
        p_idx_matches: assert (val_at_idx == max_val);
    end

    // NaN detection per input
    wire n0 = (d0[14:7] == 8'hFF) & (d0[6:0] != 7'h0);
    wire n1 = (d1[14:7] == 8'hFF) & (d1[6:0] != 7'h0);
    wire n2 = (d2[14:7] == 8'hFF) & (d2[6:0] != 7'h0);
    wire n3 = (d3[14:7] == 8'hFF) & (d3[6:0] != 7'h0);
    wire n4 = (d4[14:7] == 8'hFF) & (d4[6:0] != 7'h0);
    wire n5 = (d5[14:7] == 8'hFF) & (d5[6:0] != 7'h0);
    wire n6 = (d6[14:7] == 8'hFF) & (d6[6:0] != 7'h0);
    wire n7 = (d7[14:7] == 8'hFF) & (d7[6:0] != 7'h0);
    wire any_nan = n0 | n1 | n2 | n3 | n4 | n5 | n6 | n7;
    wire r_nan = (max_val[14:7] == 8'hFF) & (max_val[6:0] != 7'h0);

    // Property 4: Output magnitude >= each non-NaN input magnitude
    // When any NaN exists, the result should be a NaN (propagated as "largest").
    // Among multiple NaNs, the DUT picks the first encountered, so we only
    // compare magnitudes against non-NaN inputs.
    always @(posedge clk) begin
        if (!n0) begin p_mag_d0: assert (max_val[14:0] >= d0[14:0]); end
        if (!n1) begin p_mag_d1: assert (max_val[14:0] >= d1[14:0]); end
        if (!n2) begin p_mag_d2: assert (max_val[14:0] >= d2[14:0]); end
        if (!n3) begin p_mag_d3: assert (max_val[14:0] >= d3[14:0]); end
        if (!n4) begin p_mag_d4: assert (max_val[14:0] >= d4[14:0]); end
        if (!n5) begin p_mag_d5: assert (max_val[14:0] >= d5[14:0]); end
        if (!n6) begin p_mag_d6: assert (max_val[14:0] >= d6[14:0]); end
        if (!n7) begin p_mag_d7: assert (max_val[14:0] >= d7[14:0]); end
    end

    // Property 4b: If any input is NaN, output must be NaN
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_propagation: assert (r_nan);
        end
    end

    // Property 5: all_zero flag
    always @(posedge clk) begin
        p_all_zero: assert (all_zero == all_z);
    end

    // Cover
    always @(posedge clk) begin
        c_all_zero: cover (all_zero);
        c_not_zero: cover (!all_zero);
        c_idx_0: cover (max_index == 0);
        c_idx_7: cover (max_index == 7);
    end

endmodule
