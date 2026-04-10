// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_fp8_e4m3_leaky_relu
// Proves FP8_E4M3 Leaky ReLU: positive passthrough, NaN propagation, negative scaling

module formal_math_fp8_e4m3_leaky_relu (
    input logic clk
);

    // Free inputs
    (* anyconst *) logic [8-1:0] a;
    logic [8-1:0] result;

    // Instantiate DUT with default ALPHA_SHIFT
    math_fp8_e4m3_leaky_relu dut (
        .i_a       (a),
        .ow_result (result)
    );

    // Field extraction
    wire w_sign = a[7];
    wire [4-1:0] w_exp = a[6:3];
    wire [3-1:0] w_mant = a[2:0];

    // Special cases
    wire w_is_zero = (w_exp == '0) & (w_mant == '0);
    wire w_is_nan = (w_exp == 4'hF) & (w_mant == 3'h7);

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: Positive input (sign=0, not NaN, not zero) -> output == input
    always @(posedge clk) begin
        ap_positive: assert (w_is_nan || w_is_zero || w_sign || (result == a));
    end

    // P2: NaN input -> output == input (NaN propagation)
    always @(posedge clk) begin
        ap_nan: assert (!w_is_nan || (result == a));
    end

    // P3: Zero input -> output == zero
    always @(posedge clk) begin
        ap_zero: assert (!w_is_zero || (result == 8'h0));
    end

    // P4: Negative input -> sign bit preserved
    always @(posedge clk) begin
        ap_neg_sign: assert (w_is_nan || w_is_zero || !w_sign || result[7]);
    end

    // P5: Negative input -> mantissa preserved
    always @(posedge clk) begin
        ap_neg_mant: assert (w_is_nan || w_is_zero || !w_sign || (result[2:0] == w_mant));
    end

    // P6: Output is one of the valid results (input, scaled, or zero)
    always @(posedge clk) begin
        ap_valid: assert (result == a || result == 8'h0 ||
                         (result[7] == w_sign && result[2:0] == w_mant));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    always @(posedge clk) begin
        cp_positive: cover (!w_sign && !w_is_nan && !w_is_zero && result == a);
    end

    always @(posedge clk) begin
        cp_negative: cover (w_sign && !w_is_nan && !w_is_zero);
    end

    always @(posedge clk) begin
        cp_nan: cover (w_is_nan && result == a);
    end

    always @(posedge clk) begin
        cp_zero: cover (w_is_zero && result == 8'h0);
    end

endmodule
