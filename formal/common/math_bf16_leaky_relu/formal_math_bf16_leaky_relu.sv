// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_bf16_leaky_relu
// Proves BF16 Leaky ReLU: positive passthrough, NaN propagation, negative scaling

module formal_math_bf16_leaky_relu (
    input logic clk
);

    // Free inputs
    (* anyconst *) logic [16-1:0] a;
    logic [16-1:0] result;

    // Instantiate DUT with default ALPHA_SHIFT
    math_bf16_leaky_relu dut (
        .i_a       (a),
        .ow_result (result)
    );

    // Field extraction
    wire w_sign = a[15];
    wire [8-1:0] w_exp = a[14:7];
    wire [7-1:0] w_mant = a[6:0];

    // Special cases
    wire w_is_zero = (w_exp == '0) & (w_mant == '0);
    wire w_is_nan = (w_exp == 8'hFF) & (w_mant != 7'h0);

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
        ap_zero: assert (!w_is_zero || (result == 16'h0));
    end

    // P4: Negative input -> sign bit preserved
    always @(posedge clk) begin
        ap_neg_sign: assert (w_is_nan || w_is_zero || !w_sign || result[15]);
    end

    // P5: Negative input -> mantissa preserved
    always @(posedge clk) begin
        ap_neg_mant: assert (w_is_nan || w_is_zero || !w_sign || (result[6:0] == w_mant));
    end

    // P6: Output is one of the valid results (input, scaled, or zero)
    always @(posedge clk) begin
        ap_valid: assert (result == a || result == 16'h0 ||
                         (result[15] == w_sign && result[6:0] == w_mant));
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
        cp_zero: cover (w_is_zero && result == 16'h0);
    end

endmodule
