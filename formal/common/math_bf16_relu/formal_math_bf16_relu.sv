// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_bf16_relu
// Proves BF16 ReLU: positive passthrough, negative zeroed, NaN propagation

module formal_math_bf16_relu (
    input logic clk
);

    // Free inputs
    (* anyconst *) logic [16-1:0] a;
    logic [16-1:0] result;

    // Instantiate DUT
    math_bf16_relu dut (
        .i_a       (a),
        .ow_result (result)
    );

    // Field extraction
    wire w_sign = a[15];
    wire [8-1:0] w_exp = a[14:7];
    wire [7-1:0] w_mant = a[6:0];

    // Special cases
    wire w_is_nan = (w_exp == 8'hFF) & (w_mant != 7'h0);

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: Positive input (sign=0, not NaN) -> output == input
    always @(posedge clk) begin
        ap_positive: assert (w_is_nan || w_sign || (result == a));
    end

    // P2: Negative input (sign=1, not NaN) -> output == +0
    always @(posedge clk) begin
        ap_negative: assert (w_is_nan || !w_sign || (result == 16'h0));
    end

    // P3: NaN input -> output == input (NaN propagation)
    always @(posedge clk) begin
        ap_nan: assert (!w_is_nan || (result == a));
    end

    // P4: Output is always either input or zero
    always @(posedge clk) begin
        ap_result_valid: assert ((result == a) || (result == 16'h0));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover positive input passthrough
    always @(posedge clk) begin
        cp_positive: cover (!w_sign && !w_is_nan && result == a);
    end

    // Cover negative input zeroed
    always @(posedge clk) begin
        cp_negative: cover (w_sign && !w_is_nan && result == 16'h0);
    end

    // Cover NaN propagation
    always @(posedge clk) begin
        cp_nan: cover (w_is_nan && result == a);
    end

    // Cover zero input
    always @(posedge clk) begin
        cp_zero: cover (a == 16'h0);
    end

endmodule
