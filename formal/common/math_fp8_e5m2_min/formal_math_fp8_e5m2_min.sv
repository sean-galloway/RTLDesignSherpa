// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_fp8_e5m2_min
// Proves FP8_E5M2 Min: output is one of inputs, NaN handling, commutativity

module formal_math_fp8_e5m2_min (
    input logic clk
);

    // Free inputs
    (* anyconst *) logic [8-1:0] a;
    (* anyconst *) logic [8-1:0] b;
    logic [8-1:0] result;
    logic [8-1:0] result_swapped;

    // Instantiate DUT
    math_fp8_e5m2_min dut (
        .i_a       (a),
        .i_b       (b),
        .ow_result (result)
    );

    // Swapped instance for commutativity check
    math_fp8_e5m2_min dut_swap (
        .i_a       (b),
        .i_b       (a),
        .ow_result (result_swapped)
    );

    // Field extraction
    wire w_sign_a = a[7];
    wire [5-1:0] w_exp_a = a[6:2];
    wire [2-1:0] w_mant_a = a[1:0];
    wire w_sign_b = b[7];
    wire [5-1:0] w_exp_b = b[6:2];
    wire [2-1:0] w_mant_b = b[1:0];

    // NaN detection
    wire w_a_is_nan = (w_exp_a == 5'h1F) & (w_mant_a != 2'h0);
    wire w_b_is_nan = (w_exp_b == 5'h1F) & (w_mant_b != 2'h0);
    wire w_any_nan = w_a_is_nan | w_b_is_nan;

    // =========================================================================
    // Safety properties
    // =========================================================================

    // P1: Output is always one of the two inputs
    always @(posedge clk) begin
        ap_one_of_inputs: assert ((result == a) || (result == b));
    end

    // P2: If a is NaN, result is b
    always @(posedge clk) begin
        ap_a_nan: assert (!w_a_is_nan || (result == b));
    end

    // P3: If b is NaN (and a is not), result is a
    always @(posedge clk) begin
        ap_b_nan: assert (w_a_is_nan || !w_b_is_nan || (result == a));
    end

    // P4: Commutativity when neither is NaN - min(a,b) == min(b,a)
    always @(posedge clk) begin
        ap_commutative: assert (w_any_nan || (result == result_swapped));
    end

    // P5: min(a,a) == a (idempotent)
    always @(posedge clk) begin
        ap_idempotent: assert ((a != b) || (result == a));
    end

    // P6: Both NaN -> result is one of the NaN inputs
    always @(posedge clk) begin
        ap_both_nan: assert (!(w_a_is_nan && w_b_is_nan) || (result == a || result == b));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    always @(posedge clk) begin
        cp_a_wins: cover (!w_a_is_nan && !w_b_is_nan && result == a && a != b);
    end

    always @(posedge clk) begin
        cp_b_wins: cover (!w_a_is_nan && !w_b_is_nan && result == b && a != b);
    end

    always @(posedge clk) begin
        cp_both_nan: cover (w_a_is_nan && w_b_is_nan);
    end

    always @(posedge clk) begin
        cp_equal: cover (a == b && !w_a_is_nan);
    end

    always @(posedge clk) begin
        cp_pos_neg: cover (!w_sign_a && w_sign_b && !w_a_is_nan && !w_b_is_nan);
    end

endmodule
