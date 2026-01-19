//      // verilator_coverage annotation
        // =============================================================================
        // Module: math_bf16_newton_raphson_recip
        // Description: BF16 reciprocal using Newton-Raphson iteration
        //
        // This module computes 1/x for BF16 inputs using Newton-Raphson refinement
        // of an initial LUT-based estimate. Each iteration roughly doubles precision.
        //
        // Algorithm:
        //   1. Get initial estimate x_0 from LUT (~5-6 bits accuracy)
        //   2. Iterate: x_{n+1} = x_n * (2 - a * x_n)
        //   3. After 1 iteration: ~10-12 bits accuracy
        //   4. After 2 iterations: full BF16 accuracy (exceeds 7-bit mantissa)
        //
        // The iteration formula derives from Newton's method on f(x) = 1/x - a:
        //   x_{n+1} = x_n - f(x_n)/f'(x_n) = x_n - (1/x_n - a)/(-1/x_n^2)
        //           = x_n + x_n - a*x_n^2 = x_n * (2 - a * x_n)
        //
        // Parameters:
        //   ITERATIONS: Number of Newton-Raphson iterations (1 or 2)
        //   LUT_DEPTH: Size of initial estimate LUT (32, 64, or 128)
        //
        // Latency: Combinational (0 cycles)
        // Logic Levels: ~10 + 15*ITERATIONS
        //   - 1 iteration: ~25 levels
        //   - 2 iterations: ~40 levels
        //
        // Special Cases:
        //   - Zero input: Returns positive infinity (0x7F80)
        //   - Infinity input: Returns zero (0x0000)
        //   - NaN input: Returns NaN (propagates)
        //   - Subnormal input: Treated as zero (returns infinity)
        //
        // Copyright (c) 2025 Sean Galloway
        // SPDX-License-Identifier: MIT
        // =============================================================================
        
        `timescale 1ns / 1ps
        
        module math_bf16_newton_raphson_recip #(
            parameter int ITERATIONS = 1,         // 1 or 2 iterations
            parameter int LUT_DEPTH = 32          // Initial estimate LUT size
        ) (
%000007     input  logic [15:0] i_bf16,           // Input BF16 value
%000007     output logic [15:0] ow_reciprocal,    // Reciprocal result (1/x)
%000002     output logic        ow_is_zero,       // Input was zero (output is inf)
%000002     output logic        ow_is_inf,        // Input was infinity (output is zero)
%000002     output logic        ow_is_nan         // Input was NaN (output is NaN)
        );
        
            // =========================================================================
            // Constants
            // =========================================================================
            localparam logic [15:0] BF16_TWO      = 16'h4000;  // 2.0 in BF16
            localparam logic [15:0] BF16_ZERO     = 16'h0000;
            localparam logic [15:0] BF16_POS_INF  = 16'h7F80;
            localparam logic [15:0] BF16_NEG_INF  = 16'hFF80;
            localparam logic [15:0] BF16_NAN      = 16'h7FC0;  // Quiet NaN
        
            // =========================================================================
            // Initial Estimate from LUT (reuses fast_reciprocal logic)
            // =========================================================================
%000007     logic [15:0] w_x0;           // Initial estimate
%000002     logic        w_init_zero;
%000002     logic        w_init_inf;
%000002     logic        w_init_nan;
%000002     logic        w_init_underflow;    // Not used in Newton-Raphson
%000005     logic [6:0]  w_init_mant_approx;  // Not used in Newton-Raphson
        
            math_bf16_fast_reciprocal #(
                .LUT_DEPTH(LUT_DEPTH)
            ) u_initial_estimate (
                .i_bf16        (i_bf16),
                .ow_reciprocal (w_x0),
                .ow_is_zero    (w_init_zero),
                .ow_is_inf     (w_init_inf),
                .ow_is_nan     (w_init_nan),
                .ow_underflow  (w_init_underflow),
                .ow_mant_approx(w_init_mant_approx)
            );
        
            // =========================================================================
            // Newton-Raphson Iteration 1: x1 = x0 * (2 - a * x0)
            // =========================================================================
%000000     logic [15:0] w_a_times_x0;    // a * x0
%000000     logic [15:0] w_two_minus_ax0; // 2 - a * x0
%000007     logic [15:0] w_x1;            // x0 * (2 - a * x0)
        
            // Unused outputs from multiplier
%000000     logic w_mult_ax0_ovf, w_mult_ax0_udf, w_mult_ax0_inv;
%000000     logic w_mult_x1_ovf, w_mult_x1_udf, w_mult_x1_inv;
        
            // Compute a * x0
            math_bf16_multiplier u_mult_ax0 (
                .i_a         (i_bf16),
                .i_b         (w_x0),
                .ow_result   (w_a_times_x0),
                .ow_overflow (w_mult_ax0_ovf),
                .ow_underflow(w_mult_ax0_udf),
                .ow_invalid  (w_mult_ax0_inv)
            );
        
            // Compute 2 - a * x0 using adder (2 + (-ax0))
            // For subtraction, flip sign bit of ax0
%000000     logic [15:0] w_neg_ax0;
            assign w_neg_ax0 = {~w_a_times_x0[15], w_a_times_x0[14:0]};
        
            // Unused outputs from adder
%000000     logic w_add1_ovf, w_add1_udf, w_add1_inv, w_add1_valid;
        
            math_bf16_adder #(
                .PIPE_STAGE_1(0),
                .PIPE_STAGE_2(0),
                .PIPE_STAGE_3(0),
                .PIPE_STAGE_4(0)
            ) u_sub_iter1 (
                .i_clk       (1'b0),
                .i_rst_n     (1'b1),
                .i_a         (BF16_TWO),
                .i_b         (w_neg_ax0),
                .i_valid     (1'b1),
                .ow_result   (w_two_minus_ax0),
                .ow_overflow (w_add1_ovf),
                .ow_underflow(w_add1_udf),
                .ow_invalid  (w_add1_inv),
                .ow_valid    (w_add1_valid)
            );
        
            // Compute x1 = x0 * (2 - a * x0)
            math_bf16_multiplier u_mult_x1 (
                .i_a         (w_x0),
                .i_b         (w_two_minus_ax0),
                .ow_result   (w_x1),
                .ow_overflow (w_mult_x1_ovf),
                .ow_underflow(w_mult_x1_udf),
                .ow_invalid  (w_mult_x1_inv)
            );
        
            // =========================================================================
            // Newton-Raphson Iteration 2 (optional): x2 = x1 * (2 - a * x1)
            // =========================================================================
            generate
                if (ITERATIONS >= 2) begin : gen_iter2
                    logic [15:0] w_a_times_x1;
                    logic [15:0] w_two_minus_ax1;
                    logic [15:0] w_x2;
        
                    // Unused outputs
                    logic w_mult_ax1_ovf, w_mult_ax1_udf, w_mult_ax1_inv;
                    logic w_mult_x2_ovf, w_mult_x2_udf, w_mult_x2_inv;
                    logic w_add2_ovf, w_add2_udf, w_add2_inv, w_add2_valid;
        
                    // Compute a * x1
                    math_bf16_multiplier u_mult_ax1 (
                        .i_a         (i_bf16),
                        .i_b         (w_x1),
                        .ow_result   (w_a_times_x1),
                        .ow_overflow (w_mult_ax1_ovf),
                        .ow_underflow(w_mult_ax1_udf),
                        .ow_invalid  (w_mult_ax1_inv)
                    );
        
                    // Compute 2 - a * x1
                    logic [15:0] w_neg_ax1;
                    assign w_neg_ax1 = {~w_a_times_x1[15], w_a_times_x1[14:0]};
        
                    math_bf16_adder #(
                        .PIPE_STAGE_1(0),
                        .PIPE_STAGE_2(0),
                        .PIPE_STAGE_3(0),
                        .PIPE_STAGE_4(0)
                    ) u_sub_iter2 (
                        .i_clk       (1'b0),
                        .i_rst_n     (1'b1),
                        .i_a         (BF16_TWO),
                        .i_b         (w_neg_ax1),
                        .i_valid     (1'b1),
                        .ow_result   (w_two_minus_ax1),
                        .ow_overflow (w_add2_ovf),
                        .ow_underflow(w_add2_udf),
                        .ow_invalid  (w_add2_inv),
                        .ow_valid    (w_add2_valid)
                    );
        
                    // Compute x2 = x1 * (2 - a * x1)
                    math_bf16_multiplier u_mult_x2 (
                        .i_a         (w_x1),
                        .i_b         (w_two_minus_ax1),
                        .ow_result   (w_x2),
                        .ow_overflow (w_mult_x2_ovf),
                        .ow_underflow(w_mult_x2_udf),
                        .ow_invalid  (w_mult_x2_inv)
                    );
        
                    // Final result with sign from input
                    logic [15:0] w_result_iter2;
                    assign w_result_iter2 = {i_bf16[15], w_x2[14:0]};
        
                    // Output selection based on special cases
                    // 1/inf = 0, 1/(-inf) = -0, preserve sign for infinity input
                    assign ow_reciprocal = w_init_nan  ? BF16_NAN :
                                           w_init_zero ? (i_bf16[15] ? BF16_NEG_INF : BF16_POS_INF) :
                                           w_init_inf  ? {i_bf16[15], 15'b0} :  // Preserve sign for 1/inf
                                                         w_result_iter2;
                end else begin : gen_iter1
                    // Single iteration result with sign from input
                    logic [15:0] w_result_iter1;
                    assign w_result_iter1 = {i_bf16[15], w_x1[14:0]};
        
                    // Output selection based on special cases
                    // 1/inf = 0, 1/(-inf) = -0, preserve sign for infinity input
                    assign ow_reciprocal = w_init_nan  ? BF16_NAN :
                                           w_init_zero ? (i_bf16[15] ? BF16_NEG_INF : BF16_POS_INF) :
                                           w_init_inf  ? {i_bf16[15], 15'b0} :  // Preserve sign for 1/inf
                                                         w_result_iter1;
                end
            endgenerate
        
            // =========================================================================
            // Status Outputs
            // =========================================================================
            assign ow_is_zero = w_init_zero;
            assign ow_is_inf  = w_init_inf;
            assign ow_is_nan  = w_init_nan;
        
        endmodule
        
