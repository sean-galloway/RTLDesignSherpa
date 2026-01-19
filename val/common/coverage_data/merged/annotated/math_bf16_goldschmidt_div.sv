//      // verilator_coverage annotation
        // =============================================================================
        // Module: math_bf16_goldschmidt_div
        // Description: BF16 division using Goldschmidt iteration
        //
        // This module computes a/b for BF16 inputs using Goldschmidt's algorithm.
        // Unlike Newton-Raphson (which only computes reciprocals), Goldschmidt can
        // compute arbitrary division directly.
        //
        // Algorithm:
        //   Initialize: N_0 = a, D_0 = b (pre-scaled so D is in [1, 2))
        //   Iterate:
        //     F_i = 2 - D_i
        //     N_{i+1} = N_i * F_i
        //     D_{i+1} = D_i * F_i
        //
        //   As D_i -> 1, N_i -> a/b
        //
        // Key Advantage:
        //   The N and D multiplications are INDEPENDENT, making Goldschmidt ideal
        //   for pipelining. Each stage computes F and both products in parallel.
        //
        // Parameters:
        //   ITERATIONS: Number of iterations (1 or 2)
        //   LUT_DEPTH: Size of initial scaling factor LUT (32, 64, or 128)
        //   PIPELINED: 1 = registered outputs (multi-cycle), 0 = combinational
        //
        // Latency:
        //   PIPELINED=0: Combinational (~20*ITERATIONS logic levels)
        //   PIPELINED=1: ITERATIONS clock cycles (~20 levels per stage)
        //
        // Accuracy:
        //   1 iteration: ~10-12 bits
        //   2 iterations: Full BF16 accuracy
        //
        // Special Cases:
        //   - Denominator zero: Returns infinity with appropriate sign
        //   - Denominator infinity: Returns zero
        //   - Either operand NaN: Returns NaN
        //   - Numerator zero: Returns zero
        //
        // Copyright (c) 2025 Sean Galloway
        // SPDX-License-Identifier: MIT
        // =============================================================================
        
        `timescale 1ns / 1ps
        
        module math_bf16_goldschmidt_div #(
            parameter int ITERATIONS = 1,         // 1 or 2 iterations
            parameter int LUT_DEPTH = 32,         // Initial estimate LUT size
            parameter bit PIPELINED = 1           // 1=registered, 0=combinational
        ) (
 000143     input  logic        i_clk,            // Clock (only used if PIPELINED=1)
%000001     input  logic        i_rst_n,          // Reset (only used if PIPELINED=1)
%000008     input  logic [15:0] i_numerator,      // Dividend a
%000007     input  logic [15:0] i_denominator,    // Divisor b
%000001     input  logic        i_valid,          // Input valid (only used if PIPELINED=1)
%000008     output logic [15:0] ow_quotient,      // Result a/b
%000001     output logic        ow_valid,         // Output valid (only used if PIPELINED=1)
%000004     output logic        ow_div_by_zero,   // Denominator was zero
%000004     output logic        ow_is_inf,        // Result is infinity
%000002     output logic        ow_is_nan         // Either operand was NaN
        );
        
            // =========================================================================
            // Constants
            // =========================================================================
            localparam logic [15:0] BF16_TWO      = 16'h4000;  // 2.0 in BF16
            localparam logic [15:0] BF16_ONE      = 16'h3F80;  // 1.0 in BF16
            localparam logic [15:0] BF16_ZERO     = 16'h0000;
            localparam logic [15:0] BF16_POS_INF  = 16'h7F80;
            localparam logic [15:0] BF16_NEG_INF  = 16'hFF80;
            localparam logic [15:0] BF16_NAN      = 16'h7FC0;  // Quiet NaN
        
            // =========================================================================
            // Input Field Extraction
            // =========================================================================
%000008     logic        w_a_sign, w_b_sign;
 000011     logic [7:0]  w_a_exp, w_b_exp;
%000007     logic [6:0]  w_a_mant, w_b_mant;
        
            assign w_a_sign = i_numerator[15];
            assign w_a_exp  = i_numerator[14:7];
            assign w_a_mant = i_numerator[6:0];
        
            assign w_b_sign = i_denominator[15];
            assign w_b_exp  = i_denominator[14:7];
            assign w_b_mant = i_denominator[6:0];
        
            // =========================================================================
            // Special Case Detection
            // =========================================================================
%000000     logic w_a_is_zero, w_a_is_inf, w_a_is_nan;
%000000     logic w_b_is_zero, w_b_is_inf, w_b_is_nan;
 000011     logic w_result_sign;
        
            assign w_a_is_zero = (w_a_exp == 8'd0);
            assign w_a_is_inf  = (w_a_exp == 8'd255) && (w_a_mant == 7'd0);
            assign w_a_is_nan  = (w_a_exp == 8'd255) && (w_a_mant != 7'd0);
        
            assign w_b_is_zero = (w_b_exp == 8'd0);
            assign w_b_is_inf  = (w_b_exp == 8'd255) && (w_b_mant == 7'd0);
            assign w_b_is_nan  = (w_b_exp == 8'd255) && (w_b_mant != 7'd0);
        
            assign w_result_sign = w_a_sign ^ w_b_sign;
        
            // =========================================================================
            // Initial Scaling: Get 1/b estimate to scale denominator toward 1
            // =========================================================================
%000006     logic [15:0] w_recip_b;       // Initial 1/b estimate
%000000     logic        w_recip_zero, w_recip_inf, w_recip_nan;
%000002     logic        w_recip_underflow;  // 1/b underflowed (b very large)
%000006     logic [6:0]  w_recip_mant_approx; // Raw mantissa approximation (valid on underflow)
        
            math_bf16_fast_reciprocal #(
                .LUT_DEPTH(LUT_DEPTH)
            ) u_initial_recip (
                .i_bf16        (i_denominator),
                .ow_reciprocal (w_recip_b),
                .ow_is_zero    (w_recip_zero),
                .ow_is_inf     (w_recip_inf),
                .ow_is_nan     (w_recip_nan),
                .ow_underflow  (w_recip_underflow),
                .ow_mant_approx(w_recip_mant_approx)
            );
        
            // =========================================================================
            // Pre-scale: N_0 = a * (1/b_estimate), D_0 = b * (1/b_estimate)
            // This brings D_0 close to 1.0
            // =========================================================================
%000000     logic [15:0] w_n0, w_d0;
        
            // Unused outputs from prescale multipliers
%000002     logic w_prescale_n_ovf, w_prescale_n_udf, w_prescale_n_inv;
%000000     logic w_prescale_d_ovf, w_prescale_d_udf, w_prescale_d_inv;
        
            math_bf16_multiplier u_prescale_n (
                .i_a         (i_numerator),
                .i_b         (w_recip_b),
                .ow_result   (w_n0),
                .ow_overflow (w_prescale_n_ovf),
                .ow_underflow(w_prescale_n_udf),
                .ow_invalid  (w_prescale_n_inv)
            );
        
            math_bf16_multiplier u_prescale_d (
                .i_a         (i_denominator),
                .i_b         (w_recip_b),
                .ow_result   (w_d0),
                .ow_overflow (w_prescale_d_ovf),
                .ow_underflow(w_prescale_d_udf),
                .ow_invalid  (w_prescale_d_inv)
            );
        
            // =========================================================================
            // Goldschmidt Iteration 1: F = 2 - D, N' = N * F, D' = D * F
            // =========================================================================
%000000     logic [15:0] w_f0;           // 2 - D_0
%000000     logic [15:0] w_n1, w_d1;     // After iteration 1
        
            // Compute F_0 = 2 - D_0
%000001     logic [15:0] w_neg_d0;
            assign w_neg_d0 = {~w_d0[15], w_d0[14:0]};
        
            // Unused outputs from adder and multipliers
%000000     logic w_add_f0_ovf, w_add_f0_udf, w_add_f0_inv, w_add_f0_valid;
%000000     logic w_mult_n1_ovf, w_mult_n1_udf, w_mult_n1_inv;
%000000     logic w_mult_d1_ovf, w_mult_d1_udf, w_mult_d1_inv;
        
            math_bf16_adder #(
                .PIPE_STAGE_1(0),
                .PIPE_STAGE_2(0),
                .PIPE_STAGE_3(0),
                .PIPE_STAGE_4(0)
            ) u_compute_f0 (
                .i_clk       (1'b0),
                .i_rst_n     (1'b1),
                .i_a         (BF16_TWO),
                .i_b         (w_neg_d0),
                .i_valid     (1'b1),
                .ow_result   (w_f0),
                .ow_overflow (w_add_f0_ovf),
                .ow_underflow(w_add_f0_udf),
                .ow_invalid  (w_add_f0_inv),
                .ow_valid    (w_add_f0_valid)
            );
        
            // Compute N_1 = N_0 * F_0 and D_1 = D_0 * F_0 (in parallel)
            math_bf16_multiplier u_mult_n1 (
                .i_a         (w_n0),
                .i_b         (w_f0),
                .ow_result   (w_n1),
                .ow_overflow (w_mult_n1_ovf),
                .ow_underflow(w_mult_n1_udf),
                .ow_invalid  (w_mult_n1_inv)
            );
        
            math_bf16_multiplier u_mult_d1 (
                .i_a         (w_d0),
                .i_b         (w_f0),
                .ow_result   (w_d1),
                .ow_overflow (w_mult_d1_ovf),
                .ow_underflow(w_mult_d1_udf),
                .ow_invalid  (w_mult_d1_inv)
            );
        
            // =========================================================================
            // Goldschmidt Iteration 2 (optional)
            // =========================================================================
            generate
                if (ITERATIONS >= 2) begin : gen_iter2
                    logic [15:0] w_f1;
                    logic [15:0] w_n2, w_d2;
        
                    // For pipelined version, register intermediate results
                    if (PIPELINED) begin : gen_pipe_regs
                        logic [15:0] r_n1, r_d1;
                        logic        r_valid_s1;
                        logic        r_special_zero, r_special_inf, r_special_nan;
                        logic        r_result_sign;
        
                        always_ff @(posedge i_clk or negedge i_rst_n) begin
                            if (!i_rst_n) begin
                                r_n1 <= '0;
                                r_d1 <= '0;
                                r_valid_s1 <= 1'b0;
                                r_special_zero <= 1'b0;
                                r_special_inf <= 1'b0;
                                r_special_nan <= 1'b0;
                                r_result_sign <= 1'b0;
                            end else begin
                                r_n1 <= w_n1;
                                r_d1 <= w_d1;
                                r_valid_s1 <= i_valid;
                                r_special_zero <= w_b_is_zero;
                                // Zero result: a is zero, b is infinity, or prescale underflowed
                                r_special_inf <= (w_a_is_zero && !w_b_is_zero) || w_b_is_inf ||
                                                w_prescale_n_udf;
                                r_special_nan <= w_a_is_nan || w_b_is_nan ||
                                                (w_a_is_zero && w_b_is_zero) ||
                                                (w_a_is_inf && w_b_is_inf);
                                r_result_sign <= w_result_sign;
                            end
                        end
        
                        // Stage 2: Compute F_1 = 2 - D_1
                        logic [15:0] w_neg_d1_p;
                        assign w_neg_d1_p = {~r_d1[15], r_d1[14:0]};
        
                        // Unused outputs for pipelined iteration 2
                        logic w_add_f1_p_ovf, w_add_f1_p_udf, w_add_f1_p_inv, w_add_f1_p_valid;
                        logic w_mult_n2_p_ovf, w_mult_n2_p_udf, w_mult_n2_p_inv;
        
                        math_bf16_adder #(
                            .PIPE_STAGE_1(0),
                            .PIPE_STAGE_2(0),
                            .PIPE_STAGE_3(0),
                            .PIPE_STAGE_4(0)
                        ) u_compute_f1 (
                            .i_clk       (1'b0),
                            .i_rst_n     (1'b1),
                            .i_a         (BF16_TWO),
                            .i_b         (w_neg_d1_p),
                            .i_valid     (1'b1),
                            .ow_result   (w_f1),
                            .ow_overflow (w_add_f1_p_ovf),
                            .ow_underflow(w_add_f1_p_udf),
                            .ow_invalid  (w_add_f1_p_inv),
                            .ow_valid    (w_add_f1_p_valid)
                        );
        
                        // Compute N_2 = N_1 * F_1
                        math_bf16_multiplier u_mult_n2 (
                            .i_a         (r_n1),
                            .i_b         (w_f1),
                            .ow_result   (w_n2),
                            .ow_overflow (w_mult_n2_p_ovf),
                            .ow_underflow(w_mult_n2_p_udf),
                            .ow_invalid  (w_mult_n2_p_inv)
                        );
        
                        // D_2 not needed for output, skip
        
                        // Output register
                        logic [15:0] r_quotient;
                        logic        r_valid_s2;
                        logic        r_div_zero, r_is_inf, r_is_nan;
        
                        always_ff @(posedge i_clk or negedge i_rst_n) begin
                            if (!i_rst_n) begin
                                r_quotient <= '0;
                                r_valid_s2 <= 1'b0;
                                r_div_zero <= 1'b0;
                                r_is_inf <= 1'b0;
                                r_is_nan <= 1'b0;
                            end else begin
                                r_valid_s2 <= r_valid_s1;
                                r_div_zero <= r_special_zero;
                                r_is_nan <= r_special_nan;
                                r_is_inf <= r_special_zero || r_special_inf;
        
                                if (r_special_nan)
                                    r_quotient <= BF16_NAN;
                                else if (r_special_zero)
                                    r_quotient <= r_result_sign ? BF16_NEG_INF : BF16_POS_INF;
                                else if (r_special_inf)
                                    r_quotient <= BF16_ZERO;
                                else
                                    r_quotient <= {r_result_sign, w_n2[14:0]};
                            end
                        end
        
                        assign ow_quotient = r_quotient;
                        assign ow_valid = r_valid_s2;
                        assign ow_div_by_zero = r_div_zero;
                        assign ow_is_inf = r_is_inf;
                        assign ow_is_nan = r_is_nan;
        
                    end else begin : gen_comb
                        // Combinational version
                        logic [15:0] w_neg_d1_c;
                        assign w_neg_d1_c = {~w_d1[15], w_d1[14:0]};
        
                        // Unused outputs for combinational iteration 2
                        logic w_add_f1_c_ovf, w_add_f1_c_udf, w_add_f1_c_inv, w_add_f1_c_valid;
                        logic w_mult_n2_c_ovf, w_mult_n2_c_udf, w_mult_n2_c_inv;
        
                        math_bf16_adder #(
                            .PIPE_STAGE_1(0),
                            .PIPE_STAGE_2(0),
                            .PIPE_STAGE_3(0),
                            .PIPE_STAGE_4(0)
                        ) u_compute_f1 (
                            .i_clk       (1'b0),
                            .i_rst_n     (1'b1),
                            .i_a         (BF16_TWO),
                            .i_b         (w_neg_d1_c),
                            .i_valid     (1'b1),
                            .ow_result   (w_f1),
                            .ow_overflow (w_add_f1_c_ovf),
                            .ow_underflow(w_add_f1_c_udf),
                            .ow_invalid  (w_add_f1_c_inv),
                            .ow_valid    (w_add_f1_c_valid)
                        );
        
                        math_bf16_multiplier u_mult_n2 (
                            .i_a         (w_n1),
                            .i_b         (w_f1),
                            .ow_result   (w_n2),
                            .ow_overflow (w_mult_n2_c_ovf),
                            .ow_underflow(w_mult_n2_c_udf),
                            .ow_invalid  (w_mult_n2_c_inv)
                        );
        
                        // Special case handling
                        logic w_special_nan, w_special_inf, w_special_zero;
                        assign w_special_nan = w_a_is_nan || w_b_is_nan ||
                                              (w_a_is_zero && w_b_is_zero) ||
                                              (w_a_is_inf && w_b_is_inf);
                        // Zero result: a is zero, b is infinity, or prescale underflowed
                        assign w_special_zero = (w_a_is_zero && !w_b_is_zero) || w_b_is_inf ||
                                               w_prescale_n_udf;
                        assign w_special_inf = w_b_is_zero || w_a_is_inf;
        
                        assign ow_quotient = w_special_nan  ? BF16_NAN :
                                             w_b_is_zero    ? (w_result_sign ? BF16_NEG_INF : BF16_POS_INF) :
                                             w_special_zero ? BF16_ZERO :
                                                              {w_result_sign, w_n2[14:0]};
                        assign ow_valid = i_valid;
                        assign ow_div_by_zero = w_b_is_zero;
                        assign ow_is_inf = w_b_is_zero || w_a_is_inf;
                        assign ow_is_nan = w_special_nan;
                    end
        
                end else begin : gen_single_iter
                    // Single iteration - output N_1 as result
                    logic w_special_nan, w_special_inf, w_special_zero;
                    assign w_special_nan = w_a_is_nan || w_b_is_nan ||
                                          (w_a_is_zero && w_b_is_zero) ||
                                          (w_a_is_inf && w_b_is_inf);
        
                    // Estimate result exponent: a_exp - b_exp + 127
                    logic signed [9:0] w_true_exp_approx;
                    assign w_true_exp_approx = $signed({2'b0, w_a_exp}) -
                                               $signed({2'b0, w_b_exp}) + 10'sd127;
                    logic w_true_underflow;
                    assign w_true_underflow = w_true_exp_approx < 10'sd1;
        
                    // =====================================================================
                    // Direct calculation fallback for when 1/b underflows but a/b is valid
                    // When b is very large (exp >= 253), 1/b underflows to zero due to FTZ.
                    // This causes N_0 = a * 0 = 0, breaking the algorithm.
                    // For these cases, compute a/b directly using the mantissa LUT.
                    // =====================================================================
                    logic w_use_direct_calc;
                    assign w_use_direct_calc = w_recip_underflow && !w_true_underflow &&
                                              !w_special_nan && !w_b_is_zero &&
                                              !w_a_is_zero && !w_b_is_inf;
        
                    // Mantissa calculation: (1.a_mant) / (1.b_mant) using reciprocal LUT
                    // The LUT gives w_recip_mant_approx ≈ (2/1.b_mant - 1) * 128
                    // So (1 + recip_mant/128) = 2/1.b_mant
                    // product = (1.a_mant) * (2/1.b_mant) in Q8.7 format
                    // product = (128 + a_mant) * (128 + recip_mant)
                    // quotient = product / 32768 represents (1.a)/(1.b)
                    logic [15:0] w_direct_product;
                    assign w_direct_product = (16'd128 + {9'd0, w_a_mant}) *
                                              (16'd128 + {9'd0, w_recip_mant_approx});
        
                    // Check if quotient >= 1.0 (product >= 32768)
                    logic w_quot_ge_one;
                    assign w_quot_ge_one = w_direct_product >= 16'd32768;
        
                    // Exponent with normalization adjustment
                    logic signed [9:0] w_direct_exp_raw;
                    assign w_direct_exp_raw = w_true_exp_approx - (w_quot_ge_one ? 10'sd0 : 10'sd1);
        
                    // Final exponent (clamp to valid range)
                    logic [7:0] w_direct_exp;
                    assign w_direct_exp = (w_direct_exp_raw < 10'sd1) ? 8'd0 :
                                          (w_direct_exp_raw > 10'sd254) ? 8'd254 :
                                          w_direct_exp_raw[7:0];
        
                    // Mantissa extraction
                    // quot >= 1: mant = (product - 32768) / 256
                    // quot < 1:  mant = (product - 16384) / 128
                    logic [6:0] w_direct_mant;
                    assign w_direct_mant = w_quot_ge_one ?
                        ((w_direct_product - 16'd32768) >> 8) :
                        ((w_direct_product - 16'd16384) >> 7);
        
                    // Direct result for fallback path
                    logic [15:0] w_direct_result;
                    assign w_direct_result = {w_result_sign, w_direct_exp, w_direct_mant};
        
                    // Use effective underflow for zero detection (when NOT using direct calc)
                    logic w_effective_underflow;
                    assign w_effective_underflow = w_recip_underflow ? w_true_underflow :
                                                                      w_prescale_n_udf;
        
                    // Zero result: input a is zero, OR b is infinity, OR effective underflow
                    assign w_special_zero = (w_a_is_zero && !w_b_is_zero) || w_b_is_inf ||
                                           w_effective_underflow;
                    assign w_special_inf = w_b_is_zero || w_a_is_inf;
        
                    if (PIPELINED) begin : gen_pipe_single
                        logic [15:0] r_quotient;
                        logic        r_valid;
                        logic        r_div_zero, r_is_inf, r_is_nan;
        
 000072                 always_ff @(posedge i_clk or negedge i_rst_n) begin
 000011                     if (!i_rst_n) begin
 000011                         r_quotient <= '0;
 000011                         r_valid <= 1'b0;
 000011                         r_div_zero <= 1'b0;
 000011                         r_is_inf <= 1'b0;
 000011                         r_is_nan <= 1'b0;
 000061                     end else begin
 000061                         r_valid <= i_valid;
 000061                         r_div_zero <= w_b_is_zero;
 000061                         r_is_inf <= w_special_inf;
 000061                         r_is_nan <= w_special_nan;
        
%000005                         if (w_special_nan)
%000005                             r_quotient <= BF16_NAN;
%000002                         else if (w_b_is_zero)
%000002                             r_quotient <= w_result_sign ? BF16_NEG_INF : BF16_POS_INF;
%000000                         else if (w_use_direct_calc)
%000000                             r_quotient <= w_direct_result;  // Fallback path
 000010                         else if (w_special_zero)
 000010                             r_quotient <= {w_result_sign, 15'd0};  // Signed zero
                                else
 000044                             r_quotient <= {w_result_sign, w_n1[14:0]};
                            end
                        end
        
                        assign ow_quotient = r_quotient;
                        assign ow_valid = r_valid;
                        assign ow_div_by_zero = r_div_zero;
                        assign ow_is_inf = r_is_inf;
                        assign ow_is_nan = r_is_nan;
        
                    end else begin : gen_comb_single
                        assign ow_quotient = w_special_nan     ? BF16_NAN :
                                             w_b_is_zero       ? (w_result_sign ? BF16_NEG_INF : BF16_POS_INF) :
                                             w_use_direct_calc ? w_direct_result :  // Fallback path
                                             w_special_zero    ? BF16_ZERO :
                                                                 {w_result_sign, w_n1[14:0]};
                        assign ow_valid = i_valid;
                        assign ow_div_by_zero = w_b_is_zero;
                        assign ow_is_inf = w_special_inf;
                        assign ow_is_nan = w_special_nan;
                    end
                end
            endgenerate
        
        endmodule
        
