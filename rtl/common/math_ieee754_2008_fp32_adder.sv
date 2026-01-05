// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_ieee754_2008_fp32_adder
// Purpose: IEEE 754-2008 FP32 floating-point adder with optional pipeline stages
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp32_adder.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_ieee754_2008_fp32_adder #(
    parameter bit PIPE_STAGE_1 = 1'b0,  // After exponent diff + swap
    parameter bit PIPE_STAGE_2 = 1'b0,  // After alignment shifter
    parameter bit PIPE_STAGE_3 = 1'b0,  // After mantissa add/sub
    parameter bit PIPE_STAGE_4 = 1'b0   // After normalize
) (
    input  logic        i_clk,
    input  logic        i_rst_n,
    input  logic [31:0] i_a,            // FP32 operand A
    input  logic [31:0] i_b,            // FP32 operand B
    input  logic        i_valid,        // Input valid
    output logic [31:0] ow_result,      // FP32 sum/difference
    output logic        ow_overflow,    // Overflow to infinity
    output logic        ow_underflow,   // Underflow to zero
    output logic        ow_invalid,     // Invalid operation (NaN)
    output logic        ow_valid        // Output valid
);

    // =========================================================================
    // Local Parameters
    // =========================================================================
    localparam int MANT_WIDTH = 23;          // Explicit mantissa bits
    localparam int EXP_WIDTH = 8;            // Exponent bits
    localparam int EXT_MANT_WIDTH = 27;      // Extended: 1.mmmmmmmmmmmmmmmmmmmmmmm + GRS bits
    localparam int CLZ_WIDTH = $clog2(EXT_MANT_WIDTH) + 1;
    localparam logic [7:0] EXT_MANT_WIDTH_8 = 8'd27;  // Sized for comparison with 8-bit exp_diff

    // Shifter control codes (from shifter_barrel)
    localparam logic [2:0] SHIFT_NONE        = 3'b000;
    localparam logic [2:0] SHIFT_RIGHT_LOGIC = 3'b001;
    localparam logic [2:0] SHIFT_LEFT_LOGIC  = 3'b100;

    // =========================================================================
    // Stage A: Unpack + Special Cases + Exponent Compare + Swap
    // =========================================================================

    // Unpack operand A
    wire        w_sign_a = i_a[31];
    wire [7:0]  w_exp_a  = i_a[30:23];
    wire [22:0] w_mant_a = i_a[22:0];

    // Unpack operand B
    wire        w_sign_b = i_b[31];
    wire [7:0]  w_exp_b  = i_b[30:23];
    wire [22:0] w_mant_b = i_b[22:0];

    // Special case detection
    wire w_a_is_zero     = (w_exp_a == 8'h00) && (w_mant_a == 23'h000000);
    wire w_b_is_zero     = (w_exp_b == 8'h00) && (w_mant_b == 23'h000000);
    wire w_a_is_subnorm  = (w_exp_a == 8'h00) && (w_mant_a != 23'h000000);
    wire w_b_is_subnorm  = (w_exp_b == 8'h00) && (w_mant_b != 23'h000000);
    wire w_a_is_inf      = (w_exp_a == 8'hFF) && (w_mant_a == 23'h000000);
    wire w_b_is_inf      = (w_exp_b == 8'hFF) && (w_mant_b == 23'h000000);
    wire w_a_is_nan      = (w_exp_a == 8'hFF) && (w_mant_a != 23'h000000);
    wire w_b_is_nan      = (w_exp_b == 8'hFF) && (w_mant_b != 23'h000000);

    // Effective zero (FTZ mode: subnormals treated as zero)
    wire w_a_eff_zero    = w_a_is_zero || w_a_is_subnorm;
    wire w_b_eff_zero    = w_b_is_zero || w_b_is_subnorm;

    // Normal number detection (has implied leading 1)
    wire w_a_is_normal   = ~w_a_eff_zero && ~w_a_is_inf && ~w_a_is_nan;
    wire w_b_is_normal   = ~w_b_eff_zero && ~w_b_is_inf && ~w_b_is_nan;

    // Special case flags
    wire w_any_nan       = w_a_is_nan || w_b_is_nan;
    wire w_inf_minus_inf = w_a_is_inf && w_b_is_inf && (w_sign_a != w_sign_b);
    wire w_any_inf       = w_a_is_inf || w_b_is_inf;

    // Exponent comparison: determine which operand has larger magnitude
    wire [8:0]  w_exp_diff_raw = {1'b0, w_exp_a} - {1'b0, w_exp_b};
    wire        w_exp_a_larger = ~w_exp_diff_raw[8];
    wire        w_exp_equal    = (w_exp_a == w_exp_b);
    wire        w_mant_a_larger = (w_mant_a >= w_mant_b);
    wire        w_a_larger     = w_exp_a_larger && (~w_exp_equal || w_mant_a_larger);

    // Absolute exponent difference (for shift amount)
    wire [7:0]  w_exp_diff     = w_a_larger ? (w_exp_a - w_exp_b) : (w_exp_b - w_exp_a);

    // Swap operands so larger magnitude is always "operand L"
    wire        w_sign_l       = w_a_larger ? w_sign_a : w_sign_b;
    wire        w_sign_s       = w_a_larger ? w_sign_b : w_sign_a;
    wire [7:0]  w_exp_l        = w_a_larger ? w_exp_a  : w_exp_b;
    wire [22:0] w_mant_l       = w_a_larger ? w_mant_a : w_mant_b;
    wire [22:0] w_mant_s       = w_a_larger ? w_mant_b : w_mant_a;
    wire        w_l_is_normal  = w_a_larger ? w_a_is_normal : w_b_is_normal;
    wire        w_s_is_normal  = w_a_larger ? w_b_is_normal : w_a_is_normal;
    wire        w_s_eff_zero   = w_a_larger ? w_b_eff_zero  : w_a_eff_zero;

    // Effective operation: add or subtract based on signs
    wire        w_eff_sub      = w_sign_l ^ w_sign_s;
    wire        w_result_sign  = w_sign_l;

    // =========================================================================
    // Pipeline Stage 1 (optional)
    // =========================================================================

    logic        r1_valid;
    logic        r1_any_nan, r1_inf_minus_inf, r1_any_inf;
    logic        r1_a_is_inf, r1_b_is_inf, r1_a_eff_zero, r1_b_eff_zero;
    logic        r1_sign_a, r1_sign_b, r1_result_sign, r1_eff_sub;
    logic [7:0]  r1_exp_l, r1_exp_diff;
    logic [22:0] r1_mant_l, r1_mant_s;
    logic        r1_l_is_normal, r1_s_is_normal, r1_s_eff_zero;

    generate
        if (PIPE_STAGE_1) begin : gen_pipe1
            always_ff @(posedge i_clk or negedge i_rst_n) begin
                if (!i_rst_n) begin
                    r1_valid        <= 1'b0;
                    r1_any_nan      <= 1'b0;
                    r1_inf_minus_inf <= 1'b0;
                    r1_any_inf      <= 1'b0;
                    r1_a_is_inf     <= 1'b0;
                    r1_b_is_inf     <= 1'b0;
                    r1_a_eff_zero   <= 1'b0;
                    r1_b_eff_zero   <= 1'b0;
                    r1_sign_a       <= 1'b0;
                    r1_sign_b       <= 1'b0;
                    r1_result_sign  <= 1'b0;
                    r1_eff_sub      <= 1'b0;
                    r1_exp_l        <= 8'h0;
                    r1_exp_diff     <= 8'h0;
                    r1_mant_l       <= 23'h0;
                    r1_mant_s       <= 23'h0;
                    r1_l_is_normal  <= 1'b0;
                    r1_s_is_normal  <= 1'b0;
                    r1_s_eff_zero   <= 1'b0;
                end else begin
                    r1_valid        <= i_valid;
                    r1_any_nan      <= w_any_nan;
                    r1_inf_minus_inf <= w_inf_minus_inf;
                    r1_any_inf      <= w_any_inf;
                    r1_a_is_inf     <= w_a_is_inf;
                    r1_b_is_inf     <= w_b_is_inf;
                    r1_a_eff_zero   <= w_a_eff_zero;
                    r1_b_eff_zero   <= w_b_eff_zero;
                    r1_sign_a       <= w_sign_a;
                    r1_sign_b       <= w_sign_b;
                    r1_result_sign  <= w_result_sign;
                    r1_eff_sub      <= w_eff_sub;
                    r1_exp_l        <= w_exp_l;
                    r1_exp_diff     <= w_exp_diff;
                    r1_mant_l       <= w_mant_l;
                    r1_mant_s       <= w_mant_s;
                    r1_l_is_normal  <= w_l_is_normal;
                    r1_s_is_normal  <= w_s_is_normal;
                    r1_s_eff_zero   <= w_s_eff_zero;
                end
            end
        end else begin : gen_no_pipe1
            always_comb begin
                r1_valid        = i_valid;
                r1_any_nan      = w_any_nan;
                r1_inf_minus_inf = w_inf_minus_inf;
                r1_any_inf      = w_any_inf;
                r1_a_is_inf     = w_a_is_inf;
                r1_b_is_inf     = w_b_is_inf;
                r1_a_eff_zero   = w_a_eff_zero;
                r1_b_eff_zero   = w_b_eff_zero;
                r1_sign_a       = w_sign_a;
                r1_sign_b       = w_sign_b;
                r1_result_sign  = w_result_sign;
                r1_eff_sub      = w_eff_sub;
                r1_exp_l        = w_exp_l;
                r1_exp_diff     = w_exp_diff;
                r1_mant_l       = w_mant_l;
                r1_mant_s       = w_mant_s;
                r1_l_is_normal  = w_l_is_normal;
                r1_s_is_normal  = w_s_is_normal;
                r1_s_eff_zero   = w_s_eff_zero;
            end
        end
    endgenerate

    // =========================================================================
    // Stage B: Mantissa Alignment
    // =========================================================================

    // Extend mantissas with implied bit and guard bits
    // Format: {implied_1, mant[22:0], guard, round, sticky_placeholder}
    // = 27 bits total for alignment
    wire [26:0] w_mant_l_ext = {r1_l_is_normal, r1_mant_l, 3'b000};
    wire [26:0] w_mant_s_ext = {r1_s_is_normal, r1_mant_s, 3'b000};

    // Alignment: right-shift smaller mantissa by exponent difference
    wire [26:0] w_mant_s_aligned;
    wire [$clog2(EXT_MANT_WIDTH):0] w_shift_amt;

    assign w_shift_amt = (r1_exp_diff > EXT_MANT_WIDTH_8) ?
                         EXT_MANT_WIDTH[$clog2(EXT_MANT_WIDTH):0] :
                         r1_exp_diff[$clog2(EXT_MANT_WIDTH):0];

    shifter_barrel #(
        .WIDTH(EXT_MANT_WIDTH)
    ) u_align_shifter (
        .data        (w_mant_s_ext),
        .ctrl        (SHIFT_RIGHT_LOGIC),
        .shift_amount(w_shift_amt),
        .data_out    (w_mant_s_aligned)
    );

    // Sticky bit: OR of all bits shifted out
    logic [26:0] w_sticky_mask;
    logic        w_sticky_from_shift;

    always_comb begin
        if (r1_exp_diff >= EXT_MANT_WIDTH_8) begin
            w_sticky_mask = 27'h7FFFFFF;
        end else begin
            w_sticky_mask = (27'h0000001 << r1_exp_diff) - 27'h0000001;
        end
        w_sticky_from_shift = |(w_mant_s_ext & w_sticky_mask);
    end

    wire [26:0] w_mant_s_final = r1_s_eff_zero ? 27'h0000000 : w_mant_s_aligned;
    wire        w_sticky_s     = r1_s_eff_zero ? 1'b0 : w_sticky_from_shift;

    // =========================================================================
    // Pipeline Stage 2 (optional)
    // =========================================================================

    logic        r2_valid;
    logic        r2_any_nan, r2_inf_minus_inf, r2_any_inf;
    logic        r2_a_is_inf, r2_b_is_inf, r2_a_eff_zero, r2_b_eff_zero;
    logic        r2_sign_a, r2_sign_b, r2_result_sign, r2_eff_sub;
    logic [7:0]  r2_exp_l;
    logic [26:0] r2_mant_l_ext, r2_mant_s_aligned;
    logic        r2_sticky_s;

    generate
        if (PIPE_STAGE_2) begin : gen_pipe2
            always_ff @(posedge i_clk or negedge i_rst_n) begin
                if (!i_rst_n) begin
                    r2_valid          <= 1'b0;
                    r2_any_nan        <= 1'b0;
                    r2_inf_minus_inf  <= 1'b0;
                    r2_any_inf        <= 1'b0;
                    r2_a_is_inf       <= 1'b0;
                    r2_b_is_inf       <= 1'b0;
                    r2_a_eff_zero     <= 1'b0;
                    r2_b_eff_zero     <= 1'b0;
                    r2_sign_a         <= 1'b0;
                    r2_sign_b         <= 1'b0;
                    r2_result_sign    <= 1'b0;
                    r2_eff_sub        <= 1'b0;
                    r2_exp_l          <= 8'h0;
                    r2_mant_l_ext     <= 27'h0;
                    r2_mant_s_aligned <= 27'h0;
                    r2_sticky_s       <= 1'b0;
                end else begin
                    r2_valid          <= r1_valid;
                    r2_any_nan        <= r1_any_nan;
                    r2_inf_minus_inf  <= r1_inf_minus_inf;
                    r2_any_inf        <= r1_any_inf;
                    r2_a_is_inf       <= r1_a_is_inf;
                    r2_b_is_inf       <= r1_b_is_inf;
                    r2_a_eff_zero     <= r1_a_eff_zero;
                    r2_b_eff_zero     <= r1_b_eff_zero;
                    r2_sign_a         <= r1_sign_a;
                    r2_sign_b         <= r1_sign_b;
                    r2_result_sign    <= r1_result_sign;
                    r2_eff_sub        <= r1_eff_sub;
                    r2_exp_l          <= r1_exp_l;
                    r2_mant_l_ext     <= w_mant_l_ext;
                    r2_mant_s_aligned <= w_mant_s_final;
                    r2_sticky_s       <= w_sticky_s;
                end
            end
        end else begin : gen_no_pipe2
            always_comb begin
                r2_valid          = r1_valid;
                r2_any_nan        = r1_any_nan;
                r2_inf_minus_inf  = r1_inf_minus_inf;
                r2_any_inf        = r1_any_inf;
                r2_a_is_inf       = r1_a_is_inf;
                r2_b_is_inf       = r1_b_is_inf;
                r2_a_eff_zero     = r1_a_eff_zero;
                r2_b_eff_zero     = r1_b_eff_zero;
                r2_sign_a         = r1_sign_a;
                r2_sign_b         = r1_sign_b;
                r2_result_sign    = r1_result_sign;
                r2_eff_sub        = r1_eff_sub;
                r2_exp_l          = r1_exp_l;
                r2_mant_l_ext     = w_mant_l_ext;
                r2_mant_s_aligned = w_mant_s_final;
                r2_sticky_s       = w_sticky_s;
            end
        end
    endgenerate

    // =========================================================================
    // Stage C: Mantissa Add/Subtract
    // =========================================================================

    logic [27:0] w_mant_sum;
    logic        w_mant_sum_sign;

    always_comb begin
        if (r2_eff_sub) begin
            w_mant_sum = {1'b0, r2_mant_l_ext} - {1'b0, r2_mant_s_aligned};
            w_mant_sum_sign = 1'b0;
        end else begin
            w_mant_sum = {1'b0, r2_mant_l_ext} + {1'b0, r2_mant_s_aligned};
            w_mant_sum_sign = 1'b0;
        end
    end

    wire w_add_overflow = w_mant_sum[27];
    wire w_sum_is_zero = (w_mant_sum == 28'h0000000) && ~r2_sticky_s;

    // =========================================================================
    // Pipeline Stage 3 (optional)
    // =========================================================================

    logic        r3_valid;
    logic        r3_any_nan, r3_inf_minus_inf, r3_any_inf;
    logic        r3_a_is_inf, r3_b_is_inf, r3_a_eff_zero, r3_b_eff_zero;
    logic        r3_sign_a, r3_sign_b, r3_result_sign, r3_eff_sub;
    logic [7:0]  r3_exp_l;
    logic [27:0] r3_mant_sum;
    logic        r3_add_overflow, r3_sum_is_zero;
    logic        r3_sticky_s;

    generate
        if (PIPE_STAGE_3) begin : gen_pipe3
            always_ff @(posedge i_clk or negedge i_rst_n) begin
                if (!i_rst_n) begin
                    r3_valid         <= 1'b0;
                    r3_any_nan       <= 1'b0;
                    r3_inf_minus_inf <= 1'b0;
                    r3_any_inf       <= 1'b0;
                    r3_a_is_inf      <= 1'b0;
                    r3_b_is_inf      <= 1'b0;
                    r3_a_eff_zero    <= 1'b0;
                    r3_b_eff_zero    <= 1'b0;
                    r3_sign_a        <= 1'b0;
                    r3_sign_b        <= 1'b0;
                    r3_result_sign   <= 1'b0;
                    r3_eff_sub       <= 1'b0;
                    r3_exp_l         <= 8'h0;
                    r3_mant_sum      <= 28'h0;
                    r3_add_overflow  <= 1'b0;
                    r3_sum_is_zero   <= 1'b0;
                    r3_sticky_s      <= 1'b0;
                end else begin
                    r3_valid         <= r2_valid;
                    r3_any_nan       <= r2_any_nan;
                    r3_inf_minus_inf <= r2_inf_minus_inf;
                    r3_any_inf       <= r2_any_inf;
                    r3_a_is_inf      <= r2_a_is_inf;
                    r3_b_is_inf      <= r2_b_is_inf;
                    r3_a_eff_zero    <= r2_a_eff_zero;
                    r3_b_eff_zero    <= r2_b_eff_zero;
                    r3_sign_a        <= r2_sign_a;
                    r3_sign_b        <= r2_sign_b;
                    r3_result_sign   <= r2_result_sign;
                    r3_eff_sub       <= r2_eff_sub;
                    r3_exp_l         <= r2_exp_l;
                    r3_mant_sum      <= w_mant_sum;
                    r3_add_overflow  <= w_add_overflow;
                    r3_sum_is_zero   <= w_sum_is_zero;
                    r3_sticky_s      <= r2_sticky_s;
                end
            end
        end else begin : gen_no_pipe3
            always_comb begin
                r3_valid         = r2_valid;
                r3_any_nan       = r2_any_nan;
                r3_inf_minus_inf = r2_inf_minus_inf;
                r3_any_inf       = r2_any_inf;
                r3_a_is_inf      = r2_a_is_inf;
                r3_b_is_inf      = r2_b_is_inf;
                r3_a_eff_zero    = r2_a_eff_zero;
                r3_b_eff_zero    = r2_b_eff_zero;
                r3_sign_a        = r2_sign_a;
                r3_sign_b        = r2_sign_b;
                r3_result_sign   = r2_result_sign;
                r3_eff_sub       = r2_eff_sub;
                r3_exp_l         = r2_exp_l;
                r3_mant_sum      = w_mant_sum;
                r3_add_overflow  = w_add_overflow;
                r3_sum_is_zero   = w_sum_is_zero;
                r3_sticky_s      = r2_sticky_s;
            end
        end
    endgenerate

    // =========================================================================
    // Stage D: Normalization (LZD + Shift)
    // =========================================================================

    // Leading zero count for normalization
    wire [27:0] w_mant_for_clz;
    wire [CLZ_WIDTH-1:0] w_lzc;

    // Bit reversal for CLZ module
    genvar gi;
    generate
        for (gi = 0; gi < 28; gi++) begin : gen_bit_reverse
            assign w_mant_for_clz[gi] = r3_mant_sum[27-gi];
        end
    endgenerate

    count_leading_zeros #(
        .WIDTH(28),
        .INSTANCE_NAME("FP32_ADD_CLZ")
    ) u_clz (
        .data(w_mant_for_clz),
        .clz (w_lzc)
    );

    // Determine normalization shift
    logic [4:0]  w_norm_shift_amt;
    logic        w_norm_shift_right;
    logic [26:0] w_mant_prenorm;
    logic        w_norm_sticky;

    always_comb begin
        if (r3_add_overflow) begin
            w_norm_shift_right = 1'b0;
            w_norm_shift_amt   = 5'd0;
            w_mant_prenorm     = r3_mant_sum[27:1];
            w_norm_sticky      = r3_mant_sum[0] | r3_sticky_s;
        end else if (w_lzc == 0) begin
            w_norm_shift_right = 1'b0;
            w_norm_shift_amt   = 5'd0;
            w_mant_prenorm     = r3_mant_sum[26:0];
            w_norm_sticky      = r3_sticky_s;
        end else begin
            w_norm_shift_right = 1'b0;
            w_norm_shift_amt   = (w_lzc > 1) ? (w_lzc[4:0] - 5'd1) : 5'd0;
            w_mant_prenorm     = r3_mant_sum[26:0];
            w_norm_sticky      = r3_sticky_s;
        end
    end

    // Apply normalization shift
    wire [26:0] w_mant_normalized;
    wire [$clog2(EXT_MANT_WIDTH):0] w_norm_shift_amt_ext;
    assign w_norm_shift_amt_ext = {1'b0, w_norm_shift_amt[$clog2(EXT_MANT_WIDTH)-1:0]};

    shifter_barrel #(
        .WIDTH(EXT_MANT_WIDTH)
    ) u_norm_shifter (
        .data        (w_mant_prenorm),
        .ctrl        (w_norm_shift_right ? SHIFT_RIGHT_LOGIC : SHIFT_LEFT_LOGIC),
        .shift_amount(w_norm_shift_amt_ext),
        .data_out    (w_mant_normalized)
    );

    // Calculate normalized exponent
    logic [8:0] w_exp_adjusted;

    always_comb begin
        if (r3_add_overflow) begin
            w_exp_adjusted = {1'b0, r3_exp_l} + 9'd1;
        end else if (w_norm_shift_amt > 0) begin
            w_exp_adjusted = {1'b0, r3_exp_l} - {4'b0, w_norm_shift_amt};
        end else begin
            w_exp_adjusted = {1'b0, r3_exp_l};
        end
    end

    wire w_exp_overflow  = w_exp_adjusted[8] || (w_exp_adjusted[7:0] >= 8'hFF);
    wire w_exp_underflow = w_exp_adjusted[8] || (w_exp_adjusted[7:0] == 8'h00);

    // =========================================================================
    // Pipeline Stage 4 (optional)
    // =========================================================================

    logic        r4_valid;
    logic        r4_any_nan, r4_inf_minus_inf, r4_any_inf;
    logic        r4_a_is_inf, r4_b_is_inf, r4_a_eff_zero, r4_b_eff_zero;
    logic        r4_sign_a, r4_sign_b, r4_result_sign;
    logic [7:0]  r4_exp_adjusted;
    logic [26:0] r4_mant_normalized;
    logic        r4_exp_overflow, r4_exp_underflow;
    logic        r4_sum_is_zero, r4_norm_sticky;

    generate
        if (PIPE_STAGE_4) begin : gen_pipe4
            always_ff @(posedge i_clk or negedge i_rst_n) begin
                if (!i_rst_n) begin
                    r4_valid           <= 1'b0;
                    r4_any_nan         <= 1'b0;
                    r4_inf_minus_inf   <= 1'b0;
                    r4_any_inf         <= 1'b0;
                    r4_a_is_inf        <= 1'b0;
                    r4_b_is_inf        <= 1'b0;
                    r4_a_eff_zero      <= 1'b0;
                    r4_b_eff_zero      <= 1'b0;
                    r4_sign_a          <= 1'b0;
                    r4_sign_b          <= 1'b0;
                    r4_result_sign     <= 1'b0;
                    r4_exp_adjusted    <= 8'h0;
                    r4_mant_normalized <= 27'h0;
                    r4_exp_overflow    <= 1'b0;
                    r4_exp_underflow   <= 1'b0;
                    r4_sum_is_zero     <= 1'b0;
                    r4_norm_sticky     <= 1'b0;
                end else begin
                    r4_valid           <= r3_valid;
                    r4_any_nan         <= r3_any_nan;
                    r4_inf_minus_inf   <= r3_inf_minus_inf;
                    r4_any_inf         <= r3_any_inf;
                    r4_a_is_inf        <= r3_a_is_inf;
                    r4_b_is_inf        <= r3_b_is_inf;
                    r4_a_eff_zero      <= r3_a_eff_zero;
                    r4_b_eff_zero      <= r3_b_eff_zero;
                    r4_sign_a          <= r3_sign_a;
                    r4_sign_b          <= r3_sign_b;
                    r4_result_sign     <= r3_result_sign;
                    r4_exp_adjusted    <= w_exp_adjusted[7:0];
                    r4_mant_normalized <= w_mant_normalized;
                    r4_exp_overflow    <= w_exp_overflow;
                    r4_exp_underflow   <= w_exp_underflow;
                    r4_sum_is_zero     <= r3_sum_is_zero;
                    r4_norm_sticky     <= w_norm_sticky;
                end
            end
        end else begin : gen_no_pipe4
            always_comb begin
                r4_valid           = r3_valid;
                r4_any_nan         = r3_any_nan;
                r4_inf_minus_inf   = r3_inf_minus_inf;
                r4_any_inf         = r3_any_inf;
                r4_a_is_inf        = r3_a_is_inf;
                r4_b_is_inf        = r3_b_is_inf;
                r4_a_eff_zero      = r3_a_eff_zero;
                r4_b_eff_zero      = r3_b_eff_zero;
                r4_sign_a          = r3_sign_a;
                r4_sign_b          = r3_sign_b;
                r4_result_sign     = r3_result_sign;
                r4_exp_adjusted    = w_exp_adjusted[7:0];
                r4_mant_normalized = w_mant_normalized;
                r4_exp_overflow    = w_exp_overflow;
                r4_exp_underflow   = w_exp_underflow;
                r4_sum_is_zero     = r3_sum_is_zero;
                r4_norm_sticky     = w_norm_sticky;
            end
        end
    endgenerate

    // =========================================================================
    // Stage E: Rounding + Result Assembly
    // =========================================================================

    // Extract mantissa and rounding bits
    // Format: {implied_1, mant[22:0], guard, round, sticky}
    wire [22:0] w_mant_final_raw = r4_mant_normalized[25:3];
    wire        w_guard_bit      = r4_mant_normalized[2];
    wire        w_round_bit      = r4_mant_normalized[1];
    wire        w_sticky_bit     = r4_mant_normalized[0] | r4_norm_sticky;

    // Round-to-Nearest-Even
    wire w_round_up = w_guard_bit && (w_round_bit || w_sticky_bit || w_mant_final_raw[0]);

    // Apply rounding
    wire [23:0] w_mant_rounded = {1'b0, w_mant_final_raw} + {23'b0, w_round_up};

    // Check for rounding overflow
    wire w_round_overflow = w_mant_rounded[23];

    // Final mantissa
    wire [22:0] w_mant_out = w_round_overflow ? 23'h000000 : w_mant_rounded[22:0];

    // Final exponent
    wire [8:0] w_exp_out_raw = {1'b0, r4_exp_adjusted} + {8'b0, w_round_overflow};
    wire [7:0] w_exp_out     = w_exp_out_raw[7:0];

    // Final overflow check
    wire w_final_overflow = r4_exp_overflow || (w_exp_out_raw >= 9'h0FF);

    // Sign of zero
    wire w_final_sign = r4_sum_is_zero ? 1'b0 : r4_result_sign;

    // =========================================================================
    // Special Case Result Selection
    // =========================================================================

    always_comb begin
        ow_result    = {w_final_sign, w_exp_out, w_mant_out};
        ow_overflow  = 1'b0;
        ow_underflow = 1'b0;
        ow_invalid   = 1'b0;

        if (r4_any_nan || r4_inf_minus_inf) begin
            ow_result  = {1'b0, 8'hFF, 23'h400000};  // Canonical qNaN
            ow_invalid = r4_inf_minus_inf;
        end else if (r4_any_inf) begin
            ow_result = {r4_a_is_inf ? r4_sign_a : r4_sign_b, 8'hFF, 23'h000000};
        end else if (r4_a_eff_zero && r4_b_eff_zero) begin
            ow_result = {r4_sign_a & r4_sign_b, 8'h00, 23'h000000};
        end else if (r4_a_eff_zero) begin
            ow_result = {r4_sign_b, r4_exp_adjusted, w_mant_out};
        end else if (r4_b_eff_zero) begin
            ow_result = {r4_sign_a, r4_exp_adjusted, w_mant_out};
        end else if (r4_sum_is_zero) begin
            ow_result = {1'b0, 8'h00, 23'h000000};
        end else if (w_final_overflow) begin
            ow_result   = {w_final_sign, 8'hFF, 23'h000000};
            ow_overflow = 1'b1;
        end else if (r4_exp_underflow) begin
            ow_result    = {w_final_sign, 8'h00, 23'h000000};
            ow_underflow = 1'b1;
        end
    end

    assign ow_valid = r4_valid;

endmodule : math_ieee754_2008_fp32_adder
