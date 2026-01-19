//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: math_bf16_adder
        // Purpose: BF16 floating-point adder with optional pipeline stages
        //
        // BF16 Format:
        //   [15]    - Sign bit
        //   [14:7]  - 8-bit biased exponent (bias = 127)
        //   [6:0]   - 7-bit mantissa (implied leading 1 for normalized)
        //
        // Features:
        //   - Configurable pipeline stages for frequency/latency tradeoff
        //   - Flush-to-zero (FTZ) for subnormal inputs
        //   - Round-to-nearest-even (RNE) rounding
        //   - Full special case handling (zero, inf, NaN)
        //   - Reuses existing shifter_barrel and count_leading_zeros modules
        //
        // Pipeline Stages (each independently configurable):
        //   PIPE_STAGE_1: After exponent compare + operand swap
        //   PIPE_STAGE_2: After mantissa alignment
        //   PIPE_STAGE_3: After mantissa add/subtract
        //   PIPE_STAGE_4: After normalization
        //
        // Latency: 1 + PIPE_STAGE_1 + PIPE_STAGE_2 + PIPE_STAGE_3 + PIPE_STAGE_4 cycles
        //
        // Documentation: docs/bf16-research.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-11-26
        
        `timescale 1ns / 1ps
        
        module math_bf16_adder #(
            parameter int PIPE_STAGE_1 = 0,  // After exponent diff + swap
            parameter int PIPE_STAGE_2 = 0,  // After alignment shifter
            parameter int PIPE_STAGE_3 = 0,  // After mantissa add/sub
            parameter int PIPE_STAGE_4 = 0   // After normalize
        ) (
%000000     input  logic        i_clk,
%000001     input  logic        i_rst_n,
%000000     input  logic [15:0] i_a,            // BF16 operand A
%000000     input  logic [15:0] i_b,            // BF16 operand B
%000001     input  logic        i_valid,        // Input valid
%000000     output logic [15:0] ow_result,      // BF16 sum/difference
%000000     output logic        ow_overflow,    // Overflow to infinity
%000000     output logic        ow_underflow,   // Underflow to zero
%000000     output logic        ow_invalid,     // Invalid operation (NaN)
%000001     output logic        ow_valid        // Output valid
        );
        
            // =========================================================================
            // Local Parameters
            // =========================================================================
            localparam int MANT_WIDTH = 7;           // Explicit mantissa bits
            localparam int EXP_WIDTH = 8;            // Exponent bits
            localparam int EXT_MANT_WIDTH = 11;      // Extended: 1.mmmmmmm + GRS bits
            localparam int CLZ_WIDTH = $clog2(EXT_MANT_WIDTH) + 1;
        
            // Shifter control codes (from shifter_barrel)
            localparam logic [2:0] SHIFT_NONE        = 3'b000;
            localparam logic [2:0] SHIFT_RIGHT_LOGIC = 3'b001;
            localparam logic [2:0] SHIFT_LEFT_LOGIC  = 3'b100;
        
            // =========================================================================
            // Stage A: Unpack + Special Cases + Exponent Compare + Swap
            // =========================================================================
        
            // Unpack operand A
%000000     wire        w_sign_a = i_a[15];
%000000     wire [7:0]  w_exp_a  = i_a[14:7];
%000000     wire [6:0]  w_mant_a = i_a[6:0];
        
            // Unpack operand B
%000001     wire        w_sign_b = i_b[15];
%000001     wire [7:0]  w_exp_b  = i_b[14:7];
%000000     wire [6:0]  w_mant_b = i_b[6:0];
        
            // Special case detection
%000000     wire w_a_is_zero     = (w_exp_a == 8'h00) && (w_mant_a == 7'h00);
%000000     wire w_b_is_zero     = (w_exp_b == 8'h00) && (w_mant_b == 7'h00);
%000000     wire w_a_is_subnorm  = (w_exp_a == 8'h00) && (w_mant_a != 7'h00);
%000000     wire w_b_is_subnorm  = (w_exp_b == 8'h00) && (w_mant_b != 7'h00);
%000000     wire w_a_is_inf      = (w_exp_a == 8'hFF) && (w_mant_a == 7'h00);
%000000     wire w_b_is_inf      = (w_exp_b == 8'hFF) && (w_mant_b == 7'h00);
%000000     wire w_a_is_nan      = (w_exp_a == 8'hFF) && (w_mant_a != 7'h00);
%000002     wire w_b_is_nan      = (w_exp_b == 8'hFF) && (w_mant_b != 7'h00);
        
            // Effective zero (FTZ mode: subnormals treated as zero)
%000000     wire w_a_eff_zero    = w_a_is_zero || w_a_is_subnorm;
%000000     wire w_b_eff_zero    = w_b_is_zero || w_b_is_subnorm;
        
            // Normal number detection (has implied leading 1)
%000001     wire w_a_is_normal   = ~w_a_eff_zero && ~w_a_is_inf && ~w_a_is_nan;
%000001     wire w_b_is_normal   = ~w_b_eff_zero && ~w_b_is_inf && ~w_b_is_nan;
        
            // Special case flags
%000002     wire w_any_nan       = w_a_is_nan || w_b_is_nan;
%000000     wire w_inf_minus_inf = w_a_is_inf && w_b_is_inf && (w_sign_a != w_sign_b);
%000000     wire w_any_inf       = w_a_is_inf || w_b_is_inf;
        
            // Exponent comparison: determine which operand has larger magnitude
            // If exponents equal, compare mantissas
%000000     wire [8:0]  w_exp_diff_raw = {1'b0, w_exp_a} - {1'b0, w_exp_b};
%000001     wire        w_exp_a_larger = ~w_exp_diff_raw[8];  // A >= B if no borrow
%000000     wire        w_exp_equal    = (w_exp_a == w_exp_b);
%000002     wire        w_mant_a_larger = (w_mant_a >= w_mant_b);
%000001     wire        w_a_larger     = w_exp_a_larger && (~w_exp_equal || w_mant_a_larger);
        
            // Absolute exponent difference (for shift amount)
%000000     wire [7:0]  w_exp_diff     = w_a_larger ? (w_exp_a - w_exp_b) : (w_exp_b - w_exp_a);
        
            // Swap operands so larger magnitude is always "operand L" (large)
            // and smaller magnitude is "operand S" (small, to be shifted)
%000002     wire        w_sign_l       = w_a_larger ? w_sign_a : w_sign_b;
%000001     wire        w_sign_s       = w_a_larger ? w_sign_b : w_sign_a;
%000001     wire [7:0]  w_exp_l        = w_a_larger ? w_exp_a  : w_exp_b;
%000000     wire [6:0]  w_mant_l       = w_a_larger ? w_mant_a : w_mant_b;
%000000     wire [6:0]  w_mant_s       = w_a_larger ? w_mant_b : w_mant_a;
%000001     wire        w_l_is_normal  = w_a_larger ? w_a_is_normal : w_b_is_normal;
%000001     wire        w_s_is_normal  = w_a_larger ? w_b_is_normal : w_a_is_normal;
%000000     wire        w_s_eff_zero   = w_a_larger ? w_b_eff_zero  : w_a_eff_zero;
        
            // Effective operation: add or subtract based on signs
%000001     wire        w_eff_sub      = w_sign_l ^ w_sign_s;
        
            // Result sign is sign of larger magnitude operand
%000002     wire        w_result_sign  = w_sign_l;
        
            // =========================================================================
            // Pipeline Stage 1 (optional)
            // =========================================================================
        
            // Signals to be registered
%000001     logic        r1_valid;
%000000     logic        r1_any_nan, r1_inf_minus_inf, r1_any_inf;
%000000     logic        r1_a_is_inf, r1_b_is_inf, r1_a_eff_zero, r1_b_eff_zero;
%000000     logic        r1_sign_a, r1_sign_b, r1_result_sign, r1_eff_sub;
%000000     logic [7:0]  r1_exp_l, r1_exp_diff;
%000000     logic [6:0]  r1_mant_l, r1_mant_s;
%000000     logic        r1_l_is_normal, r1_s_is_normal, r1_s_eff_zero;
        
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
                            r1_mant_l       <= 7'h0;
                            r1_mant_s       <= 7'h0;
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
%000001             always_comb begin
%000001                 r1_valid        = i_valid;
%000001                 r1_any_nan      = w_any_nan;
%000001                 r1_inf_minus_inf = w_inf_minus_inf;
%000001                 r1_any_inf      = w_any_inf;
%000001                 r1_a_is_inf     = w_a_is_inf;
%000001                 r1_b_is_inf     = w_b_is_inf;
%000001                 r1_a_eff_zero   = w_a_eff_zero;
%000001                 r1_b_eff_zero   = w_b_eff_zero;
%000001                 r1_sign_a       = w_sign_a;
%000001                 r1_sign_b       = w_sign_b;
%000001                 r1_result_sign  = w_result_sign;
%000001                 r1_eff_sub      = w_eff_sub;
%000001                 r1_exp_l        = w_exp_l;
%000001                 r1_exp_diff     = w_exp_diff;
%000001                 r1_mant_l       = w_mant_l;
%000001                 r1_mant_s       = w_mant_s;
%000001                 r1_l_is_normal  = w_l_is_normal;
%000001                 r1_s_is_normal  = w_s_is_normal;
%000001                 r1_s_eff_zero   = w_s_eff_zero;
                    end
                end
            endgenerate
        
            // =========================================================================
            // Stage B: Mantissa Alignment
            // =========================================================================
        
            // Extend mantissas with implied bit and guard bits
            // Format: {implied_1, mant[6:0], guard, round, sticky_placeholder}
            // = 11 bits total for alignment, sticky computed separately
%000000     wire [10:0] w_mant_l_ext = {r1_l_is_normal, r1_mant_l, 3'b000};
%000000     wire [10:0] w_mant_s_ext = {r1_s_is_normal, r1_mant_s, 3'b000};
        
            // Alignment: right-shift smaller mantissa by exponent difference
            // Use shifter_barrel in logical right shift mode
%000000     wire [10:0] w_mant_s_aligned;
%000000     wire [$clog2(EXT_MANT_WIDTH):0] w_shift_amt;
        
            // Clamp shift amount to mantissa width (shifts beyond this produce zero + sticky)
            assign w_shift_amt = (r1_exp_diff > EXT_MANT_WIDTH) ? 
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
            // Create mask of bits that will be shifted out, then OR with original
%000001     logic [10:0] w_sticky_mask;
%000002     logic        w_sticky_from_shift;
        
 000061     always_comb begin
                // All bits below shift position get shifted out
 000012         if (r1_exp_diff >= EXT_MANT_WIDTH) begin
                    // Everything shifted out
 000012             w_sticky_mask = 11'h7FF;
 000049         end else begin
 000049             w_sticky_mask = (11'h001 << r1_exp_diff) - 11'h001;
                end
 000061         w_sticky_from_shift = |(w_mant_s_ext & w_sticky_mask);
            end
        
            // If smaller operand is effectively zero, aligned mantissa is zero
%000000     wire [10:0] w_mant_s_final = r1_s_eff_zero ? 11'h000 : w_mant_s_aligned;
%000002     wire        w_sticky_s     = r1_s_eff_zero ? 1'b0 : w_sticky_from_shift;
        
            // =========================================================================
            // Pipeline Stage 2 (optional)
            // =========================================================================
        
%000001     logic        r2_valid;
%000000     logic        r2_any_nan, r2_inf_minus_inf, r2_any_inf;
%000000     logic        r2_a_is_inf, r2_b_is_inf, r2_a_eff_zero, r2_b_eff_zero;
%000000     logic        r2_sign_a, r2_sign_b, r2_result_sign, r2_eff_sub;
%000001     logic [7:0]  r2_exp_l;
%000000     logic [10:0] r2_mant_l_ext, r2_mant_s_aligned;
%000002     logic        r2_sticky_s;
        
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
                            r2_mant_l_ext     <= 11'h0;
                            r2_mant_s_aligned <= 11'h0;
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
%000001             always_comb begin
%000001                 r2_valid          = r1_valid;
%000001                 r2_any_nan        = r1_any_nan;
%000001                 r2_inf_minus_inf  = r1_inf_minus_inf;
%000001                 r2_any_inf        = r1_any_inf;
%000001                 r2_a_is_inf       = r1_a_is_inf;
%000001                 r2_b_is_inf       = r1_b_is_inf;
%000001                 r2_a_eff_zero     = r1_a_eff_zero;
%000001                 r2_b_eff_zero     = r1_b_eff_zero;
%000001                 r2_sign_a         = r1_sign_a;
%000001                 r2_sign_b         = r1_sign_b;
%000001                 r2_result_sign    = r1_result_sign;
%000001                 r2_eff_sub        = r1_eff_sub;
%000001                 r2_exp_l          = r1_exp_l;
%000001                 r2_mant_l_ext     = w_mant_l_ext;
%000001                 r2_mant_s_aligned = w_mant_s_final;
%000001                 r2_sticky_s       = w_sticky_s;
                    end
                end
            endgenerate
        
            // =========================================================================
            // Stage C: Mantissa Add/Subtract
            // =========================================================================
        
            // Perform addition or subtraction based on effective operation
            // Result needs extra bit for potential overflow (addition case)
%000000     logic [11:0] w_mant_sum;
%000000     logic        w_mant_sum_sign;  // For subtraction result sign correction
        
 000061     always_comb begin
%000000         if (r2_eff_sub) begin
                    // Effective subtraction: L - S (L is always larger magnitude)
 000061             w_mant_sum = {1'b0, r2_mant_l_ext} - {1'b0, r2_mant_s_aligned};
                    // Since L >= S, result should always be positive
 000061             w_mant_sum_sign = 1'b0;
%000000         end else begin
                    // Effective addition: L + S
%000000             w_mant_sum = {1'b0, r2_mant_l_ext} + {1'b0, r2_mant_s_aligned};
%000000             w_mant_sum_sign = 1'b0;
                end
            end
        
            // Detect addition overflow (sum >= 2.0, MSB set)
%000000     wire w_add_overflow = w_mant_sum[11];
        
            // Detect if result is zero (for sign handling)
%000000     wire w_sum_is_zero = (w_mant_sum == 12'h000) && ~r2_sticky_s;
        
            // =========================================================================
            // Pipeline Stage 3 (optional)
            // =========================================================================
        
%000001     logic        r3_valid;
%000000     logic        r3_any_nan, r3_inf_minus_inf, r3_any_inf;
%000000     logic        r3_a_is_inf, r3_b_is_inf, r3_a_eff_zero, r3_b_eff_zero;
%000000     logic        r3_sign_a, r3_sign_b, r3_result_sign, r3_eff_sub;
%000001     logic [7:0]  r3_exp_l;
%000000     logic [11:0] r3_mant_sum;
%000000     logic        r3_add_overflow, r3_sum_is_zero;
%000002     logic        r3_sticky_s;
        
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
                            r3_mant_sum      <= 12'h0;
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
%000001             always_comb begin
%000001                 r3_valid         = r2_valid;
%000001                 r3_any_nan       = r2_any_nan;
%000001                 r3_inf_minus_inf = r2_inf_minus_inf;
%000001                 r3_any_inf       = r2_any_inf;
%000001                 r3_a_is_inf      = r2_a_is_inf;
%000001                 r3_b_is_inf      = r2_b_is_inf;
%000001                 r3_a_eff_zero    = r2_a_eff_zero;
%000001                 r3_b_eff_zero    = r2_b_eff_zero;
%000001                 r3_sign_a        = r2_sign_a;
%000001                 r3_sign_b        = r2_sign_b;
%000001                 r3_result_sign   = r2_result_sign;
%000001                 r3_eff_sub       = r2_eff_sub;
%000001                 r3_exp_l         = r2_exp_l;
%000001                 r3_mant_sum      = w_mant_sum;
%000001                 r3_add_overflow  = w_add_overflow;
%000001                 r3_sum_is_zero   = w_sum_is_zero;
%000001                 r3_sticky_s      = r2_sticky_s;
                    end
                end
            endgenerate
        
            // =========================================================================
            // Stage D: Normalization (LZD + Shift)
            // =========================================================================
        
            // For addition overflow: right shift by 1, increment exponent
            // For subtraction: may need left shift, decrement exponent
        
            // Leading zero count for normalization (subtraction case)
            // Reverse bits because count_leading_zeros scans from bit[0]
%000000     wire [11:0] w_mant_for_clz;
%000000     wire [CLZ_WIDTH-1:0] w_lzc;
        
            // Bit reversal for CLZ module
            genvar gi;
            generate
                for (gi = 0; gi < 12; gi++) begin : gen_bit_reverse
                    assign w_mant_for_clz[gi] = r3_mant_sum[11-gi];
                end
            endgenerate
        
            count_leading_zeros #(
                .WIDTH(12),
                .INSTANCE_NAME("BF16_ADD_CLZ")
            ) u_clz (
                .data(w_mant_for_clz),
                .clz (w_lzc)
            );
        
            // Determine normalization shift amount and direction
            // After add/sub, mantissa is in format: x.xxxxxxxxxx (12 bits)
            // Normalized form should have implied 1 at bit[10] of 11-bit mantissa
            //
            // Addition overflow (bit[11]=1): right shift 1, exp++
            // Normal (bit[10]=1): no shift needed
            // Subnormal result (bit[10]=0): left shift by LZC-1, exp -= (LZC-1)
        
%000000     logic [3:0]  w_norm_shift_amt;
%000000     logic        w_norm_shift_right;
%000000     logic [10:0] w_mant_prenorm;
%000002     logic        w_norm_sticky;
        
 000061     always_comb begin
%000000         if (r3_add_overflow) begin
                    // Addition overflow: extract bits [11:1] which is already right-shifted
                    // No further shift needed (shift_amt=0), just pass through shifter
%000000             w_norm_shift_right = 1'b0;  // Direction doesn't matter when shift_amt=0
%000000             w_norm_shift_amt   = 4'd0;  // No shift - [11:1] extraction already did it
%000000             w_mant_prenorm     = r3_mant_sum[11:1];  // Upper 11 bits (already shifted)
%000000             w_norm_sticky      = r3_mant_sum[0] | r3_sticky_s;
%000000         end else if (w_lzc == 0) begin
                    // Already normalized (implied 1 at correct position)
%000000             w_norm_shift_right = 1'b0;
%000000             w_norm_shift_amt   = 4'd0;
%000000             w_mant_prenorm     = r3_mant_sum[10:0];
%000000             w_norm_sticky      = r3_sticky_s;
 000061         end else begin
                    // Need left shift to normalize
 000061             w_norm_shift_right = 1'b0;
                    // LZC counts leading zeros; we need to shift left by (LZC - 1)
                    // because bit[11] being 0 means we count from bit[10]
                    // Actually, with 12-bit mant_sum and implied 1 target at bit[10]:
                    // If LZC=1, bit[10]=1, no shift needed
                    // If LZC=2, bit[9]=1, shift left by 1
                    // So shift amount = LZC - 1 (but LZC=0 handled above)
 000061             w_norm_shift_amt   = (w_lzc > 1) ? (w_lzc[3:0] - 4'd1) : 4'd0;
 000061             w_mant_prenorm     = r3_mant_sum[10:0];
 000061             w_norm_sticky      = r3_sticky_s;
                end
            end
        
            // Apply normalization shift using shifter_barrel
%000000     wire [10:0] w_mant_normalized;
%000000     wire [$clog2(EXT_MANT_WIDTH):0] w_norm_shift_amt_ext;
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
            // Addition overflow: exp + 1
            // Subtraction normalization: exp - shift_amt
%000000     logic [8:0] w_exp_adjusted;
        
 000061     always_comb begin
%000000         if (r3_add_overflow) begin
%000000             w_exp_adjusted = {1'b0, r3_exp_l} + 9'd1;
%000000         end else if (w_norm_shift_amt > 0) begin
 000061             w_exp_adjusted = {1'b0, r3_exp_l} - {5'b0, w_norm_shift_amt};
%000000         end else begin
%000000             w_exp_adjusted = {1'b0, r3_exp_l};
                end
            end
        
            // Overflow/underflow detection
%000000     wire w_exp_overflow  = w_exp_adjusted[8] || (w_exp_adjusted[7:0] >= 8'hFF);
%000000     wire w_exp_underflow = w_exp_adjusted[8] || (w_exp_adjusted[7:0] == 8'h00);
        
            // =========================================================================
            // Pipeline Stage 4 (optional)
            // =========================================================================
        
%000001     logic        r4_valid;
%000000     logic        r4_any_nan, r4_inf_minus_inf, r4_any_inf;
%000000     logic        r4_a_is_inf, r4_b_is_inf, r4_a_eff_zero, r4_b_eff_zero;
%000000     logic        r4_sign_a, r4_sign_b, r4_result_sign;
%000001     logic [7:0]  r4_exp_adjusted;
%000000     logic [10:0] r4_mant_normalized;
%000000     logic        r4_exp_overflow, r4_exp_underflow;
%000000     logic        r4_sum_is_zero, r4_norm_sticky;
        
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
                            r4_mant_normalized <= 11'h0;
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
%000001             always_comb begin
%000001                 r4_valid           = r3_valid;
%000001                 r4_any_nan         = r3_any_nan;
%000001                 r4_inf_minus_inf   = r3_inf_minus_inf;
%000001                 r4_any_inf         = r3_any_inf;
%000001                 r4_a_is_inf        = r3_a_is_inf;
%000001                 r4_b_is_inf        = r3_b_is_inf;
%000001                 r4_a_eff_zero      = r3_a_eff_zero;
%000001                 r4_b_eff_zero      = r3_b_eff_zero;
%000001                 r4_sign_a          = r3_sign_a;
%000001                 r4_sign_b          = r3_sign_b;
%000001                 r4_result_sign     = r3_result_sign;
%000001                 r4_exp_adjusted    = w_exp_adjusted[7:0];
%000001                 r4_mant_normalized = w_mant_normalized;
%000001                 r4_exp_overflow    = w_exp_overflow;
%000001                 r4_exp_underflow   = w_exp_underflow;
%000001                 r4_sum_is_zero     = r3_sum_is_zero;
%000001                 r4_norm_sticky     = w_norm_sticky;
                    end
                end
            endgenerate
        
            // =========================================================================
            // Stage E: Rounding + Result Assembly
            // =========================================================================
        
            // Extract mantissa bits and rounding bits from normalized mantissa
            // Format: {implied_1, mant[6:0], guard, round, sticky}
            //          [10]       [9:3]      [2]    [1]    [0]
%000000     wire [6:0] w_mant_final_raw = r4_mant_normalized[9:3];
%000000     wire       w_guard_bit      = r4_mant_normalized[2];
%000000     wire       w_round_bit      = r4_mant_normalized[1];
%000002     wire       w_sticky_bit     = r4_mant_normalized[0] | r4_norm_sticky;
        
            // Round-to-Nearest-Even (RNE)
            // Round up if: guard && (round || sticky || LSB)
%000000     wire w_round_up = w_guard_bit && (w_round_bit || w_sticky_bit || w_mant_final_raw[0]);
        
            // Apply rounding
%000000     wire [7:0] w_mant_rounded = {1'b0, w_mant_final_raw} + {7'b0, w_round_up};
        
            // Check for mantissa overflow from rounding (0x7F + 1 = 0x80)
%000000     wire w_round_overflow = w_mant_rounded[7];
        
            // Final mantissa (handle rounding overflow)
%000000     wire [6:0] w_mant_out = w_round_overflow ? 7'h00 : w_mant_rounded[6:0];
        
            // Final exponent (handle rounding overflow)
%000000     wire [8:0] w_exp_out_raw = {1'b0, r4_exp_adjusted} + {8'b0, w_round_overflow};
%000001     wire [7:0] w_exp_out     = w_exp_out_raw[7:0];
        
            // Final overflow check (including rounding overflow)
%000000     wire w_final_overflow = r4_exp_overflow || (w_exp_out_raw >= 9'h0FF);
        
            // Sign of zero: per IEEE 754, x - x = +0 in RNE mode
%000002     wire w_final_sign = r4_sum_is_zero ? 1'b0 : r4_result_sign;
        
            // =========================================================================
            // Special Case Result Selection
            // =========================================================================
        
 000061     always_comb begin
                // Default: normal result
 000061         ow_result    = {w_final_sign, w_exp_out, w_mant_out};
 000061         ow_overflow  = 1'b0;
 000061         ow_underflow = 1'b0;
 000061         ow_invalid   = 1'b0;
        
                // Priority order (highest to lowest)
 000012         if (r4_any_nan || r4_inf_minus_inf) begin
                    // NaN result (input NaN or inf - inf)
 000012             ow_result  = {1'b0, 8'hFF, 7'h40};  // Canonical quiet NaN
 000012             ow_invalid = r4_inf_minus_inf;
%000000         end else if (r4_any_inf) begin
                    // Infinity result (one input is inf, not inf-inf case)
                    // Result sign is sign of the infinity input
%000000             ow_result = {r4_a_is_inf ? r4_sign_a : r4_sign_b, 8'hFF, 7'h00};
%000000         end else if (r4_a_eff_zero && r4_b_eff_zero) begin
                    // Both inputs zero: result is zero
                    // Sign: -0 + -0 = -0, otherwise +0
%000000             ow_result = {r4_sign_a & r4_sign_b, 8'h00, 7'h00};
%000000         end else if (r4_a_eff_zero) begin
                    // A is zero: result is B (already handled via swap, but explicit for clarity)
                    // This case shouldn't normally hit due to swap logic
%000000             ow_result = {r4_sign_b, r4_exp_adjusted, w_mant_out};
%000000         end else if (r4_b_eff_zero) begin
                    // B is zero: result is A
%000000             ow_result = {r4_sign_a, r4_exp_adjusted, w_mant_out};
%000000         end else if (r4_sum_is_zero) begin
                    // Exact zero from subtraction
%000000             ow_result = {1'b0, 8'h00, 7'h00};  // +0 per IEEE 754 RNE
%000000         end else if (w_final_overflow) begin
                    // Overflow to infinity
%000000             ow_result   = {w_final_sign, 8'hFF, 7'h00};
%000000             ow_overflow = 1'b1;
%000000         end else if (r4_exp_underflow) begin
                    // Underflow to zero (FTZ mode)
%000000             ow_result    = {w_final_sign, 8'h00, 7'h00};
%000000             ow_underflow = 1'b1;
                end
                // else: normal result (default assignment above)
            end
        
            // Output valid follows pipeline
            assign ow_valid = r4_valid;
        
        endmodule : math_bf16_adder
        
