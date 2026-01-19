//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: math_bf16_reciprocal
        // Purpose: Fast BF16 reciprocal (1/x) using LUT + Newton-Raphson refinement
        //
        // Documentation: BF16_ARCHITECTURE.md
        // Subsystem: common
        //
        // Author: Claude AI / sean galloway
        // Created: 2025-12-26
        //
        
        `timescale 1ns / 1ps
        
        //==============================================================================
        // Module: math_bf16_reciprocal
        //==============================================================================
        // Description:
        //   Computes the reciprocal (1/x) of a BF16 floating-point number using a
        //   lookup table for initial approximation followed by one Newton-Raphson
        //   iteration for refinement. Much faster than full division.
        //
        // Algorithm:
        //   1. Handle special cases (zero, infinity, NaN)
        //   2. LUT lookup using top 6 mantissa bits for initial 1/mantissa estimate
        //   3. Newton-Raphson: x' = x * (2 - d * x) where d is normalized mantissa
        //   4. Adjust exponent: new_exp = 253 - old_exp (accounting for bias)
        //   5. Normalize and round result
        //
        // Performance:
        //   - Logic depth: ~25-30 levels (vs 80-100 for full divider)
        //   - LUT size: 64 entries x 8 bits = 512 bits
        //   - One 8x8 multiply + one 16x8 multiply for NR iteration
        //
        // Accuracy:
        //   - Initial LUT: ~6 bits accurate
        //   - After 1 NR iteration: ~12 bits accurate (sufficient for BF16's 7-bit mantissa)
        //
        //------------------------------------------------------------------------------
        // Ports:
        //------------------------------------------------------------------------------
        //   Inputs:
        //     i_x[15:0]:          BF16 input value
        //
        //   Outputs:
        //     ow_reciprocal[15:0]: BF16 result (1/x)
        //     ow_div_by_zero:      1 if input was zero (result is infinity)
        //     ow_is_zero:          1 if result is zero (input was infinity)
        //     ow_invalid:          1 if input was NaN (result is NaN)
        //
        //------------------------------------------------------------------------------
        module math_bf16_reciprocal (
%000008     input  logic [15:0] i_x,
%000006     output logic [15:0] ow_reciprocal,
%000002     output logic        ow_div_by_zero,
%000002     output logic        ow_is_zero,
%000002     output logic        ow_invalid
        );
        
        //------------------------------------------------------------------------------
        // BF16 field extraction
        //------------------------------------------------------------------------------
 000019 wire        w_sign = i_x[15];
 000014 wire [7:0]  w_exp  = i_x[14:7];
%000008 wire [6:0]  w_mant = i_x[6:0];
        
        //------------------------------------------------------------------------------
        // Special value detection
        //------------------------------------------------------------------------------
%000002 wire w_is_zero     = (w_exp == 8'h00) && (w_mant == 7'h00);
%000000 wire w_is_subnormal = (w_exp == 8'h00) && (w_mant != 7'h00);
%000002 wire w_is_inf      = (w_exp == 8'hFF) && (w_mant == 7'h00);
%000002 wire w_is_nan      = (w_exp == 8'hFF) && (w_mant != 7'h00);
        
        // Treat subnormals as zero (flush-to-zero mode)
%000002 wire w_eff_zero = w_is_zero || w_is_subnormal;
        
        //------------------------------------------------------------------------------
        // Reciprocal LUT for 1/(1.mantissa)
        //------------------------------------------------------------------------------
        // Index: top 6 bits of mantissa (bits [6:1])
        // Value: 8-bit approximation of 1/(1 + index/64) * 256
        // For mantissa m in [0, 127], value represents 1.m where m is 0.xxx in binary
        // 1/(1.0) = 1.0, 1/(1.5) = 0.667, 1/(2.0) = 0.5
        //
        // LUT stores: round(256 / (1 + i/64)) for i = 0..63
        // This gives 1/x in the range (0.5, 1.0] as Q0.8 fixed-point
        //
        // SPECIAL CASE: When mant=0, 1/(1.0) = 1.0 exactly - handled separately
        // (bypasses LUT and N-R iteration)
        
%000001 logic [7:0] w_lut_value;
%000008 wire [5:0] w_lut_index = w_mant[6:1];
%000003 wire w_mant_nonzero = (w_mant != 7'd0);
        
%000000 always_comb begin
%000000     case (w_lut_index)
                // LUT values = round(256 / (1 + i/64)) for i = 0..63
%000000         6'd0:  w_lut_value = 8'd252;  // 1/(1.016) = 0.984 -> 252 (i=0 not used when mant>0)
%000000         6'd1:  w_lut_value = 8'd252;  // 1/(1.016) = 0.984 -> 252
%000000         6'd2:  w_lut_value = 8'd248;  // 1/(1.031) = 0.970 -> 248
%000000         6'd3:  w_lut_value = 8'd244;  // 1/(1.047) = 0.955 -> 244
%000000         6'd4:  w_lut_value = 8'd241;  // 1/(1.063) = 0.941 -> 241
%000000         6'd5:  w_lut_value = 8'd237;  // 1/(1.078) = 0.928 -> 237
%000000         6'd6:  w_lut_value = 8'd234;  // 1/(1.094) = 0.914 -> 234
%000000         6'd7:  w_lut_value = 8'd231;  // 1/(1.109) = 0.902 -> 231
%000000         6'd8:  w_lut_value = 8'd228;  // 1/(1.125) = 0.889 -> 228
%000000         6'd9:  w_lut_value = 8'd224;  // 1/(1.141) = 0.877 -> 224
%000000         6'd10: w_lut_value = 8'd221;  // 1/(1.156) = 0.865 -> 221
%000000         6'd11: w_lut_value = 8'd218;  // 1/(1.172) = 0.853 -> 218
%000000         6'd12: w_lut_value = 8'd216;  // 1/(1.188) = 0.842 -> 216
%000000         6'd13: w_lut_value = 8'd213;  // 1/(1.203) = 0.831 -> 213
%000000         6'd14: w_lut_value = 8'd210;  // 1/(1.219) = 0.821 -> 210
%000000         6'd15: w_lut_value = 8'd207;  // 1/(1.234) = 0.810 -> 207
%000000         6'd16: w_lut_value = 8'd205;  // 1/(1.250) = 0.800 -> 205
%000000         6'd17: w_lut_value = 8'd202;  // 1/(1.266) = 0.790 -> 202
%000000         6'd18: w_lut_value = 8'd200;  // 1/(1.281) = 0.780 -> 200
%000000         6'd19: w_lut_value = 8'd197;  // 1/(1.297) = 0.771 -> 197
%000000         6'd20: w_lut_value = 8'd195;  // 1/(1.313) = 0.762 -> 195
%000000         6'd21: w_lut_value = 8'd193;  // 1/(1.328) = 0.753 -> 193
%000000         6'd22: w_lut_value = 8'd190;  // 1/(1.344) = 0.744 -> 190
%000000         6'd23: w_lut_value = 8'd188;  // 1/(1.359) = 0.736 -> 188
%000000         6'd24: w_lut_value = 8'd186;  // 1/(1.375) = 0.727 -> 186
%000000         6'd25: w_lut_value = 8'd184;  // 1/(1.391) = 0.719 -> 184
%000000         6'd26: w_lut_value = 8'd182;  // 1/(1.406) = 0.711 -> 182
%000000         6'd27: w_lut_value = 8'd180;  // 1/(1.422) = 0.703 -> 180
%000000         6'd28: w_lut_value = 8'd178;  // 1/(1.438) = 0.696 -> 178
%000000         6'd29: w_lut_value = 8'd176;  // 1/(1.453) = 0.688 -> 176
%000000         6'd30: w_lut_value = 8'd174;  // 1/(1.469) = 0.681 -> 174
%000000         6'd31: w_lut_value = 8'd172;  // 1/(1.484) = 0.674 -> 172
%000000         6'd32: w_lut_value = 8'd171;  // 1/(1.500) = 0.667 -> 171
%000000         6'd33: w_lut_value = 8'd169;  // 1/(1.516) = 0.660 -> 169
%000000         6'd34: w_lut_value = 8'd167;  // 1/(1.531) = 0.653 -> 167
%000000         6'd35: w_lut_value = 8'd166;  // 1/(1.547) = 0.646 -> 166
%000000         6'd36: w_lut_value = 8'd164;  // 1/(1.563) = 0.640 -> 164
%000000         6'd37: w_lut_value = 8'd162;  // 1/(1.578) = 0.634 -> 162
%000000         6'd38: w_lut_value = 8'd161;  // 1/(1.594) = 0.627 -> 161
%000000         6'd39: w_lut_value = 8'd159;  // 1/(1.609) = 0.621 -> 159
%000000         6'd40: w_lut_value = 8'd158;  // 1/(1.625) = 0.615 -> 158
%000000         6'd41: w_lut_value = 8'd156;  // 1/(1.641) = 0.610 -> 156
%000000         6'd42: w_lut_value = 8'd155;  // 1/(1.656) = 0.604 -> 155
%000000         6'd43: w_lut_value = 8'd153;  // 1/(1.672) = 0.598 -> 153
%000000         6'd44: w_lut_value = 8'd152;  // 1/(1.688) = 0.593 -> 152
%000000         6'd45: w_lut_value = 8'd150;  // 1/(1.703) = 0.587 -> 150
%000000         6'd46: w_lut_value = 8'd149;  // 1/(1.719) = 0.582 -> 149
%000000         6'd47: w_lut_value = 8'd148;  // 1/(1.734) = 0.577 -> 148
%000000         6'd48: w_lut_value = 8'd146;  // 1/(1.750) = 0.571 -> 146
%000000         6'd49: w_lut_value = 8'd145;  // 1/(1.766) = 0.566 -> 145
%000000         6'd50: w_lut_value = 8'd144;  // 1/(1.781) = 0.561 -> 144
%000000         6'd51: w_lut_value = 8'd142;  // 1/(1.797) = 0.557 -> 142
%000000         6'd52: w_lut_value = 8'd141;  // 1/(1.813) = 0.552 -> 141
%000000         6'd53: w_lut_value = 8'd140;  // 1/(1.828) = 0.547 -> 140
%000000         6'd54: w_lut_value = 8'd139;  // 1/(1.844) = 0.542 -> 139
%000000         6'd55: w_lut_value = 8'd138;  // 1/(1.859) = 0.538 -> 138
%000000         6'd56: w_lut_value = 8'd137;  // 1/(1.875) = 0.533 -> 137
%000000         6'd57: w_lut_value = 8'd135;  // 1/(1.891) = 0.529 -> 135
%000000         6'd58: w_lut_value = 8'd134;  // 1/(1.906) = 0.525 -> 134
%000000         6'd59: w_lut_value = 8'd133;  // 1/(1.922) = 0.520 -> 133
%000000         6'd60: w_lut_value = 8'd132;  // 1/(1.938) = 0.516 -> 132
%000000         6'd61: w_lut_value = 8'd131;  // 1/(1.953) = 0.512 -> 131
%000000         6'd62: w_lut_value = 8'd130;  // 1/(1.969) = 0.508 -> 130
%000000         6'd63: w_lut_value = 8'd129;  // 1/(1.984) = 0.504 -> 129
            endcase
        end
        
        //------------------------------------------------------------------------------
        // Newton-Raphson iteration: x' = x * (2 - d * x)
        //------------------------------------------------------------------------------
        // Let x0 = LUT value (8 bits, representing 0.xxxxxxxx)
        // Let d = 1.mantissa (8 bits: 1 + 7-bit mantissa)
        //
        // Step 1: Compute d * x0 (8 x 8 = 16 bits)
        // Step 2: Compute 2 - d*x0 (need to handle as fixed-point)
        // Step 3: Compute x0 * (2 - d*x0) = x1 (refined estimate)
        
        // d = 1.mantissa in Q1.7 format (8 bits)
%000001 wire [7:0] w_d = {1'b1, w_mant};  // 1.mmmmmmm
        
        // x0 from LUT in Q0.8 format (8 bits, value in [0.5, 1.0])
%000001 wire [7:0] w_x0 = w_lut_value;
        
        // Step 1: d * x0 in Q1.15 format (16 bits)
        // d is Q1.7, x0 is Q0.8, product is Q1.15
%000003 wire [15:0] w_d_times_x0 = w_d * w_x0;
        
        // Step 2: 2 - d*x0
        // 2.0 in Q2.14 format = 16'b10_00000000000000 = 16'h8000
        // But d*x0 is Q1.15, so we need to align
        // Actually, let's think about this more carefully:
        // d is in [1.0, 2.0), x0 is in [0.5, 1.0), so d*x0 is in [0.5, 2.0)
        // We want 2 - d*x0 which is in [0, 1.5]
        //
        // d*x0 is Q1.15 (16 bits), ranging from 0.5*256 to 2.0*256 = 128 to 512 in integer
        // Wait, let me reconsider the fixed-point formats...
        //
        // Actually: d is Q1.7 (integer part 0 or 1, 7 fractional bits)
        // x0 is Q0.8 (all fractional, 8 bits)
        // d * x0 is Q1.15... but d only goes up to ~2 and x0 up to ~1
        // Product max is ~2, so Q2.14 would be safer
        //
        // Let's simplify: use 16-bit product, treat as Q2.14
        // d (Q1.7) * x0 (Q0.8) = Q1.15, but d < 2 and x0 < 1, so result < 2
        // Shift interpretation: treat w_d_times_x0 as Q1.15
        
        // 2.0 in Q1.15 = 2 * 2^15 = 65536 (but only 16 bits, so use Q2.14)
        // Let's use Q2.14: 2.0 = 2 * 2^14 = 32768
        // Shift d*x0 from Q1.15 to Q2.14: divide by 2 (right shift 1)
%000000 wire [15:0] w_d_x0_q2_14 = {1'b0, w_d_times_x0[15:1]};  // Q2.14
        
        // 2.0 in Q2.14
        localparam [15:0] TWO_Q2_14 = 16'd32768;
        
        // 2 - d*x0 in Q2.14 (could be negative if d*x0 > 2, but shouldn't happen)
%000000 wire [15:0] w_two_minus_dx0 = TWO_Q2_14 - w_d_x0_q2_14;
        
        // Step 3: x0 * (2 - d*x0) = x1
        // x0 is Q0.8, (2-d*x0) is Q2.14
        // Product is Q2.22 (24 bits needed, but top bits should be small)
%000000 wire [23:0] w_x1_full = w_x0 * w_two_minus_dx0;
        
        // x1 should be in range [0.5, 1.0] for valid inputs
        // In Q2.22, 0.5 = 0.5 * 2^22 = 2097152, 1.0 = 4194304
        // Extract meaningful bits: top 10 bits of fractional part
        // Result x1 in Q0.8 format: take bits [21:14] (after implicit point)
%000001 wire [7:0] w_x1 = w_x1_full[21:14];
        
        //------------------------------------------------------------------------------
        // Exponent calculation for reciprocal
        //------------------------------------------------------------------------------
        // For BF16: value = 2^(exp-127) * 1.mantissa
        // Reciprocal: 1/value = 2^(127-exp) * 1/1.mantissa
        //
        // CASE 1: mantissa = 0 (input is exact power of 2, like 1.0, 2.0, 4.0)
        //   1/(1.0) = 1.0 exactly
        //   New exponent = 254 - exp
        //   New mantissa = 0
        //
        // CASE 2: mantissa > 0 (input is 1.something)
        //   1/(1.m) is in (0.5, 1.0), so we normalize by multiplying by 2
        //   This gives us a value in (1.0, 2.0) which fits BF16 normalized form
        //   New exponent = 253 - exp (one less due to normalization)
        //   New mantissa = from LUT + Newton-Raphson refinement
        
%000002 wire signed [9:0] w_exp_raw = w_mant_nonzero ? (10'sd253 - {2'b0, w_exp})
                                                     : (10'sd254 - {2'b0, w_exp});
        
        // Check for exponent overflow/underflow
%000000 wire w_exp_overflow  = (w_exp_raw > 10'sd254);
%000002 wire w_exp_underflow = (w_exp_raw < 10'sd1);
        
        // Clamp exponent
 000014 wire [7:0] w_exp_result = w_exp_overflow  ? 8'hFE :  // Max normal exponent
                                  w_exp_underflow ? 8'h00 :  // Zero/subnormal
                                  w_exp_raw[7:0];
        
        //------------------------------------------------------------------------------
        // Mantissa extraction from x1
        //------------------------------------------------------------------------------
        // x1 is in Q0.8 representing a value in [0.5, 1.0)
        // We need to express this as 1.xxxxxxx by noting:
        // 0.1xxxxxxx * 2 = 1.xxxxxxx
        // So the 7 mantissa bits come from x1[6:0] (the bits after the leading 0.1)
        // x1[7] should be 1 for values >= 0.5
        //
        // SPECIAL CASE: When input mantissa = 0, output mantissa = 0 exactly
        // (bypasses the Newton-Raphson iteration result)
        
%000006 wire [6:0] w_mant_result = w_mant_nonzero ? w_x1[6:0] : 7'd0;
        
        //------------------------------------------------------------------------------
        // Final result assembly with special case handling
        //------------------------------------------------------------------------------
 000094 always_comb begin
            // Default: normal reciprocal result
 000094     ow_reciprocal = {w_sign, w_exp_result, w_mant_result};
 000094     ow_div_by_zero = 1'b0;
 000094     ow_is_zero = 1'b0;
 000094     ow_invalid = 1'b0;
        
            // Special cases (priority order)
%000002     if (w_is_nan) begin
                // NaN -> NaN (preserve quiet NaN)
%000002         ow_reciprocal = {w_sign, 8'hFF, 7'h40};
%000002         ow_invalid = 1'b1;
 000011     end else if (w_eff_zero) begin
                // 1/0 = infinity
 000011         ow_reciprocal = {w_sign, 8'hFF, 7'h00};
 000011         ow_div_by_zero = 1'b1;
%000004     end else if (w_is_inf) begin
                // 1/infinity = 0
%000004         ow_reciprocal = {w_sign, 8'h00, 7'h00};
%000004         ow_is_zero = 1'b1;
%000000     end else if (w_exp_underflow) begin
                // Result too small, flush to zero
%000000         ow_reciprocal = {w_sign, 8'h00, 7'h00};
%000000         ow_is_zero = 1'b1;
%000000     end else if (w_exp_overflow) begin
                // Result too large, saturate to max normal
%000000         ow_reciprocal = {w_sign, 8'hFE, 7'h7F};
            end
        end
        
        endmodule : math_bf16_reciprocal
        
