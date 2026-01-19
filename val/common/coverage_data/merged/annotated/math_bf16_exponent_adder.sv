//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: math_bf16_exponent_adder
        // Purpose: BF16 exponent adder with bias handling and overflow/underflow detection
        //
        // Documentation: BF16_ARCHITECTURE.md
        // Subsystem: common
        //
        // Author: sean galloway
        // Created: 2025-11-25
        //
        // AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
        // Generator: bin/rtl_generators/bf16/bf16_exponent_adder.py
        // Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/bf16/generate_all.py rtl/common
        //
        
        `timescale 1ns / 1ps
        
        module math_bf16_exponent_adder(
 000011     input  logic [7:0] i_exp_a,
%000008     input  logic [7:0] i_exp_b,
%000000     input  logic       i_norm_adjust,
%000007     output logic [7:0] ow_exp_out,
%000000     output logic       ow_overflow,
%000000     output logic       ow_underflow,
%000004     output logic       ow_a_is_zero,
%000004     output logic       ow_b_is_zero,
%000004     output logic       ow_a_is_inf,
%000006     output logic       ow_b_is_inf,
%000004     output logic       ow_a_is_nan,
%000006     output logic       ow_b_is_nan
        );
        
        // Special case detection
        // exp = 0: Zero (if mantissa = 0) or subnormal
        // exp = 255: Inf (if mantissa = 0) or NaN (if mantissa != 0)
        
        assign ow_a_is_zero = (i_exp_a == 8'h00);  // Note: caller checks mantissa
        assign ow_b_is_zero = (i_exp_b == 8'h00);
        assign ow_a_is_inf  = (i_exp_a == 8'hFF);  // Caller checks mantissa for NaN
        assign ow_b_is_inf  = (i_exp_b == 8'hFF);
        assign ow_a_is_nan  = (i_exp_a == 8'hFF);  // Actual NaN needs mantissa != 0
        assign ow_b_is_nan  = (i_exp_b == 8'hFF);
        
        // Exponent addition with bias handling
        // result_exp = exp_a + exp_b - bias + norm_adjust
        // 
        // Use 10-bit intermediate to detect overflow/underflow
        // Bias = 127 (8'h7F)
        
        // Extended precision for overflow/underflow detection
%000004 wire [9:0] w_exp_sum_raw;
        
        // Calculate: exp_a + exp_b - bias + norm_adjust
        // Rearranged as: (exp_a + exp_b + norm_adjust) - 8'd127
        assign w_exp_sum_raw = {2'b0, i_exp_a} + {2'b0, i_exp_b} + 
                               {9'b0, i_norm_adjust} - 10'd127;
        
        // Underflow detection: result <= 0 (signed comparison)
        // If MSB of 10-bit result is set, it's negative (underflow)
        // Must check underflow BEFORE overflow since negative values appear large in unsigned
%000004 wire w_underflow_raw = w_exp_sum_raw[9] | (w_exp_sum_raw == 10'd0);
        
        // Overflow detection: result > 254 (255 reserved for inf/nan)
        // Only check overflow if not underflow (negative values wrap to large positive)
%000004 wire w_overflow_raw = ~w_underflow_raw & (w_exp_sum_raw > 10'd254);
        
        // Special cases override normal overflow/underflow
%000002 wire w_either_special = ow_a_is_inf | ow_b_is_inf | ow_a_is_zero | ow_b_is_zero;
        
        assign ow_overflow  = w_overflow_raw & ~w_either_special;
        assign ow_underflow = w_underflow_raw & ~w_either_special;
        
        // Result exponent with saturation
        // - Overflow: saturate to 255 (inf)
        // - Underflow: saturate to 0 (zero)
        // - Normal: use computed value
        
 000052 always_comb begin
%000000     if (ow_overflow) begin
%000000         ow_exp_out = 8'hFF;  // Infinity
%000000     end else if (ow_underflow) begin
%000000         ow_exp_out = 8'h00;  // Zero
 000052     end else begin
 000052         ow_exp_out = w_exp_sum_raw[7:0];
            end
        end
        
        endmodule
        
