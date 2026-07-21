// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_bf16_to_fp32
// Purpose: Convert BF16 to FP32 (upconvert)
//
// Documentation: IEEE754_ARCHITECTURE.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2026-01-03
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp_conversions.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/common
//

`timescale 1ns / 1ps

module math_bf16_to_fp32 (
    input  logic [15:0] i_a,
    output logic [31:0] ow_result,
    output logic                  ow_invalid
);

// BF16 field extraction
wire       w_sign = i_a[15];
wire [7:0] w_exp  = i_a[14:7];
wire [6:0] w_mant = i_a[6:0];

// Special case detection
wire w_is_zero = (w_exp == 8'h0) & (w_mant == 7'h0);
wire w_is_subnormal = (w_exp == 8'h0) & (w_mant != 7'h0);
wire w_is_inf = (w_exp == 8'hFF) & (w_mant == 7'h0);
wire w_is_nan = (w_exp == 8'hFF) & (w_mant != 7'h0);

// Exponent conversion: add bias difference
wire [7:0] w_exp_converted = w_exp + 8'd0;

// Mantissa extension: pad with zeros
wire [22:0] w_mant_extended = {w_mant, 16'b0};

// Result assembly
logic [31:0] r_result;
logic r_invalid;

always_comb begin
    r_result = {w_sign, w_exp_converted, w_mant_extended};
    r_invalid = 1'b0;

    if (w_is_nan) begin
        // Propagate as quiet NaN
        r_result = {w_sign, 8'hFF, 23'h400000};
        r_invalid = 1'b1;
    end else if (w_is_inf) begin
        r_result = {w_sign, 8'hFF, 23'h0};
    end else if (w_is_zero | w_is_subnormal) begin
        // Flush subnormals to zero
        r_result = {w_sign, 8'h0, 23'h0};
    end
end

assign ow_result = r_result;
assign ow_invalid = r_invalid;

endmodule

