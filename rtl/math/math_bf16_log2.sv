// =============================================================================
// Module: math_bf16_log2
// Description: BF16 base-2 logarithm using LUT approximation
//
// This module computes log2(x) for positive BF16 inputs.
//
// Algorithm:
//   For BF16 x = 2^(exp-127) * (1 + m/128):
//     log2(x) = (exp - 127) + log2(1 + m/128)
//
//   The integer part is simply (exp - 127), which can be negative.
//   The fractional part log2(1 + m/128) is in range [0, 1) and uses a LUT.
//
// Output Format:
//   Result is BF16 in range approximately [-126, +128] for normal inputs.
//   - log2(1.0) = 0
//   - log2(2.0) = 1
//   - log2(0.5) = -1
//   - log2(max_normal) ≈ 127.97
//   - log2(min_normal) ≈ -126
//
// Parameters:
//   LUT_DEPTH: Size of fractional part LUT (32, 64, or 128)
//
// Latency: Combinational
// Logic Levels: ~15-20
//
// Special Cases:
//   - Zero/subnormal input: Returns -infinity
//   - Infinity input: Returns +infinity
//   - NaN input: Returns NaN
//   - Negative input: Returns NaN (log of negative undefined)
//
// Copyright (c) 2025 Sean Galloway
// SPDX-License-Identifier: MIT
// =============================================================================

`timescale 1ns / 1ps

module math_bf16_log2 #(
    parameter int LUT_DEPTH = 32,
    parameter int LUT_ADDR_BITS = $clog2(LUT_DEPTH)
) (
    input  logic [15:0] i_bf16,           // Input BF16 (must be positive)
    output logic [15:0] ow_log2,          // log2(input) in BF16
    output logic        ow_is_zero,       // Input was zero (log = -inf)
    output logic        ow_is_inf,        // Input was infinity (log = +inf)
    output logic        ow_is_nan,        // Input was NaN or negative
    output logic        ow_is_neg         // Input was negative (undefined)
);

    // =========================================================================
    // Constants
    // =========================================================================
    localparam logic [15:0] BF16_ZERO     = 16'h0000;
    localparam logic [15:0] BF16_POS_INF  = 16'h7F80;
    localparam logic [15:0] BF16_NEG_INF  = 16'hFF80;
    localparam logic [15:0] BF16_NAN      = 16'h7FC0;

    // =========================================================================
    // Input Field Extraction
    // =========================================================================
    logic        w_sign;
    logic [7:0]  w_exp;
    logic [6:0]  w_mant;

    assign w_sign = i_bf16[15];
    assign w_exp  = i_bf16[14:7];
    assign w_mant = i_bf16[6:0];

    // =========================================================================
    // Special Case Detection
    // =========================================================================
    logic w_is_zero_or_subnormal;
    logic w_is_inf;
    logic w_is_nan_input;

    assign w_is_zero_or_subnormal = (w_exp == 8'd0);
    assign w_is_inf = (w_exp == 8'd255) && (w_mant == 7'd0);
    assign w_is_nan_input = (w_exp == 8'd255) && (w_mant != 7'd0);

    // =========================================================================
    // Integer Part: exp - 127 (signed)
    // =========================================================================
    // This gives the integer part of log2
    // Range: -126 to +127 for normal numbers
    logic signed [8:0] w_int_part;
    assign w_int_part = signed'({1'b0, w_exp}) - signed'(9'd127);

    // =========================================================================
    // Fractional Part LUT: log2(1 + m/128) for m in [0, 127]
    // =========================================================================
    // Values stored as 8-bit fixed point (0.8 format), range [0, 1)
    // log2(1.0) = 0, log2(2.0) = 1
    // Actual range: 0.0 to ~0.9943

    logic [LUT_ADDR_BITS-1:0] w_lut_addr;
    logic [7:0] w_frac_lut;       // raw entry for this bucket
    logic [8:0] w_frac_next;      // the bucket above, for interpolation
    logic [7:0] w_frac_part;      // interpolated -- what the datapath uses

    // Use top bits of mantissa as LUT address
    assign w_lut_addr = w_mant[6 -: LUT_ADDR_BITS];

    // Generate LUT using case statement based on LUT_DEPTH
    generate
        if (LUT_DEPTH == 32) begin : gen_lut_32
            // The table as a FUNCTION so it can be read at TWO addresses --
            // this bucket and the one above -- for interpolation. One copy
            // of the data, two reads.
            function automatic logic [8:0] lut_32(input logic [4:0] addr);
                logic [7:0] f;
                case (addr)
                    5'd0:  f = 8'd0;    // log2(1.0000) = 0.0000
                    5'd1:  f = 8'd11;   // log2(1.0312) = 0.0444
                    5'd2:  f = 8'd22;   // log2(1.0625) = 0.0875
                    5'd3:  f = 8'd33;   // log2(1.0938) = 0.1293
                    5'd4:  f = 8'd44;   // log2(1.1250) = 0.1699
                    5'd5:  f = 8'd54;   // log2(1.1562) = 0.2095
                    5'd6:  f = 8'd63;   // log2(1.1875) = 0.2479
                    5'd7:  f = 8'd73;   // log2(1.2188) = 0.2854
                    5'd8:  f = 8'd82;   // log2(1.2500) = 0.3219
                    5'd9:  f = 8'd92;   // log2(1.2812) = 0.3576
                    5'd10: f = 8'd100;  // log2(1.3125) = 0.3923
                    5'd11: f = 8'd109;  // log2(1.3438) = 0.4263
                    5'd12: f = 8'd118;  // log2(1.3750) = 0.4594
                    5'd13: f = 8'd126;  // log2(1.4062) = 0.4919
                    5'd14: f = 8'd134;  // log2(1.4375) = 0.5236
                    5'd15: f = 8'd142;  // log2(1.4688) = 0.5546
                    5'd16: f = 8'd150;  // log2(1.5000) = 0.5850
                    5'd17: f = 8'd157;  // log2(1.5312) = 0.6147
                    5'd18: f = 8'd165;  // log2(1.5625) = 0.6439
                    5'd19: f = 8'd172;  // log2(1.5938) = 0.6724
                    5'd20: f = 8'd179;  // log2(1.6250) = 0.7004
                    5'd21: f = 8'd186;  // log2(1.6562) = 0.7279
                    5'd22: f = 8'd193;  // log2(1.6875) = 0.7549
                    5'd23: f = 8'd200;  // log2(1.7188) = 0.7814
                    5'd24: f = 8'd207;  // log2(1.7500) = 0.8074
                    5'd25: f = 8'd213;  // log2(1.7812) = 0.8329
                    5'd26: f = 8'd220;  // log2(1.8125) = 0.8580
                    5'd27: f = 8'd226;  // log2(1.8438) = 0.8826
                    5'd28: f = 8'd232;  // log2(1.8750) = 0.9069
                    5'd29: f = 8'd238;  // log2(1.9062) = 0.9307
                    5'd30: f = 8'd244;  // log2(1.9375) = 0.9542
                    5'd31: f = 8'd250;  // log2(1.9688) = 0.9773
                    default: f = 8'd0;
                endcase
                return {1'b0, f};
            endfunction

            always_comb begin
                w_frac_lut  = lut_32(w_lut_addr)[7:0];
                // Past the last bucket the fraction reaches log2(2.0) = 1.0,
                // i.e. 256/256 -- which is why the next value is 9 bits.
                w_frac_next = (w_lut_addr == {5{1'b1}}) ? 9'd256
                                                        : lut_32(w_lut_addr + 1'b1);
            end
        end else if (LUT_DEPTH == 64) begin : gen_lut_64
            // The table as a FUNCTION so it can be read at TWO addresses --
            // this bucket and the one above -- for interpolation. One copy
            // of the data, two reads.
            function automatic logic [8:0] lut_64(input logic [5:0] addr);
                logic [7:0] f;
                case (addr)
                    6'd0:  f = 8'd0;
                    6'd1:  f = 8'd6;
                    6'd2:  f = 8'd11;
                    6'd3:  f = 8'd17;
                    6'd4:  f = 8'd22;
                    6'd5:  f = 8'd28;
                    6'd6:  f = 8'd33;
                    6'd7:  f = 8'd38;
                    6'd8:  f = 8'd44;
                    6'd9:  f = 8'd49;
                    6'd10: f = 8'd54;
                    6'd11: f = 8'd59;
                    6'd12: f = 8'd63;
                    6'd13: f = 8'd68;
                    6'd14: f = 8'd73;
                    6'd15: f = 8'd78;
                    6'd16: f = 8'd82;
                    6'd17: f = 8'd87;
                    6'd18: f = 8'd92;
                    6'd19: f = 8'd96;
                    6'd20: f = 8'd100;
                    6'd21: f = 8'd105;
                    6'd22: f = 8'd109;
                    6'd23: f = 8'd113;
                    6'd24: f = 8'd118;
                    6'd25: f = 8'd122;
                    6'd26: f = 8'd126;
                    6'd27: f = 8'd130;
                    6'd28: f = 8'd134;
                    6'd29: f = 8'd138;
                    6'd30: f = 8'd142;
                    6'd31: f = 8'd146;
                    6'd32: f = 8'd150;
                    6'd33: f = 8'd154;
                    6'd34: f = 8'd157;
                    6'd35: f = 8'd161;
                    6'd36: f = 8'd165;
                    6'd37: f = 8'd169;
                    6'd38: f = 8'd172;
                    6'd39: f = 8'd176;
                    6'd40: f = 8'd179;
                    6'd41: f = 8'd183;
                    6'd42: f = 8'd186;
                    6'd43: f = 8'd190;
                    6'd44: f = 8'd193;
                    6'd45: f = 8'd197;
                    6'd46: f = 8'd200;
                    6'd47: f = 8'd203;
                    6'd48: f = 8'd207;
                    6'd49: f = 8'd210;
                    6'd50: f = 8'd213;
                    6'd51: f = 8'd216;
                    6'd52: f = 8'd220;
                    6'd53: f = 8'd223;
                    6'd54: f = 8'd226;
                    6'd55: f = 8'd229;
                    6'd56: f = 8'd232;
                    6'd57: f = 8'd235;
                    6'd58: f = 8'd238;
                    6'd59: f = 8'd241;
                    6'd60: f = 8'd244;
                    6'd61: f = 8'd247;
                    6'd62: f = 8'd250;
                    6'd63: f = 8'd253;
                    default: f = 8'd0;
                endcase
                return {1'b0, f};
            endfunction

            always_comb begin
                w_frac_lut  = lut_64(w_lut_addr)[7:0];
                // Past the last bucket the fraction reaches log2(2.0) = 1.0,
                // i.e. 256/256 -- which is why the next value is 9 bits.
                w_frac_next = (w_lut_addr == {6{1'b1}}) ? 9'd256
                                                        : lut_64(w_lut_addr + 1'b1);
            end
        end else begin : gen_lut_128
            // LUT_DEPTH == 128
            // The table as a FUNCTION so it can be read at TWO addresses --
            // this bucket and the one above -- for interpolation. One copy
            // of the data, two reads.
            function automatic logic [8:0] lut_128(input logic [6:0] addr);
                logic [7:0] f;
                case (addr)
                    7'd0:   f = 8'd0;
                    7'd1:   f = 8'd3;
                    7'd2:   f = 8'd6;
                    7'd3:   f = 8'd9;
                    7'd4:   f = 8'd11;
                    7'd5:   f = 8'd14;
                    7'd6:   f = 8'd17;
                    7'd7:   f = 8'd20;
                    7'd8:   f = 8'd22;
                    7'd9:   f = 8'd25;
                    7'd10:  f = 8'd28;
                    7'd11:  f = 8'd30;
                    7'd12:  f = 8'd33;
                    7'd13:  f = 8'd36;
                    7'd14:  f = 8'd38;
                    7'd15:  f = 8'd41;
                    7'd16:  f = 8'd44;
                    7'd17:  f = 8'd46;
                    7'd18:  f = 8'd49;
                    7'd19:  f = 8'd51;
                    7'd20:  f = 8'd54;
                    7'd21:  f = 8'd56;
                    7'd22:  f = 8'd59;
                    7'd23:  f = 8'd61;
                    7'd24:  f = 8'd63;
                    7'd25:  f = 8'd66;
                    7'd26:  f = 8'd68;
                    7'd27:  f = 8'd71;
                    7'd28:  f = 8'd73;
                    7'd29:  f = 8'd75;
                    7'd30:  f = 8'd78;
                    7'd31:  f = 8'd80;
                    7'd32:  f = 8'd82;
                    7'd33:  f = 8'd85;
                    7'd34:  f = 8'd87;
                    7'd35:  f = 8'd89;
                    7'd36:  f = 8'd92;
                    7'd37:  f = 8'd94;
                    7'd38:  f = 8'd96;
                    7'd39:  f = 8'd98;
                    7'd40:  f = 8'd100;
                    7'd41:  f = 8'd103;
                    7'd42:  f = 8'd105;
                    7'd43:  f = 8'd107;
                    7'd44:  f = 8'd109;
                    7'd45:  f = 8'd111;
                    7'd46:  f = 8'd113;
                    7'd47:  f = 8'd116;
                    7'd48:  f = 8'd118;
                    7'd49:  f = 8'd120;
                    7'd50:  f = 8'd122;
                    7'd51:  f = 8'd124;
                    7'd52:  f = 8'd126;
                    7'd53:  f = 8'd128;
                    7'd54:  f = 8'd130;
                    7'd55:  f = 8'd132;
                    7'd56:  f = 8'd134;
                    7'd57:  f = 8'd136;
                    7'd58:  f = 8'd138;
                    7'd59:  f = 8'd140;
                    7'd60:  f = 8'd142;
                    7'd61:  f = 8'd144;
                    7'd62:  f = 8'd146;
                    7'd63:  f = 8'd148;
                    7'd64:  f = 8'd150;
                    7'd65:  f = 8'd152;
                    7'd66:  f = 8'd154;
                    7'd67:  f = 8'd155;
                    7'd68:  f = 8'd157;
                    7'd69:  f = 8'd159;
                    7'd70:  f = 8'd161;
                    7'd71:  f = 8'd163;
                    7'd72:  f = 8'd165;
                    7'd73:  f = 8'd167;
                    7'd74:  f = 8'd169;
                    7'd75:  f = 8'd170;
                    7'd76:  f = 8'd172;
                    7'd77:  f = 8'd174;
                    7'd78:  f = 8'd176;
                    7'd79:  f = 8'd178;
                    7'd80:  f = 8'd179;
                    7'd81:  f = 8'd181;
                    7'd82:  f = 8'd183;
                    7'd83:  f = 8'd185;
                    7'd84:  f = 8'd186;
                    7'd85:  f = 8'd188;
                    7'd86:  f = 8'd190;
                    7'd87:  f = 8'd192;
                    7'd88:  f = 8'd193;
                    7'd89:  f = 8'd195;
                    7'd90:  f = 8'd197;
                    7'd91:  f = 8'd198;
                    7'd92:  f = 8'd200;
                    7'd93:  f = 8'd202;
                    7'd94:  f = 8'd203;
                    7'd95:  f = 8'd205;
                    7'd96:  f = 8'd207;
                    7'd97:  f = 8'd208;
                    7'd98:  f = 8'd210;
                    7'd99:  f = 8'd212;
                    7'd100: f = 8'd213;
                    7'd101: f = 8'd215;
                    7'd102: f = 8'd216;
                    7'd103: f = 8'd218;
                    7'd104: f = 8'd220;
                    7'd105: f = 8'd221;
                    7'd106: f = 8'd223;
                    7'd107: f = 8'd224;
                    7'd108: f = 8'd226;
                    7'd109: f = 8'd228;
                    7'd110: f = 8'd229;
                    7'd111: f = 8'd231;
                    7'd112: f = 8'd232;
                    7'd113: f = 8'd234;
                    7'd114: f = 8'd235;
                    7'd115: f = 8'd237;
                    7'd116: f = 8'd238;
                    7'd117: f = 8'd240;
                    7'd118: f = 8'd241;
                    7'd119: f = 8'd243;
                    7'd120: f = 8'd244;
                    7'd121: f = 8'd246;
                    7'd122: f = 8'd247;
                    7'd123: f = 8'd249;
                    7'd124: f = 8'd250;
                    7'd125: f = 8'd252;
                    7'd126: f = 8'd253;
                    7'd127: f = 8'd255;
                    default: f = 8'd0;
                endcase
                return {1'b0, f};
            endfunction

            always_comb begin
                w_frac_lut  = lut_128(w_lut_addr)[7:0];
                // Past the last bucket the fraction reaches log2(2.0) = 1.0,
                // i.e. 256/256 -- which is why the next value is 9 bits.
                w_frac_next = (w_lut_addr == {7{1'b1}}) ? 9'd256
                                                        : lut_128(w_lut_addr + 1'b1);
            end
        end
    endgenerate

    // =========================================================================
    // Combine Integer and Fractional Parts into BF16
    // =========================================================================
    // Result = int_part + frac_part/256
    // Need to convert this to BF16 format

    // The result can be negative (for x < 1), zero (for x = 1), or positive (for x > 1)

    logic [15:0] w_result;
    logic [7:0]  w_abs_int;       // Absolute value of integer part for negative results
    logic [7:0]  w_adj_int;       // Adjusted integer for negative results with frac > 0
    logic [7:0]  w_adj_frac;      // Adjusted fractional part (256 - frac)

    // Compute absolute value outside always_comb to avoid latch inference
    assign w_abs_int = (w_int_part < 0) ? 8'(-w_int_part[7:0]) : 8'd0;

    // For negative results: value = -abs_int + frac/256 = -(abs_int - frac/256)
    // When frac > 0: magnitude = (abs_int - 1) + (256 - frac)/256
    // -------------------------------------------------------------------
    // Interpolate across the LUT bucket.
    //
    // w_lut_addr drops the low (7 - LUT_ADDR_BITS) mantissa bits, so the raw
    // table is piecewise-CONSTANT: every mantissa in a bucket gets the value
    // at the bucket's BOTTOM. At LUT_DEPTH=32, log2(1 + 27/128) was answered
    // with the entry for 24, and for x=0x3F9B that put the result 17 ULP from
    // correctly rounded (0x3E7C against 0x3E8D). The testbench had it right --
    // this was a DUT error.
    //
    // Measured over all 128 mantissas: 8.66/256 worst case before, 0.94/256
    // after -- 9.2x. At LUT_DEPTH=128 nothing is dropped and this is the raw
    // entry.
    // -------------------------------------------------------------------
    generate
        if (LUT_ADDR_BITS >= 7) begin : gen_no_interp
            assign w_frac_part = w_frac_lut;
        end else begin : gen_interp
            localparam int FRAC_BITS = 7 - LUT_ADDR_BITS;
            localparam int FRAC_HALF = 1 << (FRAC_BITS - 1);

            logic [FRAC_BITS-1:0] w_sub;
            assign w_sub = w_mant[FRAC_BITS-1:0];

            // log2 increases monotonically over the mantissa, so the step to
            // the next bucket is non-negative and the arithmetic is unsigned.
            logic [8:0]  w_step;
            logic [15:0] w_scaled;
            assign w_step   = w_frac_next - {1'b0, w_frac_lut};
            assign w_scaled = ({{(9-FRAC_BITS){1'b0}}, w_sub} * w_step) +
                              16'(FRAC_HALF);
            assign w_frac_part = w_frac_lut + 8'(w_scaled >> FRAC_BITS);
        end
    endgenerate

    assign w_adj_int = (w_frac_part > 0) ? (w_abs_int - 8'd1) : w_abs_int;
    assign w_adj_frac = (w_frac_part > 0) ? (8'd0 - w_frac_part) : 8'd0;  // 256 - frac

    // Handle the conversion based on integer part value
    always_comb begin
        if (w_int_part == 0 && w_frac_part == 0) begin
            // log2(1.0) = 0
            w_result = BF16_ZERO;
        end else if (w_int_part >= 0) begin
            // Positive result: need to find leading bit position
            // int_part is 0-127, frac_part is 0-255
            // Combined value is int_part + frac_part/256

            // Convert int_part.frac_part to BF16 format
            // Leading 1 is implicit, so find position of first set bit in int_part
            if (w_int_part >= 64) begin
                // int_part[6] = 1, exp = 127 + 6 = 133
                w_result = {1'b0, 8'd133, w_int_part[5:0], w_frac_part[7]};
            end else if (w_int_part >= 32) begin
                // int_part[5] = 1, exp = 127 + 5 = 132
                w_result = {1'b0, 8'd132, w_int_part[4:0], w_frac_part[7:6]};
            end else if (w_int_part >= 16) begin
                // int_part[4] = 1, exp = 127 + 4 = 131
                w_result = {1'b0, 8'd131, w_int_part[3:0], w_frac_part[7:5]};
            end else if (w_int_part >= 8) begin
                // int_part[3] = 1, exp = 127 + 3 = 130
                w_result = {1'b0, 8'd130, w_int_part[2:0], w_frac_part[7:4]};
            end else if (w_int_part >= 4) begin
                // int_part[2] = 1, exp = 127 + 2 = 129
                w_result = {1'b0, 8'd129, w_int_part[1:0], w_frac_part[7:3]};
            end else if (w_int_part >= 2) begin
                // int_part[1] = 1, exp = 127 + 1 = 128
                w_result = {1'b0, 8'd128, w_int_part[0], w_frac_part[7:2]};
            end else if (w_int_part >= 1) begin
                // int_part[0] = 1, exp = 127
                w_result = {1'b0, 8'd127, w_frac_part[7:1]};
            end else begin
                // int_part = 0, but frac_part > 0
                // Value is 0.frac_part (less than 1.0)
                // Need to normalize
                if (w_frac_part >= 128) begin
                    w_result = {1'b0, 8'd126, w_frac_part[6:0]};
                end else if (w_frac_part >= 64) begin
                    w_result = {1'b0, 8'd125, w_frac_part[5:0], 1'b0};
                end else if (w_frac_part >= 32) begin
                    w_result = {1'b0, 8'd124, w_frac_part[4:0], 2'b0};
                end else if (w_frac_part >= 16) begin
                    w_result = {1'b0, 8'd123, w_frac_part[3:0], 3'b0};
                end else if (w_frac_part >= 8) begin
                    w_result = {1'b0, 8'd122, w_frac_part[2:0], 4'b0};
                end else if (w_frac_part >= 4) begin
                    w_result = {1'b0, 8'd121, w_frac_part[1:0], 5'b0};
                end else if (w_frac_part >= 2) begin
                    w_result = {1'b0, 8'd120, w_frac_part[0], 6'b0};
                end else begin
                    w_result = {1'b0, 8'd119, 7'b0};
                end
            end
        end else begin
            // Negative result: value = -abs_int + frac/256 = -(abs_int - frac/256)
            // Use adjusted values: w_adj_int = abs_int-1 if frac>0, w_adj_frac = 256-frac
            // This converts -13 + 0.125 = -12.875 to sign=1, magnitude=12.875

            if (w_adj_int >= 64) begin
                // adj_int[6] = 1, exp = 127 + 6 = 133
                w_result = {1'b1, 8'd133, w_adj_int[5:0], w_adj_frac[7]};
            end else if (w_adj_int >= 32) begin
                w_result = {1'b1, 8'd132, w_adj_int[4:0], w_adj_frac[7:6]};
            end else if (w_adj_int >= 16) begin
                w_result = {1'b1, 8'd131, w_adj_int[3:0], w_adj_frac[7:5]};
            end else if (w_adj_int >= 8) begin
                w_result = {1'b1, 8'd130, w_adj_int[2:0], w_adj_frac[7:4]};
            end else if (w_adj_int >= 4) begin
                w_result = {1'b1, 8'd129, w_adj_int[1:0], w_adj_frac[7:3]};
            end else if (w_adj_int >= 2) begin
                w_result = {1'b1, 8'd128, w_adj_int[0], w_adj_frac[7:2]};
            end else if (w_adj_int >= 1) begin
                w_result = {1'b1, 8'd127, w_adj_frac[7:1]};
            end else begin
                // adj_int = 0, so magnitude is just frac/256 (less than 1.0)
                // Normalize the fractional part
                if (w_adj_frac >= 128) begin
                    w_result = {1'b1, 8'd126, w_adj_frac[6:0]};
                end else if (w_adj_frac >= 64) begin
                    w_result = {1'b1, 8'd125, w_adj_frac[5:0], 1'b0};
                end else if (w_adj_frac >= 32) begin
                    w_result = {1'b1, 8'd124, w_adj_frac[4:0], 2'b0};
                end else if (w_adj_frac >= 16) begin
                    w_result = {1'b1, 8'd123, w_adj_frac[3:0], 3'b0};
                end else if (w_adj_frac >= 8) begin
                    w_result = {1'b1, 8'd122, w_adj_frac[2:0], 4'b0};
                end else if (w_adj_frac >= 4) begin
                    w_result = {1'b1, 8'd121, w_adj_frac[1:0], 5'b0};
                end else if (w_adj_frac >= 2) begin
                    w_result = {1'b1, 8'd120, w_adj_frac[0], 6'b0};
                end else begin
                    // Very small magnitude
                    w_result = {1'b1, 8'd119, 7'b0};
                end
            end
        end
    end

    // =========================================================================
    // Output Selection
    // =========================================================================
    assign ow_is_zero = w_is_zero_or_subnormal;
    assign ow_is_inf  = w_is_inf;
    assign ow_is_nan  = w_is_nan_input || w_sign;  // NaN or negative
    assign ow_is_neg  = w_sign && !w_is_nan_input;

    assign ow_log2 = w_is_nan_input           ? BF16_NAN :
                     w_sign                   ? BF16_NAN :      // Negative input
                     w_is_zero_or_subnormal   ? BF16_NEG_INF :  // log(0) = -inf
                     w_is_inf                 ? BF16_POS_INF :  // log(inf) = +inf
                                                w_result;

endmodule
