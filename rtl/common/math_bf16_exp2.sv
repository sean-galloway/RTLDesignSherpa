// =============================================================================
// Module: math_bf16_exp2
// Description: BF16 base-2 exponential (2^x) using LUT approximation
//
// This module computes 2^x for BF16 inputs.
//
// Algorithm:
//   For input x = int_part + frac_part (where frac is in [0, 1)):
//     2^x = 2^int_part * 2^frac_part
//
//   - 2^int_part: Sets the BF16 exponent to 127 + int_part
//   - 2^frac_part: LUT lookup, gives value in [1.0, 2.0)
//
// Input Range:
//   Useful range: approximately [-126, +127]
//   - exp2(-126) = min normal BF16
//   - exp2(127) = max normal BF16
//   - Values outside this range overflow/underflow
//
// Parameters:
//   LUT_DEPTH: Size of fractional part LUT (32, 64, or 128)
//
// Latency: Combinational
// Logic Levels: ~15-20
//
// Special Cases:
//   - Large positive input: Returns +infinity (overflow)
//   - Large negative input: Returns 0 (underflow)
//   - NaN input: Returns NaN
//   - Zero input: Returns 1.0 (2^0 = 1)
//
// Copyright (c) 2025 Sean Galloway
// SPDX-License-Identifier: MIT
// =============================================================================

`timescale 1ns / 1ps

module math_bf16_exp2 #(
    parameter int LUT_DEPTH = 32,
    parameter int LUT_ADDR_BITS = $clog2(LUT_DEPTH)
) (
    input  logic [15:0] i_bf16,           // Input exponent in BF16
    output logic [15:0] ow_exp2,          // 2^input in BF16
    output logic        ow_is_zero,       // Result underflowed to zero
    output logic        ow_is_inf,        // Result overflowed to infinity
    output logic        ow_is_nan         // Input was NaN
);

    // =========================================================================
    // Constants
    // =========================================================================
    localparam logic [15:0] BF16_ONE      = 16'h3F80;  // 1.0
    localparam logic [15:0] BF16_ZERO     = 16'h0000;
    localparam logic [15:0] BF16_POS_INF  = 16'h7F80;
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
    logic w_is_zero_input;
    logic w_is_inf_input;
    logic w_is_nan_input;

    assign w_is_zero_input = (w_exp == 8'd0);
    assign w_is_inf_input = (w_exp == 8'd255) && (w_mant == 7'd0);
    assign w_is_nan_input = (w_exp == 8'd255) && (w_mant != 7'd0);

    // =========================================================================
    // Extract Integer and Fractional Parts from BF16 Input
    // =========================================================================
    // Input is a BF16 number representing the exponent
    // Need to convert to integer.fraction format

    // First, get the actual value's magnitude
    // BF16: value = 2^(exp-127) * (1 + mant/128)
    // For small values (exp < 127), we have a fraction < 1
    // For larger values (exp >= 127), we have integer >= 1

    logic signed [8:0] w_int_part;    // Integer part of input (signed)
    logic [7:0]        w_frac_part;   // Fractional part (0.8 fixed point)

    always_comb begin
        if (w_exp >= 8'd135) begin
            // Very large magnitude (|x| >= 256)
            // Will definitely overflow or underflow
            w_int_part = w_sign ? -9'sd256 : 9'sd256;
            w_frac_part = 8'd0;
        end else if (w_exp >= 8'd127) begin
            // |x| >= 1.0
            // Integer part comes from mantissa shifted by (exp - 127)
            case (w_exp - 8'd127)
                8'd0: begin  // 1.xxx
                    w_int_part = w_sign ? -9'sd1 : 9'sd1;
                    w_frac_part = {w_mant, 1'b0};
                end
                8'd1: begin  // 2.xxx to 3.xxx
                    w_int_part = w_sign ? -9'(signed'({1'b0, 1'b1, w_mant[6]})) :
                                           9'(signed'({1'b0, 1'b1, w_mant[6]}));
                    w_frac_part = {w_mant[5:0], 2'b0};
                end
                8'd2: begin  // 4.xxx to 7.xxx
                    w_int_part = w_sign ? -9'(signed'({1'b0, 1'b1, w_mant[6:5]})) :
                                           9'(signed'({1'b0, 1'b1, w_mant[6:5]}));
                    w_frac_part = {w_mant[4:0], 3'b0};
                end
                8'd3: begin  // 8.xxx to 15.xxx
                    w_int_part = w_sign ? -9'(signed'({1'b0, 1'b1, w_mant[6:4]})) :
                                           9'(signed'({1'b0, 1'b1, w_mant[6:4]}));
                    w_frac_part = {w_mant[3:0], 4'b0};
                end
                8'd4: begin  // 16.xxx to 31.xxx
                    w_int_part = w_sign ? -9'(signed'({1'b0, 1'b1, w_mant[6:3]})) :
                                           9'(signed'({1'b0, 1'b1, w_mant[6:3]}));
                    w_frac_part = {w_mant[2:0], 5'b0};
                end
                8'd5: begin  // 32.xxx to 63.xxx
                    w_int_part = w_sign ? -9'(signed'({1'b0, 1'b1, w_mant[6:2]})) :
                                           9'(signed'({1'b0, 1'b1, w_mant[6:2]}));
                    w_frac_part = {w_mant[1:0], 6'b0};
                end
                8'd6: begin  // 64.xxx to 127.xxx
                    w_int_part = w_sign ? -9'(signed'({1'b0, 1'b1, w_mant[6:1]})) :
                                           9'(signed'({1'b0, 1'b1, w_mant[6:1]}));
                    w_frac_part = {w_mant[0], 7'b0};
                end
                8'd7: begin  // 128.xxx to 255.xxx
                    w_int_part = w_sign ? -9'(signed'({2'b01, w_mant})) :
                                           9'(signed'({2'b01, w_mant}));
                    w_frac_part = 8'd0;  // All mantissa bits used for integer
                end
                default: begin  // >= 256 (will definitely overflow)
                    w_int_part = w_sign ? -9'sd256 : 9'sd256;
                    w_frac_part = 8'd0;
                end
            endcase
        end else if (w_exp == 8'd126) begin
            // 0.5 <= |x| < 1.0
            // Value = 2^-1 * (1 + mant/128) = 0.5 + mant*0.5/128
            // frac = |x| * 256 = 128 + mant (always positive magnitude)
            w_int_part = 9'sd0;
            w_frac_part = {1'b1, w_mant};  // 0.1mmmmmmm = 128 + mant
            // Note: Floor adjustment for negative handled by w_adj_* signals
        end else if (w_exp == 8'd125) begin
            // 0.25 <= |x| < 0.5
            w_int_part = 9'sd0;
            w_frac_part = {2'b01, w_mant[6:1]};  // 0.01mmmmmm = 64 + mant/2
        end else if (w_exp == 8'd124) begin
            // 0.125 <= |x| < 0.25
            w_int_part = 9'sd0;
            w_frac_part = {3'b001, w_mant[6:2]};  // 0.001mmmmm
        end else if (w_exp == 8'd123) begin
            // 0.0625 <= |x| < 0.125
            w_int_part = 9'sd0;
            w_frac_part = {4'b0001, w_mant[6:3]};  // 0.0001mmmm
        end else begin
            // |x| < 0.0625, treat as approximately zero
            w_int_part = 9'sd0;
            w_frac_part = 8'd0;
        end
    end

    // =========================================================================
    // Fractional Part LUT: 2^frac for frac in [0, 1)
    // =========================================================================
    // Values stored as 7-bit mantissa (implicit 1.xxx format)
    // 2^0 = 1.0 (mantissa = 0)
    // 2^0.5 ≈ 1.414 (mantissa ≈ 53)
    // 2^1 = 2.0 (but this wraps to next integer)

    logic [LUT_ADDR_BITS-1:0] w_lut_addr;
    logic [6:0] w_result_mant;

    assign w_lut_addr = w_frac_part[7:8-LUT_ADDR_BITS];

    // Generate LUT using case statement based on LUT_DEPTH
    // LUT values: mantissa for 2^(i/LUT_DEPTH) where result = 1.mantissa
    // mantissa = round((2^(i/LUT_DEPTH) - 1) * 128)
    generate
        if (LUT_DEPTH == 32) begin : gen_lut_32
            always_comb begin
                case (w_lut_addr)
                    5'd0:  w_result_mant = 7'd0;    // 2^(0/32) = 1.0000
                    5'd1:  w_result_mant = 7'd3;    // 2^(1/32) = 1.0219
                    5'd2:  w_result_mant = 7'd6;    // 2^(2/32) = 1.0443
                    5'd3:  w_result_mant = 7'd9;    // 2^(3/32) = 1.0671
                    5'd4:  w_result_mant = 7'd12;   // 2^(4/32) = 1.0905
                    5'd5:  w_result_mant = 7'd15;   // 2^(5/32) = 1.1144
                    5'd6:  w_result_mant = 7'd18;   // 2^(6/32) = 1.1388
                    5'd7:  w_result_mant = 7'd21;   // 2^(7/32) = 1.1637
                    5'd8:  w_result_mant = 7'd24;   // 2^(8/32) = 1.1892
                    5'd9:  w_result_mant = 7'd28;   // 2^(9/32) = 1.2152
                    5'd10: w_result_mant = 7'd31;   // 2^(10/32) = 1.2419
                    5'd11: w_result_mant = 7'd34;   // 2^(11/32) = 1.2691
                    5'd12: w_result_mant = 7'd38;   // 2^(12/32) = 1.2968
                    5'd13: w_result_mant = 7'd42;   // 2^(13/32) = 1.3252
                    5'd14: w_result_mant = 7'd45;   // 2^(14/32) = 1.3543
                    5'd15: w_result_mant = 7'd49;   // 2^(15/32) = 1.3839
                    5'd16: w_result_mant = 7'd53;   // 2^(16/32) = 1.4142 (sqrt(2))
                    5'd17: w_result_mant = 7'd57;   // 2^(17/32) = 1.4452
                    5'd18: w_result_mant = 7'd61;   // 2^(18/32) = 1.4768
                    5'd19: w_result_mant = 7'd65;   // 2^(19/32) = 1.5092
                    5'd20: w_result_mant = 7'd69;   // 2^(20/32) = 1.5422
                    5'd21: w_result_mant = 7'd74;   // 2^(21/32) = 1.5760
                    5'd22: w_result_mant = 7'd78;   // 2^(22/32) = 1.6105
                    5'd23: w_result_mant = 7'd83;   // 2^(23/32) = 1.6458
                    5'd24: w_result_mant = 7'd87;   // 2^(24/32) = 1.6818
                    5'd25: w_result_mant = 7'd92;   // 2^(25/32) = 1.7186
                    5'd26: w_result_mant = 7'd97;   // 2^(26/32) = 1.7563
                    5'd27: w_result_mant = 7'd102;  // 2^(27/32) = 1.7947
                    5'd28: w_result_mant = 7'd107;  // 2^(28/32) = 1.8340
                    5'd29: w_result_mant = 7'd112;  // 2^(29/32) = 1.8742
                    5'd30: w_result_mant = 7'd117;  // 2^(30/32) = 1.9152
                    5'd31: w_result_mant = 7'd123;  // 2^(31/32) = 1.9571
                    default: w_result_mant = 7'd0;
                endcase
            end
        end else if (LUT_DEPTH == 64) begin : gen_lut_64
            always_comb begin
                case (w_lut_addr)
                    6'd0:  w_result_mant = 7'd0;    // 2^(0/64) = 1.0000
                    6'd1:  w_result_mant = 7'd1;    // 2^(1/64) = 1.0109
                    6'd2:  w_result_mant = 7'd3;    // 2^(2/64) = 1.0219
                    6'd3:  w_result_mant = 7'd4;    // 2^(3/64) = 1.0330
                    6'd4:  w_result_mant = 7'd6;    // 2^(4/64) = 1.0443
                    6'd5:  w_result_mant = 7'd7;    // 2^(5/64) = 1.0556
                    6'd6:  w_result_mant = 7'd9;    // 2^(6/64) = 1.0671
                    6'd7:  w_result_mant = 7'd10;   // 2^(7/64) = 1.0788
                    6'd8:  w_result_mant = 7'd12;   // 2^(8/64) = 1.0905
                    6'd9:  w_result_mant = 7'd13;   // 2^(9/64) = 1.1024
                    6'd10: w_result_mant = 7'd15;   // 2^(10/64) = 1.1144
                    6'd11: w_result_mant = 7'd16;   // 2^(11/64) = 1.1265
                    6'd12: w_result_mant = 7'd18;   // 2^(12/64) = 1.1388
                    6'd13: w_result_mant = 7'd19;   // 2^(13/64) = 1.1512
                    6'd14: w_result_mant = 7'd21;   // 2^(14/64) = 1.1637
                    6'd15: w_result_mant = 7'd23;   // 2^(15/64) = 1.1764
                    6'd16: w_result_mant = 7'd24;   // 2^(16/64) = 1.1892
                    6'd17: w_result_mant = 7'd26;   // 2^(17/64) = 1.2022
                    6'd18: w_result_mant = 7'd28;   // 2^(18/64) = 1.2152
                    6'd19: w_result_mant = 7'd29;   // 2^(19/64) = 1.2285
                    6'd20: w_result_mant = 7'd31;   // 2^(20/64) = 1.2419
                    6'd21: w_result_mant = 7'd33;   // 2^(21/64) = 1.2554
                    6'd22: w_result_mant = 7'd34;   // 2^(22/64) = 1.2691
                    6'd23: w_result_mant = 7'd36;   // 2^(23/64) = 1.2829
                    6'd24: w_result_mant = 7'd38;   // 2^(24/64) = 1.2968
                    6'd25: w_result_mant = 7'd40;   // 2^(25/64) = 1.3110
                    6'd26: w_result_mant = 7'd42;   // 2^(26/64) = 1.3252
                    6'd27: w_result_mant = 7'd43;   // 2^(27/64) = 1.3397
                    6'd28: w_result_mant = 7'd45;   // 2^(28/64) = 1.3543
                    6'd29: w_result_mant = 7'd47;   // 2^(29/64) = 1.3690
                    6'd30: w_result_mant = 7'd49;   // 2^(30/64) = 1.3839
                    6'd31: w_result_mant = 7'd51;   // 2^(31/64) = 1.3990
                    6'd32: w_result_mant = 7'd53;   // 2^(32/64) = 1.4142
                    6'd33: w_result_mant = 7'd55;   // 2^(33/64) = 1.4296
                    6'd34: w_result_mant = 7'd57;   // 2^(34/64) = 1.4452
                    6'd35: w_result_mant = 7'd59;   // 2^(35/64) = 1.4609
                    6'd36: w_result_mant = 7'd61;   // 2^(36/64) = 1.4768
                    6'd37: w_result_mant = 7'd63;   // 2^(37/64) = 1.4929
                    6'd38: w_result_mant = 7'd65;   // 2^(38/64) = 1.5092
                    6'd39: w_result_mant = 7'd67;   // 2^(39/64) = 1.5256
                    6'd40: w_result_mant = 7'd69;   // 2^(40/64) = 1.5422
                    6'd41: w_result_mant = 7'd72;   // 2^(41/64) = 1.5590
                    6'd42: w_result_mant = 7'd74;   // 2^(42/64) = 1.5760
                    6'd43: w_result_mant = 7'd76;   // 2^(43/64) = 1.5931
                    6'd44: w_result_mant = 7'd78;   // 2^(44/64) = 1.6105
                    6'd45: w_result_mant = 7'd80;   // 2^(45/64) = 1.6280
                    6'd46: w_result_mant = 7'd83;   // 2^(46/64) = 1.6458
                    6'd47: w_result_mant = 7'd85;   // 2^(47/64) = 1.6637
                    6'd48: w_result_mant = 7'd87;   // 2^(48/64) = 1.6818
                    6'd49: w_result_mant = 7'd90;   // 2^(49/64) = 1.7001
                    6'd50: w_result_mant = 7'd92;   // 2^(50/64) = 1.7186
                    6'd51: w_result_mant = 7'd94;   // 2^(51/64) = 1.7373
                    6'd52: w_result_mant = 7'd97;   // 2^(52/64) = 1.7563
                    6'd53: w_result_mant = 7'd99;   // 2^(53/64) = 1.7754
                    6'd54: w_result_mant = 7'd102;  // 2^(54/64) = 1.7947
                    6'd55: w_result_mant = 7'd104;  // 2^(55/64) = 1.8143
                    6'd56: w_result_mant = 7'd107;  // 2^(56/64) = 1.8340
                    6'd57: w_result_mant = 7'd109;  // 2^(57/64) = 1.8540
                    6'd58: w_result_mant = 7'd112;  // 2^(58/64) = 1.8742
                    6'd59: w_result_mant = 7'd115;  // 2^(59/64) = 1.8946
                    6'd60: w_result_mant = 7'd117;  // 2^(60/64) = 1.9152
                    6'd61: w_result_mant = 7'd120;  // 2^(61/64) = 1.9361
                    6'd62: w_result_mant = 7'd123;  // 2^(62/64) = 1.9571
                    6'd63: w_result_mant = 7'd125;  // 2^(63/64) = 1.9785
                    default: w_result_mant = 7'd0;
                endcase
            end
        end else begin : gen_lut_128
            // Default to 128 entries
            always_comb begin
                case (w_lut_addr)
                    7'd0:   w_result_mant = 7'd0;    // 2^(0/128) = 1.0000
                    7'd1:   w_result_mant = 7'd1;    // 2^(1/128) = 1.0054
                    7'd2:   w_result_mant = 7'd1;    // 2^(2/128) = 1.0109
                    7'd3:   w_result_mant = 7'd2;    // 2^(3/128) = 1.0164
                    7'd4:   w_result_mant = 7'd3;    // 2^(4/128) = 1.0219
                    7'd5:   w_result_mant = 7'd3;    // 2^(5/128) = 1.0274
                    7'd6:   w_result_mant = 7'd4;    // 2^(6/128) = 1.0330
                    7'd7:   w_result_mant = 7'd5;    // 2^(7/128) = 1.0386
                    7'd8:   w_result_mant = 7'd6;    // 2^(8/128) = 1.0443
                    7'd9:   w_result_mant = 7'd6;    // 2^(9/128) = 1.0499
                    7'd10:  w_result_mant = 7'd7;    // 2^(10/128) = 1.0556
                    7'd11:  w_result_mant = 7'd8;    // 2^(11/128) = 1.0614
                    7'd12:  w_result_mant = 7'd9;    // 2^(12/128) = 1.0671
                    7'd13:  w_result_mant = 7'd9;    // 2^(13/128) = 1.0729
                    7'd14:  w_result_mant = 7'd10;   // 2^(14/128) = 1.0787
                    7'd15:  w_result_mant = 7'd11;   // 2^(15/128) = 1.0846
                    7'd16:  w_result_mant = 7'd11;   // 2^(16/128) = 1.0905
                    7'd17:  w_result_mant = 7'd12;   // 2^(17/128) = 1.0964
                    7'd18:  w_result_mant = 7'd13;   // 2^(18/128) = 1.1024
                    7'd19:  w_result_mant = 7'd14;   // 2^(19/128) = 1.1083
                    7'd20:  w_result_mant = 7'd14;   // 2^(20/128) = 1.1143
                    7'd21:  w_result_mant = 7'd15;   // 2^(21/128) = 1.1203
                    7'd22:  w_result_mant = 7'd16;   // 2^(22/128) = 1.1264
                    7'd23:  w_result_mant = 7'd17;   // 2^(23/128) = 1.1325
                    7'd24:  w_result_mant = 7'd17;   // 2^(24/128) = 1.1387
                    7'd25:  w_result_mant = 7'd18;   // 2^(25/128) = 1.1448
                    7'd26:  w_result_mant = 7'd19;   // 2^(26/128) = 1.1510
                    7'd27:  w_result_mant = 7'd20;   // 2^(27/128) = 1.1573
                    7'd28:  w_result_mant = 7'd20;   // 2^(28/128) = 1.1636
                    7'd29:  w_result_mant = 7'd21;   // 2^(29/128) = 1.1699
                    7'd30:  w_result_mant = 7'd22;   // 2^(30/128) = 1.1763
                    7'd31:  w_result_mant = 7'd23;   // 2^(31/128) = 1.1827
                    7'd32:  w_result_mant = 7'd23;   // 2^(32/128) = 1.1892
                    7'd33:  w_result_mant = 7'd24;   // 2^(33/128) = 1.1956
                    7'd34:  w_result_mant = 7'd25;   // 2^(34/128) = 1.2022
                    7'd35:  w_result_mant = 7'd26;   // 2^(35/128) = 1.2087
                    7'd36:  w_result_mant = 7'd27;   // 2^(36/128) = 1.2153
                    7'd37:  w_result_mant = 7'd27;   // 2^(37/128) = 1.2219
                    7'd38:  w_result_mant = 7'd28;   // 2^(38/128) = 1.2286
                    7'd39:  w_result_mant = 7'd29;   // 2^(39/128) = 1.2353
                    7'd40:  w_result_mant = 7'd30;   // 2^(40/128) = 1.2420
                    7'd41:  w_result_mant = 7'd31;   // 2^(41/128) = 1.2488
                    7'd42:  w_result_mant = 7'd31;   // 2^(42/128) = 1.2556
                    7'd43:  w_result_mant = 7'd32;   // 2^(43/128) = 1.2624
                    7'd44:  w_result_mant = 7'd33;   // 2^(44/128) = 1.2693
                    7'd45:  w_result_mant = 7'd34;   // 2^(45/128) = 1.2763
                    7'd46:  w_result_mant = 7'd35;   // 2^(46/128) = 1.2833
                    7'd47:  w_result_mant = 7'd36;   // 2^(47/128) = 1.2903
                    7'd48:  w_result_mant = 7'd36;   // 2^(48/128) = 1.2974
                    7'd49:  w_result_mant = 7'd37;   // 2^(49/128) = 1.3045
                    7'd50:  w_result_mant = 7'd38;   // 2^(50/128) = 1.3116
                    7'd51:  w_result_mant = 7'd39;   // 2^(51/128) = 1.3188
                    7'd52:  w_result_mant = 7'd40;   // 2^(52/128) = 1.3260
                    7'd53:  w_result_mant = 7'd41;   // 2^(53/128) = 1.3333
                    7'd54:  w_result_mant = 7'd42;   // 2^(54/128) = 1.3406
                    7'd55:  w_result_mant = 7'd43;   // 2^(55/128) = 1.3479
                    7'd56:  w_result_mant = 7'd43;   // 2^(56/128) = 1.3553
                    7'd57:  w_result_mant = 7'd44;   // 2^(57/128) = 1.3628
                    7'd58:  w_result_mant = 7'd45;   // 2^(58/128) = 1.3702
                    7'd59:  w_result_mant = 7'd46;   // 2^(59/128) = 1.3778
                    7'd60:  w_result_mant = 7'd47;   // 2^(60/128) = 1.3853
                    7'd61:  w_result_mant = 7'd48;   // 2^(61/128) = 1.3929
                    7'd62:  w_result_mant = 7'd49;   // 2^(62/128) = 1.4006
                    7'd63:  w_result_mant = 7'd50;   // 2^(63/128) = 1.4083
                    7'd64:  w_result_mant = 7'd50;   // 2^(64/128) = 1.4142
                    7'd65:  w_result_mant = 7'd51;   // 2^(65/128) = 1.4219
                    7'd66:  w_result_mant = 7'd52;   // 2^(66/128) = 1.4296
                    7'd67:  w_result_mant = 7'd53;   // 2^(67/128) = 1.4377
                    7'd68:  w_result_mant = 7'd54;   // 2^(68/128) = 1.4459
                    7'd69:  w_result_mant = 7'd55;   // 2^(69/128) = 1.4540
                    7'd70:  w_result_mant = 7'd56;   // 2^(70/128) = 1.4620
                    7'd71:  w_result_mant = 7'd57;   // 2^(71/128) = 1.4702
                    7'd72:  w_result_mant = 7'd57;   // 2^(72/128) = 1.4784
                    7'd73:  w_result_mant = 7'd58;   // 2^(73/128) = 1.4867
                    7'd74:  w_result_mant = 7'd59;   // 2^(74/128) = 1.4950
                    7'd75:  w_result_mant = 7'd60;   // 2^(75/128) = 1.5034
                    7'd76:  w_result_mant = 7'd61;   // 2^(76/128) = 1.5117
                    7'd77:  w_result_mant = 7'd62;   // 2^(77/128) = 1.5202
                    7'd78:  w_result_mant = 7'd63;   // 2^(78/128) = 1.5287
                    7'd79:  w_result_mant = 7'd64;   // 2^(79/128) = 1.5373
                    7'd80:  w_result_mant = 7'd65;   // 2^(80/128) = 1.5459
                    7'd81:  w_result_mant = 7'd66;   // 2^(81/128) = 1.5545
                    7'd82:  w_result_mant = 7'd67;   // 2^(82/128) = 1.5633
                    7'd83:  w_result_mant = 7'd68;   // 2^(83/128) = 1.5720
                    7'd84:  w_result_mant = 7'd69;   // 2^(84/128) = 1.5809
                    7'd85:  w_result_mant = 7'd70;   // 2^(85/128) = 1.5897
                    7'd86:  w_result_mant = 7'd71;   // 2^(86/128) = 1.5987
                    7'd87:  w_result_mant = 7'd72;   // 2^(87/128) = 1.6077
                    7'd88:  w_result_mant = 7'd73;   // 2^(88/128) = 1.6168
                    7'd89:  w_result_mant = 7'd74;   // 2^(89/128) = 1.6259
                    7'd90:  w_result_mant = 7'd75;   // 2^(90/128) = 1.6350
                    7'd91:  w_result_mant = 7'd76;   // 2^(91/128) = 1.6442
                    7'd92:  w_result_mant = 7'd77;   // 2^(92/128) = 1.6535
                    7'd93:  w_result_mant = 7'd78;   // 2^(93/128) = 1.6628
                    7'd94:  w_result_mant = 7'd79;   // 2^(94/128) = 1.6722
                    7'd95:  w_result_mant = 7'd80;   // 2^(95/128) = 1.6817
                    7'd96:  w_result_mant = 7'd81;   // 2^(96/128) = 1.6910
                    7'd97:  w_result_mant = 7'd82;   // 2^(97/128) = 1.7006
                    7'd98:  w_result_mant = 7'd83;   // 2^(98/128) = 1.7101
                    7'd99:  w_result_mant = 7'd84;   // 2^(99/128) = 1.7197
                    7'd100: w_result_mant = 7'd85;   // 2^(100/128) = 1.7293
                    7'd101: w_result_mant = 7'd86;   // 2^(101/128) = 1.7391
                    7'd102: w_result_mant = 7'd87;   // 2^(102/128) = 1.7489
                    7'd103: w_result_mant = 7'd88;   // 2^(103/128) = 1.7587
                    7'd104: w_result_mant = 7'd89;   // 2^(104/128) = 1.7686
                    7'd105: w_result_mant = 7'd90;   // 2^(105/128) = 1.7786
                    7'd106: w_result_mant = 7'd91;   // 2^(106/128) = 1.7885
                    7'd107: w_result_mant = 7'd92;   // 2^(107/128) = 1.7986
                    7'd108: w_result_mant = 7'd93;   // 2^(108/128) = 1.8087
                    7'd109: w_result_mant = 7'd94;   // 2^(109/128) = 1.8189
                    7'd110: w_result_mant = 7'd95;   // 2^(110/128) = 1.8291
                    7'd111: w_result_mant = 7'd96;   // 2^(111/128) = 1.8394
                    7'd112: w_result_mant = 7'd97;   // 2^(112/128) = 1.8497
                    7'd113: w_result_mant = 7'd98;   // 2^(113/128) = 1.8601
                    7'd114: w_result_mant = 7'd99;   // 2^(114/128) = 1.8706
                    7'd115: w_result_mant = 7'd100;  // 2^(115/128) = 1.8812
                    7'd116: w_result_mant = 7'd101;  // 2^(116/128) = 1.8917
                    7'd117: w_result_mant = 7'd102;  // 2^(117/128) = 1.9024
                    7'd118: w_result_mant = 7'd103;  // 2^(118/128) = 1.9130
                    7'd119: w_result_mant = 7'd104;  // 2^(119/128) = 1.9238
                    7'd120: w_result_mant = 7'd105;  // 2^(120/128) = 1.9346
                    7'd121: w_result_mant = 7'd106;  // 2^(121/128) = 1.9455
                    7'd122: w_result_mant = 7'd107;  // 2^(122/128) = 1.9564
                    7'd123: w_result_mant = 7'd108;  // 2^(123/128) = 1.9674
                    7'd124: w_result_mant = 7'd109;  // 2^(124/128) = 1.9785
                    7'd125: w_result_mant = 7'd110;  // 2^(125/128) = 1.9896
                    7'd126: w_result_mant = 7'd111;  // 2^(126/128) = 2.0008
                    7'd127: w_result_mant = 7'd112;  // 2^(127/128) = 2.0121
                    default: w_result_mant = 7'd0;
                endcase
            end
        end
    endgenerate

    // =========================================================================
    // Adjust for floor semantics on negative inputs
    // =========================================================================
    // For negative x with frac > 0, we need floor(x), not truncate(x)
    // Example: x = -4.875 should give int = -5, frac = 0.125
    //          not int = -4, frac = 0.875
    // So: adj_int = int_part - 1, adj_frac = 256 - frac_part

    logic signed [8:0] w_adj_int_part;
    logic [7:0]        w_adj_frac_part;
    logic [LUT_ADDR_BITS-1:0] w_adj_lut_addr;
    logic [6:0]        w_adj_result_mant;

    // Apply floor adjustment for negative inputs with fractional part
    assign w_adj_int_part  = (w_sign && w_frac_part > 0) ? (w_int_part - 9'sd1) : w_int_part;
    assign w_adj_frac_part = (w_sign && w_frac_part > 0) ? (8'd0 - w_frac_part) : w_frac_part;
    assign w_adj_lut_addr  = w_adj_frac_part[7:8-LUT_ADDR_BITS];

    // LUT lookup for adjusted fractional part (for negative inputs)
    // Reuse same LUT logic with adjusted address
    generate
        if (LUT_DEPTH == 32) begin : gen_adj_lut_32
            always_comb begin
                case (w_adj_lut_addr)
                    5'd0:  w_adj_result_mant = 7'd0;    // 2^(0/32) = 1.0000
                    5'd1:  w_adj_result_mant = 7'd3;    // 2^(1/32) = 1.0219
                    5'd2:  w_adj_result_mant = 7'd6;    // 2^(2/32) = 1.0443
                    5'd3:  w_adj_result_mant = 7'd9;    // 2^(3/32) = 1.0671
                    5'd4:  w_adj_result_mant = 7'd12;   // 2^(4/32) = 1.0905
                    5'd5:  w_adj_result_mant = 7'd15;   // 2^(5/32) = 1.1144
                    5'd6:  w_adj_result_mant = 7'd18;   // 2^(6/32) = 1.1388
                    5'd7:  w_adj_result_mant = 7'd21;   // 2^(7/32) = 1.1637
                    5'd8:  w_adj_result_mant = 7'd24;   // 2^(8/32) = 1.1892
                    5'd9:  w_adj_result_mant = 7'd28;   // 2^(9/32) = 1.2152
                    5'd10: w_adj_result_mant = 7'd31;   // 2^(10/32) = 1.2419
                    5'd11: w_adj_result_mant = 7'd34;   // 2^(11/32) = 1.2691
                    5'd12: w_adj_result_mant = 7'd38;   // 2^(12/32) = 1.2968
                    5'd13: w_adj_result_mant = 7'd42;   // 2^(13/32) = 1.3252
                    5'd14: w_adj_result_mant = 7'd45;   // 2^(14/32) = 1.3543
                    5'd15: w_adj_result_mant = 7'd49;   // 2^(15/32) = 1.3839
                    5'd16: w_adj_result_mant = 7'd53;   // 2^(16/32) = 1.4142
                    5'd17: w_adj_result_mant = 7'd57;   // 2^(17/32) = 1.4452
                    5'd18: w_adj_result_mant = 7'd61;   // 2^(18/32) = 1.4768
                    5'd19: w_adj_result_mant = 7'd65;   // 2^(19/32) = 1.5092
                    5'd20: w_adj_result_mant = 7'd69;   // 2^(20/32) = 1.5422
                    5'd21: w_adj_result_mant = 7'd74;   // 2^(21/32) = 1.5760
                    5'd22: w_adj_result_mant = 7'd78;   // 2^(22/32) = 1.6105
                    5'd23: w_adj_result_mant = 7'd83;   // 2^(23/32) = 1.6458
                    5'd24: w_adj_result_mant = 7'd87;   // 2^(24/32) = 1.6818
                    5'd25: w_adj_result_mant = 7'd92;   // 2^(25/32) = 1.7186
                    5'd26: w_adj_result_mant = 7'd97;   // 2^(26/32) = 1.7563
                    5'd27: w_adj_result_mant = 7'd102;  // 2^(27/32) = 1.7947
                    5'd28: w_adj_result_mant = 7'd107;  // 2^(28/32) = 1.8340
                    5'd29: w_adj_result_mant = 7'd112;  // 2^(29/32) = 1.8742
                    5'd30: w_adj_result_mant = 7'd117;  // 2^(30/32) = 1.9152
                    5'd31: w_adj_result_mant = 7'd123;  // 2^(31/32) = 1.9571
                    default: w_adj_result_mant = 7'd0;
                endcase
            end
        end else if (LUT_DEPTH == 64) begin : gen_adj_lut_64
            always_comb begin
                case (w_adj_lut_addr)
                    6'd0:  w_adj_result_mant = 7'd0;    // 2^(0/64) = 1.0000
                    6'd1:  w_adj_result_mant = 7'd1;    // 2^(1/64) = 1.0109
                    6'd2:  w_adj_result_mant = 7'd3;    // 2^(2/64) = 1.0219
                    6'd3:  w_adj_result_mant = 7'd4;    // 2^(3/64) = 1.0330
                    6'd4:  w_adj_result_mant = 7'd6;    // 2^(4/64) = 1.0443
                    6'd5:  w_adj_result_mant = 7'd7;    // 2^(5/64) = 1.0556
                    6'd6:  w_adj_result_mant = 7'd9;    // 2^(6/64) = 1.0671
                    6'd7:  w_adj_result_mant = 7'd10;   // 2^(7/64) = 1.0788
                    6'd8:  w_adj_result_mant = 7'd12;   // 2^(8/64) = 1.0905
                    6'd9:  w_adj_result_mant = 7'd13;   // 2^(9/64) = 1.1024
                    6'd10: w_adj_result_mant = 7'd15;   // 2^(10/64) = 1.1144
                    6'd11: w_adj_result_mant = 7'd16;   // 2^(11/64) = 1.1265
                    6'd12: w_adj_result_mant = 7'd18;   // 2^(12/64) = 1.1388
                    6'd13: w_adj_result_mant = 7'd19;   // 2^(13/64) = 1.1512
                    6'd14: w_adj_result_mant = 7'd21;   // 2^(14/64) = 1.1637
                    6'd15: w_adj_result_mant = 7'd23;   // 2^(15/64) = 1.1764
                    6'd16: w_adj_result_mant = 7'd24;   // 2^(16/64) = 1.1892
                    6'd17: w_adj_result_mant = 7'd26;   // 2^(17/64) = 1.2022
                    6'd18: w_adj_result_mant = 7'd28;   // 2^(18/64) = 1.2152
                    6'd19: w_adj_result_mant = 7'd29;   // 2^(19/64) = 1.2285
                    6'd20: w_adj_result_mant = 7'd31;   // 2^(20/64) = 1.2419
                    6'd21: w_adj_result_mant = 7'd33;   // 2^(21/64) = 1.2554
                    6'd22: w_adj_result_mant = 7'd34;   // 2^(22/64) = 1.2691
                    6'd23: w_adj_result_mant = 7'd36;   // 2^(23/64) = 1.2829
                    6'd24: w_adj_result_mant = 7'd38;   // 2^(24/64) = 1.2968
                    6'd25: w_adj_result_mant = 7'd40;   // 2^(25/64) = 1.3110
                    6'd26: w_adj_result_mant = 7'd42;   // 2^(26/64) = 1.3252
                    6'd27: w_adj_result_mant = 7'd43;   // 2^(27/64) = 1.3397
                    6'd28: w_adj_result_mant = 7'd45;   // 2^(28/64) = 1.3543
                    6'd29: w_adj_result_mant = 7'd47;   // 2^(29/64) = 1.3690
                    6'd30: w_adj_result_mant = 7'd49;   // 2^(30/64) = 1.3839
                    6'd31: w_adj_result_mant = 7'd51;   // 2^(31/64) = 1.3990
                    6'd32: w_adj_result_mant = 7'd53;   // 2^(32/64) = 1.4142
                    6'd33: w_adj_result_mant = 7'd55;   // 2^(33/64) = 1.4296
                    6'd34: w_adj_result_mant = 7'd57;   // 2^(34/64) = 1.4452
                    6'd35: w_adj_result_mant = 7'd59;   // 2^(35/64) = 1.4609
                    6'd36: w_adj_result_mant = 7'd61;   // 2^(36/64) = 1.4768
                    6'd37: w_adj_result_mant = 7'd63;   // 2^(37/64) = 1.4929
                    6'd38: w_adj_result_mant = 7'd65;   // 2^(38/64) = 1.5092
                    6'd39: w_adj_result_mant = 7'd67;   // 2^(39/64) = 1.5256
                    6'd40: w_adj_result_mant = 7'd69;   // 2^(40/64) = 1.5422
                    6'd41: w_adj_result_mant = 7'd72;   // 2^(41/64) = 1.5590
                    6'd42: w_adj_result_mant = 7'd74;   // 2^(42/64) = 1.5760
                    6'd43: w_adj_result_mant = 7'd76;   // 2^(43/64) = 1.5931
                    6'd44: w_adj_result_mant = 7'd78;   // 2^(44/64) = 1.6105
                    6'd45: w_adj_result_mant = 7'd80;   // 2^(45/64) = 1.6280
                    6'd46: w_adj_result_mant = 7'd83;   // 2^(46/64) = 1.6458
                    6'd47: w_adj_result_mant = 7'd85;   // 2^(47/64) = 1.6637
                    6'd48: w_adj_result_mant = 7'd87;   // 2^(48/64) = 1.6818
                    6'd49: w_adj_result_mant = 7'd90;   // 2^(49/64) = 1.7001
                    6'd50: w_adj_result_mant = 7'd92;   // 2^(50/64) = 1.7186
                    6'd51: w_adj_result_mant = 7'd94;   // 2^(51/64) = 1.7373
                    6'd52: w_adj_result_mant = 7'd97;   // 2^(52/64) = 1.7563
                    6'd53: w_adj_result_mant = 7'd99;   // 2^(53/64) = 1.7754
                    6'd54: w_adj_result_mant = 7'd102;  // 2^(54/64) = 1.7947
                    6'd55: w_adj_result_mant = 7'd104;  // 2^(55/64) = 1.8143
                    6'd56: w_adj_result_mant = 7'd107;  // 2^(56/64) = 1.8340
                    6'd57: w_adj_result_mant = 7'd109;  // 2^(57/64) = 1.8540
                    6'd58: w_adj_result_mant = 7'd112;  // 2^(58/64) = 1.8742
                    6'd59: w_adj_result_mant = 7'd114;  // 2^(59/64) = 1.8946
                    6'd60: w_adj_result_mant = 7'd117;  // 2^(60/64) = 1.9152
                    6'd61: w_adj_result_mant = 7'd120;  // 2^(61/64) = 1.9360
                    6'd62: w_adj_result_mant = 7'd122;  // 2^(62/64) = 1.9571
                    6'd63: w_adj_result_mant = 7'd125;  // 2^(63/64) = 1.9785
                    default: w_adj_result_mant = 7'd0;
                endcase
            end
        end else begin : gen_adj_lut_128
            always_comb begin
                // Use same values as main LUT
                w_adj_result_mant = w_result_mant;  // For 128, just reuse
            end
        end
    endgenerate

    // Select the appropriate mantissa based on sign
    logic [6:0] w_final_mant;
    assign w_final_mant = w_sign ? w_adj_result_mant : w_result_mant;

    // =========================================================================
    // Compute Result Exponent
    // =========================================================================
    // Result exponent = 127 + int_part (or adj_int_part for negative)
    // Must check for overflow/underflow

    logic signed [9:0] w_result_exp_signed;
    logic [7:0]        w_result_exp;
    logic              w_overflow;
    logic              w_underflow;

    assign w_result_exp_signed = 10'sd127 + w_adj_int_part;
    assign w_overflow = (w_result_exp_signed >= 10'sd255);
    assign w_underflow = (w_result_exp_signed <= 10'sd0);
    assign w_result_exp = w_result_exp_signed[7:0];

    // =========================================================================
    // Output Assembly
    // =========================================================================
    logic [15:0] w_result;

    always_comb begin
        if (w_is_nan_input) begin
            w_result = BF16_NAN;
        end else if (w_is_zero_input) begin
            // 2^0 = 1.0
            w_result = BF16_ONE;
        end else if (w_sign && w_is_inf_input) begin
            // 2^(-inf) = 0
            w_result = BF16_ZERO;
        end else if (!w_sign && w_is_inf_input) begin
            // 2^(+inf) = +inf
            w_result = BF16_POS_INF;
        end else if (w_overflow) begin
            w_result = BF16_POS_INF;
        end else if (w_underflow) begin
            w_result = BF16_ZERO;
        end else begin
            // Normal result: positive, exp = 127 + adj_int_part, mant from LUT
            w_result = {1'b0, w_result_exp, w_final_mant};
        end
    end

    // =========================================================================
    // Outputs
    // =========================================================================
    assign ow_exp2 = w_result;
    assign ow_is_zero = w_underflow || (w_sign && w_is_inf_input);
    assign ow_is_inf = w_overflow || (!w_sign && w_is_inf_input);
    assign ow_is_nan = w_is_nan_input;

endmodule
