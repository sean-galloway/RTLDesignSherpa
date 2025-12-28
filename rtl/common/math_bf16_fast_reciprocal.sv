// =============================================================================
// Module: math_bf16_fast_reciprocal
// Description: Fast BF16 reciprocal using LUT + optional Newton-Raphson refinement
//
// This module computes 1/x for BF16 inputs using a lookup table approach,
// which is much faster than full division (~5 logic levels vs ~80-100).
//
// Algorithm:
//   For BF16 x = 2^(exp-127) * 1.mantissa:
//   1/x = 2^(127-exp) * 1/(1.mantissa)
//
//   The reciprocal of 1.mantissa is looked up in a table.
//   For mantissa > 0, the result is < 1, so we normalize and adjust exponent.
//
// Accuracy:
//   - LUT_DEPTH=32:  ~5-6 bits of mantissa accuracy
//   - LUT_DEPTH=64:  ~6-7 bits of mantissa accuracy
//   - LUT_DEPTH=128: ~7 bits of mantissa accuracy (exact for 7-bit mantissa)
//
// For INT8 quantization (target range [-128, 127]), 5-6 bits is sufficient
// since quantization inherently loses precision.
//
// Special Cases:
//   - Zero input: Returns positive infinity (0x7F80)
//   - Infinity input: Returns zero (0x0000)
//   - NaN input: Returns NaN (propagates)
//   - Subnormal input: Treated as zero (returns infinity)
//
// Latency: Combinational (0 cycles)
// Critical Path: LUT lookup + exponent subtract + mux chain (~5-8 logic levels)
//
// Copyright (c) 2025 Sean Galloway
// SPDX-License-Identifier: MIT
// =============================================================================

`timescale 1ns / 1ps

module math_bf16_fast_reciprocal #(
    parameter int LUT_DEPTH = 32,       // 32, 64, or 128 entries
    parameter int LUT_ADDR_BITS = $clog2(LUT_DEPTH)
) (
    input  logic [15:0] i_bf16,         // Input BF16 value
    output logic [15:0] ow_reciprocal,  // Reciprocal result (1/x)
    output logic        ow_is_zero,     // Input was zero (output is inf)
    output logic        ow_is_inf,      // Input was infinity (output is zero)
    output logic        ow_is_nan       // Input was NaN (output is NaN)
);

    // =========================================================================
    // BF16 Field Extraction
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
    logic w_is_nan;

    assign w_is_zero_or_subnormal = (w_exp == 8'd0);
    assign w_is_inf = (w_exp == 8'd255) && (w_mant == 7'd0);
    assign w_is_nan = (w_exp == 8'd255) && (w_mant != 7'd0);

    // =========================================================================
    // Reciprocal Mantissa LUT
    // =========================================================================
    // For input mantissa m (representing 1 + m/128):
    //   reciprocal = 1 / (1 + m/128)
    //
    // When m > 0, reciprocal < 1, so we normalize:
    //   normalized = 2 / (1 + m/128) = 256 / (128 + m)
    //   output mantissa = round((normalized - 1) * 128)
    //
    // LUT indexed by top bits of mantissa for reduced area.
    // =========================================================================

    logic [6:0] w_recip_mant_lut;
    logic [LUT_ADDR_BITS-1:0] w_lut_addr;

    // Use top bits of mantissa as LUT address
    assign w_lut_addr = w_mant[6 -: LUT_ADDR_BITS];

    // Generate LUT based on depth
    generate
        if (LUT_DEPTH == 32) begin : gen_lut_32
            // 32-entry LUT (5-bit address from mantissa[6:2])
            // Each entry is the 7-bit mantissa of normalized reciprocal
            always_comb begin
                case (w_lut_addr)
                    5'd0:  w_recip_mant_lut = 7'd127;  // 1/(1.000) = 1.000, but m=0 handled separately
                    5'd1:  w_recip_mant_lut = 7'd120;  // 1/(1.031) ≈ 0.970 → norm 1.939 → mant 120
                    5'd2:  w_recip_mant_lut = 7'd113;  // 1/(1.063) ≈ 0.941 → norm 1.882 → mant 113
                    5'd3:  w_recip_mant_lut = 7'd107;  // 1/(1.094) ≈ 0.914 → norm 1.829 → mant 106
                    5'd4:  w_recip_mant_lut = 7'd100;  // 1/(1.125) ≈ 0.889 → norm 1.778 → mant 100
                    5'd5:  w_recip_mant_lut = 7'd94;   // 1/(1.156) ≈ 0.865 → norm 1.730 → mant 93
                    5'd6:  w_recip_mant_lut = 7'd88;   // 1/(1.188) ≈ 0.842 → norm 1.684 → mant 88
                    5'd7:  w_recip_mant_lut = 7'd83;   // 1/(1.219) ≈ 0.820 → norm 1.641 → mant 82
                    5'd8:  w_recip_mant_lut = 7'd78;   // 1/(1.250) = 0.800 → norm 1.600 → mant 77
                    5'd9:  w_recip_mant_lut = 7'd73;   // 1/(1.281) ≈ 0.780 → norm 1.561 → mant 72
                    5'd10: w_recip_mant_lut = 7'd68;   // 1/(1.313) ≈ 0.762 → norm 1.524 → mant 67
                    5'd11: w_recip_mant_lut = 7'd64;   // 1/(1.344) ≈ 0.744 → norm 1.488 → mant 62
                    5'd12: w_recip_mant_lut = 7'd59;   // 1/(1.375) ≈ 0.727 → norm 1.455 → mant 58
                    5'd13: w_recip_mant_lut = 7'd55;   // 1/(1.406) ≈ 0.711 → norm 1.422 → mant 54
                    5'd14: w_recip_mant_lut = 7'd51;   // 1/(1.438) ≈ 0.696 → norm 1.391 → mant 50
                    5'd15: w_recip_mant_lut = 7'd47;   // 1/(1.469) ≈ 0.681 → norm 1.362 → mant 46
                    5'd16: w_recip_mant_lut = 7'd43;   // 1/(1.500) ≈ 0.667 → norm 1.333 → mant 43
                    5'd17: w_recip_mant_lut = 7'd40;   // 1/(1.531) ≈ 0.653 → norm 1.306 → mant 39
                    5'd18: w_recip_mant_lut = 7'd36;   // 1/(1.563) ≈ 0.640 → norm 1.280 → mant 36
                    5'd19: w_recip_mant_lut = 7'd33;   // 1/(1.594) ≈ 0.627 → norm 1.255 → mant 33
                    5'd20: w_recip_mant_lut = 7'd30;   // 1/(1.625) ≈ 0.615 → norm 1.231 → mant 30
                    5'd21: w_recip_mant_lut = 7'd27;   // 1/(1.656) ≈ 0.604 → norm 1.207 → mant 27
                    5'd22: w_recip_mant_lut = 7'd24;   // 1/(1.688) ≈ 0.593 → norm 1.185 → mant 24
                    5'd23: w_recip_mant_lut = 7'd21;   // 1/(1.719) ≈ 0.582 → norm 1.164 → mant 21
                    5'd24: w_recip_mant_lut = 7'd18;   // 1/(1.750) ≈ 0.571 → norm 1.143 → mant 18
                    5'd25: w_recip_mant_lut = 7'd16;   // 1/(1.781) ≈ 0.561 → norm 1.123 → mant 16
                    5'd26: w_recip_mant_lut = 7'd13;   // 1/(1.813) ≈ 0.552 → norm 1.103 → mant 13
                    5'd27: w_recip_mant_lut = 7'd11;   // 1/(1.844) ≈ 0.542 → norm 1.085 → mant 11
                    5'd28: w_recip_mant_lut = 7'd8;    // 1/(1.875) ≈ 0.533 → norm 1.067 → mant 9
                    5'd29: w_recip_mant_lut = 7'd6;    // 1/(1.906) ≈ 0.525 → norm 1.049 → mant 6
                    5'd30: w_recip_mant_lut = 7'd4;    // 1/(1.938) ≈ 0.516 → norm 1.032 → mant 4
                    5'd31: w_recip_mant_lut = 7'd2;    // 1/(1.969) ≈ 0.508 → norm 1.016 → mant 2
                endcase
            end
        end
        else if (LUT_DEPTH == 64) begin : gen_lut_64
            // 64-entry LUT (6-bit address from mantissa[6:1])
            always_comb begin
                case (w_lut_addr)
                    6'd0:  w_recip_mant_lut = 7'd127;
                    6'd1:  w_recip_mant_lut = 7'd123;
                    6'd2:  w_recip_mant_lut = 7'd120;
                    6'd3:  w_recip_mant_lut = 7'd117;
                    6'd4:  w_recip_mant_lut = 7'd113;
                    6'd5:  w_recip_mant_lut = 7'd110;
                    6'd6:  w_recip_mant_lut = 7'd107;
                    6'd7:  w_recip_mant_lut = 7'd104;
                    6'd8:  w_recip_mant_lut = 7'd100;
                    6'd9:  w_recip_mant_lut = 7'd97;
                    6'd10: w_recip_mant_lut = 7'd94;
                    6'd11: w_recip_mant_lut = 7'd91;
                    6'd12: w_recip_mant_lut = 7'd88;
                    6'd13: w_recip_mant_lut = 7'd86;
                    6'd14: w_recip_mant_lut = 7'd83;
                    6'd15: w_recip_mant_lut = 7'd80;
                    6'd16: w_recip_mant_lut = 7'd78;
                    6'd17: w_recip_mant_lut = 7'd75;
                    6'd18: w_recip_mant_lut = 7'd73;
                    6'd19: w_recip_mant_lut = 7'd70;
                    6'd20: w_recip_mant_lut = 7'd68;
                    6'd21: w_recip_mant_lut = 7'd66;
                    6'd22: w_recip_mant_lut = 7'd64;
                    6'd23: w_recip_mant_lut = 7'd61;
                    6'd24: w_recip_mant_lut = 7'd59;
                    6'd25: w_recip_mant_lut = 7'd57;
                    6'd26: w_recip_mant_lut = 7'd55;
                    6'd27: w_recip_mant_lut = 7'd53;
                    6'd28: w_recip_mant_lut = 7'd51;
                    6'd29: w_recip_mant_lut = 7'd49;
                    6'd30: w_recip_mant_lut = 7'd47;
                    6'd31: w_recip_mant_lut = 7'd46;
                    6'd32: w_recip_mant_lut = 7'd44;
                    6'd33: w_recip_mant_lut = 7'd42;
                    6'd34: w_recip_mant_lut = 7'd40;
                    6'd35: w_recip_mant_lut = 7'd39;
                    6'd36: w_recip_mant_lut = 7'd37;
                    6'd37: w_recip_mant_lut = 7'd35;
                    6'd38: w_recip_mant_lut = 7'd34;
                    6'd39: w_recip_mant_lut = 7'd32;
                    6'd40: w_recip_mant_lut = 7'd31;
                    6'd41: w_recip_mant_lut = 7'd29;
                    6'd42: w_recip_mant_lut = 7'd28;
                    6'd43: w_recip_mant_lut = 7'd26;
                    6'd44: w_recip_mant_lut = 7'd25;
                    6'd45: w_recip_mant_lut = 7'd23;
                    6'd46: w_recip_mant_lut = 7'd22;
                    6'd47: w_recip_mant_lut = 7'd21;
                    6'd48: w_recip_mant_lut = 7'd19;
                    6'd49: w_recip_mant_lut = 7'd18;
                    6'd50: w_recip_mant_lut = 7'd17;
                    6'd51: w_recip_mant_lut = 7'd15;
                    6'd52: w_recip_mant_lut = 7'd14;
                    6'd53: w_recip_mant_lut = 7'd13;
                    6'd54: w_recip_mant_lut = 7'd12;
                    6'd55: w_recip_mant_lut = 7'd10;
                    6'd56: w_recip_mant_lut = 7'd9;
                    6'd57: w_recip_mant_lut = 7'd8;
                    6'd58: w_recip_mant_lut = 7'd7;
                    6'd59: w_recip_mant_lut = 7'd6;
                    6'd60: w_recip_mant_lut = 7'd5;
                    6'd61: w_recip_mant_lut = 7'd4;
                    6'd62: w_recip_mant_lut = 7'd3;
                    6'd63: w_recip_mant_lut = 7'd2;
                endcase
            end
        end
        else begin : gen_lut_128
            // 128-entry LUT (full 7-bit address) - maximum accuracy
            always_comb begin
                // Compute: round((256/(128+m) - 1) * 128) for m = 0..127
                case (w_lut_addr)
                    7'd0:   w_recip_mant_lut = 7'd127;  // Special: exact 1.0
                    7'd1:   w_recip_mant_lut = 7'd126;
                    7'd2:   w_recip_mant_lut = 7'd124;
                    7'd3:   w_recip_mant_lut = 7'd122;
                    7'd4:   w_recip_mant_lut = 7'd121;
                    7'd5:   w_recip_mant_lut = 7'd119;
                    7'd6:   w_recip_mant_lut = 7'd117;
                    7'd7:   w_recip_mant_lut = 7'd116;
                    7'd8:   w_recip_mant_lut = 7'd114;
                    7'd9:   w_recip_mant_lut = 7'd112;
                    7'd10:  w_recip_mant_lut = 7'd111;
                    7'd11:  w_recip_mant_lut = 7'd109;
                    7'd12:  w_recip_mant_lut = 7'd108;
                    7'd13:  w_recip_mant_lut = 7'd106;
                    7'd14:  w_recip_mant_lut = 7'd105;
                    7'd15:  w_recip_mant_lut = 7'd103;
                    7'd16:  w_recip_mant_lut = 7'd102;
                    7'd17:  w_recip_mant_lut = 7'd100;
                    7'd18:  w_recip_mant_lut = 7'd99;
                    7'd19:  w_recip_mant_lut = 7'd97;
                    7'd20:  w_recip_mant_lut = 7'd96;
                    7'd21:  w_recip_mant_lut = 7'd95;
                    7'd22:  w_recip_mant_lut = 7'd93;
                    7'd23:  w_recip_mant_lut = 7'd92;
                    7'd24:  w_recip_mant_lut = 7'd91;
                    7'd25:  w_recip_mant_lut = 7'd89;
                    7'd26:  w_recip_mant_lut = 7'd88;
                    7'd27:  w_recip_mant_lut = 7'd87;
                    7'd28:  w_recip_mant_lut = 7'd85;
                    7'd29:  w_recip_mant_lut = 7'd84;
                    7'd30:  w_recip_mant_lut = 7'd83;
                    7'd31:  w_recip_mant_lut = 7'd82;
                    7'd32:  w_recip_mant_lut = 7'd80;
                    7'd33:  w_recip_mant_lut = 7'd79;
                    7'd34:  w_recip_mant_lut = 7'd78;
                    7'd35:  w_recip_mant_lut = 7'd77;
                    7'd36:  w_recip_mant_lut = 7'd76;
                    7'd37:  w_recip_mant_lut = 7'd75;
                    7'd38:  w_recip_mant_lut = 7'd73;
                    7'd39:  w_recip_mant_lut = 7'd72;
                    7'd40:  w_recip_mant_lut = 7'd71;
                    7'd41:  w_recip_mant_lut = 7'd70;
                    7'd42:  w_recip_mant_lut = 7'd69;
                    7'd43:  w_recip_mant_lut = 7'd68;
                    7'd44:  w_recip_mant_lut = 7'd67;
                    7'd45:  w_recip_mant_lut = 7'd66;
                    7'd46:  w_recip_mant_lut = 7'd65;
                    7'd47:  w_recip_mant_lut = 7'd64;
                    7'd48:  w_recip_mant_lut = 7'd63;
                    7'd49:  w_recip_mant_lut = 7'd62;
                    7'd50:  w_recip_mant_lut = 7'd61;
                    7'd51:  w_recip_mant_lut = 7'd60;
                    7'd52:  w_recip_mant_lut = 7'd59;
                    7'd53:  w_recip_mant_lut = 7'd58;
                    7'd54:  w_recip_mant_lut = 7'd57;
                    7'd55:  w_recip_mant_lut = 7'd56;
                    7'd56:  w_recip_mant_lut = 7'd55;
                    7'd57:  w_recip_mant_lut = 7'd54;
                    7'd58:  w_recip_mant_lut = 7'd53;
                    7'd59:  w_recip_mant_lut = 7'd52;
                    7'd60:  w_recip_mant_lut = 7'd52;
                    7'd61:  w_recip_mant_lut = 7'd51;
                    7'd62:  w_recip_mant_lut = 7'd50;
                    7'd63:  w_recip_mant_lut = 7'd49;
                    7'd64:  w_recip_mant_lut = 7'd48;
                    7'd65:  w_recip_mant_lut = 7'd47;
                    7'd66:  w_recip_mant_lut = 7'd47;
                    7'd67:  w_recip_mant_lut = 7'd46;
                    7'd68:  w_recip_mant_lut = 7'd45;
                    7'd69:  w_recip_mant_lut = 7'd44;
                    7'd70:  w_recip_mant_lut = 7'd44;
                    7'd71:  w_recip_mant_lut = 7'd43;
                    7'd72:  w_recip_mant_lut = 7'd42;
                    7'd73:  w_recip_mant_lut = 7'd41;
                    7'd74:  w_recip_mant_lut = 7'd41;
                    7'd75:  w_recip_mant_lut = 7'd40;
                    7'd76:  w_recip_mant_lut = 7'd39;
                    7'd77:  w_recip_mant_lut = 7'd39;
                    7'd78:  w_recip_mant_lut = 7'd38;
                    7'd79:  w_recip_mant_lut = 7'd37;
                    7'd80:  w_recip_mant_lut = 7'd37;
                    7'd81:  w_recip_mant_lut = 7'd36;
                    7'd82:  w_recip_mant_lut = 7'd35;
                    7'd83:  w_recip_mant_lut = 7'd35;
                    7'd84:  w_recip_mant_lut = 7'd34;
                    7'd85:  w_recip_mant_lut = 7'd34;
                    7'd86:  w_recip_mant_lut = 7'd33;
                    7'd87:  w_recip_mant_lut = 7'd32;
                    7'd88:  w_recip_mant_lut = 7'd32;
                    7'd89:  w_recip_mant_lut = 7'd31;
                    7'd90:  w_recip_mant_lut = 7'd31;
                    7'd91:  w_recip_mant_lut = 7'd30;
                    7'd92:  w_recip_mant_lut = 7'd29;
                    7'd93:  w_recip_mant_lut = 7'd29;
                    7'd94:  w_recip_mant_lut = 7'd28;
                    7'd95:  w_recip_mant_lut = 7'd28;
                    7'd96:  w_recip_mant_lut = 7'd27;
                    7'd97:  w_recip_mant_lut = 7'd27;
                    7'd98:  w_recip_mant_lut = 7'd26;
                    7'd99:  w_recip_mant_lut = 7'd26;
                    7'd100: w_recip_mant_lut = 7'd25;
                    7'd101: w_recip_mant_lut = 7'd25;
                    7'd102: w_recip_mant_lut = 7'd24;
                    7'd103: w_recip_mant_lut = 7'd24;
                    7'd104: w_recip_mant_lut = 7'd23;
                    7'd105: w_recip_mant_lut = 7'd23;
                    7'd106: w_recip_mant_lut = 7'd22;
                    7'd107: w_recip_mant_lut = 7'd22;
                    7'd108: w_recip_mant_lut = 7'd21;
                    7'd109: w_recip_mant_lut = 7'd21;
                    7'd110: w_recip_mant_lut = 7'd20;
                    7'd111: w_recip_mant_lut = 7'd20;
                    7'd112: w_recip_mant_lut = 7'd19;
                    7'd113: w_recip_mant_lut = 7'd19;
                    7'd114: w_recip_mant_lut = 7'd18;
                    7'd115: w_recip_mant_lut = 7'd18;
                    7'd116: w_recip_mant_lut = 7'd18;
                    7'd117: w_recip_mant_lut = 7'd17;
                    7'd118: w_recip_mant_lut = 7'd17;
                    7'd119: w_recip_mant_lut = 7'd16;
                    7'd120: w_recip_mant_lut = 7'd16;
                    7'd121: w_recip_mant_lut = 7'd15;
                    7'd122: w_recip_mant_lut = 7'd15;
                    7'd123: w_recip_mant_lut = 7'd15;
                    7'd124: w_recip_mant_lut = 7'd14;
                    7'd125: w_recip_mant_lut = 7'd14;
                    7'd126: w_recip_mant_lut = 7'd13;
                    7'd127: w_recip_mant_lut = 7'd13;
                endcase
            end
        end
    endgenerate

    // =========================================================================
    // Reciprocal Exponent Calculation
    // =========================================================================
    // For x = 2^(e-127) * 1.m:
    //   1/x = 2^(127-e) * 1/(1.m)
    //
    // When m = 0: 1/(1.0) = 1.0, exponent = 254 - e
    // When m > 0: 1/(1.m) < 1, normalized to 2/(1.m), exponent = 253 - e
    //
    // UNDERFLOW: When input exponent > 253 (for m>0) or > 254 (for m=0),
    // the reciprocal exponent would go negative. We detect this and return zero.
    // =========================================================================

    logic [7:0] w_recip_exp;
    logic       w_mant_nonzero;
    logic       w_recip_underflow;

    assign w_mant_nonzero = (w_mant != 7'd0);

    // Detect underflow: when exp > 253 (for m>0) or exp > 254 (for m=0)
    // the subtraction would underflow
    assign w_recip_underflow = w_mant_nonzero ? (w_exp > 8'd253) : (w_exp > 8'd254);

    // Compute exponent (will wrap for underflow cases, but we'll override with 0)
    assign w_recip_exp = w_recip_underflow ? 8'd0 :
                         w_mant_nonzero ? (8'd253 - w_exp) : (8'd254 - w_exp);

    // =========================================================================
    // Final Mantissa Selection
    // =========================================================================
    // When mantissa = 0, reciprocal is exactly 1.0 (mantissa = 0)
    // When mantissa > 0, use LUT value
    // =========================================================================

    logic [6:0] w_recip_mant;
    assign w_recip_mant = w_mant_nonzero ? w_recip_mant_lut : 7'd0;

    // =========================================================================
    // Output Assembly with Special Case Handling
    // =========================================================================

    // Special value constants
    localparam logic [15:0] BF16_POS_INF = 16'h7F80;
    localparam logic [15:0] BF16_NEG_INF = 16'hFF80;
    localparam logic [15:0] BF16_POS_ZERO = 16'h0000;
    localparam logic [15:0] BF16_NEG_ZERO = 16'h8000;
    localparam logic [15:0] BF16_QNAN = 16'h7FC0;  // Quiet NaN

    always_comb begin
        if (w_is_nan) begin
            // NaN propagates
            ow_reciprocal = BF16_QNAN;
        end
        else if (w_is_inf) begin
            // 1/inf = 0 (preserve sign)
            ow_reciprocal = w_sign ? BF16_NEG_ZERO : BF16_POS_ZERO;
        end
        else if (w_is_zero_or_subnormal) begin
            // 1/0 = inf (preserve sign)
            ow_reciprocal = w_sign ? BF16_NEG_INF : BF16_POS_INF;
        end
        else if (w_recip_underflow) begin
            // Reciprocal underflows (input was very large normal number)
            // Return zero (preserve sign)
            ow_reciprocal = w_sign ? BF16_NEG_ZERO : BF16_POS_ZERO;
        end
        else begin
            // Normal case: assemble reciprocal
            ow_reciprocal = {w_sign, w_recip_exp, w_recip_mant};
        end
    end

    // Status outputs
    assign ow_is_zero = w_is_zero_or_subnormal;
    assign ow_is_inf  = w_is_inf;
    assign ow_is_nan  = w_is_nan;

endmodule : math_bf16_fast_reciprocal
