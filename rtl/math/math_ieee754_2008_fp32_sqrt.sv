// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_ieee754_2008_fp32_sqrt
// Purpose: IEEE 754-2008 FP32 square root (Newton-Raphson reciprocal-sqrt with exact-residual RNE, 10-cycle iterative (11 for even exponents) latency)
//
// Documentation: docs/markdown/rtl-math/overview.md
// Subsystem: math
//
// Author: sean galloway
// Created: 2026-10-07
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp32_sqrt.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/math
//

`timescale 1ns / 1ps

`include "reset_defs.svh"

module math_ieee754_2008_fp32_sqrt #(
    parameter bit SUBNORMAL_SUPPORT = 1'b0  // 0: FTZ (legacy); 1: IEEE 754-2008 gradual underflow
) (
    input  logic        i_clk,
    input  logic        i_rst_n,
    input  logic [31:0] i_a,
    input  logic        i_valid,
    output logic [31:0] ow_result,
    output logic        ow_underflow,
    output logic        ow_invalid,
    output logic        ow_valid
);

// FSM states: iterative, one multiply per cycle
localparam logic [3:0] S_IDLE  = 4'd0,
                       S_U1    = 4'd1,
                       S_T1    = 4'd2,
                       S_E1R   = 4'd3,
                       S_U2    = 4'd4,
                       S_T2    = 4'd5,
                       S_E2R   = 4'd6,
                       S_Y     = 4'd7,
                       S_SCALE = 4'd8,
                       S_SQ    = 4'd9,
                       S_RNE   = 4'd10,
                       S_OUT   = 4'd11;

// Input field extraction (combinatorial, sampled at accept)
// Format: [31]=sign, [30:23]=exponent, [22:0]=mantissa

wire        w_sign_a = i_a[31];
wire [7:0]  w_exp_a  = i_a[30:23];
wire [22:0] w_mant_a = i_a[22:0];

// Special value detection

// Zero: exp=0, mant=0
wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 23'h000000);

// Subnormal: exp=0, mant!=0 (flushed to zero in FTZ mode)
wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 23'h000000);

// Infinity: exp=FF, mant=0
wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 23'h000000);

// NaN: exp=FF, mant!=0
wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 23'h000000);

// Effective zero: FTZ folds subnormals into zero
wire w_a_eff_zero = w_a_is_zero | (w_a_is_subnormal & ~SUBNORMAL_SUPPORT);

// IEEE 754-2008 special cases (priority order)
// NaN in -> canonical qNaN + invalid; sqrt(-inf) -> qNaN + invalid;
// sqrt(+inf) -> +inf; sqrt(+/-0) -> +/-0 (sign kept);
// sqrt(-x) for nonzero x -> qNaN + invalid;
// FTZ: positive subnormal input acts as +0 (no invalid).
// Declared here (before first use); assigned in the mux below
reg [31:0] w_spec_result;
reg        w_spec_invalid;

// Datapath runs only for positive, non-special operands
wire w_is_special = w_a_is_nan | w_a_is_inf | w_a_eff_zero | w_sign_a;

always_comb begin
    w_spec_result  = {w_sign_a, 8'h00, 23'h000000};
    w_spec_invalid = 1'b0;
    if (w_a_is_nan | (w_a_is_inf & w_sign_a) |
        (~w_a_is_inf & ~w_a_eff_zero & w_sign_a)) begin
        w_spec_result  = {w_sign_a, 8'hFF, 23'h400000};
        w_spec_invalid = 1'b1;
    end else if (w_a_is_inf) begin
        w_spec_result = 32'h7F800000;
    end
//     remaining cases: +/-0 and FTZ subnormal -> signed zero by default
end

// -------------------------------------------------------------------------
// Operand preparation: 24-bit significand, exponent parity,
// halved result exponent. At SUBNORMAL_SUPPORT=1 a subnormal
// operand left-normalizes into [1,2) with E_x = k-149; at =0
// subnormals never reach this path (effective zero routed to
// the special cases).
// -------------------------------------------------------------------------

// Left-shift amount for a subnormal operand: 23 - leading-bit-pos,
// last assignment wins (loop keeps the highest set bit)
logic [4:0] r_a_sub_shift;
always_comb begin
    r_a_sub_shift = 5'd0;
    for (int i = 0; i < 23; i++) begin
        if (w_mant_a[i]) r_a_sub_shift = 5'd23 - 5'(i);
    end
end

// Significand with hidden bit: subnormal operand = {1'b0, mant} << shift
wire [23:0] w_sig_a_norm = {1'b0, w_mant_a} << r_a_sub_shift;
wire [23:0] w_sig_a = SUBNORMAL_SUPPORT & w_a_is_subnormal ?
    w_sig_a_norm : {1'b1, w_mant_a};

// Effective exponent E_x (signed): subnormal operates at k-149
wire signed [10:0] w_ex_sub = -11'sd126 - $signed({6'b000000, r_a_sub_shift});
wire signed [10:0] w_ex_s = (SUBNORMAL_SUPPORT & w_a_is_subnormal) ?
    w_ex_sub : ($signed({3'b000, w_exp_a}) - 11'sd127);

// Exponent parity (two's-complement LSB == floor-mod-2) and the
// halved biased result exponent e_r = floor(E_x/2) + 127
wire w_g = w_ex_s[0];
wire signed [10:0] w_er_s = (w_ex_s >>> 1) + 11'sd127;

// Registered operands and datapath state
logic [3:0]   r_state;
logic [23:0]  r_s24;
logic         r_g;
logic [8:0]   r_er;
logic [23:0]  r_r0, r_u1, r_t1, r_r1, r_u2, r_t2, r_r2;
logic [23:0]  r_yc, r_y0;
logic [47:0]  r_sq;     // S_SQ: exact biased-root square
logic [31:0]  r_result;
logic         r_underflow, r_invalid, r_owv;

// Newton factor: e = 3/2 - b*r^2/2 at the 2^23 scale
// (t = b*r^2 at 2^23; exhaustively verified: e stays in
// [2^23/2, 2^24) so its own bit 23 is the true hidden bit on
// the multiplier B port)
wire [24:0] w_e1_full = 25'h0C00000 - {1'b0, r_t1};
wire [24:0] w_e2_full = 25'h0C00000 - {1'b0, r_t2};
wire [23:0] w_e1 = w_e1_full[23:0];
wire [23:0] w_e2 = w_e2_full[23:0];

// Shared product tail: refine products (r*e, b*r2) and the
// 1/sqrt(2) scale all add 2^22 then drop 23 bits; saturated
wire [48:0] w_ref_sum  = {1'b0, w_prod} + 49'h00000400000;
wire [25:0] w_ref_wide = w_ref_sum[48:23];
wire [23:0] w_ref_sat  = w_ref_wide[24] ? 24'hFFFFFF :
                                         w_ref_wide[23:0];
wire [23:0] w_ref_usat = w_ref_wide[23:0];

// t-stage rounding: t = (b*u + 2^24) >> 25
wire [48:0] w_t_sum = {1'b0, w_prod} + 49'h000001000000;
// -------------------------------------------------------------------------
// Reciprocal-sqrt seed LUT: 7-bit index (significand
// S[22:16]), 12-bit bucket-center entries targeting
// r* = 2^23*sqrt(2/b) so every seed keeps its true hidden bit.
// Measured |r0/r0* - 1| <= 2^-8 class at every bucket end; two
// Newton refinements follow (exhaustively bounded at generate
// time over all 2^24 significands).
// -------------------------------------------------------------------------

logic [11:0] r_lut_val;
// Index mux: operand is live at accept, registered afterwards
wire [6:0] w_lut_idx =
    (r_state == S_IDLE) ? w_sig_a[22:16] : r_s24[22:16];
always_comb begin
    case (w_lut_idx)
        7'd0: r_lut_val = 12'hB4B;
        7'd1: r_lut_val = 12'hB3F;
        7'd2: r_lut_val = 12'hB34;
        7'd3: r_lut_val = 12'hB2A;
        7'd4: r_lut_val = 12'hB1F;
        7'd5: r_lut_val = 12'hB14;
        7'd6: r_lut_val = 12'hB09;
        7'd7: r_lut_val = 12'hAFF;
        7'd8: r_lut_val = 12'hAF5;
        7'd9: r_lut_val = 12'hAEA;
        7'd10: r_lut_val = 12'hAE0;
        7'd11: r_lut_val = 12'hAD6;
        7'd12: r_lut_val = 12'hACC;
        7'd13: r_lut_val = 12'hAC3;
        7'd14: r_lut_val = 12'hAB9;
        7'd15: r_lut_val = 12'hAAF;
        7'd16: r_lut_val = 12'hAA6;
        7'd17: r_lut_val = 12'hA9D;
        7'd18: r_lut_val = 12'hA93;
        7'd19: r_lut_val = 12'hA8A;
        7'd20: r_lut_val = 12'hA81;
        7'd21: r_lut_val = 12'hA78;
        7'd22: r_lut_val = 12'hA6F;
        7'd23: r_lut_val = 12'hA66;
        7'd24: r_lut_val = 12'hA5D;
        7'd25: r_lut_val = 12'hA55;
        7'd26: r_lut_val = 12'hA4C;
        7'd27: r_lut_val = 12'hA44;
        7'd28: r_lut_val = 12'hA3B;
        7'd29: r_lut_val = 12'hA33;
        7'd30: r_lut_val = 12'hA2B;
        7'd31: r_lut_val = 12'hA23;
        7'd32: r_lut_val = 12'hA1A;
        7'd33: r_lut_val = 12'hA12;
        7'd34: r_lut_val = 12'hA0B;
        7'd35: r_lut_val = 12'hA03;
        7'd36: r_lut_val = 12'h9FB;
        7'd37: r_lut_val = 12'h9F3;
        7'd38: r_lut_val = 12'h9EB;
        7'd39: r_lut_val = 12'h9E4;
        7'd40: r_lut_val = 12'h9DC;
        7'd41: r_lut_val = 12'h9D5;
        7'd42: r_lut_val = 12'h9CE;
        7'd43: r_lut_val = 12'h9C6;
        7'd44: r_lut_val = 12'h9BF;
        7'd45: r_lut_val = 12'h9B8;
        7'd46: r_lut_val = 12'h9B1;
        7'd47: r_lut_val = 12'h9A9;
        7'd48: r_lut_val = 12'h9A2;
        7'd49: r_lut_val = 12'h99C;
        7'd50: r_lut_val = 12'h995;
        7'd51: r_lut_val = 12'h98E;
        7'd52: r_lut_val = 12'h987;
        7'd53: r_lut_val = 12'h980;
        7'd54: r_lut_val = 12'h97A;
        7'd55: r_lut_val = 12'h973;
        7'd56: r_lut_val = 12'h96C;
        7'd57: r_lut_val = 12'h966;
        7'd58: r_lut_val = 12'h95F;
        7'd59: r_lut_val = 12'h959;
        7'd60: r_lut_val = 12'h953;
        7'd61: r_lut_val = 12'h94C;
        7'd62: r_lut_val = 12'h946;
        7'd63: r_lut_val = 12'h940;
        7'd64: r_lut_val = 12'h93A;
        7'd65: r_lut_val = 12'h934;
        7'd66: r_lut_val = 12'h92E;
        7'd67: r_lut_val = 12'h928;
        7'd68: r_lut_val = 12'h922;
        7'd69: r_lut_val = 12'h91C;
        7'd70: r_lut_val = 12'h916;
        7'd71: r_lut_val = 12'h910;
        7'd72: r_lut_val = 12'h90A;
        7'd73: r_lut_val = 12'h904;
        7'd74: r_lut_val = 12'h8FF;
        7'd75: r_lut_val = 12'h8F9;
        7'd76: r_lut_val = 12'h8F3;
        7'd77: r_lut_val = 12'h8EE;
        7'd78: r_lut_val = 12'h8E8;
        7'd79: r_lut_val = 12'h8E3;
        7'd80: r_lut_val = 12'h8DD;
        7'd81: r_lut_val = 12'h8D8;
        7'd82: r_lut_val = 12'h8D3;
        7'd83: r_lut_val = 12'h8CD;
        7'd84: r_lut_val = 12'h8C8;
        7'd85: r_lut_val = 12'h8C3;
        7'd86: r_lut_val = 12'h8BD;
        7'd87: r_lut_val = 12'h8B8;
        7'd88: r_lut_val = 12'h8B3;
        7'd89: r_lut_val = 12'h8AE;
        7'd90: r_lut_val = 12'h8A9;
        7'd91: r_lut_val = 12'h8A4;
        7'd92: r_lut_val = 12'h89F;
        7'd93: r_lut_val = 12'h89A;
        7'd94: r_lut_val = 12'h895;
        7'd95: r_lut_val = 12'h890;
        7'd96: r_lut_val = 12'h88B;
        7'd97: r_lut_val = 12'h886;
        7'd98: r_lut_val = 12'h881;
        7'd99: r_lut_val = 12'h87C;
        7'd100: r_lut_val = 12'h878;
        7'd101: r_lut_val = 12'h873;
        7'd102: r_lut_val = 12'h86E;
        7'd103: r_lut_val = 12'h86A;
        7'd104: r_lut_val = 12'h865;
        7'd105: r_lut_val = 12'h860;
        7'd106: r_lut_val = 12'h85C;
        7'd107: r_lut_val = 12'h857;
        7'd108: r_lut_val = 12'h853;
        7'd109: r_lut_val = 12'h84E;
        7'd110: r_lut_val = 12'h84A;
        7'd111: r_lut_val = 12'h845;
        7'd112: r_lut_val = 12'h841;
        7'd113: r_lut_val = 12'h83D;
        7'd114: r_lut_val = 12'h838;
        7'd115: r_lut_val = 12'h834;
        7'd116: r_lut_val = 12'h830;
        7'd117: r_lut_val = 12'h82B;
        7'd118: r_lut_val = 12'h827;
        7'd119: r_lut_val = 12'h823;
        7'd120: r_lut_val = 12'h81F;
        7'd121: r_lut_val = 12'h81B;
        7'd122: r_lut_val = 12'h816;
        7'd123: r_lut_val = 12'h812;
        7'd124: r_lut_val = 12'h80E;
        7'd125: r_lut_val = 12'h80A;
        7'd126: r_lut_val = 12'h806;
        7'd127: r_lut_val = 12'h802;
        default: r_lut_val = 12'h000;
    endcase
end

// -------------------------------------------------------------------------
// Shared significand multiplier: one 24x24 Dadda multiply per
// FSM cycle (Newton u/t/refine stages, the final y = b*r2, the
// 1/sqrt(2) even-exponent scale, and the exact residual square
// all reuse this instance). i_*_is_normal IS the operand hidden
// bit, so each operand presents its own bit 23 in EVERY state:
// the 1/sqrt(2) constant is 0x5A827A < 2^23 (own bit 23 = 0),
// and the biased root y0 can sit at or below 2^23 (own bit 23
// may be 0). A hardwired 1 would graft a phantom hidden bit and
// corrupt the exact residual -- the divider slice's root-cause
// lesson. The exhaustive proof in verify_accuracy_bounds
// assumes exactly this reconstruction (plain 24x24 products).
// -------------------------------------------------------------------------

logic [22:0] w_mult_a;
logic [22:0] w_mult_b;
wire [47:0] w_prod;

math_ieee754_2008_fp32_mantissa_mult u_mant_mult (
    .i_mant_a(w_mult_a),
    .i_mant_b(w_mult_b),
//     hidden-bit semantics per operand: i_*_is_normal IS the
//     operand hidden bit, so EVERY state presents its own bit 23
    .i_a_is_normal((r_state == S_SCALE) ? r_yc[23]   :
                   (r_state == S_SQ)    ? r_y0[23]   :
                   (r_state == S_T1)    ? r_s24[23]  :
                   (r_state == S_T2)    ? r_s24[23]  :
                   (r_state == S_Y)     ? r_s24[23]  :
                   (r_state == S_E1R)   ? r_r0[23]   :
                   (r_state == S_E2R)   ? r_r1[23]   :
                   (r_state == S_U1)    ? r_r0[23]   :
                   (r_state == S_U2)    ? r_r1[23]   : 1'b1),
//     S_SCALE B port: the 1/sqrt(2) constant's OWN bit 23 (=0)
    .i_b_is_normal((r_state == S_SCALE) ? 1'b0       :
                   (r_state == S_SQ)    ? r_y0[23]   :
                   (r_state == S_T1)    ? r_u1[23]   :
                   (r_state == S_T2)    ? r_u2[23]   :
                   (r_state == S_Y)     ? r_r2[23]   :
                   (r_state == S_E1R)   ? w_e1[23]   :
                   (r_state == S_E2R)   ? w_e2[23]   :
                   (r_state == S_U1)    ? r_r0[23]   :
                   (r_state == S_U2)    ? r_r1[23]   : 1'b1),
    .ow_product(w_prod),
    .ow_needs_norm(),
    .ow_mant_out(),
    .ow_guard_bit(),
    .ow_round_bit(),
    .ow_sticky_bit()
);

// Multiplier operand mux (registered values only)
always_comb begin
    w_mult_a = 23'h000000;
    w_mult_b = 23'h000000;
    case (r_state)
        S_U1: begin
            w_mult_a = r_r0[22:0];
            w_mult_b = r_r0[22:0];
        end
        S_T1: begin
            w_mult_a = r_s24[22:0];
            w_mult_b = r_u1[22:0];
        end
        S_E1R: begin
            w_mult_a = r_r0[22:0];
            w_mult_b = w_e1[22:0];
        end
        S_U2: begin
            w_mult_a = r_r1[22:0];
            w_mult_b = r_r1[22:0];
        end
        S_T2: begin
            w_mult_a = r_s24[22:0];
            w_mult_b = r_u2[22:0];
        end
        S_E2R: begin
            w_mult_a = r_r1[22:0];
            w_mult_b = w_e2[22:0];
        end
        S_Y: begin
            w_mult_a = r_s24[22:0];
            w_mult_b = r_r2[22:0];
        end
        S_SCALE: begin
//             even exponents: scale the significand root by
//             1/sqrt(2) = 0x5A827A (own bit 23 = 0, see above)
            w_mult_a = r_yc[22:0];
            w_mult_b = 23'h5A827A;
        end
        S_SQ: begin
//             exact residual: square of the biased root
            w_mult_a = r_y0[22:0];
            w_mult_b = r_y0[22:0];
        end
        default: begin
            w_mult_a = 23'h000000;
            w_mult_b = 23'h000000;
        end
    endcase
end

// -------------------------------------------------------------------------
// Exact residual rounding (S_RNE, combinational)

// rem = W - y0^2 in [0, 15*2y0) exactly (W = S<<(23+g) is the
// exact radicand). A 4-stage binary chain (8, 4, 2, 1) tests
// (y0+k+step)^2 <= W with incremental squares -- exact integer
// compares -- so Y_base = y0+k with (Y_base+1)^2 > W. Round up
// iff rem' = W - Y_base^2 >= Y_base+1, i.e. Y_real >= Y_base+1/2.
// Half-ULP ties can NEVER occur (W is an integer, (k+1/2)^2 is
// not), so RNE degenerates to exact round-to-nearest with TRUE
// sticky (inexact = rem' != 0). No unfaithful last bit.
// -------------------------------------------------------------------------

// Exact radicand W = S << (23+g): 48 bits either parity
wire [47:0] w_wp = r_g ? {r_s24, 24'h000000} :
                        {1'b0, r_s24, 23'h000000};
wire [48:0] w_rem = {1'b0, w_wp} - {1'b0, r_sq};  // >= 0 by proof

// 4-stage binary square-test chain (every stage explicit)
logic [24:0] w_kc;    // running y0+k
logic [48:0] w_ksq;   // running (y0+k)^2
always_comb begin
    w_kc  = {1'b0, r_y0};
    w_ksq = {1'b0, r_sq};
//     step 8: (cur+8)^2 = cursq + (cur<<4) + 64
    if ((w_ksq + {20'b00000000000000000000, w_kc, 4'b0000} + 49'd64) <= {1'b0, w_wp}) begin
        w_ksq = w_ksq + {20'b00000000000000000000, w_kc, 4'b0000} + 49'd64;
        w_kc = w_kc + 25'd8;
    end
//     step 4: (cur+4)^2 = cursq + (cur<<3) + 16
    if ((w_ksq + {21'b000000000000000000000, w_kc, 3'b000} + 49'd16) <= {1'b0, w_wp}) begin
        w_ksq = w_ksq + {21'b000000000000000000000, w_kc, 3'b000} + 49'd16;
        w_kc = w_kc + 25'd4;
    end
//     step 2: (cur+2)^2 = cursq + (cur<<2) + 4
    if ((w_ksq + {22'b0000000000000000000000, w_kc, 2'b00} + 49'd4) <= {1'b0, w_wp}) begin
        w_ksq = w_ksq + {22'b0000000000000000000000, w_kc, 2'b00} + 49'd4;
        w_kc = w_kc + 25'd2;
    end
//     step 1: (cur+1)^2 = cursq + (cur<<1) + 1
    if ((w_ksq + {23'b00000000000000000000000, w_kc, 1'b0} + 49'd1) <= {1'b0, w_wp}) begin
        w_ksq = w_ksq + {23'b00000000000000000000000, w_kc, 1'b0} + 49'd1;
        w_kc = w_kc + 25'd1;
    end
end

wire [48:0] w_remp  = {1'b0, w_wp} - w_ksq;        // in [0, 2*Y_base]
wire        w_ru    = (w_remp >= {24'b000000000000000000000000, w_kc} + 49'd1);
wire [25:0] w_yf    = {1'b0, w_kc} + {25'b0000000000000000000000000, w_ru};
wire        w_carry = w_yf[24];                   // rounding carry out
wire [23:0] w_ysig  = w_carry ? 24'h800000 : w_yf[23:0];
wire        w_inexact = (w_remp != 49'd0);

// Result exponent: e_r + carry (carry out of the significand)
wire [9:0] w_er_f = {1'b0, r_er} + {9'b000000000, w_carry};
wire [31:0] w_out_result = {1'b0, w_er_f[7:0], w_ysig[22:0]};

// -------------------------------------------------------------------------
// Multi-cycle FSM: 10 cycles accept-to-ow_valid on the odd-
// exponent path (11 for even exponents, which need the
// 1/sqrt(2) significand-scale cycle), 1 cycle for special
// cases. ow_valid pulses for exactly one cycle.
// -------------------------------------------------------------------------

assign ow_result    = r_result;
assign ow_underflow = r_underflow;  // tied low: sqrt never underflows
assign ow_invalid   = r_invalid;
assign ow_valid     = r_owv;

`ALWAYS_FF_RST(i_clk, i_rst_n,
        if (`RST_ASSERTED(i_rst_n)) begin
            r_state     <= S_IDLE;
            r_owv       <= 1'b0;
            r_result    <= 32'h00000000;
            r_underflow <= 1'b0;
            r_invalid   <= 1'b0;
            r_s24       <= 24'h000000;
            r_g         <= 1'b0;
            r_er        <= 9'd0;
            r_r0        <= 24'h000000;
            r_u1        <= 24'h000000;
            r_t1        <= 24'h000000;
            r_r1        <= 24'h000000;
            r_u2        <= 24'h000000;
            r_t2        <= 24'h000000;
            r_r2        <= 24'h000000;
            r_yc        <= 24'h000000;
            r_y0        <= 24'h000000;
            r_sq        <= 48'h000000000000;
        end else begin
            r_owv <= 1'b0;
            case (r_state)
                S_IDLE: begin
                    if (i_valid) begin
                        if (w_is_special) begin
                            r_result    <= w_spec_result;
                            r_underflow <= 1'b0;
                            r_invalid   <= w_spec_invalid;
                            r_owv       <= 1'b1;
                            r_state     <= S_OUT;
                        end else begin
                            r_s24 <= w_sig_a;
                            r_g   <= w_g;
                            r_er  <= w_er_s[8:0];
                            r_r0  <= {r_lut_val, 12'h000};
                            r_state <= S_U1;
                        end
                    end
                end
    
                S_U1: begin
    //                 // u1 = trunc(r0^2 * 2^-23), 24-bit operand
                    r_u1    <= w_prod[46:23];
                    r_state <= S_T1;
                end
    
                S_T1: begin
    //                 // t1 = round(b*r0^2) at the 2^23 scale
                    r_t1    <= w_t_sum[48:25];
                    r_state <= S_E1R;
                end
    
                S_E1R: begin
    //                 // r1 = round(r0*e1); saturate at 2^24-1
                    r_r1    <= w_ref_sat;
                    r_state <= S_U2;
                end
    
                S_U2: begin
                    r_u2    <= w_prod[46:23];
                    r_state <= S_T2;
                end
    
                S_T2: begin
                    r_t2    <= w_t_sum[48:25];
                    r_state <= S_E2R;
                end
    
                S_E2R: begin
                    r_r2    <= w_ref_sat;
                    r_state <= S_Y;
                end
    
                S_Y: begin
    //                 // yc = round(b*r2) ~ 2^23*sqrt(2b), saturated;
    //                 // odd exponents (g=1): y0 = yc - BIAS, scale skipped
                    r_yc    <= w_ref_sat;
                    if (r_g) begin
                        r_y0    <= w_ref_sat - 24'd8;
                        r_state <= S_SQ;
                    end else begin
                        r_state <= S_SCALE;
                    end
                end
    
                S_SCALE: begin
    //                 // even exponent: y0 = round(yc/sqrt(2)) - BIAS
                    r_y0    <= w_ref_usat - 24'd8;
                    r_state <= S_SQ;
                end
    
                S_SQ: begin
    //                 // exact square of the biased root for the residual
                    r_sq    <= w_prod;
                    r_state <= S_RNE;
                end
    
                S_RNE: begin
                    r_result    <= w_out_result;
                    r_underflow <= 1'b0;  // tiny-after-rounding impossible
                    r_invalid   <= 1'b0;
                    r_owv       <= 1'b1;
                    r_state     <= S_OUT;
                end
    
                S_OUT: begin
                    r_state <= S_IDLE;
                end
    
                default: begin
                    r_state <= S_IDLE;
                end
            endcase
        end
)

endmodule
