// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: math_ieee754_2008_fp32_divider
// Purpose: IEEE 754-2008 FP32 divider (Goldschmidt-class multiplicative divide with exact-residual RNE, 9-cycle iterative (10 for subnormal-grid) latency)
//
// Documentation: docs/markdown/rtl-math/overview.md
// Subsystem: math
//
// Author: sean galloway
// Created: 2026-10-07
//
// AUTO-GENERATED FILE - DO NOT EDIT MANUALLY
// Generator: bin/rtl_generators/ieee754/fp32_divider.py
// Regenerate: PYTHONPATH=bin:$PYTHONPATH python3 bin/rtl_generators/ieee754/generate_all.py rtl/math
//

`timescale 1ns / 1ps

`include "reset_defs.svh"

module math_ieee754_2008_fp32_divider #(
    parameter bit SUBNORMAL_SUPPORT = 1'b0  // 0: FTZ (legacy); 1: IEEE 754-2008 gradual underflow
) (
    input  logic        i_clk,
    input  logic        i_rst_n,
    input  logic [31:0] i_a,
    input  logic [31:0] i_b,
    input  logic        i_valid,
    output logic [31:0] ow_result,
    output logic        ow_overflow,
    output logic        ow_underflow,
    output logic        ow_invalid,
    output logic        ow_valid
);

// FSM states: iterative, one multiply per cycle
localparam logic [3:0] S_IDLE  = 4'd0,
                       S_LUT   = 4'd1,
                       S_NR1A  = 4'd2,
                       S_NR1B  = 4'd3,
                       S_NR2A  = 4'd4,
                       S_NR2B  = 4'd5,
                       S_Q0    = 4'd6,
                       S_REM   = 4'd7,
                       S_RNE   = 4'd8,
                       S_OUT   = 4'd9,
                       S_SUBN  = 4'd10;

// Input field extraction (combinatorial, sampled at accept)
// Format: [31]=sign, [30:23]=exponent, [22:0]=mantissa

wire        w_sign_a = i_a[31];
wire [7:0]  w_exp_a  = i_a[30:23];
wire [22:0] w_mant_a = i_a[22:0];

wire        w_sign_b = i_b[31];
wire [7:0]  w_exp_b  = i_b[30:23];
wire [22:0] w_mant_b = i_b[22:0];

// Special value detection

// Zero: exp=0, mant=0
wire w_a_is_zero = (w_exp_a == 8'h00) & (w_mant_a == 23'h000000);
wire w_b_is_zero = (w_exp_b == 8'h00) & (w_mant_b == 23'h000000);

// Subnormal: exp=0, mant!=0 (flushed to zero in FTZ mode)
wire w_a_is_subnormal = (w_exp_a == 8'h00) & (w_mant_a != 23'h000000);
wire w_b_is_subnormal = (w_exp_b == 8'h00) & (w_mant_b != 23'h000000);

// Infinity: exp=FF, mant=0
wire w_a_is_inf = (w_exp_a == 8'hFF) & (w_mant_a == 23'h000000);
wire w_b_is_inf = (w_exp_b == 8'hFF) & (w_mant_b == 23'h000000);

// NaN: exp=FF, mant!=0
wire w_a_is_nan = (w_exp_a == 8'hFF) & (w_mant_a != 23'h000000);
wire w_b_is_nan = (w_exp_b == 8'hFF) & (w_mant_b != 23'h000000);

// Effective zero: FTZ folds subnormals into zero; with
// SUBNORMAL_SUPPORT=1 only true zeros are effective zero
wire w_a_eff_zero = w_a_is_zero | (w_a_is_subnormal & ~SUBNORMAL_SUPPORT);
wire w_b_eff_zero = w_b_is_zero | (w_b_is_subnormal & ~SUBNORMAL_SUPPORT);

// Result sign: XOR of input signs (all non-NaN results)
wire w_sign_result = w_sign_a ^ w_sign_b;

// IEEE 754-2008 special cases (priority order)
// NaN in -> canonical qNaN + invalid; 0/0 and inf/inf -> qNaN + invalid;
// x/0 -> inf; 0/x -> zero; inf/x -> inf; x/inf -> zero
// Declared here (before first use); assigned in the mux below
reg [31:0] w_spec_result;
reg        w_spec_invalid;

wire w_any_nan   = w_a_is_nan | w_b_is_nan;
wire w_zero_zero = w_a_eff_zero & w_b_eff_zero;
wire w_inf_inf   = w_a_is_inf & w_b_is_inf;
wire w_is_special = w_any_nan | w_zero_zero | w_inf_inf |
    w_a_eff_zero | w_b_eff_zero | w_a_is_inf | w_b_is_inf;

always_comb begin
    w_spec_result  = {w_sign_result, 8'h00, 23'h000000};
    w_spec_invalid = 1'b0;
    if (w_any_nan | w_zero_zero | w_inf_inf) begin
        w_spec_result  = {w_sign_result, 8'hFF, 23'h400000};
        w_spec_invalid = 1'b1;
    end else if (w_b_eff_zero | w_a_is_inf) begin
        w_spec_result = {w_sign_result, 8'hFF, 23'h000000};
    end
//     remaining cases (w_a_eff_zero | w_b_is_inf) -> signed zero by default
end

// -------------------------------------------------------------------------
// Operand preparation: 24-bit significands, signed effective
// exponents. At SUBNORMAL_SUPPORT=1 a subnormal operand is
// left-normalized into [1,2) with exponent debit k-22; at =0
// subnormals never reach this path (effective zero routed to
// the special cases).
// -------------------------------------------------------------------------

// Left-shift amount for a subnormal operand: 23 - leading-bit-pos,
// last assignment wins (loop keeps the highest set bit)
logic [4:0] r_a_sub_shift;
logic [4:0] r_b_sub_shift;
always_comb begin
    r_a_sub_shift = 5'd0;
    for (int i = 0; i < 23; i++) begin
        if (w_mant_a[i]) r_a_sub_shift = 5'd23 - 5'(i);
    end
    r_b_sub_shift = 5'd0;
    for (int i = 0; i < 23; i++) begin
        if (w_mant_b[i]) r_b_sub_shift = 5'd23 - 5'(i);
    end
end

// Significands with hidden bit: subnormal operand = {1'b0, mant} << shift
wire [23:0] w_sig_a_norm = {1'b0, w_mant_a} << r_a_sub_shift;
wire [23:0] w_sig_b_norm = {1'b0, w_mant_b} << r_b_sub_shift;
wire [23:0] w_sig_a = SUBNORMAL_SUPPORT & w_a_is_subnormal ?
    w_sig_a_norm : {1'b1, w_mant_a};
wire [23:0] w_sig_b = SUBNORMAL_SUPPORT & w_b_is_subnormal ?
    w_sig_b_norm : {1'b1, w_mant_b};

// Effective biased exponents: subnormal operates at 1 - shift
wire signed [9:0] w_ea_sub = 10'sd1 - $signed({5'b00000, r_a_sub_shift});
wire signed [9:0] w_eb_sub = 10'sd1 - $signed({5'b00000, r_b_sub_shift});
wire signed [9:0] w_ea_s = (SUBNORMAL_SUPPORT & w_a_is_subnormal) ?
    w_ea_sub : $signed({2'b00, w_exp_a});
wire signed [9:0] w_eb_s = (SUBNORMAL_SUPPORT & w_b_is_subnormal) ?
    w_eb_sub : $signed({2'b00, w_exp_b});

// Quotient significand ratio < 1: debit one exponent, track via r_half
wire w_half = (w_sig_a < w_sig_b);

// Registered operands and datapath state
logic [3:0]   r_state;
logic [23:0]  r_a24, r_b24;
logic signed [9:0] r_ea_s, r_eb_s;
logic         r_sign, r_half;
logic [23:0]  r_r0, r_t1, r_r1, r_t2, r_r2, r_q0;
logic [27:0]  r_rem;
logic [47:0]  r_mprod;   // S_RNE: exact m*B for the grid compare
logic [27:0]  r_red;     // S_RNE: exact residual remainder
logic [23:0]  r_qbase;   // S_RNE: exact quotient integer part
logic [4:0]   r_sh;      // S_RNE: subnormal grid shift
logic [31:0]  r_result;
logic         r_overflow, r_underflow, r_invalid, r_owv;

// Newton factors: e = 2 - t, t = trunc(B*r) at 2^-23
wire [24:0] w_e1_full = 25'h1000000 - {1'b0, r_t1};
wire [24:0] w_e2_full = 25'h1000000 - {1'b0, r_t2};
wire [23:0] w_e1 = w_e1_full[23:0];
wire [23:0] w_e2 = w_e2_full[23:0];

// Newton refine products: (r*e + 2^22) >> 23, saturated at 2^24-1
wire [47:0] w_re_sum = w_prod + 48'h000000400000;
wire [24:0] w_r1_wide = w_re_sum[47:23];
wire [24:0] w_r2_wide = w_re_sum[47:23];

// -------------------------------------------------------------------------
// Reciprocal seed LUT: 7-bit index (divisor
// significand B[22:16]), 12-bit bucket-center entries,
// saturated so R0 = entry<<12 stays below 2^24. Measured
// |r0*b - 1| <= 2^-7.96 at every bucket end; two Newton
// refinements follow (exhaustively bounded at generate time).
// -------------------------------------------------------------------------

logic [11:0] r_lut_val;
// Index mux: divisor is live at accept, registered afterwards
wire [6:0] w_lut_idx =
    (r_state == S_IDLE) ? w_sig_b[22:16] : r_b24[22:16];
always_comb begin
    case (w_lut_idx)
        7'd0: r_lut_val = 12'hFF0;
        7'd1: r_lut_val = 12'hFD1;
        7'd2: r_lut_val = 12'hFB2;
        7'd3: r_lut_val = 12'hF93;
        7'd4: r_lut_val = 12'hF75;
        7'd5: r_lut_val = 12'hF57;
        7'd6: r_lut_val = 12'hF3A;
        7'd7: r_lut_val = 12'hF1D;
        7'd8: r_lut_val = 12'hF01;
        7'd9: r_lut_val = 12'hEE5;
        7'd10: r_lut_val = 12'hEC9;
        7'd11: r_lut_val = 12'hEAE;
        7'd12: r_lut_val = 12'hE94;
        7'd13: r_lut_val = 12'hE79;
        7'd14: r_lut_val = 12'hE5F;
        7'd15: r_lut_val = 12'hE46;
        7'd16: r_lut_val = 12'hE2C;
        7'd17: r_lut_val = 12'hE13;
        7'd18: r_lut_val = 12'hDFB;
        7'd19: r_lut_val = 12'hDE2;
        7'd20: r_lut_val = 12'hDCB;
        7'd21: r_lut_val = 12'hDB3;
        7'd22: r_lut_val = 12'hD9C;
        7'd23: r_lut_val = 12'hD85;
        7'd24: r_lut_val = 12'hD6E;
        7'd25: r_lut_val = 12'hD58;
        7'd26: r_lut_val = 12'hD41;
        7'd27: r_lut_val = 12'hD2C;
        7'd28: r_lut_val = 12'hD16;
        7'd29: r_lut_val = 12'hD01;
        7'd30: r_lut_val = 12'hCEC;
        7'd31: r_lut_val = 12'hCD7;
        7'd32: r_lut_val = 12'hCC3;
        7'd33: r_lut_val = 12'hCAE;
        7'd34: r_lut_val = 12'hC9A;
        7'd35: r_lut_val = 12'hC87;
        7'd36: r_lut_val = 12'hC73;
        7'd37: r_lut_val = 12'hC60;
        7'd38: r_lut_val = 12'hC4D;
        7'd39: r_lut_val = 12'hC3A;
        7'd40: r_lut_val = 12'hC28;
        7'd41: r_lut_val = 12'hC15;
        7'd42: r_lut_val = 12'hC03;
        7'd43: r_lut_val = 12'hBF1;
        7'd44: r_lut_val = 12'hBDF;
        7'd45: r_lut_val = 12'hBCE;
        7'd46: r_lut_val = 12'hBBD;
        7'd47: r_lut_val = 12'hBAB;
        7'd48: r_lut_val = 12'hB9A;
        7'd49: r_lut_val = 12'hB8A;
        7'd50: r_lut_val = 12'hB79;
        7'd51: r_lut_val = 12'hB69;
        7'd52: r_lut_val = 12'hB59;
        7'd53: r_lut_val = 12'hB49;
        7'd54: r_lut_val = 12'hB39;
        7'd55: r_lut_val = 12'hB29;
        7'd56: r_lut_val = 12'hB1A;
        7'd57: r_lut_val = 12'hB0A;
        7'd58: r_lut_val = 12'hAFB;
        7'd59: r_lut_val = 12'hAEC;
        7'd60: r_lut_val = 12'hADD;
        7'd61: r_lut_val = 12'hACF;
        7'd62: r_lut_val = 12'hAC0;
        7'd63: r_lut_val = 12'hAB2;
        7'd64: r_lut_val = 12'hAA4;
        7'd65: r_lut_val = 12'hA95;
        7'd66: r_lut_val = 12'hA88;
        7'd67: r_lut_val = 12'hA7A;
        7'd68: r_lut_val = 12'hA6C;
        7'd69: r_lut_val = 12'hA5F;
        7'd70: r_lut_val = 12'hA51;
        7'd71: r_lut_val = 12'hA44;
        7'd72: r_lut_val = 12'hA37;
        7'd73: r_lut_val = 12'hA2A;
        7'd74: r_lut_val = 12'hA1D;
        7'd75: r_lut_val = 12'hA10;
        7'd76: r_lut_val = 12'hA04;
        7'd77: r_lut_val = 12'h9F7;
        7'd78: r_lut_val = 12'h9EB;
        7'd79: r_lut_val = 12'h9DF;
        7'd80: r_lut_val = 12'h9D3;
        7'd81: r_lut_val = 12'h9C7;
        7'd82: r_lut_val = 12'h9BB;
        7'd83: r_lut_val = 12'h9AF;
        7'd84: r_lut_val = 12'h9A3;
        7'd85: r_lut_val = 12'h998;
        7'd86: r_lut_val = 12'h98C;
        7'd87: r_lut_val = 12'h981;
        7'd88: r_lut_val = 12'h976;
        7'd89: r_lut_val = 12'h96B;
        7'd90: r_lut_val = 12'h95F;
        7'd91: r_lut_val = 12'h955;
        7'd92: r_lut_val = 12'h94A;
        7'd93: r_lut_val = 12'h93F;
        7'd94: r_lut_val = 12'h934;
        7'd95: r_lut_val = 12'h92A;
        7'd96: r_lut_val = 12'h91F;
        7'd97: r_lut_val = 12'h915;
        7'd98: r_lut_val = 12'h90B;
        7'd99: r_lut_val = 12'h901;
        7'd100: r_lut_val = 12'h8F6;
        7'd101: r_lut_val = 12'h8EC;
        7'd102: r_lut_val = 12'h8E3;
        7'd103: r_lut_val = 12'h8D9;
        7'd104: r_lut_val = 12'h8CF;
        7'd105: r_lut_val = 12'h8C5;
        7'd106: r_lut_val = 12'h8BC;
        7'd107: r_lut_val = 12'h8B2;
        7'd108: r_lut_val = 12'h8A9;
        7'd109: r_lut_val = 12'h8A0;
        7'd110: r_lut_val = 12'h896;
        7'd111: r_lut_val = 12'h88D;
        7'd112: r_lut_val = 12'h884;
        7'd113: r_lut_val = 12'h87B;
        7'd114: r_lut_val = 12'h872;
        7'd115: r_lut_val = 12'h869;
        7'd116: r_lut_val = 12'h860;
        7'd117: r_lut_val = 12'h858;
        7'd118: r_lut_val = 12'h84F;
        7'd119: r_lut_val = 12'h846;
        7'd120: r_lut_val = 12'h83E;
        7'd121: r_lut_val = 12'h835;
        7'd122: r_lut_val = 12'h82D;
        7'd123: r_lut_val = 12'h825;
        7'd124: r_lut_val = 12'h81C;
        7'd125: r_lut_val = 12'h814;
        7'd126: r_lut_val = 12'h80C;
        7'd127: r_lut_val = 12'h804;
        default: r_lut_val = 12'h000;
    endcase
end

// -------------------------------------------------------------------------
// Shared significand multiplier: one 24x24 Dadda multiply per
// FSM cycle (Newton factors, q0, and the exact residual all
// reuse this instance). i_*_is_normal IS the operand hidden
// bit, so each operand presents its own bit 23 (see below).
// -------------------------------------------------------------------------

logic [22:0] w_mult_a;
logic [22:0] w_mult_b;
wire [47:0] w_prod;
// w_m drives the S_RNE A-port hidden bit; declared here
// (before the instantiation) and assigned in S_RNE logic.
wire [23:0] w_m;

math_ieee754_2008_fp32_mantissa_mult u_mant_mult (
    .i_mant_a(w_mult_a),
    .i_mant_b(w_mult_b),
//     hidden-bit semantics per operand: i_*_is_normal IS the
//     operand hidden bit, so EVERY state presents its own
//     bit 23. The refined r1 (measured as low as 0x7FFFE1),
//     the Newton factors e1/e2, the biased q0, and the
//     subnormal-grid m can all dip below 2^23; a hardwired 1
//     would graft a phantom hidden bit onto them and corrupt
//     the exact residual. The exhaustive Newton proof in
//     verify_accuracy_bounds assumes exactly this
//     reconstruction (plain 24x24 products).
    .i_a_is_normal((r_state == S_RNE)  ? w_m[23]   :
                   (r_state == S_NR1B) ? r_r0[23]  :
                   (r_state == S_NR2B) ? r_r1[23]  :
                   (r_state == S_Q0)   ? r_a24[23] : 1'b1),
    .i_b_is_normal((r_state == S_REM)  ? r_q0[23]  :
                   (r_state == S_NR1B) ? w_e1[23]  :
                   (r_state == S_NR2B) ? w_e2[23]  :
                   (r_state == S_NR1A) ? r_r0[23]  :
                   (r_state == S_NR2A) ? r_r1[23]  :
                   (r_state == S_Q0)   ? r_r2[23]  : 1'b1),
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
        S_NR1A: begin
            w_mult_a = r_b24[22:0];
            w_mult_b = r_r0[22:0];
        end
        S_NR1B: begin
            w_mult_a = r_r0[22:0];
            w_mult_b = w_e1[22:0];
        end
        S_NR2A: begin
            w_mult_a = r_b24[22:0];
            w_mult_b = r_r1[22:0];
        end
        S_NR2B: begin
            w_mult_a = r_r1[22:0];
            w_mult_b = w_e2[22:0];
        end
        S_Q0: begin
            w_mult_a = r_a24[22:0];
            w_mult_b = r_r2[22:0];
        end
        S_REM: begin
            w_mult_a = r_b24[22:0];
            w_mult_b = r_q0[22:0];
        end
        S_RNE: begin
//             subnormal-grid prep: m * B (exact residual fraction)
            w_mult_a = w_m[22:0];
            w_mult_b = r_b24[22:0];
        end
        default: begin
            w_mult_a = 23'h000000;
            w_mult_b = 23'h000000;
        end
    endcase
end

// -------------------------------------------------------------------------
// Exact residual rounding (S_RNE, combinational)

// rem = B*(sig_true - q0) in [0, 16B) exactly. Reduce
// rem = k*B + remp with a 4-stage binary chain (8B, 4B, 2B, B),
// then q_base = q0 + k and textbook RNE on the exact remainder:
//   round up iff (2*remp > B) | ((2*remp == B) & LSB(q_base))
// TRUE sticky by construction: the residual is exact, so a tie
// (2*remp == B) is detected exactly and rounds to even.
// -------------------------------------------------------------------------

logic [3:0]  w_k;
logic [27:0] w_red;
//   every stage explicitly 28 bits wide
wire [27:0] w_b8 = {1'b0, r_b24, 3'b000};
wire [27:0] w_b4 = {2'b00, r_b24, 2'b00};
wire [27:0] w_b2 = {3'b000, r_b24, 1'b0};
wire [27:0] w_b1 = {4'b0000, r_b24};
always_comb begin
    w_k  = 4'd0;
    w_red = r_rem;
    if (w_red >= w_b8) begin
        w_red = w_red - w_b8;
        w_k = 4'd8;
    end
    if (w_red >= w_b4) begin
        w_red = w_red - w_b4;
        w_k = w_k + 4'd4;
    end
    if (w_red >= w_b2) begin
        w_red = w_red - w_b2;
        w_k = w_k + 4'd2;
    end
    if (w_red >= w_b1) begin
        w_red = w_red - w_b1;
        w_k = w_k + 4'd1;
    end
end

wire [24:0] w_qbase = {1'b0, r_q0} + {21'b0, w_k};
wire [24:0] w_two   = {w_red[23:0], 1'b0};  // 2*remp
//   remp < B < 2^24 so 2*remp fits 25 bits
wire w_ru = (w_two > {1'b0, r_b24}) |
          ((w_two == {1'b0, r_b24}) & w_qbase[0]);
wire [24:0] w_qf = w_qbase + {24'b0, w_ru};
wire w_inexact = (w_red != 28'h0000000);

// Quotient exponent: e_f = ea_s - eb_s + 127 - half
wire signed [10:0] w_e_f = $signed({r_ea_s[9], r_ea_s}) -
    $signed({r_eb_s[9], r_eb_s}) + 11'sd127 - {10'b0000000000, r_half};

// Stage outputs (expression part-selects spelled out for tool
// compatibility): q0 with its 8-S-unit bias, exact residual
wire [47:0] w_bias = r_half ? 48'h000004000000 : 48'h000008000000;
wire [47:0] w_q0_full = (w_prod - w_bias) >> (5'd24 - {4'b0000, r_half});
wire [47:0] w_a_s = {1'b0, r_a24, 23'h0000000} << r_half;
wire [47:0] w_rem_full = w_a_s - w_prod;  // B*q0 < 2^48

// Subnormal grid (SUBNORMAL_SUPPORT=1), EXACT like the normal path:
// the result grid (shift sh = 1-e_f) can be COARSER than the 24-bit
// significand grid, so re-rounding the rounded q_f would double-
// round. Instead the exact value q_base + red/B is compared at the
// result grid: with m = q_base mod 2^sh and X = m*B + red,
//   N_true = (q_base + red/B) / 2^sh, frac = X / (2^sh * B)
//   g = X >= B<<(sh-1); r = 2*rem_g >= B<<(sh-1);
//   sticky = remainder != 0; inexact = (X != 0)
// all exact integer compares (the m*B product is computed by the
// shared multiplier during S_RNE, one extra cycle for subnormal
// results). Deep shifts (sh >= 25) flush in S_RNE as before.
wire [7:0] w_sh = (w_e_f <= 11'sd0) ? (8'd1 - w_e_f[7:0]) : 8'd0;
wire        w_deep = (w_e_f < -11'sd23);  // shift >= 25: guard bit gone
//   q_base WITHOUT the normal-path round-up: the exact integer part
wire [24:0] w_qbase_x = {1'b0, r_q0} + {21'b0, w_k};
assign w_m = w_qbase_x[23:0] & ((24'h000001 << w_sh[4:0]) - 24'h000001);
wire        w_need_subn = (w_e_f <= 11'sd0) & SUBNORMAL_SUPPORT & ~w_deep;

// S_SUBN: exact grid compares from the registered m*B product
wire [47:0] w_x_sub = r_mprod + {20'h00000, r_red};
wire [47:0] w_bsh  = {24'h000000, r_b24} << (r_sh - 5'd1);
wire        w_g_sn = (w_x_sub >= w_bsh);
wire [47:0] w_rg_sn = w_x_sub - (w_g_sn ? w_bsh : 48'h000000000000);
wire [48:0] w_2rg   = {w_rg_sn, 1'b0};
wire        w_r_sn = (w_2rg >= {1'b0, w_bsh});
wire [48:0] w_rr_sn = w_2rg - (w_r_sn ? {1'b0, w_bsh} : 49'h0000000000000);
wire        w_s_sn = (w_rr_sn != 49'h0000000000000);
wire        w_inex_sn = (w_x_sub != 48'h000000000000);
wire [23:0] w_n_sn = r_qbase >> r_sh;
wire        w_ru_sn = w_g_sn & (w_r_sn | w_s_sn | w_n_sn[0]);
wire [23:0] w_n_rnd = w_n_sn + {23'b0, w_ru_sn};
wire        w_sub_carry = w_n_rnd[23];  // BUG-004: -> min-normal

// -------------------------------------------------------------------------
// Result assembly (S_RNE, combinational into output regs).
// The subnormal GRID result is NOT assembled here: re-rounding
// q_f at a coarser grid would double-round, so grid-bound
// results complete one cycle later in S_SUBN from the exact
// X = m*B + red comparison.
// -------------------------------------------------------------------------
// Stage-output declarations precede every use (lint clean).
logic [31:0] w_out_result;
logic w_out_overflow, w_out_underflow, w_out_invalid;
logic [31:0] w_subn_result;
logic w_subn_underflow;

always_comb begin
    w_out_result  = {r_sign, 8'h00, 23'h000000};
    w_out_overflow  = 1'b0;
    w_out_underflow = 1'b0;
    w_out_invalid   = 1'b0;
    if (w_e_f >= 11'sd255) begin
//         // Overflow: quotient magnitude >= 2^128
        w_out_result  = {r_sign, 8'hFF, 23'h000000};
        w_out_overflow = 1'b1;
    end else if (w_e_f >= 11'sd1) begin
//         // Normal range
        w_out_result  = {r_sign, w_e_f[7:0], w_qf[22:0]};
    end else if (!SUBNORMAL_SUPPORT) begin
//         // FTZ: nonzero quotient flushes to signed zero + flag
        w_out_underflow = 1'b1;
    end else begin
//         // deep shift (>= 25): below half min_sub, signed zero + flag
        w_out_underflow = 1'b1;
    end
end

// S_SUBN output: exact subnormal-grid result
always_comb begin
    w_subn_result  = {r_sign, 8'h00, w_n_rnd[22:0]};
    w_subn_underflow = 1'b0;
    if (w_sub_carry) begin
//         // BUG-004: rounding carry out of pre-round exponent 0
//         // yields min-normal, not a flush; not tiny, no flag
        w_subn_result  = {r_sign, 8'h01, 23'h000000};
    end else begin
//         // IEEE underflow: tiny after rounding AND inexact
        w_subn_underflow = w_inex_sn;
    end
end

// -------------------------------------------------------------------------
// Multi-cycle FSM: 9 cycles accept-to-ow_valid on the normal
// path (10 for exact subnormal-grid results, which need the
// m*B compare cycle), 1 cycle for special cases. ow_valid
// pulses for exactly one cycle.
// -------------------------------------------------------------------------

assign ow_result  = r_result;
assign ow_overflow  = r_overflow;
assign ow_underflow = r_underflow;
assign ow_invalid   = r_invalid;
assign ow_valid     = r_owv;

`ALWAYS_FF_RST(i_clk, i_rst_n,
        if (`RST_ASSERTED(i_rst_n)) begin
            r_state    <= S_IDLE;
            r_owv      <= 1'b0;
            r_result   <= 32'h00000000;
            r_overflow <= 1'b0;
            r_underflow <= 1'b0;
            r_invalid  <= 1'b0;
            r_a24      <= 24'h000000;
            r_b24      <= 24'h000000;
            r_ea_s     <= 10'sd0;
            r_eb_s     <= 10'sd0;
            r_sign     <= 1'b0;
            r_half     <= 1'b0;
            r_r0       <= 24'h000000;
            r_t1       <= 24'h000000;
            r_r1       <= 24'h000000;
            r_t2       <= 24'h000000;
            r_r2       <= 24'h000000;
            r_q0       <= 24'h000000;
            r_rem      <= 28'h0000000;
            r_mprod    <= 48'h000000000000;
            r_red      <= 28'h0000000;
            r_qbase    <= 24'h000000;
            r_sh       <= 5'd0;
        end else begin
            r_owv <= 1'b0;
            case (r_state)
                S_IDLE: begin
                    if (i_valid) begin
                        if (w_is_special) begin
                            r_result   <= w_spec_result;
                            r_overflow <= 1'b0;
                            r_underflow <= 1'b0;
                            r_invalid  <= w_spec_invalid;
                            r_owv      <= 1'b1;
                            r_state    <= S_OUT;
                        end else begin
                            r_a24   <= w_sig_a;
                            r_b24   <= w_sig_b;
                            r_ea_s  <= w_ea_s;
                            r_eb_s  <= w_eb_s;
                            r_sign  <= w_sign_result;
                            r_half  <= w_half;
                            r_state <= S_LUT;
                        end
                    end
                end
    
                S_LUT: begin
                    r_r0   <= {r_lut_val, 12'h000};
                    r_state <= S_NR1A;
                end
    
                S_NR1A: begin
                    r_t1    <= w_prod[47:24];  // t1 = trunc(B*r0 * 2^-24) * 2^23
                    r_state <= S_NR1B;
                end
    
                S_NR1B: begin
    //                 // r1 = round(r0*(2-t1)); saturate at 2^24-1
                    r_r1    <= w_r1_wide[24] ? 24'hFFFFFF : w_r1_wide[23:0];
                    r_state <= S_NR2A;
                end
    
                S_NR2A: begin
                    r_t2    <= w_prod[47:24];
                    r_state <= S_NR2B;
                end
    
                S_NR2B: begin
                    r_r2    <= w_r2_wide[24] ? 24'hFFFFFF : w_r2_wide[23:0];
                    r_state <= S_Q0;
                end
    
                S_Q0: begin
    //                 // q0 = (A*r2 - bias) >> (24-half); the 8-S-unit bias
    //                 // (8<<23 when half, 8<<24 otherwise) keeps the exact
    //                 // residual non-negative
                    r_q0    <= w_q0_full[23:0];
                    r_state <= S_REM;
                end
    
                S_REM: begin
    //                 // rem = (A << (23+half)) - B*q0, exact, in [0, 16B)
                    r_rem   <= w_rem_full[27:0];
                    r_state <= S_RNE;
                end
    
                S_RNE: begin
                    if (w_need_subn) begin
    //                     // subnormal grid: carry the EXACT value into
    //                     // S_SUBN (m*B from the multiplier this cycle)
                        r_mprod    <= w_prod;
                        r_red      <= w_red;
                        r_qbase    <= w_qbase_x[23:0];
                        r_sh       <= w_sh[4:0];
                        r_state    <= S_SUBN;
                    end else begin
                        r_result   <= w_out_result;
                        r_overflow <= w_out_overflow;
                        r_underflow <= w_out_underflow;
                        r_invalid  <= w_out_invalid;
                        r_owv      <= 1'b1;
                        r_state    <= S_OUT;
                    end
                end
    
                S_SUBN: begin
    //                 // exact subnormal-grid result (RNE, TRUE sticky)
                    r_result   <= w_subn_result;
                    r_overflow <= 1'b0;
                    r_underflow <= w_subn_underflow;
                    r_invalid  <= 1'b0;
                    r_owv      <= 1'b1;
                    r_state    <= S_OUT;
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
