// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mod_3_compress
// Purpose: Combinational d_in mod 3 for a 16-bit operand, built in the same
//          carry-save-compressor style as common/rtl/div_by_15_ceil_32compress.sv
//          (3:2 compressor tree -> final carry-propagate add -> small fold),
//          but computing only the remainder -- which is all the monbus
//          burst-writer needs to round a beat count down to a whole number of
//          3-beat records (rounded = X - (X mod 3)).
//
//          Method: base-4 digit sum. Every 2-bit group of d_in is a base-4
//          digit with weight 4^k == 1 (mod 3), so the sum of the eight groups
//          is congruent to d_in (mod 3). The eight digits are reduced with 3:2
//          (carry-save) compressors instead of a ripple-add chain, then a
//          final fold + conditional subtract collapses the group sum to 0..2.
//          No '*' / '/' operator -> no inferred DSP or iterative divider.
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway

`timescale 1ns / 1ps

module mod_3_compress (
    input  logic [15:0] d_in,
    output logic [1:0]  rem_out   // d_in mod 3  (0..2)
);

    // Group sum (0..24) needs 5 bits; use a 6-bit datapath so the carry-
    // weight-2x left shifts have headroom (the always-0 top carry is dropped,
    // exactly as the div-by-15 reference does with {carry[62:0],1'b0}).
    localparam int BITS = 6;

    // ----------------------------
    // 0. Base-4 digits (2-bit groups), zero-extended to the CSA width.
    // ----------------------------
    logic [BITS-1:0] w_g0, w_g1, w_g2, w_g3, w_g4, w_g5, w_g6, w_g7;
    assign w_g0 = {{(BITS-2){1'b0}}, d_in[1:0]};
    assign w_g1 = {{(BITS-2){1'b0}}, d_in[3:2]};
    assign w_g2 = {{(BITS-2){1'b0}}, d_in[5:4]};
    assign w_g3 = {{(BITS-2){1'b0}}, d_in[7:6]};
    assign w_g4 = {{(BITS-2){1'b0}}, d_in[9:8]};
    assign w_g5 = {{(BITS-2){1'b0}}, d_in[11:10]};
    assign w_g6 = {{(BITS-2){1'b0}}, d_in[13:12]};
    assign w_g7 = {{(BITS-2){1'b0}}, d_in[15:14]};

    // ----------------------------
    // 1. 3:2 compressor tree over the eight digits (carry weight 2x, so it is
    //    shifted left 1 wherever it feeds the next level).
    // ----------------------------
    logic [BITS-1:0] w_sumA1, w_carryA1;   // level 1
    logic [BITS-1:0] w_sumB1, w_carryB1;
    logic [BITS-1:0] w_sumC1, w_carryC1;
    logic [BITS-1:0] w_sumD2, w_carryD2;   // level 2
    logic [BITS-1:0] w_sumE2, w_carryE2;
    logic [BITS-1:0] w_sumF3, w_carryF3;   // level 3
    logic [BITS-1:0] w_sumG4, w_carryG4;   // level 4
    logic [BITS-1:0] w_grp_sum;

    // Level 1: eight digits, three at a time (last triple padded with 0).
    math_adder_carry_save_nbit #(.N(BITS))
        comp1 (.i_a(w_g0), .i_b(w_g1), .i_c(w_g2), .ow_sum(w_sumA1), .ow_carry(w_carryA1));
    math_adder_carry_save_nbit #(.N(BITS))
        comp2 (.i_a(w_g3), .i_b(w_g4), .i_c(w_g5), .ow_sum(w_sumB1), .ow_carry(w_carryB1));
    math_adder_carry_save_nbit #(.N(BITS))
        comp3 (.i_a(w_g6), .i_b(w_g7), .i_c({BITS{1'b0}}), .ow_sum(w_sumC1), .ow_carry(w_carryC1));

    // Level 2
    math_adder_carry_save_nbit #(.N(BITS))
        comp4 (.i_a(w_sumA1), .i_b({w_carryA1[BITS-2:0], 1'b0}), .i_c(w_sumB1),
               .ow_sum(w_sumD2), .ow_carry(w_carryD2));
    math_adder_carry_save_nbit #(.N(BITS))
        comp5 (.i_a({w_carryB1[BITS-2:0], 1'b0}), .i_b(w_sumC1), .i_c({w_carryC1[BITS-2:0], 1'b0}),
               .ow_sum(w_sumE2), .ow_carry(w_carryE2));

    // Level 3 (w_carryE2 held for the next level)
    math_adder_carry_save_nbit #(.N(BITS))
        comp6 (.i_a(w_sumD2), .i_b({w_carryD2[BITS-2:0], 1'b0}), .i_c(w_sumE2),
               .ow_sum(w_sumF3), .ow_carry(w_carryF3));

    // Level 4
    math_adder_carry_save_nbit #(.N(BITS))
        comp7 (.i_a(w_sumF3), .i_b({w_carryF3[BITS-2:0], 1'b0}), .i_c({w_carryE2[BITS-2:0], 1'b0}),
               .ow_sum(w_sumG4), .ow_carry(w_carryG4));

    // Final carry-propagate add -> digit sum (0..24, == d_in (mod 3)).
    assign w_grp_sum = w_sumG4 + {w_carryG4[BITS-2:0], 1'b0};

    // ----------------------------
    // 2. Fold the group sum (0..24) to its own base-4 digits (== same residue
    //    mod 3), then a final conditional subtract to 0..2.
    // ----------------------------
    logic [3:0] w_fold;   // 0..7
    assign w_fold = {2'b0, w_grp_sum[1:0]} + {2'b0, w_grp_sum[3:2]}
                  + {3'b0, w_grp_sum[4]};
    assign rem_out = 2'((w_fold >= 4'd6) ? (w_fold - 4'd6)
                      : (w_fold >= 4'd3) ? (w_fold - 4'd3)
                                         : w_fold);

endmodule : mod_3_compress
