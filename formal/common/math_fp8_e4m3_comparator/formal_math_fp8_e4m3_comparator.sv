// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp8_e4m3_comparator
//
// Verifies:
//   - Exactly one of {lt, eq, gt, unord} asserted
//   - NaN produces unordered
//   - Reflexive: a == a (when not NaN)
//   - Antisymmetric: (a < b) implies (b > a)
//   - Derived flags: le, ge, ne consistency
//   - +0 == -0
//
// Note: FP8 E4M3 has a single NaN encoding: exp=0xF, mant=0x7

`timescale 1ns / 1ps

module formal_math_fp8_e4m3_comparator (
    input logic clk
);

    (* anyconst *) logic [7:0] a;
    (* anyconst *) logic [7:0] b;

    logic ow_eq, ow_lt, ow_gt, ow_le, ow_ge, ow_ne, ow_unord;

    math_fp8_e4m3_comparator dut (
        .i_a(a), .i_b(b),
        .ow_eq(ow_eq), .ow_lt(ow_lt), .ow_gt(ow_gt),
        .ow_le(ow_le), .ow_ge(ow_ge), .ow_ne(ow_ne), .ow_unord(ow_unord)
    );

    logic rev_eq, rev_lt, rev_gt, rev_le, rev_ge, rev_ne, rev_unord;

    math_fp8_e4m3_comparator dut_rev (
        .i_a(b), .i_b(a),
        .ow_eq(rev_eq), .ow_lt(rev_lt), .ow_gt(rev_gt),
        .ow_le(rev_le), .ow_ge(rev_ge), .ow_ne(rev_ne), .ow_unord(rev_unord)
    );

    // NaN detection (E4M3: only exp=F, mant=7 is NaN)
    wire a_nan = (a[6:3] == 4'hF) & (a[2:0] == 3'h7);
    wire b_nan = (b[6:3] == 4'hF) & (b[2:0] == 3'h7);
    wire either_nan = a_nan | b_nan;
    wire a_zero = (a[6:0] == 7'h0);
    wire b_zero = (b[6:0] == 7'h0);

    // Exactly one of {lt, eq, gt, unord}
    always @(posedge clk) begin
        p_exactly_one: assert ((ow_lt + ow_eq + ow_gt + ow_unord) == 1);
    end

    // NaN => unordered
    always @(posedge clk) begin
        if (either_nan) begin
            p_nan_unord: assert (ow_unord);
            p_nan_no_eq: assert (!ow_eq);
            p_nan_no_lt: assert (!ow_lt);
            p_nan_no_gt: assert (!ow_gt);
        end
    end

    // Reflexive
    always @(posedge clk) begin
        if (a == b && !either_nan) begin
            p_reflexive: assert (ow_eq);
        end
    end

    // Antisymmetric
    always @(posedge clk) begin
        if (ow_lt) begin p_antisym_lt: assert (rev_gt); end
        if (ow_gt) begin p_antisym_gt: assert (rev_lt); end
        if (ow_eq) begin p_sym_eq: assert (rev_eq); end
    end

    // Derived flags
    always @(posedge clk) begin
        p_le_def: assert (ow_le == (ow_lt | ow_eq));
        p_ge_def: assert (ow_ge == (ow_gt | ow_eq));
        p_ne_def: assert (ow_ne == (ow_lt | ow_gt));
    end

    // +0 == -0
    always @(posedge clk) begin
        if (a_zero && b_zero) begin
            p_zero_eq: assert (ow_eq);
        end
    end

    // Cover
    always @(posedge clk) begin
        c_lt: cover (ow_lt);
        c_eq: cover (ow_eq);
        c_gt: cover (ow_gt);
        c_unord: cover (ow_unord);
        c_zero_eq: cover (a_zero && b_zero && a[7] != b[7]);
    end

endmodule
