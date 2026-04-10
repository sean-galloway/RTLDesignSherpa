// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_comparator
//
// Verifies:
//   - Exactly one of {lt, eq, gt, unord} asserted (mutual exclusion)
//   - NaN produces unordered, clears all ordered flags
//   - Reflexive: a == a (when not NaN)
//   - Antisymmetric: (a < b) implies (b > a)
//   - Derived flags: le == (lt | eq), ge == (gt | eq), ne == !eq
//   - +0 == -0

`timescale 1ns / 1ps

module formal_math_bf16_comparator (
    input logic clk
);

    // Free inputs
    (* anyconst *) logic [15:0] a;
    (* anyconst *) logic [15:0] b;

    // DUT
    logic ow_eq, ow_lt, ow_gt, ow_le, ow_ge, ow_ne, ow_unord;

    math_bf16_comparator dut (
        .i_a      (a),
        .i_b      (b),
        .ow_eq    (ow_eq),
        .ow_lt    (ow_lt),
        .ow_gt    (ow_gt),
        .ow_le    (ow_le),
        .ow_ge    (ow_ge),
        .ow_ne    (ow_ne),
        .ow_unord (ow_unord)
    );

    // Reverse comparator for antisymmetry check
    logic rev_eq, rev_lt, rev_gt, rev_le, rev_ge, rev_ne, rev_unord;

    math_bf16_comparator dut_rev (
        .i_a      (b),
        .i_b      (a),
        .ow_eq    (rev_eq),
        .ow_lt    (rev_lt),
        .ow_gt    (rev_gt),
        .ow_le    (rev_le),
        .ow_ge    (rev_ge),
        .ow_ne    (rev_ne),
        .ow_unord (rev_unord)
    );

    // NaN detection
    wire a_nan = (a[14:7] == 8'hFF) & (a[6:0] != 7'h0);
    wire b_nan = (b[14:7] == 8'hFF) & (b[6:0] != 7'h0);
    wire either_nan = a_nan | b_nan;

    // +/-0 detection
    wire a_zero = (a[14:0] == 15'h0);
    wire b_zero = (b[14:0] == 15'h0);

    // Property 1: Exactly one of {lt, eq, gt, unord}
    always @(posedge clk) begin
        p_exactly_one: assert ((ow_lt + ow_eq + ow_gt + ow_unord) == 1);
    end

    // Property 2: NaN => unordered, all ordered flags clear
    always @(posedge clk) begin
        if (either_nan) begin
            p_nan_unord: assert (ow_unord);
            p_nan_no_eq: assert (!ow_eq);
            p_nan_no_lt: assert (!ow_lt);
            p_nan_no_gt: assert (!ow_gt);
        end
    end

    // Property 3: Reflexive: a == a (when not NaN)
    always @(posedge clk) begin
        if (a == b && !either_nan) begin
            p_reflexive: assert (ow_eq);
        end
    end

    // Property 4: Antisymmetric: (a < b) => (b > a)
    always @(posedge clk) begin
        if (ow_lt) begin
            p_antisym_lt: assert (rev_gt);
        end
        if (ow_gt) begin
            p_antisym_gt: assert (rev_lt);
        end
        if (ow_eq) begin
            p_sym_eq: assert (rev_eq);
        end
    end

    // Property 5: Derived flag consistency
    always @(posedge clk) begin
        p_le_def: assert (ow_le == (ow_lt | ow_eq));
        p_ge_def: assert (ow_ge == (ow_gt | ow_eq));
        p_ne_def: assert (ow_ne == (ow_lt | ow_gt));
    end

    // Property 6: +0 == -0
    always @(posedge clk) begin
        if (a_zero && b_zero) begin
            p_zero_eq: assert (ow_eq);
        end
    end

    // Cover properties
    always @(posedge clk) begin
        c_lt:    cover (ow_lt);
        c_eq:    cover (ow_eq);
        c_gt:    cover (ow_gt);
        c_unord: cover (ow_unord);
        c_zero_eq: cover (a_zero && b_zero && a[15] != b[15]);
    end

endmodule
