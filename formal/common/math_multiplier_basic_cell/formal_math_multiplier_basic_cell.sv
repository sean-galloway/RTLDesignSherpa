// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_multiplier_basic_cell
// Proves: the cell performs a full-add of (i_i & i_j), i_c, and i_p
// Output: ow_p = sum, ow_c = carry of the three inputs

module formal_math_multiplier_basic_cell (
    input logic clk
);

    (* anyconst *) logic ii;
    (* anyconst *) logic ij;
    (* anyconst *) logic ic;
    (* anyconst *) logic ip;

    logic oc;
    logic op;

    math_multiplier_basic_cell dut (
        .i_i (ii),
        .i_j (ij),
        .i_c (ic),
        .i_p (ip),
        .ow_c(oc),
        .ow_p(op)
    );

    // The partial product bit
    wire pp = ii & ij;

    // Reference: full-add of pp, ic, ip
    wire [1:0] ref_result = {1'b0, pp} + {1'b0, ic} + {1'b0, ip};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Sum output (ow_p) is XOR of pp, ic, ip
    always @(posedge clk)
        ap_sum: assert (op == (pp ^ ic ^ ip));

    // Carry output (ow_c) is majority of pp, ic, ip
    always @(posedge clk)
        ap_carry: assert (oc == ((ic & ip) | (ic & pp) | (ip & pp)));

    // Combined: {oc, op} == pp + ic + ip
    always @(posedge clk)
        ap_combined: assert ({oc, op} == ref_result);

    // Partial product is AND of multiplier bits
    always @(posedge clk)
        ap_partial_product: assert (pp == (ii & ij));

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: all inputs zero
    always @(posedge clk)
        cp_all_zero: cover (ii == 0 && ij == 0 && ic == 0 && ip == 0);

    // Cover: partial product generated with carry
    always @(posedge clk)
        cp_pp_with_carry: cover (pp == 1 && ic == 1 && oc == 1);

    // Cover: carry and sum both set
    always @(posedge clk)
        cp_both_outputs: cover (oc == 1 && op == 1);

    // Cover: only sum set
    always @(posedge clk)
        cp_sum_only: cover (oc == 0 && op == 1);

endmodule
