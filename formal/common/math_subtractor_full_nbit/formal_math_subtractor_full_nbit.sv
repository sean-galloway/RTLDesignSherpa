// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_subtractor_full_nbit (N-bit full subtractor)
// Proves: {borrow_out, diff} == a - b - borrow_in

module formal_math_subtractor_full_nbit #(
    parameter int WIDTH = 8
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH-1:0] a;
    (* anyconst *) logic [WIDTH-1:0] b;
    (* anyconst *) logic             bin;

    logic [WIDTH-1:0] diff;
    logic             bout;

    math_subtractor_full_nbit #(.N(WIDTH)) dut (
        .i_a   (a),
        .i_b   (b),
        .i_b_in(bin),
        .ow_d  (diff),
        .ow_b  (bout)
    );

    // Reference: (WIDTH+1)-bit result of a - b - bin
    wire [WIDTH:0] ref_result = {1'b0, a} - {1'b0, b} - {{WIDTH{1'b0}}, bin};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Difference matches reference lower bits
    always @(posedge clk)
        ap_diff: assert (diff == ref_result[WIDTH-1:0]);

    // Borrow out matches reference MSB
    always @(posedge clk)
        ap_bout: assert (bout == ref_result[WIDTH]);

    // Combined equivalence
    always @(posedge clk)
        ap_combined: assert ({bout, diff} == ref_result);

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: no borrow (a > b)
    always @(posedge clk)
        cp_no_borrow: cover (bout == 1'b0 && a > b);

    // Cover: borrow out
    always @(posedge clk)
        cp_borrow: cover (bout == 1'b1);

    // Cover: zero result
    always @(posedge clk)
        cp_zero_diff: cover (diff == '0 && bout == 1'b0);

    // Cover: max result
    always @(posedge clk)
        cp_max_diff: cover (diff == {WIDTH{1'b1}});

    // Cover: borrow-in propagates through
    always @(posedge clk)
        cp_bin_propagate: cover (a == '0 && b == '0 && bin == 1'b1 && bout == 1'b1);

endmodule
