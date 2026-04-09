// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_addsub_full_nbit (N-bit adder/subtractor)
// Proves: when i_c==0, {cout,sum} == a+b; when i_c==1, {cout,sum} == a-b
// The module uses two's complement: sub = add with (b XOR 1) + 1

module formal_math_addsub_full_nbit #(
    parameter int WIDTH = 8
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH-1:0] a;
    (* anyconst *) logic [WIDTH-1:0] b;
    (* anyconst *) logic             mode;  // 0=add, 1=subtract

    logic [WIDTH-1:0] sum;
    logic             cout;

    math_addsub_full_nbit #(.N(WIDTH)) dut (
        .i_a     (a),
        .i_b     (b),
        .i_c     (mode),
        .ow_sum  (sum),
        .ow_carry(cout)
    );

    // Reference for addition: a + b
    wire [WIDTH:0] ref_add = {1'b0, a} + {1'b0, b};

    // Reference for subtraction: a - b (using two's complement)
    // a - b = a + ~b + 1, carry out is inverted borrow
    wire [WIDTH:0] ref_sub = {1'b0, a} + {1'b0, ~b} + {{WIDTH{1'b0}}, 1'b1};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Addition mode (mode==0): {cout, sum} == a + b
    always @(posedge clk)
        ap_add_correct: assert (mode != 1'b0 || {cout, sum} == ref_add);

    // Subtraction mode (mode==1): {cout, sum} == a + ~b + 1
    always @(posedge clk)
        ap_sub_correct: assert (mode != 1'b1 || {cout, sum} == ref_sub);

    // In subtract mode, sum should equal a - b (lower bits)
    always @(posedge clk)
        ap_sub_diff: assert (mode != 1'b1 || sum == (a - b));

    // In add mode, sum should equal a + b (lower bits)
    always @(posedge clk)
        ap_add_sum: assert (mode != 1'b0 || sum == ref_add[WIDTH-1:0]);

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: addition with no overflow
    always @(posedge clk)
        cp_add_no_overflow: cover (mode == 1'b0 && cout == 1'b0 && a != '0 && b != '0);

    // Cover: addition with overflow
    always @(posedge clk)
        cp_add_overflow: cover (mode == 1'b0 && cout == 1'b1);

    // Cover: subtraction with no borrow (a >= b)
    always @(posedge clk)
        cp_sub_no_borrow: cover (mode == 1'b1 && cout == 1'b1 && a > b);

    // Cover: subtraction with borrow (a < b)
    always @(posedge clk)
        cp_sub_borrow: cover (mode == 1'b1 && cout == 1'b0 && a < b);

    // Cover: subtraction yielding zero
    always @(posedge clk)
        cp_sub_zero: cover (mode == 1'b1 && sum == '0 && a == b);

endmodule
