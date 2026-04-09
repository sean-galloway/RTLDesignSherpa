// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_adder_carry_save_nbit (N-bit carry-save adder)
// Proves: for each bit i, {carry[i], sum[i]} == a[i] + b[i] + c[i]
// The N-bit CSA performs independent 1-bit 3:2 compressions per column.

module formal_math_adder_carry_save_nbit #(
    parameter int WIDTH = 8
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH-1:0] a;
    (* anyconst *) logic [WIDTH-1:0] b;
    (* anyconst *) logic [WIDTH-1:0] c;

    logic [WIDTH-1:0] sum;
    logic [WIDTH-1:0] carry;

    math_adder_carry_save_nbit #(.N(WIDTH)) dut (
        .i_a     (a),
        .i_b     (b),
        .i_c     (c),
        .ow_sum  (sum),
        .ow_carry(carry)
    );

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Per-bit correctness: {carry[i], sum[i]} == a[i] + b[i] + c[i]
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_bit_check
            always @(posedge clk)
                assert ({carry[i], sum[i]} ==
                    ({1'b0, a[i]} + {1'b0, b[i]} + {1'b0, c[i]}));
        end
    endgenerate

    // Sum is bitwise XOR
    always @(posedge clk)
        ap_sum_xor: assert (sum == (a ^ b ^ c));

    // Carry is bitwise majority
    always @(posedge clk)
        ap_carry_majority: assert (carry == ((a & b) | (a & c) | (b & c)));

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: all zeros
    always @(posedge clk)
        cp_all_zero: cover (a == '0 && b == '0 && c == '0);

    // Cover: all ones
    always @(posedge clk)
        cp_all_ones: cover (a == {WIDTH{1'b1}} && b == {WIDTH{1'b1}} && c == {WIDTH{1'b1}});

    // Cover: carry vector all set
    always @(posedge clk)
        cp_all_carry: cover (carry == {WIDTH{1'b1}});

    // Cover: sum vector all set
    always @(posedge clk)
        cp_all_sum: cover (sum == {WIDTH{1'b1}});

endmodule
