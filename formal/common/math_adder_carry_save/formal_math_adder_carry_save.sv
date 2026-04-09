// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_adder_carry_save (1-bit carry-save adder)
// Proves: sum + carry*2 == a + b + c (3:2 compression preserving value)

module formal_math_adder_carry_save (
    input logic clk
);

    (* anyconst *) logic a;
    (* anyconst *) logic b;
    (* anyconst *) logic c;

    logic sum;
    logic carry;

    math_adder_carry_save dut (
        .i_a     (a),
        .i_b     (b),
        .i_c     (c),
        .ow_sum  (sum),
        .ow_carry(carry)
    );

    // Reference: total input weight
    wire [1:0] input_sum = {1'b0, a} + {1'b0, b} + {1'b0, c};
    wire [1:0] output_sum = {carry, sum};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Core correctness: {carry, sum} == a + b + c
    always @(posedge clk)
        ap_sum_preserved: assert (output_sum == input_sum);

    // Sum is XOR of all inputs
    always @(posedge clk)
        ap_sum_xor: assert (sum == (a ^ b ^ c));

    // Carry is majority function
    always @(posedge clk)
        ap_carry_majority: assert (carry == ((a & b) | (a & c) | (b & c)));

    // Carry-save is identical to full adder for 1 bit
    always @(posedge clk)
        ap_matches_full_adder: assert ({carry, sum} == ({1'b0, a} + {1'b0, b} + {1'b0, c}));

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: all zeros
    always @(posedge clk)
        cp_all_zero: cover (a == 0 && b == 0 && c == 0);

    // Cover: all ones (sum=1, carry=1)
    always @(posedge clk)
        cp_all_ones: cover (a == 1 && b == 1 && c == 1);

    // Cover: carry without sum (exactly 2 inputs high)
    always @(posedge clk)
        cp_carry_no_sum: cover (carry == 1'b1 && sum == 1'b0);

    // Cover: sum without carry (exactly 1 input high)
    always @(posedge clk)
        cp_sum_no_carry: cover (carry == 1'b0 && sum == 1'b1);

endmodule
