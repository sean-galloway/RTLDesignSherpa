// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_adder_brent_kung_sum (N-bit sum extraction)
// Proves: sum[k] == gg[k] ^ p[k+1], carry == gg[N]

module formal_math_adder_brent_kung_sum #(
    parameter int WIDTH = 8
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH:0] p;
    (* anyconst *) logic [WIDTH:0] gg;

    logic [WIDTH-1:0] sum;
    logic             carry;

    math_adder_brent_kung_sum #(.N(WIDTH)) dut (
        .i_p     (p),
        .i_gg    (gg),
        .ow_sum  (sum),
        .ow_carry(carry)
    );

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Sum bit k == gg[k] ^ p[k+1] for each bit position
    genvar k;
    generate
        for (k = 0; k < WIDTH; k++) begin : gen_sum_check
            always @(posedge clk)
                assert (sum[k] == (gg[k] ^ p[k+1]));
        end
    endgenerate

    // Carry is the MSB of the group-generate
    always @(posedge clk)
        ap_carry: assert (carry == gg[WIDTH]);

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: no carry
    always @(posedge clk)
        cp_no_carry: cover (carry == 1'b0 && sum != '0);

    // Cover: carry set
    always @(posedge clk)
        cp_carry_set: cover (carry == 1'b1);

    // Cover: all sum bits set
    always @(posedge clk)
        cp_all_sum: cover (sum == {WIDTH{1'b1}});

    // Cover: sum is zero
    always @(posedge clk)
        cp_zero_sum: cover (sum == '0);

endmodule
