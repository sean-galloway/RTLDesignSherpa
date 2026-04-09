// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_adder_brent_kung_bitwisepg (N-bit bitwise PG)
// Proves: p[k+1] == a[k]^b[k], g[k+1] == a[k]&b[k], g[0] == cin, p[0] == 0

module formal_math_adder_brent_kung_bitwisepg #(
    parameter int WIDTH = 8
) (
    input logic clk
);

    (* anyconst *) logic [WIDTH-1:0] a;
    (* anyconst *) logic [WIDTH-1:0] b;
    (* anyconst *) logic             cin;

    logic [WIDTH:0] g;
    logic [WIDTH:0] p;

    math_adder_brent_kung_bitwisepg #(.N(WIDTH)) dut (
        .i_a (a),
        .i_b (b),
        .i_c (cin),
        .ow_g(g),
        .ow_p(p)
    );

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Bit-0 initialization: p[0] == 0, g[0] == cin
    always @(posedge clk)
        ap_p0_zero: assert (p[0] == 1'b0);

    always @(posedge clk)
        ap_g0_cin: assert (g[0] == cin);

    // Per-bit PG generation: p[k+1] == a[k]^b[k], g[k+1] == a[k]&b[k]
    genvar k;
    generate
        for (k = 0; k < WIDTH; k++) begin : gen_pg_check
            always @(posedge clk)
                assert (p[k+1] == (a[k] ^ b[k]));
            always @(posedge clk)
                assert (g[k+1] == (a[k] & b[k]));
        end
    endgenerate

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: all propagate (a and b differ on every bit)
    always @(posedge clk)
        cp_all_prop: cover (p[WIDTH:1] == {WIDTH{1'b1}});

    // Cover: all generate (a and b both 1 on every bit)
    always @(posedge clk)
        cp_all_gen: cover (g[WIDTH:1] == {WIDTH{1'b1}});

    // Cover: no generate, no propagate (a and b both 0 on every bit)
    always @(posedge clk)
        cp_all_kill: cover (g[WIDTH:1] == '0 && p[WIDTH:1] == '0);

    // Cover: carry-in set
    always @(posedge clk)
        cp_cin_set: cover (cin == 1'b1);

endmodule
