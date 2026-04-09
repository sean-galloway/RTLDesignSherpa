// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_adder_brent_kung_grouppg_016
// Proves the 16-bit group PG tree correctly computes carry chain outputs
// by comparing against a ripple-carry reference model.

module formal_math_adder_brent_kung_grouppg_016 (
    input logic clk
);

    localparam int N = 16;

    (* anyconst *) logic [N:0] i_p;
    (* anyconst *) logic [N:0] i_g;

    logic [N:0] ow_gg;
    logic [N:0] ow_pp;

    math_adder_brent_kung_grouppg_016 #(
        .N(N)
    ) dut (
        .i_p  (i_p),
        .i_g  (i_g),
        .ow_gg(ow_gg),
        .ow_pp(ow_pp)
    );

    // =========================================================================
    // Reference model: ripple carry computation from PG inputs
    // =========================================================================
    logic [N:0] ref_carry;

    always_comb begin
        ref_carry[0] = i_g[0];
        for (int k = 1; k <= N; k++) begin
            ref_carry[k] = i_g[k] | (i_p[k] & ref_carry[k-1]);
        end
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Primary property: ow_gg matches ripple-carry reference for all bit positions
    generate
        genvar k;
        for (k = 0; k <= N; k++) begin : gen_carry_check
            always @(posedge clk)
                assert (ow_gg[k] == ref_carry[k]);
        end
    endgenerate

    // Passthrough: ow_gg[0] is directly i_g[0]
    always @(posedge clk)
        ap_gg0_passthrough: assert (ow_gg[0] == i_g[0]);

    // Passthrough: ow_pp[0] is directly i_p[0]
    always @(posedge clk)
        ap_pp0_passthrough: assert (ow_pp[0] == i_p[0]);

    // If all generates are set, all carries must be set
    always @(posedge clk)
        ap_all_gen: assert (!(i_g == {(N+1){1'b1}}) || (ow_gg == {(N+1){1'b1}}));

    // If no generate and no propagate above bit 0, upper carries are zero
    always @(posedge clk)
        if (i_g[N:1] == '0 && i_p[N:1] == '0)
            ap_no_gen_no_prop: assert (ow_gg[N:1] == '0);

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: all carries generated
    always @(posedge clk)
        cp_all_carries: cover (ow_gg == {(N+1){1'b1}});

    // Cover: no carries at all
    always @(posedge clk)
        cp_no_carries: cover (ow_gg == '0);

    // Cover: carry propagates from bit 0 all the way to bit N
    always @(posedge clk)
        cp_full_propagation: cover (i_g[0] == 1'b1 && i_g[N:1] == '0 &&
                                    i_p == {(N+1){1'b1}} && ow_gg[N] == 1'b1);

    // Cover: only MSB carry set
    always @(posedge clk)
        cp_msb_only: cover (ow_gg[N] == 1'b1 && ow_gg[N-1:1] == '0);

endmodule
