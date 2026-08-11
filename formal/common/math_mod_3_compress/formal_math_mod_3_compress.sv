// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Formal wrapper for math_mod_3_compress (16-bit combinational mod-3)
// Proves: rem_out == d_in % 3 against the SMT modulo, over the full input space.

module formal_math_mod_3_compress (
    input logic clk
);

    (* anyconst *) logic [15:0] d_in;

    logic [1:0] rem_out;

    math_mod_3_compress dut (
        .d_in   (d_in),
        .rem_out(rem_out)
    );

    // Reference: exact modulo computed by the solver
    wire [1:0] ref_rem = 2'(d_in % 16'd3);

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Core correctness: compressor tree + fold == d_in mod 3
    always @(posedge clk)
        ap_rem_correct: assert (rem_out == ref_rem);

    // Residue range: mod-3 never emits 3
    always @(posedge clk)
        ap_rem_range: assert (rem_out <= 2'd2);

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: each residue value reachable
    always @(posedge clk)
        cp_rem_0: cover (rem_out == 2'd0 && d_in != '0);
    always @(posedge clk)
        cp_rem_1: cover (rem_out == 2'd1);
    always @(posedge clk)
        cp_rem_2: cover (rem_out == 2'd2);

    // Cover: zero input
    always @(posedge clk)
        cp_zero: cover (d_in == '0 && rem_out == 2'd0);

    // Cover: all-ones input, maximum digit sum (24) through the whole tree
    always @(posedge clk)
        cp_all_ones: cover (d_in == 16'hFFFF && rem_out == 2'd0);

    // Cover: fold lands in the >=6 subtract branch (five base-4 digits of 3
    // give digit sum 15 -> fold 6)
    always @(posedge clk)
        cp_fold_ge6: cover (d_in == 16'h03FF && rem_out == 2'd0);

    // Cover: fold lands in the >=3 subtract branch (digit sum 6 -> fold 3)
    always @(posedge clk)
        cp_fold_ge3: cover (d_in == 16'h000F && rem_out == 2'd0);

endmodule
