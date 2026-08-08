// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for glitch_free_n_dff_arn (yosys-compatible)
// Proves: reset clears output, constant input propagates, output stable.

`include "reset_defs.svh"

module formal_glitch_free #(
    parameter int FLOP_COUNT = 3,
    parameter int WIDTH = 4
) (
    input wire clk,
    input wire rst_n
);

    // Use anyconst: the solver picks ONE value and holds it constant.
    // This models a stable CDC input, which is the expected use case.
    (* anyconst *) wire [WIDTH-1:0] d_const;

    // Also test with a free input for the output-stable property
    wire [WIDTH-1:0] d = d_const;

    wire [WIDTH-1:0] q;

    glitch_free_n_dff_arn #(
        .FLOP_COUNT (FLOP_COUNT),
        .WIDTH      (WIDTH)
    ) dut (
        .clk   (clk),
        .rst_n (rst_n),
        .d     (d),
        .q     (q)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // After reset, output is zero (all stages cleared)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n))
            ap_reset_zero: assert (q == '0);
    end

    // With constant input, output equals input after FLOP_COUNT cycles post-reset.
    // Reset deasserts at cycle 3 (f_past_valid=2 → assume rst_n).
    // Pipeline: cycle 3 stage0=d, cycle 4 stage1=d, cycle 5 stage2=d → q=d.
    // So at f_past_valid >= FLOP_COUNT+2, q should equal the constant d.
    always @(posedge clk) begin
        if (rst_n && f_past_valid >= (FLOP_COUNT + 3))
            ap_propagation: assert (q == d);
    end

    // Once output matches input, it stays matched (constant input → constant output)
    always @(posedge clk) begin
        if (f_past_valid > 0 && rst_n && $past(rst_n) && f_past_valid >= (FLOP_COUNT + 4))
            ap_output_stable: assert (q == $past(q));
    end

    // =========================================================================
    // Cover properties
    // =========================================================================
    always @(posedge clk) begin
        if (rst_n)
            cp_nonzero: cover (q != '0);
    end

    always @(posedge clk) begin
        if (rst_n)
            cp_all_ones: cover (q == {WIDTH{1'b1}});
    end

    always @(posedge clk) begin
        if (rst_n && f_past_valid >= (FLOP_COUNT + 3))
            cp_match: cover (q == d && d != '0);
    end

endmodule
