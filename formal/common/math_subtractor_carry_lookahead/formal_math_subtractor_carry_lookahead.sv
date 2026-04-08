// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_subtractor_carry_lookahead
// Proves N-bit CLA subtractor: {bout, diff} == a - b - bin

module formal_math_subtractor_carry_lookahead #(
    parameter int WIDTH = 8
) (
    input logic clk
);

    // =========================================================================
    // Free inputs -- solver explores all values
    // =========================================================================
    (* anyconst *) logic [WIDTH-1:0] a;
    (* anyconst *) logic [WIDTH-1:0] b;
    (* anyconst *) logic             bin;

    logic [WIDTH-1:0] diff;
    logic [WIDTH-1:0] ow_d;
    logic              bout;
    logic              ow_b;

    // Instantiate DUT
    math_subtractor_carry_lookahead #(.N(WIDTH)) dut (
        .i_a          (a),
        .i_b          (b),
        .i_borrow_in  (bin),
        .ow_difference(diff),
        .ow_d         (ow_d),
        .ow_borrow_out(bout),
        .ow_b         (ow_b)
    );

    // =========================================================================
    // Reference model
    // =========================================================================
    logic [WIDTH:0] ref_result;
    assign ref_result = {1'b0, a} - {1'b0, b} - {{WIDTH{1'b0}}, bin};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Difference matches reference
    always @(posedge clk) begin
        ap_diff: assert (diff == ref_result[WIDTH-1:0]);
    end

    // Borrow out matches reference
    always @(posedge clk) begin
        ap_bout: assert (bout == ref_result[WIDTH]);
    end

    // Combined equivalence
    always @(posedge clk) begin
        ap_combined: assert ({bout, diff} == ref_result);
    end

    // Duplicate outputs match primary outputs
    always @(posedge clk) begin
        ap_ow_d_matches: assert (ow_d == diff);
    end

    always @(posedge clk) begin
        ap_ow_b_matches: assert (ow_b == bout);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover no borrow
    always @(posedge clk) begin
        cp_no_borrow: cover (bout == 1'b0 && a > b);
    end

    // Cover borrow out
    always @(posedge clk) begin
        cp_borrow: cover (bout == 1'b1);
    end

    // Cover zero result
    always @(posedge clk) begin
        cp_zero_diff: cover (diff == '0 && bout == 1'b0);
    end

    // Cover max result
    always @(posedge clk) begin
        cp_max_diff: cover (diff == {WIDTH{1'b1}});
    end

endmodule
