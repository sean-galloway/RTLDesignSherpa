// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for math_subtractor_full
// Proves 1-bit full subtractor correctness: {bout, diff} == a - b - bin

module formal_math_subtractor_full (
    input logic clk
);

    // =========================================================================
    // Free inputs -- solver explores all values
    // =========================================================================
    (* anyconst *) logic a;
    (* anyconst *) logic b;
    (* anyconst *) logic bin;

    logic diff, bout;

    // Instantiate DUT
    math_subtractor_full dut (
        .i_a   (a),
        .i_b   (b),
        .i_b_in(bin),
        .ow_d  (diff),
        .ow_b  (bout)
    );

    // =========================================================================
    // Reference model
    // =========================================================================
    logic [1:0] ref_result;
    assign ref_result = {1'b0, a} - {1'b0, b} - {1'b0, bin};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Difference bit matches reference
    always @(posedge clk) begin
        ap_diff: assert (diff == ref_result[0]);
    end

    // Borrow out matches reference (borrow = complement of carry in 2-bit subtraction)
    always @(posedge clk) begin
        ap_bout: assert (bout == ref_result[1]);
    end

    // Combined: {bout, diff} == a - b - bin (as 2-bit unsigned)
    always @(posedge clk) begin
        ap_combined: assert ({bout, diff} == ref_result);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover no borrow case
    always @(posedge clk) begin
        cp_no_borrow: cover (bout == 1'b0 && diff == 1'b1);
    end

    // Cover borrow case
    always @(posedge clk) begin
        cp_borrow: cover (bout == 1'b1);
    end

    // Cover all zeros
    always @(posedge clk) begin
        cp_all_zero: cover (a == 0 && b == 0 && bin == 0);
    end

    // Cover all ones
    always @(posedge clk) begin
        cp_all_one: cover (a == 1 && b == 1 && bin == 1);
    end

endmodule
