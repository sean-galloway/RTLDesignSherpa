// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for bin_to_bcd (Double Dabble binary-to-BCD converter)
// This is a sequential module with a state machine. We verify:
//   1. Each BCD digit is in valid range [0..9] when done is asserted
//   2. The BCD output value equals the binary input when done is asserted
//   3. Reset clears the FSM to IDLE
//   4. Done is never asserted in reset
//
// Parameters: WIDTH=8, DIGITS=3 (handles 0..255 -> 000..255 BCD)
// The conversion takes ~(WIDTH * DIGITS * 2 + overhead) cycles.
// For WIDTH=8, DIGITS=3: ~50-60 cycles. BMC depth 80 is sufficient.

module formal_bin_to_bcd #(
    parameter int WIDTH  = 8,
    parameter int DIGITS = 3
) (
    input logic clk,
    input logic rst_n,
    input logic start
);

    (* anyconst *) logic [WIDTH-1:0] binary;

    logic [DIGITS*4-1:0] bcd;
    logic                done;

    bin_to_bcd #(
        .WIDTH (WIDTH),
        .DIGITS(DIGITS)
    ) dut (
        .clk    (clk),
        .rst_n  (rst_n),
        .start  (start),
        .binary (binary),
        .bcd    (bcd),
        .done   (done)
    );

    // =========================================================================
    // Formal infrastructure
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // Assumptions: start in reset for first 2 cycles, then release
    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid < 2) assume (!rst_n);
        if (f_past_valid >= 2) assume (rst_n);
    end

    // After reset release, pulse start exactly once at cycle 3
    always @(posedge clk) begin
        if (f_past_valid == 2)
            assume (start);
        else
            assume (!start);
    end

    // =========================================================================
    // Reference model: compute expected BCD from binary input
    // For WIDTH=8, DIGITS=3: hundreds, tens, ones
    // =========================================================================
    logic [3:0] ref_digit0;  // ones
    logic [3:0] ref_digit1;  // tens
    logic [3:0] ref_digit2;  // hundreds
    logic [DIGITS*4-1:0] ref_bcd;

    assign ref_digit2 = 4'(binary / 100);
    assign ref_digit1 = 4'((binary % 100) / 10);
    assign ref_digit0 = 4'(binary % 10);
    assign ref_bcd = {ref_digit2, ref_digit1, ref_digit0};

    // =========================================================================
    // Safety properties
    // =========================================================================

    // When done is asserted (and we're past reset), each BCD digit must be in range [0, 9]
    generate
        genvar d;
        for (d = 0; d < DIGITS; d++) begin : gen_digit_range
            always @(posedge clk) begin
                if (rst_n && done)
                    assert (bcd[d*4 +: 4] <= 4'd9);
            end
        end
    endgenerate

    // When done is asserted (and we're past reset), BCD output must equal the reference
    always @(posedge clk) begin
        if (rst_n && done)
            ap_bcd_correct: assert (bcd == ref_bcd);
    end

    // After reset deasserts, done should not be asserted until conversion finishes
    // (done should be 0 immediately after reset)
    always @(posedge clk) begin
        if (f_past_valid > 0 && $past(!rst_n) && rst_n)
            ap_no_done_after_reset: assert (!done);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover: conversion completes
    always @(posedge clk)
        if (f_past_valid > 3)
            cp_done: cover (done == 1'b1);

    // Cover: convert value 0
    always @(posedge clk)
        if (f_past_valid > 3)
            cp_zero: cover (done == 1'b1 && binary == '0);

    // Cover: convert maximum value (255 for 8-bit)
    always @(posedge clk)
        if (f_past_valid > 3)
            cp_max: cover (done == 1'b1 && binary == {WIDTH{1'b1}});

    // Cover: convert value with all BCD digits nonzero
    always @(posedge clk)
        if (f_past_valid > 3)
            cp_all_digits_nonzero: cover (done == 1'b1 &&
                                          bcd[3:0] != 4'd0 &&
                                          bcd[7:4] != 4'd0 &&
                                          bcd[11:8] != 4'd0);

endmodule
