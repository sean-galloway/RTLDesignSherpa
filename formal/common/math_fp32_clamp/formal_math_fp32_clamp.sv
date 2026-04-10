// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_fp32_clamp
//
// Verifies:
//   - Output in [min, max] range when no NaN
//   - NaN passthrough (any NaN input => result == i_x)
//   - Identity when input already in range
//   - Clamp to min when x < min
//   - Clamp to max when x > max

`timescale 1ns / 1ps

module formal_math_fp32_clamp (
    input logic clk
);

    // Free inputs
    (* anyconst *) logic [31:0] x;
    (* anyconst *) logic [31:0] lo;
    (* anyconst *) logic [31:0] hi;

    // DUT
    logic [31:0] result;

    math_fp32_clamp dut (
        .i_x       (x),
        .i_min     (lo),
        .i_max     (hi),
        .ow_result (result)
    );

    // Field extraction
    wire [7:0]  exp_x   = x[30:23];
    wire [22:0] mant_x  = x[22:0];
    wire [7:0]  exp_lo  = lo[30:23];
    wire [22:0] mant_lo = lo[22:0];
    wire [7:0]  exp_hi  = hi[30:23];
    wire [22:0] mant_hi = hi[22:0];

    // NaN detection
    wire x_nan  = (exp_x  == 8'hFF) & (mant_x  != 23'h0);
    wire lo_nan = (exp_lo == 8'hFF) & (mant_lo != 23'h0);
    wire hi_nan = (exp_hi == 8'hFF) & (mant_hi != 23'h0);
    wire any_nan = x_nan | lo_nan | hi_nan;

    // Property 1: NaN passthrough
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_passthrough: assert (result == x);
        end
    end

    // Property 2: Result is one of {x, lo, hi}
    always @(posedge clk) begin
        p_result_is_input: assert (result == x || result == lo || result == hi);
    end

    // FP comparison helpers
    wire x_lt_lo;
    assign x_lt_lo = (x[31] != lo[31]) ? x[31] :
                     (x[31] == 1'b0)   ? (x[30:0] < lo[30:0]) :
                                         (x[30:0] > lo[30:0]);

    wire hi_lt_x;
    assign hi_lt_x = (hi[31] != x[31]) ? hi[31] :
                     (hi[31] == 1'b0)  ? (hi[30:0] < x[30:0]) :
                                         (hi[30:0] > x[30:0]);

    // Property 3: Clamp to min
    always @(posedge clk) begin
        if (!any_nan && x_lt_lo) begin
            p_clamp_to_min: assert (result == lo);
        end
    end

    // Property 4: Clamp to max (only when min check doesn't fire first)
    always @(posedge clk) begin
        if (!any_nan && hi_lt_x && !x_lt_lo) begin
            p_clamp_to_max: assert (result == hi);
        end
    end

    // Property 5: Identity when in range
    always @(posedge clk) begin
        if (!any_nan && !x_lt_lo && !hi_lt_x) begin
            p_identity: assert (result == x);
        end
    end

    // Cover properties
    always @(posedge clk) begin
        c_clamp_lo: cover (!any_nan && x_lt_lo);
        c_clamp_hi: cover (!any_nan && hi_lt_x);
        c_identity: cover (!any_nan && !x_lt_lo && !hi_lt_x);
        c_nan_x:    cover (x_nan);
    end

endmodule
