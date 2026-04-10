// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal verification wrapper for math_bf16_clamp
//
// Verifies:
//   - Output in [min, max] range when no NaN
//   - NaN passthrough (any NaN input => result == i_x)
//   - Identity when input already in range
//   - Clamp to min when x < min
//   - Clamp to max when x > max

`timescale 1ns / 1ps

module formal_math_bf16_clamp (
    input logic clk
);

    // Free inputs
    (* anyconst *) logic [15:0] x;
    (* anyconst *) logic [15:0] lo;
    (* anyconst *) logic [15:0] hi;

    // DUT
    logic [15:0] result;

    math_bf16_clamp dut (
        .i_x       (x),
        .i_min     (lo),
        .i_max     (hi),
        .ow_result (result)
    );

    // Field extraction
    wire [7:0] exp_x  = x[14:7];
    wire [6:0] mant_x = x[6:0];
    wire [7:0] exp_lo = lo[14:7];
    wire [6:0] mant_lo = lo[6:0];
    wire [7:0] exp_hi = hi[14:7];
    wire [6:0] mant_hi = hi[6:0];

    // NaN detection
    wire x_nan  = (exp_x  == 8'hFF) & (mant_x  != 7'h0);
    wire lo_nan = (exp_lo == 8'hFF) & (mant_lo != 7'h0);
    wire hi_nan = (exp_hi == 8'hFF) & (mant_hi != 7'h0);
    wire any_nan = x_nan | lo_nan | hi_nan;

    // Property 1: NaN passthrough -- any NaN => result == x
    always @(posedge clk) begin
        if (any_nan) begin
            p_nan_passthrough: assert (result == x);
        end
    end

    // Property 2: Result is one of {x, lo, hi}
    always @(posedge clk) begin
        p_result_is_input: assert (result == x || result == lo || result == hi);
    end

    // Property 3: When no NaN, result == lo when x < lo
    // Use the DUT's own comparison logic: fp_less_than(x, lo)
    // We replicate it: negative < positive; same sign => compare magnitudes
    wire x_lt_lo;
    assign x_lt_lo = (x[15] != lo[15]) ? x[15] :
                     (x[15] == 1'b0)   ? (x[14:0] < lo[14:0]) :
                                         (x[14:0] > lo[14:0]);

    wire hi_lt_x;
    assign hi_lt_x = (hi[15] != x[15]) ? hi[15] :
                     (hi[15] == 1'b0)  ? (hi[14:0] < x[14:0]) :
                                         (hi[14:0] > x[14:0]);

    always @(posedge clk) begin
        if (!any_nan && x_lt_lo) begin
            p_clamp_to_min: assert (result == lo);
        end
    end

    // Property 4: When no NaN, result == hi when x > hi (and x >= lo, per priority)
    always @(posedge clk) begin
        if (!any_nan && hi_lt_x && !x_lt_lo) begin
            p_clamp_to_max: assert (result == hi);
        end
    end

    // Property 5: When no NaN and in range, result == x (identity)
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
        c_nan_lo:   cover (lo_nan);
        c_nan_hi:   cover (hi_nan);
    end

endmodule
