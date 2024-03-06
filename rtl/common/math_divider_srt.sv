`timescale 1ns / 1ps

// Based on code from: https://projectf.io/posts/division-in-verilog/
// Heavily modified for naming conventions
module math_divider_srt #(
    parameter int DATA_WIDTH = 16
) (
    input logic i_clk,
    input logic i_rst_b,
    input logic i_start,
    output logic o_busy,
    output logic o_done,
    output logic o_valid,
    output logic o_dbz,
    input logic [DATA_WIDTH-1:0] i_dividend,
    input logic [DATA_WIDTH-1:0] i_divisor,
    output logic [DATA_WIDTH-1:0] o_quotient,
    output logic [DATA_WIDTH-1:0] o_remainder
);

    logic [DATA_WIDTH-1:0] r_divisor;
    logic [DATA_WIDTH-1:0] r_quo, w_quo_next;
    logic [DATA_WIDTH:0] r_acc, w_acc_next;
    logic [$clog2(DATA_WIDTH)-1:0] r_i;

    always_comb begin
        if (r_acc >= {1'b0, r_divisor}) begin
            w_acc_next = r_acc - r_divisor;
            {w_acc_next, w_quo_next} = {w_acc_next[DATA_WIDTH-1:0], r_quo, 1'b1};
        end else begin
            {w_acc_next, w_quo_next} = {r_acc, r_quo} << 1;
        end
    end

    always_ff @(posedge i_clk, negedge i_rst_b) begin
        if (!i_rst_b) begin
            // Reset state
            o_busy      <= 0;
            o_done      <= 0;
            o_valid     <= 0;
            o_dbz       <= 0;
            o_quotient  <= 0;
            o_remainder <= 0;
            r_i         <= 0;
            // $display("Reset: Time = %0t", $time);
        end else begin
            o_done <= 0;
            if (i_start) begin
                // Start division
                o_valid <= 0;
                r_i     <= 0;
                if (i_divisor == 0) begin
                    // Handle divide by zero
                    o_busy <= 0;
                    o_done <= 1;
                    o_dbz  <= 1;
                    // $display("Divide by zero: Time = %0t", $time);
                end else begin
                    // Initialize division
                    o_busy         <= 1;
                    o_dbz          <= 0;
                    r_divisor      <= i_divisor;
                    {r_acc, r_quo} <= {{DATA_WIDTH{1'b0}}, i_dividend, 1'b0};
                    // $display("Start Division: Dividend = %0d, Divisor = %0d, Time = %0t", i_dividend, i_divisor, $time);
                end
            end else if (o_busy) begin
                // Division in progress
                if (r_i == DATA_WIDTH - 1) begin
                    // Division complete
                    o_busy      <= 0;
                    o_done      <= 1;
                    o_valid     <= 1;
                    o_quotient  <= w_quo_next;
                    o_remainder <= w_acc_next[DATA_WIDTH:1];
                    // $display("Division Complete: Quotient = %0d, Remainder = %0d, Time = %0t", o_quotient, o_remainder, $time);
                end else begin
                    // Next iteration
                    r_i   <= r_i + 1;
                    r_acc <= w_acc_next;
                    r_quo <= w_quo_next;
                    // $display("Iteration %0d: Acc = %0d, Quo = %0d, Time = %0t", r_i, r_acc, r_quo, $time);
                end
            end
        end
    end
endmodule : math_divider_srt
