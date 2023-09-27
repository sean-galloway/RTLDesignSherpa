`timescale 1ns / 1ps

module pwm #(
    parameter int WIDTH = 8
) (
    input  logic             i_clk,
    i_rst_n,  // clock and reset
    input  logic             i_start,         // i_start the pwm
    input  logic [WIDTH-1:0] i_duty,          // max count for keeping PWM high
    input  logic [WIDTH-1:0] i_period,        // max total count
    input  logic [WIDTH-1:0] i_repeat_count,  // repeat the counter
    output logic             ow_done,
    output logic             o_pwm            // done and the pwm signal
);

    logic [WIDTH-1:0] r_count;
    logic [WIDTH-1:0] r_repeat_value;
    logic w_count_met, w_counting, w_done_repeat;

    assign w_count_met = (r_count == i_period - 1);
    assign w_counting = (i_start && !ow_done);
    assign w_done_repeat = (i_repeat_count != 'b0) && (r_repeat_value == i_repeat_count);
    assign ow_done = w_done_repeat;

    // count handling
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) r_count <= 'b0;
        else if (w_count_met) r_count <= 'b0;
        else if (w_counting) r_count <= r_count + 1;
    end

    // repeat w_counting
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) r_repeat_value <= 'b0;
        else if (w_counting && w_count_met) r_repeat_value <= r_repeat_value + 'b1;
    end

    // pwm signal handling
    always_comb begin
        if (r_count < i_duty && !ow_done) o_pwm = 1;
        else o_pwm = 0;
    end

    // synopsys translate_off
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, pwm);
    end
    // synopsys translate_on

endmodule : pwm
