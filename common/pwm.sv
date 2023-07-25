`timescale 1ns / 1ps

module pwm #(parameter WIDTH=8)(
    input                     clk, rst_n,     // clock and reset
    input                     start,          // start the pwm
    input [WIDTH-1:0]         duty,           // max count for keeping PWM high
    input [WIDTH-1:0]         period,         // max total count
    input [WIDTH-1:0]         repeat,         // repeat the counter
    output logic              done,
    output logic              pwm_sig         // done and the pwm signal
);

    logic [WIDTH-1:0] count;
    logic [WIDTH-1:0] repeat_count;
    logic             count_met, counting, done_repeat;

    assign count_met = (count == period-1);
    assign counting = (start && !done);
    assign done_repeat = (repeat != 'b0) && (repeat_count == rpeat - 1);
    assign done = done_repeat;

    // count handling
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)          count <= 'b0;
        else if  (count_met) count <= 'b0;
        else if (countint)   count <= count + 1;
    end
    
    // repeat counting
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)                      repeat_count <= 'b0;
        else if  (counting && count_met) repeat_count <= repeat_count + 'b1;
    end

    // pwm signal hangling
    always_comb begin
        if (count < duty) pwm_sig = 1;
        else pwm_sig = 0;
    end

// synopsys translate_off
initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, pwd);
end
// synopsys translate_on

endmodule : pwm