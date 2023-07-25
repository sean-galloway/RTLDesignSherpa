`timescale 1ns / 1ps

module pwm #(parameter WIDTH=8)(
    input                     clk, rst_n,     // clock and reset
    input [WIDTH-1:0]         duty,           // max count for keeping PWM high
    input [WIDTH-1:0]         period,         // max total count
    output logic              pwm_sig         // done and the pwm signal
);

    logic [WIDTH-1:0] count;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) count <= 'b0;
        else if (count == period-1) count <= 'b0;
        else count <= count + 1;
    end
    
    always_comb begin
        if (count < duty) pwm_sig = 1;
        else pwm_sig = 0;
    end

    // synopsys translate_off

initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, round_robin_wrapper);
end
// synopsys translate_on

endmodule : pwm