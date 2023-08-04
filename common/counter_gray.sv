`timescale 1ns / 1ps

// A parameterized gray counter for async fifo's
module counter_gray #(
    parameter WIDTH = 4
)(
    input wire clk,
    input wire rst_n,
    input wire enable,
    output reg [WIDTH - 1:0] counter_out_gray
);

    reg [WIDTH - 1:0] counter_out_gray_next;

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n)
            counter_out_gray <= 'b0;
        else if (enable)
            counter_out_gray <= counter_out_gray_next;
    end

    always_comb begin
        counter_out_gray_next = counter_out_gray ^ (counter_out_gray >> 1);
    end

endmodule : counter_gray