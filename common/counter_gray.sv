`timescale 1ns / 1ps

// A parameterized gray counter for async fifo's
module counter_gray #(
    parameter WIDTH = 4
)(
    input wire i_clk,
    input wire i_rst_n,
    input wire i_enable,
    output reg [WIDTH - 1:0] o_counter_gray
);

    reg [WIDTH - 1:0] counter_gray_next;

    // Flop stage for the counter
    always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!rst_n)
            o_counter_gray <= 'b0;
        else if (enable)
            o_counter_gray <= counter_gray_next;
    end

    // Calculate the next bits by XORing the current register
    always_comb begin
        counter_gray_next = o_counter_gray ^ (o_counter_gray >> 1);
    end

endmodule : counter_gray