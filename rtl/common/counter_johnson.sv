`timescale 1ns / 1ps

module counter_johnson #(
    parameter int WIDTH = 4
) (
    input wire i_clk,
    input wire i_rst_n,
    input wire i_enable,
    output reg [WIDTH - 1:0] o_counter_gray
);

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) o_counter_gray <= {WIDTH{1'b0}};
        else if (i_enable) begin
            o_counter_gray <= {o_counter_gray[WIDTH-2:0], ~o_counter_gray[WIDTH-1]};
        end
    end

endmodule : counter_johnson
