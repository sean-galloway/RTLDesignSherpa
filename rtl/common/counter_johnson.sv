`timescale 1ns / 1ps

module counter_johnson #(
    parameter int WIDTH = 4
) (
    input wire clk,
    input wire rst_n,
    input wire enable,
    output reg [WIDTH - 1:0] counter_gray
);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) counter_gray <= {WIDTH{1'b0}};
        else if (enable) begin
            counter_gray <= {counter_gray[WIDTH-2:0], ~counter_gray[WIDTH-1]};
        end
    end

endmodule : counter_johnson
