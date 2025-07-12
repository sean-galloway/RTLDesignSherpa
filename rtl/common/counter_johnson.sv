`timescale 1ns / 1ps

module counter_johnson #(
    parameter int WIDTH = 4
) (
    input  logic                clk,
    input  logic                rst_n,
    input  logic                enable,
    output logic [WIDTH - 1:0]  counter_gray
);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) counter_gray <= {WIDTH{1'b0}};
        else if (enable) begin
            counter_gray <= {counter_gray[WIDTH-2:0], ~counter_gray[WIDTH-1]};
        end
    end

endmodule : counter_johnson
