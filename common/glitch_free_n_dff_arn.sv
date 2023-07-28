`timescale 1ns / 1ps

module glitch_free_n_dff_arn #( parameter FLOP_COUNT = 3,
                                parameter WIDTH = 4)
(
    input wire clk, rst_n,
    input wire [WIDTH-1:0] d,
    output reg [WIDTH-1:0] q
);

    localparam FC = FLOP_COUNT;

    logic [WIDTH-1:0] q_array [0:FC-1];

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < FC; i++)
                q_array[i] <= 'b0;
        end else begin
            q_array[0] <= d;
            for (int i = 1; i < FC; i++)
                q_array[i] <= q_array[i-1];
        end
    end

    assign q = q_array[FC-1];

endmodule : glitch_free_n_dff_arn