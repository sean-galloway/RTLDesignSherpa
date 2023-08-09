`timescale 1ns / 1ps

// A parameterized synchronizer
module glitch_free_n_dff_arn #( parameter FLOP_COUNT = 3,
                                parameter WIDTH = 4)
(
    input wire i_clk, i_rst_n,
    input wire [WIDTH-1:0] i_d,
    output reg [WIDTH-1:0] o_q
);

    localparam FC = FLOP_COUNT;

    logic [WIDTH-1:0] r_q_array [0:FC-1];

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            for (int i = 0; i < FC; i++)
                r_q_array[i] <= 'b0;
        end else begin
            r_q_array[0] <= i_d;
            for (int i = 1; i < FC; i++)
                r_q_array[i] <= r_q_array[i-1];
        end
    end

    assign o_q = r_q_array[FC-1];

endmodule : glitch_free_n_dff_arn