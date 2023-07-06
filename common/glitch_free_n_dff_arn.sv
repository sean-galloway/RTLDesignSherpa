`timescale 1ns / 1ps

module glitch_free_n_dff_arn  #(parameter FLOP_COUNT = 2,
                                parameter WIDTH = 4)
        (
            output reg  [WIDTH-1:0] q,
            input  wire [WIDTH-1:0] d,
            input  wire             clk, rst_n
        );

    localparam FC = FLOP_COUNT;

    logic [WIDTH-1:0] q0, q1, q2, q3;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            q0 <= 'b0;
            q1 <= 'b0;
            q2 <= 'b0;
            q3 <= 'b0;
        end else begin
            q0 <= d;
            q1 <= q0;
            q2 <= q1;
            q3 <= q2;
        end
    end

    assign q = (FC==4) ? q3 : (FC==3) ? q2 : (FC==2) ? q1 : q0;

endmodule