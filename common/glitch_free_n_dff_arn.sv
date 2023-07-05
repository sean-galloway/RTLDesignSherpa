`timescale 1ns / 1ps

module glitch_free_n_dff_arn  #(parameter FLOP_COUNT = 2,
                                parameter WIDTH = 4)
        (
            output reg  [WIDTH-1:0] q,
            input  wire [WIDTH-1:0] d,
            input  wire             clk, rst_n
        );

    logic [FLOP_COUNT-1:0] flop_out_reg [0:WIDTH-1];

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            flop_out_reg[0] <= '0;
        else
            flop_out_reg[0] <= (d);
    end

    generate
        genvar i;
        for (i = 1; i < FLOP_COUNT; i = i + 1) begin : FLOP_LOOP
            always @(posedge clk or negedge rst_n) begin
                if (!rst_n)
                    flop_out_reg[i] <= '0;
                else
                    flop_out_reg[i] <= flop_out_reg[i-1];
            end
        end
    endgenerate

    always @* begin
        assign q = flop_out_reg[FLOP_COUNT-1];
    end
endmodule