`timescale 1ns / 1ps

module counter #(
    parameter int MAX = 32767
) (
    input  logic i_clk,
    i_rst_n,
    output logic ow_tick
);

    logic [$clog2(MAX)-1:0] r_count;

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_count <= 'b0;
        end else begin
            r_count <= (r_count == MAX) ? 'b0 : r_count + 'b1;
        end
    end

    assign ow_tick = (r_count == MAX);

endmodule : counter
