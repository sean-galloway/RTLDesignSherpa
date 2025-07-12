`timescale 1ns / 1ps

module counter #(
    parameter int MAX = 32767
) (
    input  logic clk,
    rst_n,
    output logic tick
);

    logic [$clog2(MAX+1)-1:0] r_count;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_count <= '0;
        end else begin
            if (r_count == MAX[$clog2(MAX+1)-1:0]) begin
                r_count <= '0;
            end else begin
                r_count <= r_count + 1'b1;
            end
        end
    end

    assign tick = (r_count == MAX[$clog2(MAX+1)-1:0]);

endmodule : counter
