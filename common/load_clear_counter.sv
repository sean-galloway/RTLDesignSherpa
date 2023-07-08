`timescale 1ns / 1ps

module load_clear_counter #(parameter MAX=32) (
    input  wire                   clk, rst_n,
    input  wire                   clear, increment, load,
    input  wire [$clog2(MAX)-1:0] loadval,
    output reg  [$clog2(MAX)-1:0] count
);

    localparam SIZE = $clog2(MAX);

    always @(posedge clk, negedge rst_n) begin
        if (!rst_n) count <= {SIZE{1'b0}};
        else if (clear) count <= {SIZE{1'b0}};
        else if (load)  count <= loadval;
        else if (increment) begin
            count <= (count == MAX) ? {SIZE{1'b0}} : count + 'b1;
        end
    end
endmodule