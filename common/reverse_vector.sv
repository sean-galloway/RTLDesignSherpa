`timescale 1ns / 1ps

module reverse_vector #(parameter WIDTH=32) (
    input  wire [WIDTH-1:0] vector_in,
    output reg  [WIDTH-1:0] vector_out
);
    always @* begin
        for (integer i=0; i<WIDTH; i++) begin
            vector_out[(WIDTH-1)-i] = vector_in[i];
        end
    end
endmodule