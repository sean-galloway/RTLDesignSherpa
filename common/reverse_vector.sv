`timescale 1ns / 1ps

module reverse_vector #(parameter WIDTH=32) (
    input         [WIDTH-1:0] vector_in,
    output logic  [WIDTH-1:0] vector_out
);

    always_comb begin
        for (integer i=0; i<WIDTH; i++) begin
            vector_out[(WIDTH-1)-i] = vector_in[i];
        end
    end

endmodule : reverse_vector