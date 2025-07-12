`timescale 1ns / 1ps

module reverse_vector #(
    parameter int WIDTH = 32
) (
    input        [WIDTH-1:0] vector,
    output logic [WIDTH-1:0] vector
);

    always_comb begin
        for (integer i = 0; i < WIDTH; i++) begin
            vector[(WIDTH-1)-i] = vector[i];
        end
    end

endmodule : reverse_vector
