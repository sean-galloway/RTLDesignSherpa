`timescale 1ns / 1ps

module find_first_set
#(parameter int WIDTH = 32)
(
    input  logic [WIDTH-1:0]         data,
    output logic [$clog2(WIDTH)-1:0] first_set_index
);

    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin
            if (i == 0) begin
                assign first_set_index = data[i] ? i : '1; // Set to i if data[i] is 1, otherwise '1
            end
            else begin
                assign first_set_index = (!first_set_index[WIDTH-1:i+1] & data[i]) ? i : first_set_index;
            end
        end
    endgenerate

endmodule : find_first_set