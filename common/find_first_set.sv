`timescale 1ns / 1ps

module find_first_set
#(parameter int WIDTH = 32)
(
    input  logic [WIDTH-1:0]         data,
    output logic [$clog2(WIDTH)-1:0] first_set_index
);

    integer i;

    always_comb begin
        first_set_index = 0; // Default value if no set bit is found

        for (i = 0; i < WIDTH; i++) begin
            if (data[i] == 1'b1) begin
                first_set_index = i + 1; // Add 1 to get a 1-based index
            end
        end
    end

endmodule : find_first_set