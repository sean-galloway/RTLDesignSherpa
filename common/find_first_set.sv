`timescale 1ns / 1ps

module find_first_set
#(parameter      int WIDTH = 32)
(
    input  logic [WIDTH-1:0]         data,
    output logic [$clog2(WIDTH):0]   index
);

    localparam int N = $clog2(WIDTH)+1;

    logic found;

    always_comb begin
        index = {WIDTH{1'b0}}; // Default value if no bit is set
        found = 1'b0;
        
        for (int i = 0; i < WIDTH; i++) begin
            if (data[i] == 1'b1 && !found) begin
                index = i;
                found = 1'b1;
            end
        end
    end

endmodule : find_first_set