`timescale 1ns / 1ps
module find_last_set #(
    parameter int WIDTH = 32,
    parameter string INSTANCE_NAME = "FLS"
) (
    input  logic [WIDTH-1:0] data,
    output logic [$clog2(WIDTH)-1:0] index  // Changed to match arbiter's N
);
    localparam int N = $clog2(WIDTH);  // Changed to match arbiter's definition
    logic w_found;

    always_comb begin
        index = {N{1'b0}}; // Default value if no bit is set
        w_found = 1'b0;

        for (int i = WIDTH - 1; i >= 0; i--) begin
            if (data[i] && !w_found) begin
                index = i[N-1:0]; // Ensure correct bit width
                w_found = 1'b1;
            end
        end
    end
endmodule : find_last_set
