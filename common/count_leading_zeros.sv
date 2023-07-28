`timescale 1ns / 1ps

module count_leading_zeros #(parameter int WIDTH = 32)
(
    input logic [WIDTH-1:0]          data,
    output logic [$clog2(WIDTH)-1:0] leading_zeros_count
);

    logic [$clog2(WIDTH)-1:0] leading_zeros;

    always_comb begin
        leading_zeros = WIDTH - 1;
        for (int i = WIDTH-1; i >= 0; i--) begin
            if (data[i] == 1'b1) begin
                leading_zeros = i;
            end
        end
    end

    assign leading_zeros_count = WIDTH - leading_zeros - 1;

endmodule : count_leading_zeros
