`timescale 1ns / 1ps

module encoder_priority_enable #(
    parameter int WIDTH = 8
) (
    input  logic [        WIDTH-1:0] i_priority,
    input  logic                     i_enable,
    output logic [$clog2(WIDTH)-1:0] ow_encode
);

    logic found;

    always_comb begin
        found = 0;  // Initialize found to 0

        if (i_enable == 0) begin  // Disable priority encoding
            ow_encode = {$clog2(WIDTH) {1'b0}};
        end else begin
            logic [WIDTH-1:0] w_priority_levels;  // Intermediate variable

            w_priority_levels = '0;  // Initialize w_priority_levels to all zeroes

            for (integer i = 0; i < WIDTH; i++) begin
                if (i_priority[i] == 1) begin
                    w_priority_levels[i] = 1;
                    found = 1;
                end
            end

            if (found == 1) ow_encode = $onehot(w_priority_levels);  // Priority encoding
            else ow_encode = {$clog2(WIDTH) {1'b0}};
        end
    end

endmodule : encoder_priority_enable
