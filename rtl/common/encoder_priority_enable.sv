`timescale 1ns / 1ps

module encoder_priority_enable #(
    parameter int WIDTH = 8
) (
    input  logic [        WIDTH-1:0] priority_in,
    input  logic                     enable,
    output logic [$clog2(WIDTH)-1:0] encode
);

    logic found;

    always_comb begin
        // Default assignments to prevent latches
        encode = '0;
        found = 1'b0;

        if (enable == 1'b1) begin
            // Find the highest priority bit using found flag to prevent overwrites
            for (int i = WIDTH-1; i >= 0; i--) begin
                if (priority_in[i] == 1'b1 && !found) begin
                    encode = $clog2(WIDTH)'(i);
                    found = 1'b1;
                end
            end
        end
    end

endmodule : encoder_priority_enable
