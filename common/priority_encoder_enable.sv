`timescale 1ns / 1ps

module priority_encoder_enable #(parameter WIDTH = 8)(
    input [WIDTH-1:0]              priority_in,
    input                          enable,
    output reg [$clog2(WIDTH)-1:0] encoded_output
);

    reg [WIDTH-1:0] priority_levels;
    reg found;

    always @* begin
        if (enable == 0) begin // Disable priority encoding
            encoded_output = {$clog2(WIDTH){1'b0}};
        end
        else begin
            found = 0;
            for (integer i = 0; i < WIDTH; i = i + 1) begin
                if (priority_in[i] == 1) begin
                    priority_levels = {WIDTH{1'b0}};
                    priority_levels[i] = 1;
                    found = 1;
                end
            end
            if (found == 1)
                encoded_output = $onehot(priority_levels); // Priority encoding
            else
                encoded_output = {$clog2(WIDTH){1'b0}};
        end
    end

endmodule