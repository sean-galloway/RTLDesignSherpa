`timescale 1ns / 1ps

// A binary counter for fifo's
// it counts to MAX then
//      clears the lower bits
//      inverts the upper bit
module counter_bin #(
    parameter WIDTH = 4,
    parameter MAX = 16
)(
    input wire clk,
    input wire rst_n,
    input wire enable,
    output reg [WIDTH-1:0] counter_out
);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            counter_out <= 'b0;
        else if (enable && (counter_out[WIDTH-2] == MAX - 1))
            counter_out <= {~counter_out[WIDTH-1], 'b0};
        else if (enable)
            counter_out <= counter_out + 1;
    end

endmodule : counter_bin