`timescale 1ns / 1ps

// A binary counter for fifo's
// it counts to MAX then
//      clears the lower bits
//      inverts the upper bit
module counter_bin #(
    parameter WIDTH = 4,
    parameter MAX = 16
)(
    input wire i_clk,
    input wire i_rst_n,
    input wire i_enable,
    output reg [WIDTH-1:0] o_counter_out
);

    // Flop stage for the counter
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!rst_n)
            o_counter_out <= 'b0;
        else if (enable && (counter_out[WIDTH-2] == MAX - 1))
            o_counter_out <= {~counter_out[WIDTH-1], 'b0};
        else if (enable)
            o_counter_out <= counter_out + 1;
    end

endmodule : counter_bin