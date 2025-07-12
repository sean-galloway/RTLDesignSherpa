`timescale 1ns / 1ps

// Generic Ring Counter Module
module counter_ring #(
    parameter int WIDTH = 4  // Width of the ring counter, determines the number of stages
) (
    input  wire             clk,      // Clock input
    input  wire             rst_n,    // Active low reset
    input  wire             enable,   // Counter enable
    output reg  [WIDTH-1:0] ring_out  // Ring counter output
);

    // On reset, initialize the ring counter to have the first bit set and all others clear.
    // When enabled, rotate the bits to the right in each clock cycle.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ring_out <= 'b1;  // This should set the LSB, which is '1'
        end else if (enable) begin
            // Right rotate operation
            ring_out <= {ring_out[0], ring_out[WIDTH-1:1]};
        end
    end

endmodule : counter_ring
