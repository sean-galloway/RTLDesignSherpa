`timescale 1ns / 1ps

// Generic Ring Counter Module
module counter_ring #(
    parameter int WIDTH = 4  // Width of the ring counter, determines the number of stages
) (
    input  wire             i_clk,      // Clock input
    input  wire             i_rst_n,    // Active low reset
    input  wire             i_enable,   // Counter enable
    output reg  [WIDTH-1:0] o_ring_out  // Ring counter output
);

    // On reset, initialize the ring counter to have the first bit set and all others clear.
    // When enabled, rotate the bits to the right in each clock cycle.
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            o_ring_out <= 'b1;  // This should set the LSB, which is '1'
        end else if (i_enable) begin
            // Right rotate operation
            o_ring_out <= {o_ring_out[0], o_ring_out[WIDTH-1:1]};
        end
    end

    // Synopsys translate_off
    // Synopsys translate_on

endmodule : counter_ring
