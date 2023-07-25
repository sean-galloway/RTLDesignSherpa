`timescale 1ns / 1ps

module carry_lookahead_subtractor #(
parameter DW = 16 // Width of input and output data
) (
    input logic clk,              // Clock input
    input logic rst_n,            // asynchronous active-low reset
    input logic [DW-1:0] a,       // Input a
    input logic [DW-1:0] b,       // Input b
    output logic [DW-1:0] difference // Output difference (a - b)
);

logic [DW:0] lookahead_carry; // Lookahead carry signals, including an extra bit for the initial carry-in (borrow)

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        lookahead_carry <= '0; // Reset lookahead carries
    end else begin
    // Calculate lookahead carry for each bit position using a loop
    for (int i = 0; i < DW; i++) begin
        lookahead_carry[i + 1] <= (a[i] ^ b[i]) ? lookahead_carry[i] : (a[i] & lookahead_carry[i]);
    end
    end
end

always_comb begin
    // Calculate the output difference using the lookahead carry signals
    difference = a - b - lookahead_carry[DW];
end

endmodule