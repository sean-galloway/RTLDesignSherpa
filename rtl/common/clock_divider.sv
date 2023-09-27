`timescale 1ns / 1ps

module clock_divider #(
    parameter int N = 4,  // Number of output clocks
    parameter logic [16*N-1:0] PICKOFF_BITS = {16'd4, 16'd5, 16'd6, 16'd7},
    // the pick off points for the divided clock
    parameter int COUNTER_WIDTH = 8  // Width of the counter
) (
    input  logic         i_clk,         // Input clock signal
    input  logic         i_rst_n,       // Active low reset signal
    output logic [N-1:0] o_divided_clk  // Divided clock signals
);

    logic [COUNTER_WIDTH-1:0] r_divider_counters;  // Counter for all input clocks

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) r_divider_counters <= 0;
        else r_divider_counters <= r_divider_counters + 1;
    end

    always_comb begin
        for (int i = 0; i < N; i++)
        o_divided_clk[i] = (divider_counters[$unsigned(PICKOFF_BITS[i])]);
    end

endmodule : clock_divider
