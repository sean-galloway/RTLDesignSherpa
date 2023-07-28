`timescale 1ns / 1ps

module clock_divider #(
    parameter int N = 4,                           // Number of output clocks
    parameter int COUNTER_WIDTH = 8,               // Width of the counter
    parameter int PICKOFF_BITS [N] = '{1, 2, 3, 4} // the pick off points for the divided clock
) (
    input  logic         clk,                      // Input clock signal
    input  logic         rst_n,                    // Active low reset signal
    output logic [N-1:0] divided_clk_out           // Divided clock signals
);

    logic [COUNTER_WIDTH-1:0] divider_counters;    // Counter for all input clocks

    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n)
            divider_counters <= 0;
        else
            divider_counters <= divider_counters + 1;
    end

    always_comb begin
        for (int i = 0; i < N; i++)
            divided_clk_out[i] = (divider_counters[PICKOFF_BITS[i]]);
    end

endmodule : clock_divider
