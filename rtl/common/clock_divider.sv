`timescale 1ns / 1ps

module clock_divider #(
    parameter int N             = 4,  // Number of output clocks
    parameter int PO_WIDTH      = 8,  // Width of the Pick off registers
    parameter int COUNTER_WIDTH = 64  // Width of the counter
) (
    input  logic                    i_clk,             // Input clock signal
    input  logic                    i_rst_n,           // Active low reset signal
    input  logic [(N*PO_WIDTH-1):0] i_pickoff_points,  // the pick off point config registers
    output logic [           N-1:0] o_divided_clk      // Divided clock signals
);

    logic [COUNTER_WIDTH-1:0] r_divider_counters;  // Counter for all input clocks

    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) r_divider_counters <= 0;
        else r_divider_counters <= r_divider_counters + 1;
    end

    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_clk_divider
            int EndIdx = (i + 1) * PO_WIDTH - 1;
            always_ff @(posedge i_clk or negedge i_rst_n) begin
                if (!i_rst_n) o_divided_clk[i] <= 0;
                else o_divided_clk[i] <= r_divider_counters[i_pickoff_points[EndIdx-:PO_WIDTH]];
            end
        end
    endgenerate

endmodule : clock_divider
