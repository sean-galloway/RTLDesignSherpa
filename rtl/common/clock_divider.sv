`timescale 1ns / 1ps

module clock_divider #(
    parameter int N             = 4,  // Number of output clocks
    parameter int PO_WIDTH      = 8,  // Width of the Pick off registers
    parameter int COUNTER_WIDTH = 64  // Width of the counter
) (
    input  logic                    clk,             // Input clock signal
    input  logic                    rst_n,           // Active low reset signal
    input  logic [(N*PO_WIDTH-1):0] pickoff_points,  // the pick off point config registers
    output logic [           N-1:0] divided_clk      // Divided clock signals
);

    logic [COUNTER_WIDTH-1:0] r_divider_counters;  // Counter for all input clocks

    // Calculate the width needed to address all counter bits
    localparam int ADDR_WIDTH = $clog2(COUNTER_WIDTH);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) r_divider_counters <= 0;
        else r_divider_counters <= r_divider_counters + 1;
    end

    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_clk_divider
            int EndIdx = (i + 1) * PO_WIDTH - 1;

            // Extract pickoff point and limit it to valid counter address range
            logic [PO_WIDTH-1:0] w_pickoff_raw;
            logic [ADDR_WIDTH-1:0] w_pickoff_addr;
            logic [PO_WIDTH-1:0] w_counter_width_sized;

            assign w_pickoff_raw = pickoff_points[EndIdx-:PO_WIDTH];
            assign w_counter_width_sized = PO_WIDTH'(COUNTER_WIDTH);
            assign w_pickoff_addr = (w_pickoff_raw < w_counter_width_sized) ?
                                    w_pickoff_raw[ADDR_WIDTH-1:0] :
                                    ADDR_WIDTH'(COUNTER_WIDTH - 1);

            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) divided_clk[i] <= 0;
                else divided_clk[i] <= r_divider_counters[w_pickoff_addr];
            end
        end
    endgenerate

endmodule : clock_divider
