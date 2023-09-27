`timescale 1ns / 1ps

// A binary counter for fifo's
// it counts to MAX then
//      clears the lower bits
//      inverts the upper bit
module counter_bin #(
    parameter int WIDTH = 5,
    parameter int MAX   = 10
) (
    input  logic             i_clk,
    input  logic             i_rst_n,
    input  logic             i_enable,
    output logic [WIDTH-1:0] o_counter_bin
);

    // No need for max_signal or width_signal if they're not being used elsewhere

    // Flop stage for the counter
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) o_counter_bin <= 'b0;
        else if (i_enable)
            if (o_counter_bin[WIDTH-2:0] == MAX - 1)
                o_counter_bin <= {~o_counter_bin[WIDTH-1], {(WIDTH - 1) {1'b0}}};
            else o_counter_bin <= o_counter_bin + 1;
    end

endmodule : counter_bin
