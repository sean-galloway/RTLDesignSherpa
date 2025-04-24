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
    output logic [WIDTH-1:0] o_counter_bin,
    output logic [WIDTH-1:0] ow_counter_bin_next
);

    // Assign the next value
    logic [WIDTH-2:0] w_max_val;
    assign w_max_val = (WIDTH-1)'(MAX - 1);

    always_comb begin
        if (i_enable) begin
            if (o_counter_bin[WIDTH-2:0] == w_max_val)
                ow_counter_bin_next = {~o_counter_bin[WIDTH-1], {(WIDTH - 1){1'b0}}};
            else
                ow_counter_bin_next = o_counter_bin + 1;
        end else begin
            ow_counter_bin_next = o_counter_bin;
        end
    end

    // Flop stage for the counter
    always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) o_counter_bin <= 'b0;
        else o_counter_bin <= ow_counter_bin_next;
    end

endmodule : counter_bin
