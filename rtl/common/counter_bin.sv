`timescale 1ns / 1ps

// A binary counter for fifo's
// it counts to MAX then
//      clears the lower bits
//      inverts the upper bit
module counter_bin #(
    parameter int WIDTH = 5,
    parameter int MAX   = 10
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable,
    output logic [WIDTH-1:0] counter_bin_curr,
    output logic [WIDTH-1:0] counter_bin_next
);

    // Assign the next value
    logic [WIDTH-2:0] w_max_val;
    assign w_max_val = (WIDTH-1)'(MAX - 1);

    always_comb begin
        if (enable) begin
            if (counter_bin_curr[WIDTH-2:0] == w_max_val)
                counter_bin_next = {~counter_bin_curr[WIDTH-1], {(WIDTH - 1){1'b0}}};
            else
                counter_bin_next = counter_bin_curr + 1;
        end else begin
            counter_bin_next = counter_bin_curr;
        end
    end

    // Flop stage for the counter
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) counter_bin_curr <= 'b0;
        else counter_bin_curr <= counter_bin_next;
    end

endmodule : counter_bin
