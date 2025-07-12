`timescale 1ns / 1ps

// A parameterized gray counter for async fifo's
module counter_bingray #(
    parameter int WIDTH = 4
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable,
    output logic [WIDTH-1:0] counter_bin,
    output logic [WIDTH-1:0] counter_bin_next,
    output logic [WIDTH-1:0] counter_gray
);

    logic [WIDTH-1:0] w_counter_bin, w_counter_gray;

    assign w_counter_bin = enable ? (counter_bin + 1) : counter_bin;
    assign w_counter_gray = w_counter_bin ^ (w_counter_bin >> 1);
    assign counter_bin_next = w_counter_bin;

    // Increment the binary counter and convert to Gray code
    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n) begin
            counter_bin  <= 'b0;
            counter_gray <= 'b0;
        end else begin
            counter_bin  <= w_counter_bin;
            counter_gray <= w_counter_gray;
        end
    end

endmodule : counter_bingray
