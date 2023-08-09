`timescale 1ns / 1ps

// A parameterized gray counter for async fifo's
module counter_gray #(
    parameter WIDTH = 4
)(
    input  logic i_clk,
    input  logic i_rst_n,
    input  logic i_enable,
    output logic [WIDTH - 1:0] o_counter_gray
);

    logic [WIDTH-1:0] r_binary_counter, w_binary_counter, w_counter_gray;

    assign w_binary_counter = r_binary_counter + 1;
    assign w_counter_gray   = w_binary_counter ^ (w_binary_counter >> 1);

    // Increment the binary counter and convert to Gray code
    always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
            r_binary_counter <= 'b0;
            o_counter_gray   <= 'b0;
        end else if (i_enable) begin
            r_binary_counter <= w_binary_counter;
            o_counter_gray   <= w_counter_gray;
        end
    end

endmodule : counter_gray
