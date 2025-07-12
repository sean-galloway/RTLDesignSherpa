`timescale 1ns / 1ps

module clock_pulse #(
    parameter int WIDTH = 10  // Width of the generated pulse in clock cycles
) (
    input  logic clk,    // Input clock signal
    input  logic rst_n,  // Input reset signal
    output logic pulse   // Output pulse signal
);

    logic [WIDTH-1:0] r_counter;
    logic [WIDTH-1:0] w_width_minus_one;

    // Create a properly sized constant
    assign w_width_minus_one = WIDTH[WIDTH-1:0] - 1'b1;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_counter <= 'b0;
            pulse     <= 'b0;
        end else begin
            if (r_counter < w_width_minus_one) r_counter <= r_counter + 1'b1;
            else r_counter <= 'b0;

            pulse <= (r_counter == w_width_minus_one);
        end
    end

endmodule : clock_pulse
