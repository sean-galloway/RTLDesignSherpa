`timescale 1ns / 1ps

module clock_pulse #(
  parameter int WIDTH = 10 // Width of the generated pulse in clock cycles
) (
  input logic clk,           // Input clock signal
  output logic pulse_out     // Output pulse signal
);

    logic [WIDTH-1:0] counter;

    always_ff @(posedge clk) begin
        if (counter < WIDTH)
            counter <= counter + 1;
        else
            counter <= 0;
    end

    assign pulse_out = (counter == WIDTH-1);

endmodule : clock_pulse