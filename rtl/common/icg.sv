`timescale 1ns / 1ps

 // Code from "Low Power Design Methodologies and Flows"
module icg(
    input  logic en,
    input  logic clk,
    output logic gclk
);

logic en_out;

// Latch-based approach
always_latch begin
    if (!clk) begin
        en_out = en;
    end
end
assign gclk = en_out && clk;

endmodule : icg
