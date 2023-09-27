`timescale 1ns / 1ps

module reciprocal_divider #(
    parameter int DATA_WIDTH     = 16,  // Width of input and output data
    parameter int DIV_ITERATIONS = 8    // Number of iterations for reciprocal approximation
) (
    input  logic [DATA_WIDTH-1:0] dividend,
    input  logic [DATA_WIDTH-1:0] divisor,
    output logic [DATA_WIDTH-1:0] quotient
);

    localparam int DW = DATA_WIDTH;
    localparam int DI = DIV_ITERATIONS;
    // DIV_ITERATIONS will improve the accuracy of the reciprocal,
    // but it will also increase the complexity and area of the design.

    logic          signed_quotient;
    logic [DW-1:0] remainder;
    logic [DW-1:0] reciprocal;

    always_comb begin
        // Calculate the initial reciprocal value using simple approximation
        reciprocal = 1 << (2 * DW);  // Start with a large approximation

        // Perform Newton-Raphson iteration for refining the reciprocal value
        for (int i = 0; i < DI; i++) begin
            reciprocal = reciprocal - ((reciprocal * divisor) >> DW);
        end

        // Perform division using the reciprocal value
        remainder = dividend * reciprocal;  // Perform the division
        signed_quotient = dividend[DW-1] ^ divisor[DW-1];  // Determine the sign of the quotient

        // Adjust the quotient based on the sign
        if (signed_quotient) quotient = -remainder >> (2 * DW);  // Negative quotient
        else quotient = remainder >> (2 * DW);  // Positive quotient
    end

endmodule
