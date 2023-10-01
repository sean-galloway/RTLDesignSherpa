`timescale 1ns / 1ps

module math_divider_srt #(
    parameter int DW = 16  // Width of input and output data
) (
    input  logic          clk,       // Clock input
    input  logic          rst_n,     // Asynchronous active-low reset
    input  logic [DW-1:0] dividend,
    input  logic [DW-1:0] divisor,
    output logic [DW-1:0] quotient,
    output logic [DW-1:0] remainder
);

    logic [DW-1:0] quotient_reg;
    logic [DW-1:0] remainder_reg;
    logic [  DW:0] divisor_reg;
    logic [  DW:0] A_reg;
    logic [  DW:0] M_reg;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            quotient_reg <= 0;
            remainder_reg <= 0;
            divisor_reg <= {1'b0, divisor};
            A_reg <= 0;
            M_reg <= 0;
        end else begin
            quotient_reg <= quotient_reg;
            remainder_reg <= remainder_reg;
            divisor_reg <= divisor_reg;
            A_reg <= A_reg;
            M_reg <= M_reg;
        end
    end

    always_comb begin
        // Calculate the initial values for the SRT algorithm
        A_reg = dividend;
        M_reg = divisor_reg;

        // Main SRT division loop
        for (int i = 0; i < DW; i++) begin
            if (A_reg[DW*2:DW+1] >= divisor_reg[DW-1:0]) begin
                quotient_reg[DW-1-i] = 1;
                A_reg = A_reg - divisor_reg;
            end else begin
                quotient_reg[DW-1-i] = 0;
            end

            // Perform the SRT shift
            A_reg = A_reg << 1;
            divisor_reg = divisor_reg >> 1;
        end

        // Output the quotient and remainder
        quotient  = quotient_reg;
        remainder = A_reg[DW-1:0];
    end

endmodule : math_divider_srt
