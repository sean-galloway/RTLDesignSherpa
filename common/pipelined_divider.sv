`timescale 1ns / 1ps

module pipelined_divider #(
    parameter DW = 16,             // Width of input and output data
    parameter STAGES = 4           // Number of pipeline stages
) (
    input logic clk,               // Clock input
    input logic rst_n,             // Asynchronous active-low reset
    input logic start,             // Start signal to initiate division
    input logic [DW-1:0] dividend, // Dividend input
    input logic [DW-1:0] divisor,  // Divisor input
    output logic [DW-1:0] quotient,// Quotient output
    output logic [DW-1:0] remainder,// Remainder output
    output logic done              // Done signal to indicate division completion
);

    logic [DW-1:0] dividend_reg;
    logic [DW-1:0] divisor_reg;
    logic [DW-1:0] quotient_reg;
    logic [DW-1:0] remainder_reg;
    logic signed_quotient;
    logic signed_divisor;
    logic signed_remainder;
    logic [DW-1:0] signed_sub_result;
    logic [DW-1:0] sub_result;
    logic [STAGES-1:0] stage_counter;
    logic div_start;

    // Register the inputs
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            dividend_reg <= 0;
            divisor_reg <= 0;
            quotient_reg <= 0;
            remainder_reg <= 0;
            div_start <= 0;
            stage_counter <= 0;
        end else begin
            dividend_reg <= dividend;
            divisor_reg <= divisor;
            quotient_reg <= quotient_reg;
            remainder_reg <= remainder_reg;
            div_start <= start;
            if (stage_counter == STAGES - 1)
                stage_counter <= 0;
            else
                stage_counter <= stage_counter + 1;
        end
    end

    // Pipeline stages
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            signed_quotient <= 0;
            signed_divisor <= 0;
            signed_remainder <= 0;
            signed_sub_result <= 0;
        end else begin
            if (div_start) begin
                signed_quotient <= dividend_reg[DW-1] ^ divisor_reg[DW-1];
                signed_divisor <= divisor_reg;
                signed_remainder <= dividend_reg;
            end
        end
    end

    // Calculate the pipeline stages
    assign signed_sub_result = (stage_counter >= 2 && stage_counter < STAGES) ? 
                (signed_sub_result - (signed_sub_result < 0 ? 0 : divisor_reg)) :
                signed_sub_result;

    // Output the quotient and remainder
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            quotient <= 0;
            remainder <= 0;
            done <= 0;
        end else begin
            if (div_start && (stage_counter == STAGES - 1)) begin
                quotient <= signed_quotient ? sub_result : quotient_reg;
                remainder <= signed_sub_result < 0 ? signed_sub_result + divisor_reg : signed_sub_result;
                done <= 1;
            end else begin
                quotient <= quotient_reg;
                remainder <= remainder_reg;
                done <= 0;
            end
        end
    end

endmodule

