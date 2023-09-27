`timescale 1ns / 1ps

module math_multiplier_booth_radix_4_encoder #(
    parameter int N = 8
) (
    input  logic [  2:0] i_booth_group,
    input  logic [N-1:0] i_multiplier,
    input  logic [N-1:0] i_neg_multiplier,
    output logic [  N:0] ow_booth_out
);
    always_comb begin
        case (i_booth_group)
            3'b001, 3'b010: ow_booth_out = {i_multiplier[N-1], i_multiplier};
            3'b011:         ow_booth_out = {i_multiplier, 1'b0};
            3'b100:         ow_booth_out = {i_neg_multiplier[N-1:0], 1'b0};
            3'b101, 3'b110: ow_booth_out = {i_neg_multiplier[N-1], i_neg_multiplier};
            default:        ow_booth_out = '0;
        endcase
    end
endmodule
