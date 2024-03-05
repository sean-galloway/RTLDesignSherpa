`timescale 1ns / 1ps
module math_multiplier_booth_radix_4_encoder #(
    parameter int N = 8
) (
    input  logic [  2:0] i_booth_group,
    input  logic [N-1:0] i_multiplicand,
    output logic [N:0]   ow_booth_out
);

    always_comb begin
        case (i_booth_group)
            3'b000:  ow_booth_out =  {N+1{1'b0}};
            3'b001:  ow_booth_out =  {i_multiplicand[N-1], i_multiplicand};
            3'b010:  ow_booth_out =  {i_multiplicand[N-1], i_multiplicand};
            3'b011:  ow_booth_out =   i_multiplicand << 1;
            3'b100:  ow_booth_out = -(i_multiplicand << 1);
            3'b101:  ow_booth_out = -{i_multiplicand[N-1], i_multiplicand};
            3'b110:  ow_booth_out = -{i_multiplicand[N-1], i_multiplicand};
            3'b111:  ow_booth_out =  {N+1{1'b0}};
            default: ow_booth_out = '0;
        endcase
    end


endmodule : math_multiplier_booth_radix_4_encoder
