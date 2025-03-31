`timescale 1ns / 1ps
module math_multiplier_booth_radix_4_encoder #(
    parameter int N = 8
) (
    input  logic [  2:0] i_booth_group,
    input  logic [N-1:0] i_multiplicand,
    output logic [N+1:0] ow_booth_out  // Note: increased width by 1 to handle shifts
);

    // Sign-extended multiplicand (N+1 bits)
    logic [N:0] multiplicand_ext;
    assign multiplicand_ext = {i_multiplicand[N-1], i_multiplicand};
    
    always_comb begin
        case (i_booth_group)
            3'b000:  ow_booth_out = {(N+2){1'b0}};                // +0
            3'b111:  ow_booth_out = {(N+2){1'b0}};                // +0
            3'b001:  ow_booth_out = {multiplicand_ext, 1'b0};     // +1*multiplicand (shifted left by 1)
            3'b010:  ow_booth_out = {multiplicand_ext, 1'b0};     // +1*multiplicand (shifted left by 1)
            3'b011:  ow_booth_out = {multiplicand_ext, 1'b0} << 1;  // +2*multiplicand (shifted left by 2)
            3'b100:  ow_booth_out = ~({multiplicand_ext, 1'b0} << 1) + 1'b1;  // -2*multiplicand
            3'b101:  ow_booth_out = ~({multiplicand_ext, 1'b0}) + 1'b1;       // -1*multiplicand
            3'b110:  ow_booth_out = ~({multiplicand_ext, 1'b0}) + 1'b1;       // -1*multiplicand
            default: ow_booth_out = {(N+2){1'b0}};
        endcase
    end

endmodule : math_multiplier_booth_radix_4_encoder