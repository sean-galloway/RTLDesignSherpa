`timescale 1ns / 1ps

module math_multiplier_booth_radix_4_encoder (
    input  logic [2:0] booth_group,
    output logic [1:0] booth_encoded
);
    always_comb begin
        case(booth_group)
            3'b000: booth_encoded = 2'b00;
            3'b001: booth_encoded = 2'b00;
            3'b010: booth_encoded = 2'b01;
            3'b011: booth_encoded = 2'b01;
            3'b100: booth_encoded = 2'b11;
            3'b101: booth_encoded = 2'b11;
            3'b110: booth_encoded = 2'b10;
            3'b111: booth_encoded = 2'b10;
            default: booth_encoded = 2'b00;
        endcase
    end
endmodule : math_multiplier_booth_radix_4_encoder