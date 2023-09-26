`timescale 1ns / 1ps

module math_multiplier_booth_radix_4_encoder (
    input  logic [2:0] booth_group,
    output logic [1:0] booth_encoded
);
    always_comb begin
        case(booth_group)
            3'b000, 3'b001: booth_encoded = 2'b00; // 0
            3'b010, 3'b011: booth_encoded = 2'b01; // 1
            3'b100       : booth_encoded = 2'b10; // -2
            3'b101, 3'b110: booth_encoded = 2'b10; // 2
            3'b111, 3'b110: booth_encoded = 2'b11; // -1
            default: booth_encoded = 2'b00;
        endcase
    end
endmodule