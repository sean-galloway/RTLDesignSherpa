`timescale 1ns / 1ps

module hex_to_7seg(
    input        [3:0] hex_input, // 4-bit hexadecimal input
    output logic [6:0] seg_output // 7-bit seven-segment display output
);

    always_comb
    begin
        case (hex_input)
            4'h0: seg_output = 7'b1000000; // Hex 0: 0b1000000 (segment a-g: 0000001)
            4'h1: seg_output = 7'b1111001; // Hex 1: 0b1111001 (segment a-g: 0111111)
            4'h2: seg_output = 7'b0100100; // Hex 2: 0b0100100 (segment a-g: 0010010)
            4'h3: seg_output = 7'b0110000; // Hex 3: 0b0110000 (segment a-g: 0011000)
            4'h4: seg_output = 7'b0011001; // Hex 4: 0b0011001 (segment a-g: 0001100)
            4'h5: seg_output = 7'b0010010; // Hex 5: 0b0010010 (segment a-g: 0000010)
            4'h6: seg_output = 7'b0000010; // Hex 6: 0b0000010 (segment a-g: 0000000)
            4'h7: seg_output = 7'b1111000; // Hex 7: 0b1111000 (segment a-g: 0111110)
            4'h8: seg_output = 7'b0000000; // Hex 8: 0b0000000 (segment a-g: 0000000)
            4'h9: seg_output = 7'b0011000; // Hex 9: 0b0011000 (segment a-g: 0001100)
            4'ha: seg_output = 7'b0001000; // Hex A: 0b0001000 (segment a-g: 0001000)
            4'hb: seg_output = 7'b0000011; // Hex B: 0b0000011 (segment a-g: 0000000)
            4'hc: seg_output = 7'b1000110; // Hex C: 0b1000110 (segment a-g: 1000000)
            4'hd: seg_output = 7'b0100001; // Hex D: 0b0100001 (segment a-g: 0010000)
            4'he: seg_output = 7'b0000110; // Hex E: 0b0000110 (segment a-g: 0000000)
            4'hf: seg_output = 7'b0001110; // Hex F: 0b0001110 (segment a-g: 0000110)
            default: seg_output = 7'bxxxxxxx; // Display nothing for invalid inputs
        endcase
    end

endmodule : hex_to_7seg
