`timescale 1ns / 1ps

module hex_to_7seg (
    input        [3:0] i_hex,  // 4-bit hexadecimal input
    output logic [6:0] ow_seg  // 7-bit seven-segment display output
);

    always_comb begin
        case (i_hex)
            4'h0: ow_seg = 7'b1000000;  // Hex 0: 0b1000000 (segment a-g: 0000001)
            4'h1: ow_seg = 7'b1111001;  // Hex 1: 0b1111001 (segment a-g: 0111111)
            4'h2: ow_seg = 7'b0100100;  // Hex 2: 0b0100100 (segment a-g: 0010010)
            4'h3: ow_seg = 7'b0110000;  // Hex 3: 0b0110000 (segment a-g: 0011000)
            4'h4: ow_seg = 7'b0011001;  // Hex 4: 0b0011001 (segment a-g: 0001100)
            4'h5: ow_seg = 7'b0010010;  // Hex 5: 0b0010010 (segment a-g: 0000010)
            4'h6: ow_seg = 7'b0000010;  // Hex 6: 0b0000010 (segment a-g: 0000000)
            4'h7: ow_seg = 7'b1111000;  // Hex 7: 0b1111000 (segment a-g: 0111110)
            4'h8: ow_seg = 7'b0000000;  // Hex 8: 0b0000000 (segment a-g: 0000000)
            4'h9: ow_seg = 7'b0011000;  // Hex 9: 0b0011000 (segment a-g: 0001100)
            4'ha: ow_seg = 7'b0001000;  // Hex A: 0b0001000 (segment a-g: 0001000)
            4'hb: ow_seg = 7'b0000011;  // Hex B: 0b0000011 (segment a-g: 0000000)
            4'hc: ow_seg = 7'b1000110;  // Hex C: 0b1000110 (segment a-g: 1000000)
            4'hd: ow_seg = 7'b0100001;  // Hex D: 0b0100001 (segment a-g: 0010000)
            4'he: ow_seg = 7'b0000110;  // Hex E: 0b0000110 (segment a-g: 0000000)
            4'hf: ow_seg = 7'b0001110;  // Hex F: 0b0001110 (segment a-g: 0000110)
            default: ow_seg = 7'bxxxxxxx;  // Display nothing for invalid inputs
        endcase
    end

endmodule : hex_to_7seg
