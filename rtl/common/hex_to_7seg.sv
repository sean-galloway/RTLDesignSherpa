// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: hex_to_7seg
// Purpose: Hex To 7Seg module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`timescale 1ns / 1ps

module hex_to_7seg (
    input        [3:0] hex,  // 4-bit hexadecimal input
    output logic [6:0] seg   // 7-bit seven-segment display output
);

    // Common anode display: 0=on, 1=off
    // Bit order: [6:0] = {g,f,e,d,c,b,a}
    //
    //   aaa
    //  f   b
    //  f   b
    //   ggg
    //  e   c
    //  e   c
    //   ddd

    always_comb begin
        casez (hex)
            4'h0: seg = 7'b1000000;  // 0: abcdef (not g)
            4'h1: seg = 7'b1111001;  // 1: bc
            4'h2: seg = 7'b0100100;  // 2: abged
            4'h3: seg = 7'b0110000;  // 3: abgcd
            4'h4: seg = 7'b0011001;  // 4: fgbc
            4'h5: seg = 7'b0010010;  // 5: afgcd
            4'h6: seg = 7'b0000010;  // 6: afgdce
            4'h7: seg = 7'b1111000;  // 7: abc
            4'h8: seg = 7'b0000000;  // 8: all segments
            4'h9: seg = 7'b0011000;  // 9: abgcf
            4'ha: seg = 7'b0001000;  // A: abcefg (not d)
            4'hb: seg = 7'b0000011;  // b: fgedc (not ab)
            4'hc: seg = 7'b1000110;  // C: afed (not bcg)
            4'hd: seg = 7'b0100001;  // d: bgedc (not af)
            4'he: seg = 7'b0000110;  // E: afged (not bc)
            4'hf: seg = 7'b0001110;  // F: afge (not bcd)
            default: seg = 7'bxxxxxxx;  // Display nothing for invalid inputs
        endcase
    end

endmodule : hex_to_7seg
