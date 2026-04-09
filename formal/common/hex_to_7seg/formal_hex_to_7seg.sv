// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal wrapper for hex_to_7seg
// Verifies the lookup table correctness for all 16 hex inputs (0-F).
// Segment encoding: [6:0] = {g,f,e,d,c,b,a}, common anode (0=on, 1=off).
//
//   aaa
//  f   b
//  f   b
//   ggg
//  e   c
//  e   c
//   ddd

module formal_hex_to_7seg (
    input logic clk
);

    (* anyconst *) logic [3:0] hex;

    logic [6:0] seg;

    hex_to_7seg dut (
        .hex(hex),
        .seg(seg)
    );

    // =========================================================================
    // Reference model: expected segment patterns
    // =========================================================================
    logic [6:0] ref_seg;

    always_comb begin
        case (hex)
            4'h0: ref_seg = 7'b1000000;  // 0
            4'h1: ref_seg = 7'b1111001;  // 1
            4'h2: ref_seg = 7'b0100100;  // 2
            4'h3: ref_seg = 7'b0110000;  // 3
            4'h4: ref_seg = 7'b0011001;  // 4
            4'h5: ref_seg = 7'b0010010;  // 5
            4'h6: ref_seg = 7'b0000010;  // 6
            4'h7: ref_seg = 7'b1111000;  // 7
            4'h8: ref_seg = 7'b0000000;  // 8
            4'h9: ref_seg = 7'b0011000;  // 9 (note: shows 9 with segment f on)
            4'ha: ref_seg = 7'b0001000;  // A
            4'hb: ref_seg = 7'b0000011;  // b
            4'hc: ref_seg = 7'b1000110;  // C
            4'hd: ref_seg = 7'b0100001;  // d
            4'he: ref_seg = 7'b0000110;  // E
            4'hf: ref_seg = 7'b0001110;  // F
            default: ref_seg = 7'bxxxxxxx;
        endcase
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // Primary property: output matches reference for all 16 valid inputs
    always @(posedge clk)
        ap_lookup_correct: assert (seg == ref_seg);

    // Enumerate each input explicitly to verify individually
    generate
        genvar i;
        for (i = 0; i < 16; i++) begin : gen_each_hex
            always @(posedge clk)
                if (hex == i[3:0])
                    assert (seg == ref_seg);
        end
    endgenerate

    // Digit 8 lights all segments (all zero = all on for common anode)
    always @(posedge clk)
        ap_digit8_all_on: assert (!(hex == 4'h8) || (seg == 7'b0000000));

    // Digit 0 has only segment g off
    always @(posedge clk)
        ap_digit0_g_off: assert (!(hex == 4'h0) || (seg == 7'b1000000));

    // =========================================================================
    // Cover properties
    // =========================================================================

    // Cover each hex input value
    generate
        for (i = 0; i < 16; i++) begin : gen_cover_hex
            always @(posedge clk)
                cover (hex == i[3:0]);
        end
    endgenerate

    // Cover: all segments on (digit 8)
    always @(posedge clk)
        cp_all_on: cover (seg == 7'b0000000);

    // Cover: minimum segments (digit 1 = 2 segments)
    always @(posedge clk)
        cp_min_segs: cover (seg == 7'b1111001);

endmodule
