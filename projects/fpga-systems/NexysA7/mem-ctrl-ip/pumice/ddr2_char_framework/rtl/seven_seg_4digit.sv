// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: seven_seg_4digit
// Purpose: Drive the 4 right-most digits of the Nexys A7 7-segment display
//          with a 16-bit hex value. The board has 8 multiplexed digits
//          sharing a common 7-segment cathode bus; this module drives
//          AN[3:0] for the 4 right digits and forces AN[7:4] off.
//
// Subsystem: NexysA7/flows-stream-bridge
//
// Author: sean galloway
// Created: 2026-04-26
//
// ---------------------------------------------------------------------------
// Driver theory
// ---------------------------------------------------------------------------
// Both halves (digits 0-3 and digits 4-7) share the same cathode bus, so
// only one digit can be lit at a time. We rotate through digit slots 0..3
// with a divided enable, drive the cathodes for the active slot's nibble,
// and drive the corresponding AN[*] pin low (active-low anode select).
//
// Refresh rate: REFRESH_HZ Hz across all 4 digits => REFRESH_HZ/4 Hz per
// digit. 1 kHz total = 250 Hz per digit, well above flicker-fusion.
// ---------------------------------------------------------------------------

`timescale 1ns / 1ps

`include "reset_defs.svh"

module seven_seg_4digit #(
    parameter int FPGA_CLK_HZ = 100_000_000,
    parameter int REFRESH_HZ  = 1000        // total scan rate across 4 digits
) (
    input  logic        aclk,
    input  logic        aresetn,

    input  logic [15:0] i_hex,    // 4 nibbles, [3:0]=rightmost digit
    input  logic        i_enable, // 0 = blank all digits

    output logic [7:0]  o_an,     // AN[7:0], active low (1 = digit off)
    output logic [6:0]  o_seg,    // {g,f,e,d,c,b,a}, active low
    output logic        o_dp      // decimal point, active low (always off)
);

    // Per-digit dwell time = total period / 4.
    localparam int DIGIT_PERIOD = FPGA_CLK_HZ / (4 * REFRESH_HZ);
    localparam int CNT_W        = (DIGIT_PERIOD <= 1) ? 1
                                  : $clog2(DIGIT_PERIOD);

    logic [CNT_W-1:0] r_div_count;
    logic [1:0]       r_digit_sel;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_div_count <= '0;
            r_digit_sel <= 2'd0;
        end else if (r_div_count == CNT_W'(DIGIT_PERIOD - 1)) begin
            r_div_count <= '0;
            r_digit_sel <= r_digit_sel + 2'd1;
        end else begin
            r_div_count <= r_div_count + 1'b1;
        end
    )

    logic [3:0] w_nibble;
    always_comb begin
        unique case (r_digit_sel)
            2'd0:    w_nibble = i_hex[3:0];    // rightmost
            2'd1:    w_nibble = i_hex[7:4];
            2'd2:    w_nibble = i_hex[11:8];
            2'd3:    w_nibble = i_hex[15:12];  // leftmost (of these 4)
            default: w_nibble = 4'h0;
        endcase
    end

    logic [6:0] w_seg;
    hex_to_7seg u_hex2seg (
        .hex (w_nibble),
        .seg (w_seg)
    );

    // Anode select: one of AN[3:0] active-low at a time. AN[7:4] always
    // off so the left-half digits stay blank.
    logic [3:0] w_an_low_active;
    assign w_an_low_active = ~(4'd1 << r_digit_sel);

    always_comb begin
        if (!i_enable) begin
            o_an  = 8'hFF;        // all digits blanked
            o_seg = 7'h7F;        // all segments off
        end else begin
            o_an  = {4'hF, w_an_low_active};
            o_seg = w_seg;
        end
    end

    assign o_dp = 1'b1;  // active-low: always off

endmodule : seven_seg_4digit
