// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: clock_pulse
// Purpose: Clock Pulse module
//
// Documentation: docs/markdown/rtl-common/index.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module clock_pulse #(
    // PERIOD of the pulse train in clock cycles -- NOT the pulse width. The
    // pulse is always exactly 1 cycle wide; WIDTH sets how often it fires.
    parameter int WIDTH = 10
) (
    input  logic clk,    // Input clock signal
    input  logic rst_n,  // Input reset signal
    output logic pulse   // Output pulse signal
);

    // WIDTH is the pulse PERIOD, so the counter only needs to hold 0..WIDTH-1,
    // i.e. $clog2(WIDTH) bits -- NOT WIDTH bits. Sizing it at WIDTH bits made
    // the counter as wide as the period (e.g. a 1 Hz heartbeat off a 100 MHz
    // clock, WIDTH=100_000_000, would infer ~100 M flip-flops and be
    // unsynthesizable). Guard WIDTH<2 so $clog2 never yields a zero-width reg.
    localparam int CW = (WIDTH < 2) ? 1 : $clog2(WIDTH);

    logic [CW-1:0] r_counter;
    logic [CW-1:0] w_width_minus_one;

    // Properly sized period-1 constant (WIDTH-1 always fits in CW bits).
    assign w_width_minus_one = CW'(WIDTH - 1);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_counter <= 'b0;
            pulse     <= 'b0;
        end else begin
            if (r_counter < w_width_minus_one) r_counter <= r_counter + 1'b1;
            else r_counter <= 'b0;

            pulse <= (r_counter == w_width_minus_one);
        end
    )


endmodule : clock_pulse
