// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: counter_ring
// Purpose: Counter Ring module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Generic Ring Counter Module

`include "reset_defs.svh"
module counter_ring #(
    parameter int WIDTH = 4  // Width of the ring counter, determines the number of stages
) (
    input  wire             clk,      // Clock input
    input  wire             rst_n,    // Active low reset
    input  wire             enable,   // Counter enable
    output reg  [WIDTH-1:0] ring_out  // Ring counter output
);

    // On reset, initialize the ring counter to have the first bit set and all others clear.
    // When enabled, rotate the bits to the right in each clock cycle.
    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            ring_out <= 'b1;  // This should set the LSB, which is '1'
        end else if (enable) begin
            // Right rotate operation
            ring_out <= {ring_out[0], ring_out[WIDTH-1:1]};
        end
    )


endmodule : counter_ring
