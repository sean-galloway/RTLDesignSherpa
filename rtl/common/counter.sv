// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: counter
// Purpose: Counter module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module counter #(
    parameter int MAX = 32767
) (
    input  logic clk,
    rst_n,
    output logic tick
);

    logic [$clog2(MAX+1)-1:0] r_count;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_count <= '0;
        end else begin
            if (r_count == MAX[$clog2(MAX+1)-1:0]) begin
                r_count <= '0;
            end else begin
                r_count <= r_count + 1'b1;
            end
        end
    )


    assign tick = (r_count == MAX[$clog2(MAX+1)-1:0]);

endmodule : counter
