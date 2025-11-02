// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: counter_johnson
// Purpose: Counter Johnson module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module counter_johnson #(
    parameter int WIDTH = 4
) (
    input  logic                clk,
    input  logic                rst_n,
    input  logic                enable,
    output logic [WIDTH - 1:0]  counter_gray
);

    `ALWAYS_FF_RST(clk, rst_n,
        if (!rst_n) counter_gray <= {WIDTH{1'b0}};
        else if (enable) begin
            counter_gray <= {counter_gray[WIDTH-2:0], ~counter_gray[WIDTH-1]};
        end
    )


endmodule : counter_johnson
