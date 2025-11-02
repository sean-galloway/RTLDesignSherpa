// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: dataint_checksum
// Purpose: Dataint Checksum module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Generic Checksum Module

`include "reset_defs.svh"
module dataint_checksum #(
    parameter int WIDTH = 8
) (
    input  logic             clk,
    rst_n,
    input  logic             reset,
    input  logic             valid,
    input  logic [WIDTH-1:0] data,
    output logic [WIDTH-1:0] chksum
);

    logic [WIDTH-1:0] r_count;

    `ALWAYS_FF_RST(clk, rst_n,
        if (!rst_n) r_count <= 'b0;
        else if (reset) r_count <= 'b0;
        else if (valid) r_count <= r_count + data;
    )


    assign chksum = r_count;

endmodule : dataint_checksum
