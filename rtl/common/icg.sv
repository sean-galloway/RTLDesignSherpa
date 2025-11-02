// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: icg
// Purpose: Icg module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

 // Code from "Low Power Design Methodologies and Flows"
module icg(
    input  logic en,
    input  logic clk,
    output logic gclk
);

logic en_out;

// Latch-based approach
always_latch begin
    if (!clk) begin
        en_out = en;
    end
end
assign gclk = en_out && clk;

endmodule : icg
