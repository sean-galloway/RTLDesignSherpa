// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: BUFG (Verilator-only stub)
// Purpose: Pass-through stub for Xilinx BUFG. Vivado replaces this at
//          synthesis with the real BUFG from unisims. Only compiles
//          when VERILATOR is defined so other tools ignore it.

`timescale 1ns / 1ps

`ifdef VERILATOR
module BUFG (
    input  logic I,
    output logic O
);
    assign O = I;
endmodule : BUFG
`endif
