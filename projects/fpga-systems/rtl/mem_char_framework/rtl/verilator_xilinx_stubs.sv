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

// IBUFDS -- differential input buffer. The Genesys 2 board clock is a 200 MHz
// LVDS pair, so a top that takes it needs this to elaborate under Verilator;
// Vivado substitutes the unisims cell. The stub ignores IB, which is correct
// for lint and wrong for simulating a differential failure -- nothing here
// models the negative leg.
module IBUFDS #(
    parameter DIFF_TERM    = "FALSE",
    parameter IBUF_LOW_PWR = "TRUE",
    parameter IOSTANDARD   = "DEFAULT"
) (
    input  logic I,
    input  logic IB,
    output logic O
);
    assign O = I;
endmodule : IBUFDS
`endif
