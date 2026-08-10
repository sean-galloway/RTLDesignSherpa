// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: Xilinx primitive stubs (Verilator-only)
// Purpose: LINT-ONLY pass-through stubs for the Xilinx clocking primitives a
//          board top instantiates. Vivado substitutes the real unisims at
//          synthesis; these exist so `make lint` can elaborate a board top
//          without the vendor library.
//
// Shared across every projects/fpga-systems flow -- the primitives are vendor
// generic, not specific to any one harness, so a per-flow copy would only drift.
//
// LINT-ONLY, and the distinction matters: MMCME2_BASE below passes CLKIN1
// straight through to every CLKOUT. It does NOT model the VCO multiply/divide,
// so a SIMULATION that elaborates a board top through this stub sees the input
// frequency on every output, not the intended derived clocks. The harness sims
// in this repo instantiate the HARNESS (below the top) precisely so they never
// depend on this; anything that genuinely needs derived clocks in sim wants a
// real clock model, not a wider stub.
//
// Everything is wrapped in `ifdef VERILATOR so no other tool ever sees it.

`timescale 1ns / 1ps

`ifdef VERILATOR

module BUFG (
    input  logic I,
    output logic O
);
    assign O = I;
endmodule : BUFG

// Differential input buffer: the board's LVDS system clock enters here.
module IBUFDS #(
    parameter DIFF_TERM    = "FALSE",
    parameter IBUF_LOW_PWR = "TRUE",
    parameter IOSTANDARD   = "DEFAULT"
) (
    input  logic I,
    input  logic IB,
    output logic O
);
    assign O = I;      // IB is the complement; lint only needs the port to exist
endmodule : IBUFDS

// See the header note: pass-through, NOT a frequency model.
module MMCME2_BASE #(
    parameter BANDWIDTH          = "OPTIMIZED",
    parameter real CLKFBOUT_MULT_F   = 5.000,
    parameter real CLKFBOUT_PHASE    = 0.000,
    parameter real CLKIN1_PERIOD     = 0.000,
    parameter real CLKOUT0_DIVIDE_F  = 1.000,
    parameter CLKOUT1_DIVIDE     = 1,
    parameter CLKOUT2_DIVIDE     = 1,
    parameter CLKOUT3_DIVIDE     = 1,
    parameter CLKOUT4_DIVIDE     = 1,
    parameter CLKOUT5_DIVIDE     = 1,
    parameter CLKOUT6_DIVIDE     = 1,
    parameter real CLKOUT0_DUTY_CYCLE = 0.500,
    parameter real CLKOUT0_PHASE      = 0.000,
    parameter real DIVCLK_DIVIDE      = 1,
    parameter real REF_JITTER1        = 0.010,
    parameter STARTUP_WAIT       = "FALSE"
) (
    output logic CLKOUT0,  output logic CLKOUT0B,
    output logic CLKOUT1,  output logic CLKOUT1B,
    output logic CLKOUT2,  output logic CLKOUT2B,
    output logic CLKOUT3,  output logic CLKOUT3B,
    output logic CLKOUT4,
    output logic CLKOUT5,
    output logic CLKOUT6,
    output logic CLKFBOUT, output logic CLKFBOUTB,
    output logic LOCKED,
    input  logic CLKIN1,
    input  logic CLKFBIN,
    input  logic PWRDWN,
    input  logic RST
);
    assign CLKOUT0  = CLKIN1;  assign CLKOUT0B = ~CLKIN1;
    assign CLKOUT1  = CLKIN1;  assign CLKOUT1B = ~CLKIN1;
    assign CLKOUT2  = CLKIN1;  assign CLKOUT2B = ~CLKIN1;
    assign CLKOUT3  = CLKIN1;  assign CLKOUT3B = ~CLKIN1;
    assign CLKOUT4  = CLKIN1;
    assign CLKOUT5  = CLKIN1;
    assign CLKOUT6  = CLKIN1;
    assign CLKFBOUT = CLKIN1;  assign CLKFBOUTB = ~CLKIN1;
    assign LOCKED   = ~RST;
endmodule : MMCME2_BASE

`endif
