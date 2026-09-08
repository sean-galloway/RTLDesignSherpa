// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Lint/sim-only stubs for the Xilinx clocking primitives instantiated in
// cdc_demo_top.sv (IBUF / BUFG / BUFGMUX_CTRL / MMCME2_BASE). Vivado replaces
// these with the real unisims at synthesis; they exist ONLY so `make lint-demo`
// (verilator --lint-only) can find the modules instead of erroring with
// "Cannot find file containing module". Behaviorally sane pass-throughs so
// cdc_demo_top can also be elaborated in a Verilator sim if ever needed.
//
// Guarded by `ifdef VERILATOR` (Verilator predefines it) so no other tool ever
// compiles these — the file is lint/sim-only and is NOT in any Vivado flow.

`timescale 1ns / 1ps

`ifdef VERILATOR

module IBUF (input logic I, output logic O);
    assign O = I;
endmodule : IBUF

module BUFG (input logic I, output logic O);
    assign O = I;
endmodule : BUFG

// Glitchless 2:1 clock mux — S selects I1 when high, I0 when low.
module BUFGMUX_CTRL (input logic I0, input logic I1, input logic S,
                     output logic O);
    assign O = S ? I1 : I0;
endmodule : BUFGMUX_CTRL

// Minimal MMCME2_BASE stub: declares every parameter cdc_demo_top overrides and
// every port it connects, so the `#(...)` override and named pins resolve. The
// output clocks are tied to CLKIN1 (a lint/sim placeholder — the real frequency
// synthesis only exists in hardware); LOCKED is asserted.
module MMCME2_BASE #(
    parameter BANDWIDTH          = "OPTIMIZED",
    parameter real CLKFBOUT_MULT_F   = 5.0,
    parameter real CLKFBOUT_PHASE    = 0.0,
    parameter real CLKIN1_PERIOD     = 0.0,
    parameter int  DIVCLK_DIVIDE     = 1,
    parameter real REF_JITTER1       = 0.010,
    parameter STARTUP_WAIT       = "FALSE",
    parameter real CLKOUT0_DIVIDE_F  = 1.0,
    parameter int  CLKOUT1_DIVIDE    = 1,
    parameter int  CLKOUT2_DIVIDE    = 1,
    parameter int  CLKOUT3_DIVIDE    = 1,
    parameter real CLKOUT0_DUTY_CYCLE = 0.5,
    parameter real CLKOUT0_PHASE      = 0.0,
    parameter real CLKOUT1_DUTY_CYCLE = 0.5,
    parameter real CLKOUT1_PHASE      = 0.0,
    parameter real CLKOUT2_DUTY_CYCLE = 0.5,
    parameter real CLKOUT2_PHASE      = 0.0,
    parameter real CLKOUT3_DUTY_CYCLE = 0.5,
    parameter real CLKOUT3_PHASE      = 0.0
) (
    input  logic CLKIN1,
    input  logic CLKFBIN,
    output logic CLKFBOUT,
    output logic CLKFBOUTB,
    output logic CLKOUT0,
    output logic CLKOUT0B,
    output logic CLKOUT1,
    output logic CLKOUT1B,
    output logic CLKOUT2,
    output logic CLKOUT2B,
    output logic CLKOUT3,
    output logic CLKOUT3B,
    output logic CLKOUT4,
    output logic CLKOUT5,
    output logic CLKOUT6,
    output logic LOCKED,
    input  logic PWRDWN,
    input  logic RST
);
    assign CLKFBOUT  = CLKIN1;
    assign CLKFBOUTB = ~CLKIN1;
    assign CLKOUT0   = CLKIN1;  assign CLKOUT0B = ~CLKIN1;
    assign CLKOUT1   = CLKIN1;  assign CLKOUT1B = ~CLKIN1;
    assign CLKOUT2   = CLKIN1;  assign CLKOUT2B = ~CLKIN1;
    assign CLKOUT3   = CLKIN1;  assign CLKOUT3B = ~CLKIN1;
    assign CLKOUT4   = 1'b0;
    assign CLKOUT5   = 1'b0;
    assign CLKOUT6   = 1'b0;
    assign LOCKED    = ~RST;
endmodule : MMCME2_BASE

`endif
