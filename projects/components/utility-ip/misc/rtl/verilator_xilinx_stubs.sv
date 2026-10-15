// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: Xilinx primitive stubs (Verilator-only)
// Purpose: LINT-ONLY pass-through stubs for the Xilinx clocking primitives a
//          board top instantiates, plus two FUNCTIONAL datapath primitives
//          (SRLC32E, MUXF7 -- see the section at the bottom). Vivado substitutes the real unisims at
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

// Single-ended input buffer: a plain board clock pin enters here.
module IBUF (
    input  logic I,
    output logic O
);
    assign O = I;
endmodule : IBUF

// Glitchless 2:1 clock mux -- S selects I1 when high, I0 when low. The real
// primitive guarantees a glitch-free switch; for lint the select semantics are
// all that matters.
module BUFGMUX_CTRL (
    input  logic I0,
    input  logic I1,
    input  logic S,
    output logic O
);
    assign O = S ? I1 : I0;
endmodule : BUFGMUX_CTRL

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
    parameter real CLKOUT1_DUTY_CYCLE = 0.500,
    parameter real CLKOUT1_PHASE      = 0.000,
    parameter real CLKOUT2_DUTY_CYCLE = 0.500,
    parameter real CLKOUT2_PHASE      = 0.000,
    parameter real CLKOUT3_DUTY_CYCLE = 0.500,
    parameter real CLKOUT3_PHASE      = 0.000,
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

// ---------------------------------------------------------------------------
// IDELAYCTRL -- calibrates the IDELAYE2/ODELAYE2 primitives in a 7-series
// IOB. Added 2026-10-01 for the scoria DDR3 board top, whose K7DDRPHY carries
// 33 IDELAYE2 and 67 ODELAYE2 and no IDELAYCTRL of its own (LiteX instantiates
// it at the SoC level).
//
// RDY is tied to ~RST and NOT modelled as a delay. On hardware RDY asserts
// some time after RST releases, and a reset released before it is the classic
// uncalibrated-delay failure -- every tap means nothing and the first read
// window is garbage. A stub that asserts RDY instantly cannot show that, which
// is one more reason this file must never reach a synthesis filelist.
module IDELAYCTRL (
    input  wire REFCLK,
    input  wire RST,
    output wire RDY
);
    assign RDY = ~RST;
endmodule : IDELAYCTRL

// ---------------------------------------------------------------------------
// DATAPATH primitives. Unlike the clocking stubs above these are FUNCTIONAL
// models, exact to the unisim behaviour, because they carry data: the Xilinx
// AXI Crossbar (Genesys 2 fabric benchmark, Leg B1) builds its SRL FIFOs and
// wide muxes from them when C_FAMILY names a real part. Vivado's own unisim
// .v files use deassign/specify, which Verilator cannot parse, so the cosim
// reads these instead. Added 2026-10-14.

// 32-deep shift register LUT: D shifts in at bit 0 on each enabled clock;
// Q reads the tap A addresses, Q31 the last stage (for cascading).
module SRLC32E #(
    parameter        LOC             = "UNPLACED",
    parameter [31:0] INIT            = 32'h00000000,
    parameter [0:0]  IS_CLK_INVERTED = 1'b0
) (
    output wire       Q,
    output wire       Q31,
    input  wire [4:0] A,
    input  wire       CE,
    input  wire       CLK,
    input  wire       D
);
    // INIT is the power-up content, as on the part (an SRL has no reset).
    logic [31:0] r_sr;
    initial r_sr = INIT;
    wire w_clk = CLK ^ IS_CLK_INVERTED;
    always_ff @(posedge w_clk) if (CE) r_sr <= {r_sr[30:0], D};
    assign Q   = r_sr[A];
    assign Q31 = r_sr[31];
endmodule : SRLC32E

// 2:1 mux joining two LUT6 outputs: S high selects I1.
module MUXF7 (
    output wire O,
    input  wire I0,
    input  wire I1,
    input  wire S
);
    assign O = S ? I1 : I0;
endmodule : MUXF7

`endif
