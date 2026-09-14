// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rtc_clk_mux
// Purpose: The counter-clock source mux for rtc_core, with a device-specific
//          glitchless cell where one is available (RLB-010).
//
// Documentation: projects/components/retro_legacy_blocks/docs/rtc_mas/
// Subsystem: retro_legacy_blocks/rtc
//
// Created: 2026-09-14
//
//==============================================================================
// WHY THIS MODULE EXISTS
//==============================================================================
// rtc_core selected its counter clock with one line:
//
//     assign selected_clk = r_clk_sel_held ? clk : rtc_clk;
//
// which is a plain combinational mux: changing clock_select while the RTC runs
// can emit a runt pulse on the counter clock. That was documented as a
// constraint -- change clock_select only with rtc_enable low -- because a
// PORTABLE glitch-free mux is a break-before-make handshake that needs BOTH
// clocks running to complete a switch, and the whole point of clock_select is
// running from pclk when the crystal may be absent. A portable handshake
// therefore cannot switch AWAY from a dead clock: it would replace the
// documented constraint with a worse one.
//
// A device cell can, which is why RLB-010 recorded "a device-specific cell is
// the real answer". This module is that answer, isolated the way icg.sv
// isolates a clock gate: the technology choice lives in one small file instead
// of inside rtc_core's datapath.
//
//==============================================================================
// WHAT EACH BRANCH GIVES YOU
//==============================================================================
//   XILINX  BUFGCTRL, with IGNORE0/IGNORE1 asserted. The IGNORE inputs are the
//           point: they let the switch complete WITHOUT waiting for the
//           departing clock's next edge, which is the case a portable
//           handshake cannot serve. Glitchless for a live clock_select change,
//           including when the crystal has stopped.
//   INTEL   ALTCLKCTRL, the equivalent dedicated clock-select buffer.
//   default The original combinational mux, bit-for-bit. Simulation and any
//           non-FPGA target behave exactly as before, so the DV suite sees no
//           change and the documented rtc_enable-low constraint STILL APPLIES
//           on this branch. That is deliberate: a fallback that quietly
//           behaved differently from the cell would be worse than no fallback.
//
// The constraint text in rtc_core.sv, rtl/rtc/README.md and the MAS is worded
// per-branch for this reason -- on the default branch nothing about the
// hazard has changed.

`timescale 1ns / 1ps

module rtc_clk_mux (
    input  logic sel,        // 0 = clk_0 (rtc_clk), 1 = clk_1 (pclk)
    input  logic clk_0,
    input  logic clk_1,
    output logic clk_out
);

`ifdef XILINX
    // S1 selects clk_1 when high. IGNORE* high means "do not wait for the
    // outgoing clock", which is what makes a switch away from a stopped
    // crystal possible at all.
    BUFGCTRL #(
        .INIT_OUT     (1'b0),
        .PRESELECT_I0 ("TRUE"),
        .PRESELECT_I1 ("FALSE")
    ) u_clk_mux (
        .O   (clk_out),
        .CE0 (1'b1),     .CE1 (1'b1),
        .I0  (clk_0),    .I1  (clk_1),
        .IGNORE0 (1'b1), .IGNORE1 (1'b1),
        .S0  (~sel),     .S1  (sel)
    );
`elsif INTEL
    ALTCLKCTRL #(
        .clock_type  ("AUTO"),
        .number_of_clocks (2)
    ) u_clk_mux (
        .inclk   ({clk_1, clk_0}),
        .clkselect (sel),
        .ena     (1'b1),
        .outclk  (clk_out)
    );
`else
    // Portable fallback: the original expression, unchanged. See the header --
    // the rtc_enable-low constraint still applies here.
    assign clk_out = sel ? clk_1 : clk_0;
`endif

endmodule : rtc_clk_mux
