// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_stress_w_first_gate
// Purpose: The W_FIRST gate of a bus-stress slave: AWREADY only once write
//          data is in sight, as a slave that waits for its data first does
//          (AXI A3.3.1 allows it). Shared by every AXI-family slave shell.
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-24
//==============================================================================
// Data is "in sight" when a W beat is offered this cycle OR a W burst has
// already been taken ahead of its AW. The second half is what makes the gate
// a legal slave: the shell's W skid takes beats on its own, so a W accepted
// in a cycle the channel could not take the AW would otherwise leave that AW
// waiting for a WVALID the master has no reason to raise again. An AXI4
// master escaped by luck (its next burst's W reopened the gate); a converter
// offering one AXI4-Lite beat at a time could not (bridge-stress mixed_b,
// w_first, 2026-10-24: l4s AWVALID up, WVALID down, every master behind it).
//
// `r_ahead` counts W bursts begun minus AWs accepted (a burst begins at its
// first beat; WLAST ends it -- tie WLAST high on a single-beat bus). It
// saturates and never goes below zero: an AW taken on a later beat of a
// burst already paired is not a debt. The stress pair test mirrors this in
// bin/TBClasses/amba/axi_stress_pair_tb.py.
//==============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"

module axi_stress_w_first_gate (
    input  logic aclk,
    input  logic aresetn,
    input  logic clear,        // start of a run: forget the last run's debt
    input  logic en,           // cfg w_first
    input  logic awvalid,      // at the pins
    input  logic ch_awready,   // the channel module's AWREADY
    input  logic wvalid,       // at the pins
    input  logic wready,
    input  logic wlast,
    output logic aw_gate,      // AND into the channel's AWVALID
    output logic awready       // the pin
);
    localparam int AHEAD_W = 4;

    logic               r_in_burst;   // a W burst has begun and not yet seen WLAST
    logic [AHEAD_W-1:0] r_ahead;      // W bursts begun minus AWs accepted

    wire w_hs    = wvalid && wready;
    wire w_begin = w_hs && !r_in_burst;

    assign aw_gate = !en || wvalid || (r_ahead != '0);
    assign awready = ch_awready && aw_gate;

    wire w_aw_hs = awvalid && awready;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_in_burst <= 1'b0;
            r_ahead    <= '0;
        end else if (clear) begin
            r_in_burst <= 1'b0;
            r_ahead    <= '0;
        end else begin
            if (w_hs) r_in_burst <= !wlast;
            case ({w_begin, w_aw_hs})
                2'b10:   if (r_ahead != '1) r_ahead <= r_ahead + 1'b1;
                2'b01:   if (r_ahead != '0) r_ahead <= r_ahead - 1'b1;
                default: ;
            endcase
        end
    )
endmodule : axi_stress_w_first_gate
