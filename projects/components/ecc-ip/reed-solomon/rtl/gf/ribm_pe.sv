// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ribm_pe
// Purpose:
//   One processing element of the riBM key-equation solver: holds one
//   coefficient pair (Delta_i, Theta_i) and performs the per-iteration update.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: ribm_pe
//==============================================================================
// Description:
//   Sarwate-Shanbhag 2001, one cell of the 3t+1 array:
//
//     Delta_i(r+1) = gamma(r) * Delta_{i+1}(r)  ^  delta(r) * Theta_i(r)
//     Theta_i(r+1) = swap ? Delta_{i+1}(r) : Theta_i(r)
//
//   where delta = Delta_0 (the discrepancy) and gamma, swap are broadcast by
//   the solver's control. Two gf_mul, two m-bit registers, no feedback across
//   the array: the critical path is one multiply and one XOR, whatever t is.
//   i_load presets both registers to i_init (the syndrome, or 1, or 0).
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH: m. Default 8.
//   PRIM_POLY:    primitive polynomial. Default 0x11D.
//
//==============================================================================

module ribm_pe #(
    parameter int SYMBOL_WIDTH = 8,
    parameter int PRIM_POLY    = 'h11D
) (
    input  logic                    aclk,
    input  logic                    aresetn,
    input  logic                    i_load,
    input  logic [SYMBOL_WIDTH-1:0] i_init,
    input  logic                    i_step,
    input  logic                    i_swap,
    input  logic [SYMBOL_WIDTH-1:0] i_gamma,
    input  logic [SYMBOL_WIDTH-1:0] i_delta,
    input  logic [SYMBOL_WIDTH-1:0] i_delta_next,   // Delta_{i+1} from the neighbour
    output logic [SYMBOL_WIDTH-1:0] o_delta,
    output logic [SYMBOL_WIDTH-1:0] o_theta
);

    localparam int M = SYMBOL_WIDTH;

    logic [M-1:0] r_delta;
    logic [M-1:0] r_theta;
    logic [M-1:0] w_gd;   // gamma * Delta_{i+1}
    logic [M-1:0] w_dt;   // delta * Theta_i

    gf_mul #(.SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY)) u_gd (
        .i_a(i_gamma), .i_b(i_delta_next), .ow_p(w_gd));
    gf_mul #(.SYMBOL_WIDTH(M), .PRIM_POLY(PRIM_POLY)) u_dt (
        .i_a(i_delta), .i_b(r_theta), .ow_p(w_dt));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_delta <= '0;
            r_theta <= '0;
        end else if (i_load) begin
            r_delta <= i_init;
            r_theta <= i_init;
        end else if (i_step) begin
            r_delta <= w_gd ^ w_dt;
            r_theta <= i_swap ? i_delta_next : r_theta;
        end
    )

    assign o_delta = r_delta;
    assign o_theta = r_theta;

endmodule : ribm_pe
