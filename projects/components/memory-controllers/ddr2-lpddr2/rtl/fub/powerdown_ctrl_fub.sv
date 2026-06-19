// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: powerdown_ctrl_fub
// Purpose: SKELETON — manages CKE/PDE/SREF entry/exit. Watches idle
//          timer, requests power-down via the scheduler, accepts the
//          grant, then drives dfi_cke and (later) coordinates with
//          init_sequencer for SREF exit.
//
// Status:  Port-list only. Holds CKE high, never enters PD.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module powerdown_ctrl_fub
    import ddr2_lpddr2_pkg::*;
#(
    parameter int NUM_RANKS = 1,
    parameter int CS_WIDTH  = NUM_RANKS
) (
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    input  logic [15:0]          idle_threshold_i,    // cycles
    input  logic                 enable_pde_i,
    input  logic                 enable_sref_i,

    input  logic                 controller_idle_i,   // from scheduler

    output logic                 pdn_req_o,
    input  logic                 pdn_grant_i,

    output logic [CS_WIDTH-1:0]  dfi_cke_o
);

    // -- TODO: implementation --
    assign pdn_req_o = 1'b0;
    assign dfi_cke_o = '1;   // CKE high = active

    wire unused = |{ mc_clk, mc_rst_n,
                     idle_threshold_i, enable_pde_i, enable_sref_i,
                     controller_idle_i, pdn_grant_i };

endmodule : powerdown_ctrl_fub
