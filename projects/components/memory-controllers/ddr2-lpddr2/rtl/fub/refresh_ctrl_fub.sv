// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: refresh_ctrl_fub
// Purpose: SKELETON — tracks tREFI, issues refresh_req_o to the
//          scheduler, accepts refresh_grant_i to clear the deficit.
//          Supports postponed/pulled refresh (small accumulator).
//
// Status:  Port-list only. Never requests refresh.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module refresh_ctrl_fub
    import ddr2_lpddr2_pkg::*;
(
    input  logic        mc_clk,
    input  logic        mc_rst_n,

    input  logic [15:0] t_refi_i,         // refresh interval (DFI cycles)
    input  logic [3:0]  refresh_burst_i,  // 1..8 (per-bank or all-bank)
    input  logic        enable_i,

    output logic        refresh_req_o,
    input  logic        refresh_grant_i,
    output logic [3:0]  pending_refreshes_o
);

    // -- TODO: implementation --
    assign refresh_req_o       = 1'b0;
    assign pending_refreshes_o = '0;

    wire unused = |{ mc_clk, mc_rst_n,
                     t_refi_i, refresh_burst_i, enable_i,
                     refresh_grant_i };

endmodule : refresh_ctrl_fub
