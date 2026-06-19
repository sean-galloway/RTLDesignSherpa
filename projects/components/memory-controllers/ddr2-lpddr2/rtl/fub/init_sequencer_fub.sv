// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: init_sequencer_fub
// Purpose: SKELETON — post-reset DRAM init sequence per JEDEC for the
//          chosen memtype. Drives dfi_init_start, waits for
//          dfi_init_complete, then runs the MR-load / ZQCL chain via
//          the mode_register_fub and scheduler.
//
// Status:  Port-list only. Asserts init_done immediately.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module init_sequencer_fub
    import ddr2_lpddr2_pkg::*;
(
    input  logic        mc_clk,
    input  logic        mc_rst_n,

    input  memtype_e    memtype_i,

    // ----- DFI status -----
    output logic        dfi_init_start_o,
    input  logic        dfi_init_complete_i,

    // ----- MR / scheduler injection -----
    output logic        mr_seq_we_o,
    output logic [4:0]  mr_seq_index_o,
    output logic [15:0] mr_seq_data_o,
    output logic        zqcl_req_o,
    input  logic        zqcl_grant_i,

    // ----- status -----
    output logic        init_busy_o,
    output logic        init_done_o
);

    // -- TODO: implementation --
    assign dfi_init_start_o = 1'b0;
    assign mr_seq_we_o      = 1'b0;
    assign mr_seq_index_o   = '0;
    assign mr_seq_data_o    = '0;
    assign zqcl_req_o       = 1'b0;
    assign init_busy_o      = 1'b0;
    assign init_done_o      = 1'b1;   // pretend init finished — TODO real FSM

    wire unused = |{ mc_clk, mc_rst_n, memtype_i,
                     dfi_init_complete_i, zqcl_grant_i };

endmodule : init_sequencer_fub
