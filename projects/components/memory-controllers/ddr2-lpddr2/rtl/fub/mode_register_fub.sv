// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: mode_register_fub
// Purpose: SKELETON — holds MR0..MR3 (DDR2/3) / MR0..MR16 (LPDDR2)
//          shadow registers, builds MRS commands on request, drives
//          live values (CL, BL, AL, drive strength, ODT, …) to
//          xbank_timers and dfi_cmd_formatter.
//
// Status:  Port-list only. Exposes JEDEC-default-shaped constants.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module mode_register_fub
    import ddr2_lpddr2_pkg::*;
#(
    parameter int NUM_RANKS = 1,
    parameter int RKW       = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1
) (
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    input  memtype_e             memtype_i,

    // ----- CSR-style MR writes (from init_sequencer or APB) -----
    input  logic                 mr_we_i,
    input  logic [4:0]           mr_index_i,    // 0..16 for LPDDR2
    input  logic [15:0]          mr_data_i,
    input  logic [RKW-1:0]       mr_rank_i,

    // ----- MR-issue request to scheduler -----
    output logic                 mr_req_o,
    input  logic                 mr_grant_i,
    output logic [4:0]           mr_req_index_o,
    output logic [15:0]          mr_req_data_o,
    output logic [RKW-1:0]       mr_req_rank_o,

    // ----- live values consumed elsewhere -----
    output logic [3:0]           cl_o,          // CAS latency
    output logic [3:0]           cwl_o,         // CAS write latency
    output logic [3:0]           bl_o,          // burst length
    output logic [3:0]           al_o,          // additive latency
    output logic [1:0]           drv_strength_o,
    output logic [1:0]           odt_o
);

    // -- TODO: implementation --
    assign mr_req_o        = 1'b0;
    assign mr_req_index_o  = '0;
    assign mr_req_data_o   = '0;
    assign mr_req_rank_o   = '0;
    assign cl_o            = 4'd5;   // DDR2 typical
    assign cwl_o           = 4'd4;
    assign bl_o            = 4'd4;
    assign al_o            = 4'd0;
    assign drv_strength_o  = 2'd0;
    assign odt_o           = 2'd0;

    wire unused = |{ mc_clk, mc_rst_n, memtype_i,
                     mr_we_i, mr_index_i, mr_data_i, mr_rank_i,
                     mr_grant_i };

endmodule : mode_register_fub
