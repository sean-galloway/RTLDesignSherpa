// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: mc_init_plane
// Purpose: Common DRAM initialization plane (xDDR2 generation: DDR2/LPDDR2).
//          Owns the full bring-up concern, extracted from mc_scheduler_plane:
//            1. mc_xddr2_init_sequencer — JEDEC DDR2 init chain and the
//               LPDDR2 MRW chain (Reset -> ZQ -> MR1/2/3), CSR-backed waits
//               and (LPDDR2) CSR-backed MR OP data, init_restart re-run.
//            2. mc_xddr2_mode_register — per-rank MR shadow + live CL/CWL/BL
//               decode; written by the sequencer (mr_seq_we) during bring-up.
//
//          The plane drives the DFI PHY init handshake directly and injects
//          init commands through the scheduler plane's EXTERNAL init port
//          (the scheduler plane is built with HAS_INIT_SEQUENCER=0,
//          HAS_MODE_REGISTER=0 — the same mode scoria's wrapper uses).
//          Normal scheduling is overridden by the pick core while
//          !init_done, so the injected commands reach the DRAM unarbitrated.
//
//          Telemetry: init_busy_o / init_state_o expose the FSM phase for
//          board bring-up debug (a PHY that never raises dfi_init_complete
//          parks the FSM in S_DFI_INIT == 5'd1). init_state_o is the raw
//          FSM enum, not a stable ABI.
//
//          Extracted per docs/superpowers/specs/2026-10-15-mc-init-plane-design.md;
//          both granite (product) and pumice (research) instantiate this
//          plane identically, so init work translates between them directly.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_init_plane
    import mc_common_pkg::*;
#(
    parameter int NUM_RANKS = 1,
    parameter int NUM_BANKS = 8,
    parameter int ROW_WIDTH = 14,
    parameter int BKW       = $clog2(NUM_BANKS)
) (
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    input  memtype_e             memtype_i,

    // ---- JEDEC init-sequence waits (CSR-backed, MC cycles) ----
    input  logic [15:0]          t_init_wait_i,
    input  logic [15:0]          t_dll_wait_i,
    input  logic [7:0]           t_mrd_wait_i,
    input  logic [7:0]           t_rp_wait_i,
    input  logic [7:0]           t_rfc_wait_i,

    // ---- DDR2 mode-register values (CSR-backed: MR0..MR3.VAL) ----
    input  logic [15:0]          mr0_i,
    input  logic [15:0]          mr1_i,
    input  logic [15:0]          mr2_i,
    input  logic [15:0]          mr3_i,

    // ---- LPDDR2 mode-register OP data (CSR-backed: LP_MR1/2/3_OP) ----
    input  logic [7:0]           lp_mr1_op_i,
    input  logic [7:0]           lp_mr2_op_i,
    input  logic [7:0]           lp_mr3_op_i,

    // Re-run the JEDEC chain without a controller reset (CTRL.init_force_
    // restart rising edge).
    input  logic                 init_restart_i,

    // ---- DFI PHY init handshake ----
    output logic                 dfi_init_start_o,
    input  logic                 dfi_init_complete_i,

    // ---- init command injection (to the scheduler plane external port) ----
    output logic                 init_cmd_valid_o,
    output dram_op_e             init_cmd_op_o,
    output logic [BKW-1:0]       init_cmd_bank_o,
    output logic [ROW_WIDTH-1:0] init_cmd_row_o,

    // ---- status / telemetry ----
    output logic                 init_busy_o,
    output logic                 init_done_o,
    output logic [4:0]           init_state_o,
    output logic [3:0]           cl_o,
    output logic [3:0]           cwl_o,
    output logic [3:0]           bl_o
);

    logic        w_mr_seq_we;
    logic [4:0]  w_mr_seq_index;
    logic [15:0] w_mr_seq_data;

    mc_xddr2_init_sequencer #(
        .ROW_WIDTH (ROW_WIDTH),
        .NUM_BANKS (NUM_BANKS)
    ) u_init (
        .mc_clk             (mc_clk),
        .mc_rst_n           (mc_rst_n),
        .memtype_i          (memtype_i),
        .t_init_wait_i      (t_init_wait_i),
        .t_dll_wait_i       (t_dll_wait_i),
        .t_mrd_wait_i       (t_mrd_wait_i),
        .t_rp_wait_i        (t_rp_wait_i),
        .t_rfc_wait_i       (t_rfc_wait_i),
        .mr0_i              (mr0_i),
        .mr1_i              (mr1_i),
        .mr2_i              (mr2_i),
        .mr3_i              (mr3_i),
        .lp_mr1_op_i        (lp_mr1_op_i),
        .lp_mr2_op_i        (lp_mr2_op_i),
        .lp_mr3_op_i        (lp_mr3_op_i),
        .init_restart_i     (init_restart_i),
        .dfi_init_start_o   (dfi_init_start_o),
        .dfi_init_complete_i(dfi_init_complete_i),
        .mr_seq_we_o        (w_mr_seq_we),
        .mr_seq_index_o     (w_mr_seq_index),
        .mr_seq_data_o      (w_mr_seq_data),
        .init_cmd_valid_o   (init_cmd_valid_o),
        .init_cmd_op_o      (init_cmd_op_o),
        .init_cmd_bank_o    (init_cmd_bank_o),
        .init_cmd_row_o     (init_cmd_row_o),
        .zqcl_req_o         (),
        .zqcl_grant_i       (1'b0),
        .init_busy_o        (init_busy_o),
        .init_done_o        (init_done_o),
        .init_state_o       (init_state_o)
    );

    mc_xddr2_mode_register #(
        .NUM_RANKS (NUM_RANKS)
    ) u_mode_reg (
        .mc_clk         (mc_clk),
        .mc_rst_n       (mc_rst_n),
        .memtype_i      (memtype_i),
        .mr_we_i        (w_mr_seq_we),
        .mr_index_i     (w_mr_seq_index),
        .mr_data_i      (w_mr_seq_data),
        .mr_rank_i      ('0),
        .mr_req_o       (),
        .mr_grant_i     (1'b0),
        .mr_req_index_o (),
        .mr_req_data_o  (),
        .mr_req_rank_o  (),
        .cl_o           (cl_o),
        .cwl_o          (cwl_o),
        .bl_o           (bl_o),
        .al_o           (),
        .drv_strength_o (),
        .odt_o          ()
    );

endmodule : mc_init_plane
