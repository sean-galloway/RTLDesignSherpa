// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_mshr_th
// Purpose:
//   Test harness wrapper for jet_mshr (the MAB file). Pure pass-through:
//   every jet_mshr port is exposed at the top under the same name so the
//   cocotb TB drives the DUT pins directly, and the J1/J5/geometry
//   parameters forward so -G elaboration overrides reach the DUT.
//
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-28

`timescale 1ns / 1ps

module jet_mshr_th
    import jet_pkg::*;
    import l1_pkg::*;
#(
    parameter int MSHR_COUNT   = jet_pkg::MSHR_COUNT,
    parameter int SETS         = AMBER_SETS,
    parameter int WAYS         = AMBER_WAYS,
    parameter int LINE_W       = AMBER_ADDR_WIDTH - $clog2(AMBER_LINE_BYTES),
    parameter int SEQ_W        = jet_pkg::SEQ_W,
    parameter int VICTIM_DEPTH = jet_pkg::VICTIM_DEPTH,
    localparam int SET_W  = $clog2(SETS),
    localparam int WAY_W  = $clog2(WAYS),
    localparam int MW     = $clog2(MSHR_COUNT),
    localparam int FILL_BEATS = AMBER_FILL_BEATS,
    localparam int BEAT_W = $clog2(FILL_BEATS),
    localparam int WB_W   = (VICTIM_DEPTH <= 2) ? 1 : $clog2(VICTIM_DEPTH)
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // Alloc request (grant/index combinational)
    input  logic                        alloc_i,
    input  logic [LINE_W-1:0]           alloc_line_i,
    input  logic [SET_W-1:0]            alloc_set_i,
    input  logic [1:0]                  alloc_cls_i,
    input  logic                        alloc_install_i,
    input  logic [WAY_W-1:0]            alloc_victim_way_i,
    input  logic [WB_W-1:0]             alloc_wb_slot_i,
    input  logic                        alloc_wb_valid_i,
    input  logic [SEQ_W-1:0]            alloc_seq_i,
    output logic                        alloc_gnt_o,
    output logic [MW-1:0]               alloc_idx_o,
    output logic                        full_o,
    output logic                        set_full_o,

    // Lookup-side CAM probe (merge / cross-class classify)
    input  logic [LINE_W-1:0]           lkup_line_i,
    output logic                        lkup_match_o,
    output logic                        lkup_reg_match_o,
    output logic [MW-1:0]               lkup_reg_match_idx_o,
    output logic [1:0]                  lkup_reg_match_cls_o,
    output logic [MW-1:0]               lkup_match_idx_o,
    output logic [1:0]                  lkup_match_cls_o,

    // Snoop-side CAM probe (pending-fill hazard + PF_GUARD)
    input  logic [LINE_W-1:0]           sn_line_i,
    output logic                        sn_match_o,
    output logic [MW-1:0]               sn_match_idx_o,
    output logic [FILL_BEATS-1:0]       sn_beats_rcvd_o,
    output logic                        sn_install_o,

    // Merge: append a waiter sequence tag to an entry
    input  logic                        merge_i,
    input  logic [MW-1:0]               merge_idx_i,
    input  logic [SEQ_W-1:0]            merge_seq_i,

    // Fill beat landed (PF_GUARD tracking)
    input  logic                        beat_i,
    input  logic [MW-1:0]               beat_idx_i,
    input  logic [BEAT_W-1:0]           beat_num_i,

    // Deferred post-commit snoop effect
    input  logic                        sn_eff_i,
    input  logic [MW-1:0]               sn_eff_idx_i,
    input  logic [1:0]                  sn_eff_value_i,

    // Retire on commit
    input  logic                        retire_i,
    input  logic [MW-1:0]               retire_idx_i,

    // Commit read port
    input  logic [MW-1:0]               cpl_idx_i,
    output logic [LINE_W-1:0]           cpl_line_o,
    output logic                        cpl_install_o,
    output logic [1:0]                  cpl_pend_eff_o,
    output logic [MSHR_COUNT*SEQ_W-1:0] cpl_merge_seqs_o,
    output logic [MW:0]                 cpl_merge_count_o,
    output logic [WB_W-1:0]             cpl_wb_slot_o,
    output logic                        cpl_wb_valid_o,

    // MonBus occupancy gauge (J7)
    output logic [MW:0]                 occupancy_o
);

    jet_mshr #(
        .MSHR_COUNT   (MSHR_COUNT),
        .SETS         (SETS),
        .WAYS         (WAYS),
        .LINE_W       (LINE_W),
        .SEQ_W        (SEQ_W),
        .VICTIM_DEPTH (VICTIM_DEPTH)
    ) u_mshr (.*);

endmodule : jet_mshr_th
