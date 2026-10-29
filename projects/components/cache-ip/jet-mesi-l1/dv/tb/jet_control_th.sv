// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_control_th
// Purpose:
//   Test harness for the jet_control lookup+commit+snoop bring-up (Tasks
//   5-7).  Wires the DUT to the REAL l1_tag_array / l1_data_array /
//   l1_repl / jet_mshr / jet_wb_buffer / jet_rsp_seq blocks and exposes
//   the partner handshakes (fill engine incl. PassDirty, drain engine)
//   plus the l1_snoop_resp core-facing snoop contract at the top so the
//   cocotb TB can model partner handshake timing only.  Pure wiring plus
//   three muxes: the tag-array write port (control's init/promotion/
//   commit-install/snoop-effect wins over the TB backdoor setup install),
//   the tag-array port B read (the DUT's snoop probe wins over the TB
//   backdoor readback), and the data-array write port (fill beats win
//   over control's write-hit/commit merge -- the MAS fill > write-hit
//   rule; control yields, so the two never actually collide).  The
//   response deposit port is the DUT's alone: the lookup-hit /
//   commit-deposit arbitration is internal to jet_control (Task 6).
//
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-28

`timescale 1ns / 1ps

//==============================================================================
// Module: jet_control_th
//==============================================================================
// Description:
//   Harness closure for jet_control unit DV.  The commit pipeline (Task 6)
//   is internal to the DUT: fill_done_i (with fill_pass_dirty_i) triggers
//   the D-4 store merge, the tag install, the deferred snoop effect, the
//   response deposits, and the MSHR retire -- the TB scores all of them
//   from the taps.  The snoop path (Task 7) is the DUT's: the TB drives
//   the l1_snoop_resp core-facing contract directly (sn_req/sn_addr/
//   sn_type, combinational grant-cycle CRRESP, CD beats on
//   cdvalid/cdready); the DUT's snoop probes reach the REAL jet_mshr
//   (sn_* + sn_eff record) and jet_wb_buffer (snarf incl. the BRESP-cycle
//   tap), and the tag array's port B muxes the DUT's snoop lookup over
//   the TB backdoor read (init-walk readback).
//
//   Scoreboard taps expose every scoreable internal wire: the muxed array
//   write ports with attribution enables, the repl interface, the MSHR
//   alloc grant/index and retire, the WB capture/drain head, the deposit
//   port, and the classify pulses.
//
//==============================================================================

module jet_control_th
    import jet_pkg::*;
    import l1_pkg::*;
#(
    parameter int ADDR_WIDTH   = AMBER_ADDR_WIDTH,
    parameter int SETS         = AMBER_SETS,
    parameter int WAYS         = AMBER_WAYS,
    parameter int LINE_BYTES   = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH    = AMBER_BUS_WIDTH,
    parameter int MSHR_COUNT   = jet_pkg::MSHR_COUNT,
    parameter int VICTIM_DEPTH = jet_pkg::VICTIM_DEPTH,
    localparam int SET_W       = $clog2(SETS),
    localparam int OFF_W       = $clog2(LINE_BYTES),
    localparam int TAG_W       = ADDR_WIDTH - SET_W - OFF_W,
    localparam int TSW         = TAG_W + 3,
    localparam int STRB_W      = BUS_WIDTH / 8,
    localparam int FILL_BEATS  = LINE_BYTES / STRB_W,
    localparam int BEAT_W      = $clog2(FILL_BEATS),
    localparam int WAY_W       = $clog2(WAYS),
    localparam int MEM_ADDR_W  = SET_W + BEAT_W,
    localparam int LINE_W      = ADDR_WIDTH - OFF_W,
    localparam int MW          = $clog2(MSHR_COUNT),
    localparam int RSP_DEPTH   = MSHR_COUNT + 2,
    localparam int SEQ_W       = $clog2(RSP_DEPTH),
    localparam int WB_W        = (VICTIM_DEPTH <= 2) ? 1 : $clog2(VICTIM_DEPTH),
    localparam int LINE_BITS   = LINE_BYTES * 8
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // front-end lookup request
    input  logic                        lkup_valid_i,
    input  logic [ADDR_WIDTH-1:0]       lkup_addr_i,
    input  logic                        lkup_we_i,
    input  logic [STRB_W-1:0]           lkup_be_i,
    input  logic [BUS_WIDTH-1:0]        lkup_wdata_i,
    output logic                        lkup_ready_o,

    // GAXI response channel (from jet_rsp_seq)
    output logic                        rsp_valid_o,
    output logic [BUS_WIDTH-1:0]        rsp_data_o,
    input  logic                        rsp_ready_i,

    // classify observability (from jet_control)
    output logic                        init_busy_o,
    output logic                        cap_busy_o,
    output logic                        cmt_busy_o,
    output logic                        lkup_hit_o,
    output logic                        lkup_merge_o,
    output logic                        lkup_miss_alloc_o,
    output logic                        lkup_upgrade_o,
    output logic                        lkup_stall_o,
    output logic [2:0]                  lkup_stall_reason_o,
    output logic                        lkup_wr_yield_o,
    output logic                        ctrl_error_o,

    // fill engine stub (handshake timing only; PassDirty carried to done)
    input  logic                        fill_accept_i,
    input  logic                        fill_pass_dirty_i,
    input  logic                        fill_beat_valid_i,
    input  logic [MW-1:0]               fill_beat_idx_i,
    input  logic [BEAT_W-1:0]           fill_beat_num_i,
    input  logic                        fill_done_i,
    // the burst server's burst-start pulse (the stub's model of the
    // engine's AR acceptance -- the pre-AR rule's progress input)
    input  logic                        fill_ar_done_i,
    output logic                        fill_start_o,
    output logic [ADDR_WIDTH-1:0]       fill_addr_o,
    output logic [1:0]                  fill_cls_o,

    // fill-beat array writes (the stub's W-port stream; also the TB's
    // data-array backdoor for line setup)
    input  logic                        fillbeat_wr_en,
    input  logic [MEM_ADDR_W-1:0]       fillbeat_wr_addr,
    input  logic [WAY_W-1:0]            fillbeat_wr_way,
    input  logic [BUS_WIDTH-1:0]        fillbeat_wr_data,
    input  logic [STRB_W-1:0]           fillbeat_wr_be,

    // drain engine stub + WB drain head taps
    input  logic                        drain_done_i,
    output logic                        drain_start_o,
    output logic                        wb_drain_valid_o,
    output logic [ADDR_WIDTH-1:0]       wb_drain_addr_o,
    output logic [LINE_BITS-1:0]        wb_drain_data_o,

    // snoop responder (l1_snoop_resp core-facing contract, TB-driven)
    input  logic                        sn_req_i,
    input  logic [ADDR_WIDTH-1:0]       sn_addr_i,
    input  logic [2:0]                  sn_type_i,
    input  logic                        sn_cdready_i,
    output logic                        sn_ready_o,
    output logic                        sn_safe_o,
    output logic [4:0]                  sn_crresp_o,
    output logic [BUS_WIDTH-1:0]        sn_cddata_o,
    output logic                        sn_cdlast_o,
    output logic                        sn_cdvalid_o,
    // snoop-path observability taps
    output logic [1:0]                  wb_sn_eff_o,
    output logic                        wb_sn_bresp_cycle_o,

    // TB backdoor tag install (scenario setup only; control wins the port)
    input  logic                        bd_tag_wr_en,
    input  logic [WAY_W-1:0]            bd_tag_wr_way,
    input  logic [SET_W-1:0]            bd_tag_wr_set,
    input  logic [TSW-1:0]              bd_tag_wr_tag_state,

    // scoreboard taps: muxed array write ports + attribution
    output logic                        tag_wr_en_o,
    output logic [WAYS-1:0]             tag_wr_way_onehot_o,
    output logic [SET_W-1:0]            tag_wr_set_o,
    output logic [TSW-1:0]              tag_wr_tag_state_o,
    output logic                        ctrl_tag_wr_en_o,
    output logic                        dat_wr_en_o,
    output logic [WAYS-1:0]             dat_wr_way_onehot_o,
    output logic [MEM_ADDR_W-1:0]       dat_wr_addr_o,
    output logic [BUS_WIDTH-1:0]        dat_wr_wdata_o,
    output logic [STRB_W-1:0]           dat_wr_be_o,
    output logic                        ctrl_dat_wr_en_o,

    // repl / MSHR / WB / deposit taps
    output logic                        repl_req_o,
    output logic                        repl_hit_o,
    output logic                        repl_update_o,
    output logic [WAY_W-1:0]            repl_hit_way_o,
    output logic [WAY_W-1:0]            repl_victim_way_o,
    output logic                        mshr_alloc_gnt_o,
    output logic [MW-1:0]               mshr_alloc_idx_o,
    output logic                        mshr_retire_o,
    output logic [MW-1:0]               mshr_retire_idx_o,
    output logic [MW:0]                 mshr_occupancy_o,
    output logic                        wb_cap_o,
    output logic                        wb_cap_gnt_o,
    output logic [WB_W-1:0]             wb_cap_slot_o,
    output logic                        wb_full_o,
    output logic                        cpl_valid_o,
    output logic [SEQ_W-1:0]            cpl_tag_o,
    output logic [BUS_WIDTH-1:0]        cpl_data_o,

    // tag-array port B: TB backdoor read (init-walk readback)
    input  logic [SET_W-1:0]            tag_b_set_i,
    output logic [WAYS-1:0][TSW-1:0]    tag_b_tag_state_o
);

    // ------------------------------------------------------------------
    // DUT <-> block wires
    // ------------------------------------------------------------------
    // tag array port A
    logic [SET_W-1:0]           ctrl_tag_a_set;
    logic [WAYS-1:0][TSW-1:0]   ctrl_tag_a_tag_state;
    logic                       ctrl_tag_a_wr_en;
    logic [WAYS-1:0]            ctrl_tag_a_wr_way_onehot;
    logic [SET_W-1:0]           ctrl_tag_a_wr_set;
    logic [TSW-1:0]             ctrl_tag_a_wr_tag_state;
    // data array port A
    logic [MEM_ADDR_W-1:0]      ctrl_dat_a_addr;
    logic [WAY_W-1:0]           ctrl_dat_a_way;
    logic [BUS_WIDTH-1:0]       ctrl_dat_a_rdata;
    logic                       ctrl_dat_a_wr_en;
    logic [WAYS-1:0]            ctrl_dat_a_wr_way_onehot;
    logic [MEM_ADDR_W-1:0]      ctrl_dat_a_wr_addr;
    logic [BUS_WIDTH-1:0]       ctrl_dat_a_wr_wdata;
    logic [STRB_W-1:0]          ctrl_dat_a_wr_be;
    // data array port B (victim capture)
    logic [MEM_ADDR_W-1:0]      ctrl_dat_b_addr;
    logic [WAY_W-1:0]           ctrl_dat_b_way;
    logic [BUS_WIDTH-1:0]       ctrl_dat_b_rdata;
    // repl
    logic                       ctrl_repl_req;
    logic [SET_W-1:0]           ctrl_repl_set;
    logic                       ctrl_repl_hit;
    logic                       ctrl_repl_update;
    logic [WAY_W-1:0]           ctrl_repl_hit_way;
    // MSHR: control -> file
    logic                       ctrl_mshr_alloc;
    logic [LINE_W-1:0]          ctrl_mshr_alloc_line;
    logic [SET_W-1:0]           ctrl_mshr_alloc_set;
    logic [1:0]                 ctrl_mshr_alloc_cls;
    logic                       ctrl_mshr_alloc_install;
    logic [WAY_W-1:0]           ctrl_mshr_alloc_victim_way;
    logic [WB_W-1:0]            ctrl_mshr_alloc_wb_slot;
    logic                       ctrl_mshr_alloc_wb_valid;
    logic [SEQ_W-1:0]           ctrl_mshr_alloc_seq;
    logic [LINE_W-1:0]          ctrl_mshr_lkup_line;
    logic [MW-1:0]              ctrl_mshr_cpl_idx;
    logic                       ctrl_mshr_merge;
    logic [MW-1:0]              ctrl_mshr_merge_idx;
    logic [SEQ_W-1:0]           ctrl_mshr_merge_seq;
    logic                       ctrl_mshr_beat;
    logic [MW-1:0]              ctrl_mshr_beat_idx;
    logic [BEAT_W-1:0]          ctrl_mshr_beat_num;
    logic                       ctrl_mshr_retire;
    logic [MW-1:0]              ctrl_mshr_retire_idx;
    // MSHR: file -> control
    logic                       mshr_alloc_gnt;
    logic [MW-1:0]              mshr_alloc_idx;
    logic                       mshr_full;
    logic                       mshr_set_full;
    logic                       mshr_lkup_reg_match;
    logic [MW-1:0]              mshr_lkup_reg_match_idx;
    logic [1:0]                 mshr_lkup_reg_match_cls;
    logic [MW:0]                mshr_cpl_merge_count;
    logic [LINE_W-1:0]          mshr_cpl_line;
    logic [1:0]                 mshr_cpl_pend_eff;
    logic [MSHR_COUNT*SEQ_W-1:0] mshr_cpl_merge_seqs;
    // MSHR: snoop probe + deferred-effect record (Task 7: wired to the DUT)
    logic [LINE_W-1:0]          ctrl_mshr_sn_line;
    logic                       ctrl_mshr_sn_eff;
    logic [MW-1:0]              ctrl_mshr_sn_eff_idx;
    logic [1:0]                 ctrl_mshr_sn_eff_value;
    logic                       mshr_sn_match;
    logic [MW-1:0]              mshr_sn_match_idx;
    logic [FILL_BEATS-1:0]      mshr_sn_beats_rcvd;
    logic                       mshr_sn_install;
    // MSHR: dangling (the overlay match outputs are unused -- control
    // consumes the registered-only probe; cpl_install/wb_slot/wb_valid
    // have no commit consumer)
    logic                       mshr_lkup_match_nc;
    logic [MW-1:0]              mshr_lkup_match_idx_nc;
    logic [1:0]                 mshr_lkup_match_cls_nc;
    logic                       mshr_cpl_install_nc;
    logic [WB_W-1:0]            mshr_cpl_wb_slot_nc;
    logic                       mshr_cpl_wb_valid_nc;
    // WB buffer: control <-> buffer
    logic                       ctrl_wb_cap;
    logic [LINE_W-1:0]          ctrl_wb_cap_line;
    logic                       ctrl_wb_cap_beat;
    logic [BUS_WIDTH-1:0]       ctrl_wb_cap_beat_data;
    logic [LINE_W-1:0]          ctrl_wb_sn_line;
    logic [1:0]                 ctrl_wb_sn_eff;
    logic                       wb_cap_gnt;
    logic [WB_W-1:0]            wb_cap_slot;
    logic                       wb_full;
    logic                       wb_drain_valid;
    logic                       wb_sn_hit;
    logic [LINE_BITS-1:0]       wb_sn_data;
    logic                       wb_sn_bresp_cycle;
    logic [WB_W:0]              wb_occupancy_nc;
    // rsp_seq: control <-> sequencer
    logic                       ctrl_tag_req;
    logic                       rsp_tag_gnt;
    logic [SEQ_W-1:0]           rsp_tag;
    logic                       ctrl_cpl_valid;
    logic [SEQ_W-1:0]           ctrl_cpl_tag;
    logic [BUS_WIDTH-1:0]       ctrl_cpl_data;
    // tag write mux (control init/promotion/commit wins over backdoor)
    logic                       mux_tag_wr_en;
    logic [WAYS-1:0]            mux_tag_wr_way_onehot;
    logic [SET_W-1:0]           mux_tag_wr_set;
    logic [TSW-1:0]             mux_tag_wr_tag_state;
    // tag port B mux (the DUT's snoop probe wins over the TB backdoor read)
    logic                       ctrl_tag_b_req;
    logic [SET_W-1:0]           ctrl_tag_b_set;
    logic [WAYS-1:0][TSW-1:0]   tag_b_tag_state;
    logic [SET_W-1:0]           mux_tag_b_set;
    // data write mux (fill beats win over control's write-hit/commit merge)
    logic                       mux_dat_wr_en;
    logic [WAYS-1:0]            mux_dat_wr_way_onehot;
    logic [MEM_ADDR_W-1:0]      mux_dat_wr_addr;
    logic [BUS_WIDTH-1:0]       mux_dat_wr_wdata;
    logic [STRB_W-1:0]          mux_dat_wr_be;
    logic [WAYS-1:0]            fillbeat_wr_way_onehot;
    logic [WAYS-1:0]            bd_tag_wr_way_onehot;

    // ------------------------------------------------------------------
    // DUT
    // ------------------------------------------------------------------
    jet_control #(
        .ADDR_WIDTH   (ADDR_WIDTH),
        .SETS         (SETS),
        .WAYS         (WAYS),
        .LINE_BYTES   (LINE_BYTES),
        .BUS_WIDTH    (BUS_WIDTH),
        .MSHR_COUNT   (MSHR_COUNT),
        .VICTIM_DEPTH (VICTIM_DEPTH)
    ) u_control (
        .clk                     (clk),
        .rst_n                   (rst_n),
        .init_busy_o             (init_busy_o),
        .lkup_valid_i            (lkup_valid_i),
        .lkup_addr_i             (lkup_addr_i),
        .lkup_we_i               (lkup_we_i),
        .lkup_be_i               (lkup_be_i),
        .lkup_wdata_i            (lkup_wdata_i),
        .lkup_ready_o            (lkup_ready_o),
        .lkup_hit_o              (lkup_hit_o),
        .lkup_merge_o            (lkup_merge_o),
        .lkup_miss_alloc_o       (lkup_miss_alloc_o),
        .lkup_upgrade_o          (lkup_upgrade_o),
        .lkup_stall_o            (lkup_stall_o),
        .lkup_stall_reason_o     (lkup_stall_reason_o),
        .lkup_wr_yield_o         (lkup_wr_yield_o),
        .cap_busy_o              (cap_busy_o),
        .cmt_busy_o              (cmt_busy_o),
        .ctrl_error_o            (ctrl_error_o),
        .tag_req_o               (ctrl_tag_req),
        .tag_gnt_i               (rsp_tag_gnt),
        .tag_i                   (rsp_tag),
        .cpl_valid_o             (ctrl_cpl_valid),
        .cpl_tag_o               (ctrl_cpl_tag),
        .cpl_data_o              (ctrl_cpl_data),
        .tag_a_set_o             (ctrl_tag_a_set),
        .tag_a_tag_state_i       (ctrl_tag_a_tag_state),
        .tag_a_wr_en_o           (ctrl_tag_a_wr_en),
        .tag_a_wr_way_onehot_o   (ctrl_tag_a_wr_way_onehot),
        .tag_a_wr_set_o          (ctrl_tag_a_wr_set),
        .tag_a_wr_tag_state_o    (ctrl_tag_a_wr_tag_state),
        .dat_a_addr_o            (ctrl_dat_a_addr),
        .dat_a_way_o             (ctrl_dat_a_way),
        .dat_a_rdata_i           (ctrl_dat_a_rdata),
        .dat_a_wr_en_o           (ctrl_dat_a_wr_en),
        .dat_a_wr_way_onehot_o   (ctrl_dat_a_wr_way_onehot),
        .dat_a_wr_addr_o         (ctrl_dat_a_wr_addr),
        .dat_a_wr_wdata_o        (ctrl_dat_a_wr_wdata),
        .dat_a_wr_be_o           (ctrl_dat_a_wr_be),
        .dat_b_addr_o            (ctrl_dat_b_addr),
        .dat_b_way_o             (ctrl_dat_b_way),
        .dat_b_rdata_i           (ctrl_dat_b_rdata),
        .repl_req_o              (ctrl_repl_req),
        .repl_set_o              (ctrl_repl_set),
        .repl_victim_way_i       (repl_victim_way_o),
        .repl_hit_o              (ctrl_repl_hit),
        .repl_update_o           (ctrl_repl_update),
        .repl_hit_way_o          (ctrl_repl_hit_way),
        .mshr_alloc_o            (ctrl_mshr_alloc),
        .mshr_alloc_line_o       (ctrl_mshr_alloc_line),
        .mshr_alloc_set_o        (ctrl_mshr_alloc_set),
        .mshr_alloc_cls_o        (ctrl_mshr_alloc_cls),
        .mshr_alloc_install_o    (ctrl_mshr_alloc_install),
        .mshr_alloc_victim_way_o (ctrl_mshr_alloc_victim_way),
        .mshr_alloc_wb_slot_o    (ctrl_mshr_alloc_wb_slot),
        .mshr_alloc_wb_valid_o   (ctrl_mshr_alloc_wb_valid),
        .mshr_alloc_seq_o        (ctrl_mshr_alloc_seq),
        .mshr_alloc_gnt_i        (mshr_alloc_gnt),
        .mshr_alloc_idx_i        (mshr_alloc_idx),
        .mshr_full_i             (mshr_full),
        .mshr_set_full_i         (mshr_set_full),
        .mshr_lkup_line_o        (ctrl_mshr_lkup_line),
        .mshr_lkup_reg_match_i   (mshr_lkup_reg_match),
        .mshr_lkup_reg_match_idx_i(mshr_lkup_reg_match_idx),
        .mshr_lkup_reg_match_cls_i(mshr_lkup_reg_match_cls),
        .mshr_cpl_idx_o          (ctrl_mshr_cpl_idx),
        .mshr_cpl_merge_count_i  (mshr_cpl_merge_count),
        .mshr_cpl_line_i         (mshr_cpl_line),
        .mshr_cpl_pend_eff_i     (mshr_cpl_pend_eff),
        .mshr_cpl_merge_seqs_i   (mshr_cpl_merge_seqs),
        .mshr_merge_o            (ctrl_mshr_merge),
        .mshr_merge_idx_o        (ctrl_mshr_merge_idx),
        .mshr_merge_seq_o        (ctrl_mshr_merge_seq),
        .mshr_beat_o             (ctrl_mshr_beat),
        .mshr_beat_idx_o         (ctrl_mshr_beat_idx),
        .mshr_beat_num_o         (ctrl_mshr_beat_num),
        .mshr_retire_o           (ctrl_mshr_retire),
        .mshr_retire_idx_o       (ctrl_mshr_retire_idx),
        .wb_cap_o                (ctrl_wb_cap),
        .wb_cap_line_o           (ctrl_wb_cap_line),
        .wb_cap_beat_o           (ctrl_wb_cap_beat),
        .wb_cap_beat_data_o      (ctrl_wb_cap_beat_data),
        .wb_cap_gnt_i            (wb_cap_gnt),
        .wb_cap_slot_i           (wb_cap_slot),
        .wb_full_i               (wb_full),
        .wb_sn_line_o            (ctrl_wb_sn_line),
        .wb_sn_hit_i             (wb_sn_hit),
        .wb_sn_eff_o             (ctrl_wb_sn_eff),
        .wb_sn_data_i            (wb_sn_data),
        .wb_sn_bresp_cycle_i     (wb_sn_bresp_cycle),
        .wb_drain_valid_i        (wb_drain_valid),
        .drain_start_o           (drain_start_o),
        .drain_done_i            (drain_done_i),
        .tag_b_req_o             (ctrl_tag_b_req),
        .tag_b_set_o             (ctrl_tag_b_set),
        .tag_b_tag_state_i       (tag_b_tag_state),
        .mshr_sn_line_o          (ctrl_mshr_sn_line),
        .mshr_sn_match_i         (mshr_sn_match),
        .mshr_sn_match_idx_i     (mshr_sn_match_idx),
        .mshr_sn_beats_rcvd_i    (mshr_sn_beats_rcvd),
        .mshr_sn_install_i       (mshr_sn_install),
        .mshr_sn_eff_o           (ctrl_mshr_sn_eff),
        .mshr_sn_eff_idx_o       (ctrl_mshr_sn_eff_idx),
        .mshr_sn_eff_value_o     (ctrl_mshr_sn_eff_value),
        .sn_req_i                (sn_req_i),
        .sn_addr_i               (sn_addr_i),
        .sn_type_i               (sn_type_i),
        .sn_ready_o              (sn_ready_o),
        .sn_safe_o               (sn_safe_o),
        .sn_crresp_o             (sn_crresp_o),
        .sn_cddata_o             (sn_cddata_o),
        .sn_cdlast_o             (sn_cdlast_o),
        .sn_cdvalid_o            (sn_cdvalid_o),
        .sn_cdready_i            (sn_cdready_i),
        .fill_start_o            (fill_start_o),
        .fill_addr_o             (fill_addr_o),
        .fill_cls_o              (fill_cls_o),
        .fill_accept_i           (fill_accept_i),
        .fill_pass_dirty_i       (fill_pass_dirty_i),
        .fill_beat_valid_i       (fill_beat_valid_i),
        .fill_beat_idx_i         (fill_beat_idx_i),
        .fill_beat_num_i         (fill_beat_num_i),
        .fill_done_i             (fill_done_i),
        .fill_ar_done_i          (fill_ar_done_i)
    );

    // ------------------------------------------------------------------
    // MSHR file (Task 2).  The snoop probe and the deferred-effect record
    // are the DUT's (Task 7).
    // ------------------------------------------------------------------
    jet_mshr #(
        .MSHR_COUNT   (MSHR_COUNT),
        .SETS         (SETS),
        .WAYS         (WAYS),
        .LINE_W       (LINE_W),
        .SEQ_W        (SEQ_W),
        .VICTIM_DEPTH (VICTIM_DEPTH)
    ) u_mshr (
        .clk               (clk),
        .rst_n             (rst_n),
        .alloc_i           (ctrl_mshr_alloc),
        .alloc_line_i      (ctrl_mshr_alloc_line),
        .alloc_set_i       (ctrl_mshr_alloc_set),
        .alloc_cls_i       (ctrl_mshr_alloc_cls),
        .alloc_install_i   (ctrl_mshr_alloc_install),
        .alloc_victim_way_i(ctrl_mshr_alloc_victim_way),
        .alloc_wb_slot_i   (ctrl_mshr_alloc_wb_slot),
        .alloc_wb_valid_i  (ctrl_mshr_alloc_wb_valid),
        .alloc_seq_i       (ctrl_mshr_alloc_seq),
        .alloc_gnt_o       (mshr_alloc_gnt),
        .alloc_idx_o       (mshr_alloc_idx),
        .full_o            (mshr_full),
        .set_full_o        (mshr_set_full),
        .lkup_line_i       (ctrl_mshr_lkup_line),
        .lkup_match_o      (mshr_lkup_match_nc),
        .lkup_reg_match_o  (mshr_lkup_reg_match),
        .lkup_reg_match_idx_o(mshr_lkup_reg_match_idx),
        .lkup_reg_match_cls_o(mshr_lkup_reg_match_cls),
        .lkup_match_idx_o  (mshr_lkup_match_idx_nc),
        .lkup_match_cls_o  (mshr_lkup_match_cls_nc),
        .sn_line_i         (ctrl_mshr_sn_line),
        .sn_match_o        (mshr_sn_match),
        .sn_match_idx_o    (mshr_sn_match_idx),
        .sn_beats_rcvd_o   (mshr_sn_beats_rcvd),
        .sn_install_o      (mshr_sn_install),
        .merge_i           (ctrl_mshr_merge),
        .merge_idx_i       (ctrl_mshr_merge_idx),
        .merge_seq_i       (ctrl_mshr_merge_seq),
        .beat_i            (ctrl_mshr_beat),
        .beat_idx_i        (ctrl_mshr_beat_idx),
        .beat_num_i        (ctrl_mshr_beat_num),
        .sn_eff_i          (ctrl_mshr_sn_eff),
        .sn_eff_idx_i      (ctrl_mshr_sn_eff_idx),
        .sn_eff_value_i    (ctrl_mshr_sn_eff_value),
        .retire_i          (ctrl_mshr_retire),
        .retire_idx_i      (ctrl_mshr_retire_idx),
        .cpl_idx_i         (ctrl_mshr_cpl_idx),
        .cpl_line_o        (mshr_cpl_line),
        .cpl_install_o     (mshr_cpl_install_nc),
        .cpl_pend_eff_o    (mshr_cpl_pend_eff),
        .cpl_merge_seqs_o  (mshr_cpl_merge_seqs),
        .cpl_merge_count_o (mshr_cpl_merge_count),
        .cpl_wb_slot_o     (mshr_cpl_wb_slot_nc),
        .cpl_wb_valid_o    (mshr_cpl_wb_valid_nc),
        .occupancy_o       (mshr_occupancy_o)
    );

    // ------------------------------------------------------------------
    // Writeback buffer (Task 3).  Drain head exposed for the drain stub.
    // ------------------------------------------------------------------
    jet_wb_buffer #(
        .VICTIM_DEPTH (VICTIM_DEPTH),
        .LINE_W       (LINE_W),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .LINE_BYTES   (LINE_BYTES),
        .BUS_WIDTH    (BUS_WIDTH)
    ) u_wb (
        .clk             (clk),
        .rst_n           (rst_n),
        .cap_i           (ctrl_wb_cap),
        .cap_line_i      (ctrl_wb_cap_line),
        .cap_beat_i      (ctrl_wb_cap_beat),
        .cap_beat_data_i (ctrl_wb_cap_beat_data),
        .cap_gnt_o       (wb_cap_gnt),
        .cap_slot_o      (wb_cap_slot),
        .wb_full_o       (wb_full),
        .drain_valid_o   (wb_drain_valid),
        .drain_addr_o    (wb_drain_addr_o),
        .drain_data_o    (wb_drain_data_o),
        .drain_done_i    (drain_done_i),
        .sn_line_i       (ctrl_wb_sn_line),
        .sn_hit_o        (wb_sn_hit),
        .sn_data_o       (wb_sn_data),
        .sn_bresp_cycle_o(wb_sn_bresp_cycle),
        .sn_eff_i        (ctrl_wb_sn_eff),
        .wb_occupancy_o  (wb_occupancy_nc)
    );

    assign wb_drain_valid_o = wb_drain_valid;

    // ------------------------------------------------------------------
    // Response sequencer (Task 4).  The deposit port is the DUT's alone:
    // the lookup-hit / commit-deposit arbitration is internal (Task 6).
    // ------------------------------------------------------------------
    assign cpl_valid_o = ctrl_cpl_valid;
    assign cpl_tag_o   = ctrl_cpl_tag;
    assign cpl_data_o  = ctrl_cpl_data;

    jet_rsp_seq #(
        .RSP_DEPTH (RSP_DEPTH),
        .BUS_WIDTH (BUS_WIDTH),
        .SEQ_W     (SEQ_W)
    ) u_rsp (
        .clk         (clk),
        .rst_n       (rst_n),
        .tag_req_i   (ctrl_tag_req),
        .tag_gnt_o   (rsp_tag_gnt),
        .tag_o       (rsp_tag),
        .cpl_i       (ctrl_cpl_valid),
        .cpl_tag_i   (ctrl_cpl_tag),
        .cpl_data_i  (ctrl_cpl_data),
        .rsp_valid_o (rsp_valid_o),
        .rsp_data_o  (rsp_data_o),
        .rsp_ready_i (rsp_ready_i)
    );

    // ------------------------------------------------------------------
    // Tag array.  Port B: the DUT's snoop probe (grant cycle) wins over
    // the TB backdoor read (init-walk readback).  Write mux: control
    // (init walk / E->M promotion / commit install / snoop effect) wins
    // over the backdoor setup.
    // ------------------------------------------------------------------
    always_comb begin
        for (int w = 0; w < WAYS; w++) begin
            bd_tag_wr_way_onehot[w] = (bd_tag_wr_way == WAY_W'(w));
        end
    end

    assign mux_tag_b_set         = ctrl_tag_b_req ? ctrl_tag_b_set
                                                  : tag_b_set_i;
    assign tag_b_tag_state_o     = tag_b_tag_state;

    assign mux_tag_wr_en         = ctrl_tag_a_wr_en | bd_tag_wr_en;
    assign mux_tag_wr_way_onehot = ctrl_tag_a_wr_en ? ctrl_tag_a_wr_way_onehot
                                                    : bd_tag_wr_way_onehot;
    assign mux_tag_wr_set        = ctrl_tag_a_wr_en ? ctrl_tag_a_wr_set
                                                    : bd_tag_wr_set;
    assign mux_tag_wr_tag_state  = ctrl_tag_a_wr_en ? ctrl_tag_a_wr_tag_state
                                                    : bd_tag_wr_tag_state;

    l1_tag_array #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES)
    ) u_tag (
        .clk           (clk),
        .a_set         (ctrl_tag_a_set),
        .a_tag_state   (ctrl_tag_a_tag_state),
        .b_set         (mux_tag_b_set),
        .b_tag_state   (tag_b_tag_state),
        .wr_en         (mux_tag_wr_en),
        .wr_way_onehot (mux_tag_wr_way_onehot),
        .wr_set        (mux_tag_wr_set),
        .wr_tag_state  (mux_tag_wr_tag_state)
    );

    // ------------------------------------------------------------------
    // Data array.  Write mux: fill beats win over control's write-hit and
    // commit store-data merges (the MAS fill > write-hit rule; control
    // yields, so the two never actually collide).
    // ------------------------------------------------------------------
    always_comb begin
        for (int w = 0; w < WAYS; w++) begin
            fillbeat_wr_way_onehot[w] = (fillbeat_wr_way == WAY_W'(w));
        end
    end

    assign mux_dat_wr_en         = fillbeat_wr_en | ctrl_dat_a_wr_en;
    assign mux_dat_wr_way_onehot = fillbeat_wr_en ? fillbeat_wr_way_onehot
                                                  : ctrl_dat_a_wr_way_onehot;
    assign mux_dat_wr_addr       = fillbeat_wr_en ? fillbeat_wr_addr
                                                  : ctrl_dat_a_wr_addr;
    assign mux_dat_wr_wdata      = fillbeat_wr_en ? fillbeat_wr_data
                                                  : ctrl_dat_a_wr_wdata;
    assign mux_dat_wr_be         = fillbeat_wr_en ? fillbeat_wr_be
                                                  : ctrl_dat_a_wr_be;

    l1_data_array #(
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_data (
        .clk           (clk),
        .a_addr        (ctrl_dat_a_addr),
        .a_way         (ctrl_dat_a_way),
        .a_rdata       (ctrl_dat_a_rdata),
        .b_addr        (ctrl_dat_b_addr),
        .b_way         (ctrl_dat_b_way),
        .b_rdata       (ctrl_dat_b_rdata),
        .wr_en         (mux_dat_wr_en),
        .wr_way_onehot (mux_dat_wr_way_onehot),
        .wr_addr       (mux_dat_wr_addr),
        .wr_wdata      (mux_dat_wr_wdata),
        .wr_be         (mux_dat_wr_be)
    );

    // ------------------------------------------------------------------
    // Replacement engine.
    // ------------------------------------------------------------------
    l1_repl #(
        .SETS  (SETS),
        .WAYS  (WAYS)
    ) u_repl (
        .clk             (clk),
        .rst_n           (rst_n),
        .repl_req        (ctrl_repl_req),
        .repl_set        (ctrl_repl_set),
        .repl_victim_way (repl_victim_way_o),
        .repl_hit        (ctrl_repl_hit),
        .repl_update     (ctrl_repl_update),
        .repl_hit_way    (ctrl_repl_hit_way)
    );

    // ------------------------------------------------------------------
    // Scoreboard taps
    // ------------------------------------------------------------------
    assign tag_wr_en_o         = mux_tag_wr_en;
    assign tag_wr_way_onehot_o = mux_tag_wr_way_onehot;
    assign tag_wr_set_o        = mux_tag_wr_set;
    assign tag_wr_tag_state_o  = mux_tag_wr_tag_state;
    assign ctrl_tag_wr_en_o    = ctrl_tag_a_wr_en;
    assign dat_wr_en_o         = mux_dat_wr_en;
    assign dat_wr_way_onehot_o = mux_dat_wr_way_onehot;
    assign dat_wr_addr_o       = mux_dat_wr_addr;
    assign dat_wr_wdata_o      = mux_dat_wr_wdata;
    assign dat_wr_be_o         = mux_dat_wr_be;
    assign ctrl_dat_wr_en_o    = ctrl_dat_a_wr_en;
    assign repl_req_o          = ctrl_repl_req;
    assign repl_hit_o          = ctrl_repl_hit;
    assign repl_update_o       = ctrl_repl_update;
    assign repl_hit_way_o      = ctrl_repl_hit_way;
    assign mshr_alloc_gnt_o    = mshr_alloc_gnt;
    assign mshr_alloc_idx_o    = mshr_alloc_idx;
    assign mshr_retire_o       = ctrl_mshr_retire;
    assign mshr_retire_idx_o   = ctrl_mshr_retire_idx;
    assign wb_cap_o            = ctrl_wb_cap;
    assign wb_cap_gnt_o        = wb_cap_gnt;
    assign wb_cap_slot_o       = wb_cap_slot;
    assign wb_full_o           = wb_full;
    assign wb_sn_eff_o         = ctrl_wb_sn_eff;
    assign wb_sn_bresp_cycle_o = wb_sn_bresp_cycle;

endmodule : jet_control_th
