// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Macro contract testbench: mc_xddr2_entry_store + a REAL pick core.
//
// SCHED_CORE selects the core under test (mc_common_pkg MC_SCHED_*):
//   MC_SCHED_BANK_PICK  entry store -> mc_bank_head_records (x2) -> mc_bank_pick
//   MC_SCHED_FRFCFS     entry store -> mc_cmd_arbiter (per-entry vectors)
// STORE_BACKEND selects the storage backend (granite_core's parameter):
//   0  mc_xddr2_entry_store (+ the records under BANK_PICK)
//   1  mc_bank_fifo_store, records read off the bank FIFO fronts (BANK_PICK only;
//      recovery plan Phase 4 storage battery: same contract surface, N=8, 2xN chunks)
//
// Why this exists: the store<->core commit/issue ready contract is STRUCTURAL
// ("sink has room"), and a core gates its column picks on that one scalar. A
// slot-qualified ready closes a combinational circle that permanently wedges
// the scheduler once a committed slot drains while the core's slot pointer
// still references it -- invisible at N=1 (the next push self-heals) and
// invisible to any fub-level test of the store alone. Only store+core
// co-simulation at NUM_ENTRIES>=2 with MORE than N chunks per direction
// exercises it. See the 2026-10-13/14 granite hang: 9 commits, then a
// permanent stall with 7 filled entries schedulable.
//
// The four pipeline-acceptance cells (hold-on-not-fired, zero-bubble stream,
// post-pop winner, override preempts a held pick) read the core through the
// generic observability outputs below, never through core internals, so one
// test file scores both cores.
//
// All DRAM-side inputs are tied permissive (page open to row 0 on every bank,
// every timer ok) except the cocotb-driven live gates and the init override,
// so the pick pool lives or dies purely on the contract under test.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_store_arbiter_macro_tb_top
    import mc_common_pkg::*;
#(
    parameter int NUM_ENTRIES         = 8,
    parameter int AXI_ID_WIDTH        = 8,
    parameter int AXI_DATA_WIDTH      = 64,
    parameter int NUM_RANKS           = 1,
    parameter int NUM_BANKS           = 8,
    parameter int ROW_WIDTH           = 14,
    parameter int COL_WIDTH           = 10,
    parameter int AXI_BEATS_PER_BURST = 1,
    parameter int RD_RET_DEPTH        = 32,
    parameter int SCHED_CORE          = MC_SCHED_BANK_PICK,
    parameter int STORE_BACKEND       = 0,
    // The pick core's close-on-drain is exact (AP on the last same-row entry);
    // off here so the stub bank model's AP close cannot manufacture bubbles in
    // the streaming cells. The FRFCFS core keeps its own default.
    parameter bit PICK_CLOSE_ON_DRAIN = 1'b0,
    // Derived
    parameter int IW   = AXI_ID_WIDTH,
    parameter int DW   = AXI_DATA_WIDTH,
    parameter int SW   = AXI_DATA_WIDTH / 8,
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int PTRW = (NUM_ENTRIES > 1) ? $clog2(NUM_ENTRIES) : 1,
    parameter int RTW  = $clog2(RD_RET_DEPTH)
) (
    input  logic                 aclk,
    input  logic                 aresetn,

    // WR descriptor push (from cocotb)
    input  logic                 aw_push_valid,
    output logic                 aw_push_ready,
    input  logic [BKW-1:0]       aw_push_bank,
    input  logic [ROW_WIDTH-1:0] aw_push_row,
    input  logic [COL_WIDTH-1:0] aw_push_col,
    input  logic [IW-1:0]        aw_push_id,
    input  logic [3:0]           aw_push_qos,
    input  logic                 aw_push_agg,
    input  logic                 aw_push_last,

    // WR data beats (from cocotb)
    input  logic                 wd_valid,
    output logic                 wd_ready,
    input  logic [DW-1:0]        wd_data,
    input  logic [SW-1:0]        wd_strb,
    input  logic                 wd_last,

    // RD descriptor push (from cocotb)
    input  logic                 ar_push_valid,
    output logic                 ar_push_ready,
    input  logic [BKW-1:0]       ar_push_bank,
    input  logic [ROW_WIDTH-1:0] ar_push_row,
    input  logic [COL_WIDTH-1:0] ar_push_col,
    input  logic [IW-1:0]        ar_push_id,
    input  logic [3:0]           ar_push_qos,

    // Observability: contract counters
    output logic                 wr_done_valid,
    output logic [IW-1:0]        wr_done_id,
    output logic [31:0]          commit_count,
    output logic [31:0]          drain_count,
    output logic [31:0]          rd_issue_count,
    output logic [31:0]          cmd_count,
    // Observability: the core's output stage (generic across cores)
    output logic                 pick_valid,     // a demand winner is held in the output stage
    output logic                 cmd_valid,      // fires this cycle (with cmd_ready)
    output logic                 cmd_ready,
    output logic [4:0]           cmd_op,
    output logic [BKW-1:0]       cmd_bank,
    output logic [ROW_WIDTH-1:0] cmd_row,
    output logic [COL_WIDTH-1:0] cmd_col,
    output logic                 cmd_ap,
    output logic [PTRW-1:0]      cmd_slot,       // commit / issue slot of the output command
    // Live JEDEC gate + init-override controls (from cocotb). Real TB inputs:
    // a constant-tied core port is folded by Verilator and a cocotb deposit
    // on it is a silent no-op (pumice-100mhz ledger, 2026-10-21). The _la
    // twins mirror the live gates (BANK_LA=0 semantics).
    input  logic [NUM_BANKS-1:0] bank_act_ready,
    input  logic [NUM_BANKS-1:0] bank_rdwr_ready,
    input  logic [NUM_BANKS-1:0] bank_pre_ready,
    input  logic                 init_done,
    input  logic                 init_cmd_valid,
    input  logic [4:0]           init_cmd_op,
    input  logic [BKW-1:0]       init_cmd_bank,
    input  logic [ROW_WIDTH-1:0] init_cmd_row,
    // Command-bus pacing (from cocotb): 0 = the TB's 1-in-4 drain pace (the
    // real DFI acceptance shape), 1 = ready every cycle, 2 = never ready.
    // A real input, not a deposit on the pacing counter: a register deposit
    // is overtaken by the register's own next-state at the edge.
    input  logic [1:0]           cmd_ready_mode,
    // 1 = the lookahead twins read all-ready regardless of the live gates, so a
    // live-gate dip models "the lookahead said ready, the fire stage said not
    // yet" (a reload race) rather than an unphysical timer that re-arms. 0 =
    // twins mirror the live gates (BANK_LA=0 semantics).
    input  logic                 la_open
);

    // ------------------------------------------------------------------
    // DUT wiring: store <-> core (the contract under test)
    // ------------------------------------------------------------------
    logic                     wr_commit_valid, wr_commit_ready;
    logic                     wr_commit_ready_now;
    logic [NUM_ENTRIES-1:0] wr_fill_pending;
    logic [PTRW-1:0]          wr_commit_slot;
    logic                     rd_issue_valid, rd_issue_ready;
    logic [PTRW-1:0]          rd_issue_slot;

    logic [NUM_ENTRIES-1:0]             wr_sch_valid, rd_sch_valid, wr_sch_pend;
    logic [NUM_ENTRIES*BKW-1:0]         wr_sch_bank,  rd_sch_bank;
    logic [NUM_ENTRIES*ROW_WIDTH-1:0]   wr_sch_row,   rd_sch_row;
    logic [NUM_ENTRIES*COL_WIDTH-1:0]   wr_sch_col,   rd_sch_col;
    logic [NUM_ENTRIES*NUM_ENTRIES-1:0] wr_sch_older, rd_sch_older;
    logic [NUM_ENTRIES-1:0]             wr_age_exceed, rd_age_exceed;
    logic [NUM_ENTRIES*4-1:0]           wr_sch_qos, rd_sch_qos;
    logic [15:0]                        wr_head_rel, rd_head_rel;

    logic                cm_valid, cm_ready, cm_last;
    logic [DW-1:0]       cm_data;
    logic [SW-1:0]       cm_strb;

    logic rd_iss_valid, rd_cam_ins_ready;

    // Per-bank head records (BANK_PICK): from the records modules on the entry
    // store's vectors, or straight from the FIFO store.
    mc_head_rec_t [NUM_BANKS-1:0] w_wr_head, w_wr_head2, w_rd_head, w_rd_head2;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0] stub_row_active;

    generate if (STORE_BACKEND == 1) begin : g_fifo_store
        if (SCHED_CORE != MC_SCHED_BANK_PICK)
            $error("STORE_BACKEND=1 (mc_bank_fifo_store) pairs with SCHED_CORE=BANK_PICK only");
        mc_bank_fifo_store #(
            .NUM_ENTRIES        (NUM_ENTRIES),
            .AXI_ID_WIDTH       (IW),
            .AXI_DATA_WIDTH     (DW),
            .NUM_RANKS          (NUM_RANKS),
            .NUM_BANKS          (NUM_BANKS),
            .ROW_WIDTH          (ROW_WIDTH),
            .COL_WIDTH          (COL_WIDTH),
            .AXI_BEATS_PER_BURST(AXI_BEATS_PER_BURST),
            .RD_RET_DEPTH       (RD_RET_DEPTH)
        ) u_store (
            .aclk               (aclk),
            .aresetn            (aresetn),
            .aw_push_valid_i    (aw_push_valid),
            .aw_push_ready_o    (aw_push_ready),
            .aw_push_bank_i     (aw_push_bank),
            .aw_push_row_i      (aw_push_row),
            .aw_push_col_i      (aw_push_col),
            .aw_push_id_i       (aw_push_id),
            .aw_push_qos_i      (aw_push_qos),
            .aw_push_agg_i      (aw_push_agg),
            .aw_push_last_i     (aw_push_last),
            .wd_valid_i         (wd_valid),
            .wd_ready_o         (wd_ready),
            .wd_data_i          (wd_data),
            .wd_strb_i          (wd_strb),
            .wd_last_i          (wd_last),
            .wr_done_valid_o    (wr_done_valid),
            .wr_done_id_o       (wr_done_id),
            .snarf_probe_valid_i(1'b0),
            .snarf_probe_bank_i ('0),
            .snarf_probe_row_i  ('0),
            .snarf_probe_col_i  ('0),
            .snarf_probe_id_i   ('0),
            .snarf_probe_len_i  (8'd0),
            .snarf_hit_o        (),
            .snarf_accept_i     (1'b0),
            .snarf_rd_valid_o   (),
            .snarf_rd_ready_i   (1'b0),
            .snarf_rd_data_o    (),
            .snarf_rd_last_o    (),
            .ar_push_valid_i    (ar_push_valid),
            .ar_push_ready_o    (ar_push_ready),
            .ar_push_bank_i     (ar_push_bank),
            .ar_push_row_i      (ar_push_row),
            .ar_push_col_i      (ar_push_col),
            .ar_push_id_i       (ar_push_id),
            .ar_push_qos_i      (ar_push_qos),
            .rt_alloc_ready_i   (1'b1),
            .rt_alloc_ticket_i  ('0),
            .rd_iss_ready_i     (1'b1),
            .rd_iss_valid_o     (rd_iss_valid),
            .rd_iss_ticket_o    (),
            .rd_cam_ins_ready_o (rd_cam_ins_ready),
            .sched_age_thresh_i (8'd0),
            .wr_commit_valid_i  (wr_commit_valid),
            .wr_commit_ready_o  (wr_commit_ready),
            .wr_commit_ready_now_o  (wr_commit_ready_now),
            .wr_commit_slot_i   (wr_commit_slot),
            .rd_issue_valid_i   (rd_issue_valid),
            .rd_issue_ready_o   (rd_issue_ready),
            .rd_issue_slot_i    (rd_issue_slot),
            .bank_row_active_i  (stub_row_active[0]),
            .bank_open_row_i    ('0),
            .wr_head_o          (w_wr_head),
            .wr_head2_o         (w_wr_head2),
            .rd_head_o          (w_rd_head),
            .rd_head2_o         (w_rd_head2),
            .wr_sch_row_o       (wr_sch_row),
            .wr_sch_col_o       (wr_sch_col),
            .rd_sch_row_o       (rd_sch_row),
            .rd_sch_col_o       (rd_sch_col),
            .wr_cm_rd_valid_o   (cm_valid),
            .wr_cm_rd_ready_i   (cm_ready),
            .wr_cm_rd_data_o    (cm_data),
            .wr_cm_rd_strb_o    (cm_strb),
            .wr_cm_rd_last_o    (cm_last),
            .busy_o             (),
            // combining (MERGE_EN, default 0): decision and counters unused here
            .ar_merge_o         (),
            .wr_fill_pending_o  (wr_fill_pending),
            .ar_merge_ticket_o  (),
            .stat_wr_merge_o    (),
            .stat_rd_merge_o    ()
        );
        // the FR-FCFS vectors do not exist on this backend
        assign wr_sch_valid = '0; assign wr_sch_pend = '0; assign wr_sch_bank = '0;
        assign wr_sch_older = '0;
        assign wr_age_exceed = '0; assign wr_sch_qos = '0; assign wr_head_rel = '0;
        assign rd_sch_valid = '0; assign rd_sch_bank = '0;
        assign rd_sch_older = '0; assign rd_age_exceed = '0;
        assign rd_sch_qos = '0;   assign rd_head_rel = '0;
    end else begin : g_entry_store
    mc_xddr2_entry_store #(
        .NUM_ENTRIES        (NUM_ENTRIES),
        .AXI_ID_WIDTH       (IW),
        .AXI_DATA_WIDTH     (DW),
        .NUM_RANKS          (NUM_RANKS),
        .NUM_BANKS          (NUM_BANKS),
        .ROW_WIDTH          (ROW_WIDTH),
        .COL_WIDTH          (COL_WIDTH),
        .AXI_BEATS_PER_BURST(AXI_BEATS_PER_BURST),
        .RD_RET_DEPTH       (RD_RET_DEPTH)
    ) u_store (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .aw_push_valid_i    (aw_push_valid),
        .aw_push_ready_o    (aw_push_ready),
        .aw_push_bank_i     (aw_push_bank),
        .aw_push_row_i      (aw_push_row),
        .aw_push_col_i      (aw_push_col),
        .aw_push_id_i       (aw_push_id),
        .aw_push_qos_i      (aw_push_qos),
        .aw_push_agg_i      (aw_push_agg),
        .aw_push_last_i     (aw_push_last),
        .wd_valid_i         (wd_valid),
        .wd_ready_o         (wd_ready),
        .wd_data_i          (wd_data),
        .wd_strb_i          (wd_strb),
        .wd_last_i          (wd_last),
        .wr_done_valid_o    (wr_done_valid),
        .wr_done_id_o       (wr_done_id),
        .snarf_probe_valid_i(1'b0),
        .snarf_probe_bank_i ('0),
        .snarf_probe_row_i  ('0),
        .snarf_probe_col_i  ('0),
        .snarf_probe_id_i   ('0),
        .snarf_probe_len_i  (8'd0),
        .snarf_hit_o        (),
        .snarf_accept_i     (1'b0),
        .snarf_rd_valid_o   (),
        .snarf_rd_ready_i   (1'b0),
        .snarf_rd_data_o    (),
        .snarf_rd_last_o    (),
        .ar_push_valid_i    (ar_push_valid),
        .ar_push_ready_o    (ar_push_ready),
        .ar_push_bank_i     (ar_push_bank),
        .ar_push_row_i      (ar_push_row),
        .ar_push_col_i      (ar_push_col),
        .ar_push_id_i       (ar_push_id),
        .ar_push_qos_i      (ar_push_qos),
        .rt_alloc_ready_i   (1'b1),
        .rt_alloc_ticket_i  ('0),
        .rd_iss_ready_i     (1'b1),
        .rd_iss_valid_o     (rd_iss_valid),
        .rd_iss_ticket_o    (),
        .rd_cam_ins_ready_o (rd_cam_ins_ready),
        .sched_age_thresh_i (8'd0),
        .wr_commit_valid_i  (wr_commit_valid),
        .wr_commit_ready_o  (wr_commit_ready),
        .wr_commit_ready_now_o  (wr_commit_ready_now),
        .wr_commit_slot_i   (wr_commit_slot),
        .rd_issue_valid_i   (rd_issue_valid),
        .rd_issue_ready_o   (rd_issue_ready),
        .rd_issue_slot_i    (rd_issue_slot),
        .wr_sch_valid_o     (wr_sch_valid),
        .wr_sch_pend_o      (wr_sch_pend),
        .wr_sch_bank_o      (wr_sch_bank),
        .wr_sch_row_o       (wr_sch_row),
        .wr_sch_col_o       (wr_sch_col),
        .wr_sch_older_o     (wr_sch_older),
        .wr_sch_age_exceed_o(wr_age_exceed),
        .wr_sch_qos_o       (wr_sch_qos),
        .wr_sch_head_rel_o  (wr_head_rel),
        .rd_sch_valid_o     (rd_sch_valid),
        .rd_sch_bank_o      (rd_sch_bank),
        .rd_sch_row_o       (rd_sch_row),
        .rd_sch_col_o       (rd_sch_col),
        .rd_sch_older_o     (rd_sch_older),
        .rd_sch_age_exceed_o(rd_age_exceed),
        .rd_sch_qos_o       (rd_sch_qos),
        .rd_sch_head_rel_o  (rd_head_rel),
        .wr_cm_rd_valid_o   (cm_valid),
        .wr_cm_rd_ready_i   (cm_ready),
        .wr_cm_rd_data_o    (cm_data),
        .wr_cm_rd_strb_o    (cm_strb),
        .wr_cm_rd_last_o    (cm_last),
        .busy_o             ()
    );
    end endgenerate

    // ------------------------------------------------------------------
    // Stub bank model + cocotb-driven live gates
    // ------------------------------------------------------------------
    // Close-on-AP bank model: an AP column starts a per-bank countdown, the
    // row drops at zero, an ACT re-opens it and aborts the pending close
    // (the real mc_bank_timer's shape). Rows start open to row 0.
    logic [NUM_BANKS-1:0][3:0]           stub_ap_cnt;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0] w_act_rdy, w_rdwr_rdy, w_pre_rdy;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0] w_act_la, w_rdwr_la, w_pre_la;
    always_comb begin
        w_act_rdy  = '0; w_rdwr_rdy = '0; w_pre_rdy = '0;
        w_act_rdy [0] = bank_act_ready;
        w_rdwr_rdy[0] = bank_rdwr_ready;
        w_pre_rdy [0] = bank_pre_ready;
        w_act_la  = la_open ? '1 : w_act_rdy;
        w_rdwr_la = la_open ? '1 : w_rdwr_rdy;
        w_pre_la  = la_open ? '1 : w_pre_rdy;
    end

    logic        core_cmd_valid;
    dram_op_e    core_cmd_op;
    logic        core_cmd_ap;
    logic [BKW-1:0] core_cmd_bank;
    logic [ROW_WIDTH-1:0] core_cmd_row;
    logic [COL_WIDTH-1:0] core_cmd_col;
    logic        core_pick_valid;

    generate if (SCHED_CORE == MC_SCHED_BANK_PICK) begin : g_pick
        if (STORE_BACKEND != 1) begin : g_rec
        mc_bank_head_records #(
            .NUM_ENTRIES(NUM_ENTRIES), .NUM_BANKS(NUM_BANKS),
            .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH)
        ) u_wr_heads (
            .clk(aclk), .rst_n(aresetn),
            .bank_row_active_i(stub_row_active[0]), .bank_open_row_i('0),
            .sch_valid_i(wr_sch_valid), .sch_pend_i(wr_sch_pend),
            .sch_bank_i(wr_sch_bank), .sch_row_i(wr_sch_row), .sch_col_i(wr_sch_col),
            .sch_older_i(wr_sch_older), .sch_age_exceed_i(wr_age_exceed),
            .head_o(w_wr_head), .head2_o(w_wr_head2)
        );
        mc_bank_head_records #(
            .NUM_ENTRIES(NUM_ENTRIES), .NUM_BANKS(NUM_BANKS),
            .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH)
        ) u_rd_heads (
            .clk(aclk), .rst_n(aresetn),
            .bank_row_active_i(stub_row_active[0]), .bank_open_row_i('0),
            .sch_valid_i(rd_sch_valid), .sch_pend_i('0),
            .sch_bank_i(rd_sch_bank), .sch_row_i(rd_sch_row), .sch_col_i(rd_sch_col),
            .sch_older_i(rd_sch_older), .sch_age_exceed_i(rd_age_exceed),
            .head_o(w_rd_head), .head2_o(w_rd_head2)
        );
        end

        mc_bank_pick #(
            .NUM_RANKS  (NUM_RANKS),
            .NUM_BANKS  (NUM_BANKS),
            .ROW_WIDTH  (ROW_WIDTH),
            .COL_WIDTH  (COL_WIDTH),
            .NUM_ENTRIES(NUM_ENTRIES),
            .CLOSE_ON_DRAIN(PICK_CLOSE_ON_DRAIN),
            .LA         (0)              // the TB's la twins ARE the live gates
        ) u_pick (
            .aclk               (aclk),
            .aresetn            (aresetn),
            .page_policy_i      (PAGE_POLICY_OPEN),
            .ap_mode_en_i       (1'b0),
            .ap_close_i         ('0),
            .timeout_pre_req_i  (1'b0),
            .timeout_pre_bank_i ('0),
            .wr_head_i          (w_wr_head),
            .wr_head2_i         (w_wr_head2),
            .rd_head_i          (w_rd_head),
            .rd_head2_i         (w_rd_head2),
            .wr_slot_row_i      (wr_sch_row),
            .wr_slot_col_i      (wr_sch_col),
            .rd_slot_row_i      (rd_sch_row),
            .rd_slot_col_i      (rd_sch_col),
            .wr_commit_ready_now_i  (wr_commit_ready_now),
            .wr_fill_pending_i      (wr_fill_pending),
            .wr_commit_valid_o  (wr_commit_valid),
            .wr_commit_slot_o   (wr_commit_slot),
            .rd_issue_ready_i   (rd_issue_ready),
            .rd_issue_valid_o   (rd_issue_valid),
            .rd_issue_slot_o    (rd_issue_slot),
            .init_done_i        (init_done),
            .init_cmd_valid_i   (init_cmd_valid),
            .init_cmd_op_i      (dram_op_e'(init_cmd_op)),
            .init_cmd_bank_i    (init_cmd_bank),
            .init_cmd_row_i     (init_cmd_row),
            .refresh_req_i      (1'b0),
            .refresh_drain_i    (1'b0),
            .refresh_kind_i     (1'b0),
            .refresh_bank_i     ('0),
            .refresh_grant_o    (),
            .t_rfc_i            (16'd0),
            .t_rfc_pb_i         (8'd0),
            .rd_ret_busy_i      (1'b0),
            .zq_req_i           (1'b0),
            .zq_grant_o         (),
            .t_zqcs_i           (16'd0),
            .maint_req_i        (1'b0),
            .maint_grant_o      (),
            .maint_op_i         (dram_op_e'(0)),
            .maint_bank_i       ('0),
            .maint_row_i        ('0),
            .maint_col_i        ('0),
            .maint_extra_i      ('0),
            .maint_busy_i       (1'b0),
            .bank_act_ready_i   (w_act_rdy),
            .bank_rdwr_ready_i  (w_rdwr_rdy),
            .bank_pre_ready_i   (w_pre_rdy),
            .bank_act_ready_la_i(w_act_la),
            .bank_rdwr_ready_la_i(w_rdwr_la),
            .bank_pre_ready_la_i(w_pre_la),
            .bank_row_active_i  (stub_row_active),
            .tfaw_ok_i          ('1),
            .trrd_ok_i          ('1),
            .twtr_ok_i          (1'b1),
            .trtw_ok_i          (1'b1),
            .t_ccd_i            (8'd0),
            .t_rcd_i            (8'd0),
            .t_rp_i             (8'd0),
            .t_wr_i             (8'd0),
            .t_rtp_i            (8'd0),
            .dir_batch_max_i    (8'd0),
            .evt_act_o          (),
            .evt_rd_o           (),
            .evt_wr_o           (),
            .evt_pre_o          (),
            .evt_ap_o           (),
            .evt_rank_o         (),
            .evt_bank_o         (),
            .evt_row_o          (),
            .cmd_valid_o        (core_cmd_valid),
            .cmd_timeout_pre_o (/* page-policy classification; unused here */),
            .cmd_ready_i        (cm_ready),   // real shape: cmd bus paces with the drain
            .cmd_op_o           (core_cmd_op),
            .cmd_rank_o         (),
            .cmd_bank_o         (core_cmd_bank),
            .cmd_row_o          (core_cmd_row),
            .cmd_col_o          (core_cmd_col),
            .cmd_ap_o           (core_cmd_ap),
            .cmd_extra_o        (),
            .stall_bp_o         (),
            .stall_refresh_o    (),
            .stall_turnaround_o (),
            .stall_tccd_o       (),
            .stall_actlimit_o   (),
            .stall_banktimer_o  (),
            .stall_noreq_o      (),
            .stall_zq_o         ()
        );
        assign core_pick_valid = u_pick.w_win_vld;
        assign cmd_slot = wr_commit_valid ? wr_commit_slot
                        : rd_issue_valid  ? rd_issue_slot
                        : PTRW'(u_pick.w_sel_cand.slot);
    end else begin : g_arb
        mc_cmd_arbiter #(
            .NUM_RANKS  (NUM_RANKS),
            .NUM_BANKS  (NUM_BANKS),
            .ROW_WIDTH  (ROW_WIDTH),
            .COL_WIDTH  (COL_WIDTH),
            .AXI_ID_WIDTH(IW),
            .NUM_ENTRIES(NUM_ENTRIES)
        ) u_arb (
            .aclk               (aclk),
            .aresetn            (aresetn),
            .page_policy_i      (PAGE_POLICY_OPEN),
            .sched_order_mode_i (2'd0),
            .sched_row_sel_i    (2'd0),
            .sched_col_sel_i    (2'd0),
            .sched_access_pref_i(2'd0),
            .sched_wr_high_wm_i (8'd0),
            .sched_wr_batch_max_i(8'd0),
            .sched_wr_low_wm_i  (8'd0),
            .sched_prio_sub_i   (2'd0),
            .sched_qos_en_i     (1'b0),
            .rd_sch_qos_i       (rd_sch_qos),
            .wr_sch_qos_i       (wr_sch_qos),
            .rd_sch_age_exceed_i(rd_age_exceed),
            .wr_sch_age_exceed_i(wr_age_exceed),
            .rd_sch_head_rel_i  (rd_head_rel),
            .wr_sch_head_rel_i  (wr_head_rel),
            .ap_mode_en_i       (1'b0),
            .ap_close_i         ('0),
            .timeout_pre_req_i  (1'b0),
            .timeout_pre_bank_i ('0),
            .init_done_i        (init_done),
            .init_cmd_valid_i   (init_cmd_valid),
            .init_cmd_op_i      (dram_op_e'(init_cmd_op)),
            .init_cmd_bank_i    (init_cmd_bank),
            .init_cmd_row_i     (init_cmd_row),
            .refresh_req_i      (1'b0),
            .refresh_drain_i    (1'b0),
            .refresh_kind_i     (1'b0),
            .refresh_bank_i     ('0),
            .refresh_grant_o    (),
            .t_rfc_i            (16'd0),
            .t_rfc_pb_i         (8'd0),
            .zq_req_i           (1'b0),
            .zq_grant_o         (),
            .t_zqcs_i           (16'd0),
            .maint_req_i        (1'b0),
            .maint_grant_o      (),
            .maint_op_i         (dram_op_e'(0)),
            .maint_bank_i       ('0),
            .maint_row_i        ('0),
            .maint_col_i        ('0),
            .maint_extra_i      ('0),
            .maint_busy_i       (1'b0),
            .bank_act_ready_i   (w_act_rdy),
            .bank_rdwr_ready_i  (w_rdwr_rdy),
            .bank_pre_ready_i   (w_pre_rdy),
            .bank_act_ready_la_i(w_act_la),
            .bank_rdwr_ready_la_i(w_rdwr_la),
            .bank_pre_ready_la_i(w_pre_la),
            .bank_row_active_i  (stub_row_active),
            .bank_open_row_i    ('0),
            .tfaw_ok_i          ('1),
            .trrd_ok_i          ('1),
            .twtr_ok_i          (1'b1),
            .trtw_ok_i          (1'b1),
            .tccd_ok_i          (1'b1),
            .tccd_l_ok_i        (1'b1),
            .trrd_l_ok_i        (1'b1),
            .pick_group_o       (),
            .t_ccd_i            (8'd0),
            .wr_sch_valid_i     (wr_sch_valid),
            .wr_sch_bank_i      (wr_sch_bank),
            .wr_sch_row_i       (wr_sch_row),
            .wr_sch_col_i       (wr_sch_col),
            .wr_sch_older_i     (wr_sch_older),
            .wr_sch_pend_i      (wr_sch_pend),
            .rd_sch_pend_i      ('0),
            .drain_close_ok_i   ({NUM_BANKS{1'b1}}),   // no page-policy predictor on this port list: close-on-drain ungated
            .wr_commit_ready_i  (wr_commit_ready),
            .wr_commit_valid_o  (wr_commit_valid),
            .wr_commit_slot_o   (wr_commit_slot),
            .rd_sch_valid_i     (rd_sch_valid),
            .rd_sch_bank_i      (rd_sch_bank),
            .rd_sch_row_i       (rd_sch_row),
            .rd_sch_col_i       (rd_sch_col),
            .rd_sch_older_i     (rd_sch_older),
            .rd_issue_ready_i   (rd_issue_ready),
            .rd_issue_valid_o   (rd_issue_valid),
            .rd_issue_slot_o    (rd_issue_slot),
            .evt_act_o          (),
            .evt_rd_o           (),
            .evt_wr_o           (),
            .evt_pre_o          (),
            .evt_ap_o           (),
            .evt_rank_o         (),
            .evt_bank_o         (),
            .evt_row_o          (),
            .cmd_valid_o        (core_cmd_valid),
            .cmd_timeout_pre_o (/* page-policy classification; unused here */),
            .cmd_ready_i        (cm_ready),   // real shape: cmd bus paces with the drain
            .cmd_op_o           (core_cmd_op),
            .cmd_rank_o         (),
            .cmd_bank_o         (core_cmd_bank),
            .cmd_row_o          (core_cmd_row),
            .cmd_col_o          (core_cmd_col),
            .cmd_ap_o           (core_cmd_ap),
            .cmd_extra_o        (),
            .stall_bp_o         (),
            .stall_refresh_o    (),
            .stall_turnaround_o (),
            .stall_tccd_o       (),
            .stall_actlimit_o   (),
            .stall_banktimer_o  (),
            .stall_noreq_o      (),
            .stall_zq_o         ()
        );
        assign core_pick_valid = u_arb.r_pick_valid;
        assign cmd_slot = u_arb.r_do_wr ? u_arb.r_commit_slot : u_arb.r_issue_slot;
        wire _unused_arb = &{1'b0, wr_commit_ready_now};
    end endgenerate

    assign pick_valid = core_pick_valid;
    assign cmd_valid  = core_cmd_valid;
    assign cmd_ready  = cm_ready;
    assign cmd_op     = 5'(core_cmd_op);
    assign cmd_bank   = core_cmd_bank;
    assign cmd_row    = core_cmd_row;
    assign cmd_col    = core_cmd_col;
    assign cmd_ap     = core_cmd_ap;

    // DFI-side drain paced one beat per 4 cycles -- matching the real DFI
    // acceptance rate. At full-speed (1/cycle) a pick pipeline never empties
    // between commits and the stale-pointer condition never co-occurs; the
    // full-harness hang needed the real (slow) command pacing.
    logic [1:0] r_cm_gate;
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) r_cm_gate <= '0;
        else                        r_cm_gate <= r_cm_gate + 1'b1;
    end)
    assign cm_ready = (cmd_ready_mode == 2'd1) ? 1'b1
                    : (cmd_ready_mode == 2'd2) ? 1'b0
                    : (r_cm_gate == 2'd0);

    // Close-on-AP bank model (see above).
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            stub_row_active <= '1;   // every row starts open
            stub_ap_cnt     <= '0;
        end else begin
            for (int b = 0; b < NUM_BANKS; b++) begin
                if (core_cmd_valid && cm_ready && (core_cmd_op == OP_ACT) && (core_cmd_bank == BKW'(b))) begin
                    stub_row_active[0][b] <= 1'b1;
                    stub_ap_cnt[b]        <= '0;
                end else if (core_cmd_valid && cm_ready && core_cmd_ap && (core_cmd_bank == BKW'(b))) begin
                    stub_ap_cnt[b] <= 4'd6;
                end else if (stub_ap_cnt[b] != 4'd0) begin
                    stub_ap_cnt[b] <= stub_ap_cnt[b] - 4'd1;
                    if (stub_ap_cnt[b] == 4'd1)
                        stub_row_active[0][b] <= 1'b0;
                end
            end
        end
    end)

    // ------------------------------------------------------------------
    // Contract counters (checked by the cocotb test)
    // ------------------------------------------------------------------
    logic [31:0] r_commit_count, r_drain_count, r_rd_issue_count, r_cmd_count;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_commit_count  <= '0;
            r_drain_count   <= '0;
            r_rd_issue_count<= '0;
            r_cmd_count     <= '0;
        end else begin
            if (wr_commit_valid && wr_commit_ready) r_commit_count <= r_commit_count + 1;
            if (cm_valid && cm_ready)               r_drain_count  <= r_drain_count + 1;
            if (rd_iss_valid)                       r_rd_issue_count <= r_rd_issue_count + 1;
            if (core_cmd_valid && cm_ready)         r_cmd_count <= r_cmd_count + 1;
        end
    end)

    assign commit_count   = r_commit_count;
    assign drain_count    = r_drain_count;
    assign rd_issue_count = r_rd_issue_count;
    assign cmd_count      = r_cmd_count;

    wire _unused_tb = &{1'b0, cm_data, cm_strb, cm_last, rd_cam_ins_ready, wr_commit_ready};

endmodule : mc_store_arbiter_macro_tb_top
