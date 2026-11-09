// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Equivalence harness: mc_bank_pick with the resolved effective-winner and
// stale-mask registers (memory-controllers MC-011, 2026-11-08) against the
// golden copy of the mux-resolved form (three register sets and a hold bit,
// resolved by a 2:1 mux in front of the fire stage). Same free inputs to both,
// every output compared every cycle after reset. The change is a retiming of
// the resolve mux across the register boundary -- the register holds what the
// mux produced -- so the two must agree with no exception: one differing cycle
// is a behaviour change, not noise.
//
// The inputs are free (anyseq), INCLUDING the head records, the timers'
// readiness bits and the sink readiness, and nothing assumes the storage
// plane's record contract or the timers' JEDEC behaviour: equivalence must
// hold for whatever the environment presents, which is stronger than the
// system can produce. The CSR-programmed timings are free per cycle as well
// (no term of the change spans a cycle on them).
//
// YOSYS-COMPATIBLE FORM: both DUTs pre-flattened by sv2v (the mc_head_rec_t
// records arrive as NUM_BANKS x 45-bit vectors, dram_op_e as [4:0],
// page_policy_e as [1:0]); immediate assertions.
`timescale 1ns / 1ps
module formal_bank_pick_equiv #(
    parameter int NUM_BANKS   = 8,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int NUM_ENTRIES = 8,
    parameter int LA          = 2,
    parameter bit DIR_OWNS_ROWS = 1'b1,
    parameter int DIR_HOLD_IDLE = 8
) (
    input logic clk,
    input logic rst_n
);
    localparam int NUM_RANKS = 1;
    localparam int RKW  = 1;
    localparam int BKW  = $clog2(NUM_BANKS);
    localparam int PTRW = $clog2(NUM_ENTRIES);
    localparam int RECW = 45;              // mc_head_rec_t, packed
    localparam int MEW  = 1;

    // ---- free inputs --------------------------------------------------------
    (* anyseq *) reg [1:0]                 page_policy;
    (* anyseq *) reg                       ap_mode_en, ap_conflict_only, timeout_pre_req;
    (* anyseq *) reg [NUM_BANKS-1:0]       ap_close, drain_close_ok;
    (* anyseq *) reg [BKW-1:0]             timeout_pre_bank;
    (* anyseq *) reg [NUM_BANKS*RECW-1:0]  wr_head, wr_head2, rd_head, rd_head2;
    (* anyseq *) reg [NUM_ENTRIES*ROW_WIDTH-1:0] wr_slot_row, rd_slot_row;
    (* anyseq *) reg [NUM_ENTRIES*COL_WIDTH-1:0] wr_slot_col, rd_slot_col;
    (* anyseq *) reg                       wr_commit_ready_now, rd_issue_ready;
    (* anyseq *) reg                       init_done, init_cmd_valid;
    (* anyseq *) reg [4:0]                 init_cmd_op, maint_op;
    (* anyseq *) reg [BKW-1:0]             init_cmd_bank, refresh_bank, maint_bank;
    (* anyseq *) reg [ROW_WIDTH-1:0]       init_cmd_row, maint_row;
    (* anyseq *) reg [COL_WIDTH-1:0]       maint_col;
    (* anyseq *) reg                       refresh_req, refresh_drain, refresh_kind, rd_ret_busy;
    (* anyseq *) reg [15:0]                t_rfc, t_zqcs;
    (* anyseq *) reg [7:0]                 t_rfc_pb, t_ccd, t_rcd, t_rp, t_wr, t_rtp, dir_batch_max;
    (* anyseq *) reg                       zq_req, maint_req, maint_busy;
    (* anyseq *) reg [MEW-1:0]             maint_extra;
    (* anyseq *) reg [NUM_BANKS-1:0]       act_rdy, rdwr_rdy, pre_rdy, act_la, rdwr_la, pre_la, row_active;
    (* anyseq *) reg                       tfaw_ok, trrd_ok, twtr_ok, trtw_ok, cmd_ready;

    // ---- outputs, new (n_) and golden (g_), as one bus each ----------------
    localparam int OW = 1 + PTRW + 1 + PTRW + 1 + 1 + BKW + 1      // commit / issue / cand
                      + 3                                           // refresh / zq / maint grants
                      + 5 + RKW + BKW + ROW_WIDTH                   // evt_*
                      + 2 + 5 + RKW + BKW + ROW_WIDTH + COL_WIDTH + 1 + MEW   // cmd_*
                      + 8*32                                         // stall_*
                      + 1 + 1 + 2 + 8;                              // dbg_*
    wire [OW-1:0] n_all, g_all;

`define PICK_PORTS(P) \
        .aclk(clk), .aresetn(rst_n), .page_policy_i(page_policy), \
        .ap_mode_en_i(ap_mode_en), .ap_close_i(ap_close), .ap_conflict_only_i(ap_conflict_only), \
        .drain_close_ok_i(drain_close_ok), .timeout_pre_req_i(timeout_pre_req), .timeout_pre_bank_i(timeout_pre_bank), \
        .wr_head_i(wr_head), .wr_head2_i(wr_head2), .rd_head_i(rd_head), .rd_head2_i(rd_head2), \
        .wr_slot_row_i(wr_slot_row), .wr_slot_col_i(wr_slot_col), .rd_slot_row_i(rd_slot_row), .rd_slot_col_i(rd_slot_col), \
        .wr_commit_ready_now_i(wr_commit_ready_now), .wr_commit_valid_o(P``wr_commit_valid), .wr_commit_slot_o(P``wr_commit_slot), \
        .rd_issue_ready_i(rd_issue_ready), .rd_issue_valid_o(P``rd_issue_valid), .rd_issue_slot_o(P``rd_issue_slot), \
        .wr_commit_cand_o(P``wr_commit_cand), .rd_issue_cand_o(P``rd_issue_cand), .cand_bank_o(P``cand_bank), .cand_second_o(P``cand_second), \
        .init_done_i(init_done), .init_cmd_valid_i(init_cmd_valid), .init_cmd_op_i(init_cmd_op), .init_cmd_bank_i(init_cmd_bank), .init_cmd_row_i(init_cmd_row), \
        .refresh_req_i(refresh_req), .refresh_drain_i(refresh_drain), .refresh_kind_i(refresh_kind), .refresh_bank_i(refresh_bank), \
        .refresh_grant_o(P``refresh_grant), .t_rfc_i(t_rfc), .t_rfc_pb_i(t_rfc_pb), .rd_ret_busy_i(rd_ret_busy), \
        .zq_req_i(zq_req), .zq_grant_o(P``zq_grant), .t_zqcs_i(t_zqcs), \
        .maint_req_i(maint_req), .maint_grant_o(P``maint_grant), .maint_op_i(maint_op), .maint_bank_i(maint_bank), .maint_row_i(maint_row), \
        .maint_col_i(maint_col), .maint_extra_i(maint_extra), .maint_busy_i(maint_busy), \
        .bank_act_ready_i(act_rdy), .bank_rdwr_ready_i(rdwr_rdy), .bank_pre_ready_i(pre_rdy), \
        .bank_act_ready_la_i(act_la), .bank_rdwr_ready_la_i(rdwr_la), .bank_pre_ready_la_i(pre_la), .bank_row_active_i(row_active), \
        .tfaw_ok_i(tfaw_ok), .trrd_ok_i(trrd_ok), .twtr_ok_i(twtr_ok), .trtw_ok_i(trtw_ok), \
        .t_ccd_i(t_ccd), .t_rcd_i(t_rcd), .t_rp_i(t_rp), .t_wr_i(t_wr), .t_rtp_i(t_rtp), .dir_batch_max_i(dir_batch_max), \
        .evt_act_o(P``evt_act), .evt_rd_o(P``evt_rd), .evt_wr_o(P``evt_wr), .evt_pre_o(P``evt_pre), .evt_ap_o(P``evt_ap), \
        .evt_rank_o(P``evt_rank), .evt_bank_o(P``evt_bank), .evt_row_o(P``evt_row), \
        .cmd_valid_o(P``cmd_valid), .cmd_timeout_pre_o(P``cmd_timeout_pre), .cmd_ready_i(cmd_ready), .cmd_op_o(P``cmd_op), \
        .cmd_rank_o(P``cmd_rank), .cmd_bank_o(P``cmd_bank), .cmd_row_o(P``cmd_row), .cmd_col_o(P``cmd_col), .cmd_ap_o(P``cmd_ap), .cmd_extra_o(P``cmd_extra), \
        .stall_bp_o(P``stall_bp), .stall_refresh_o(P``stall_refresh), .stall_turnaround_o(P``stall_turnaround), .stall_tccd_o(P``stall_tccd), \
        .stall_actlimit_o(P``stall_actlimit), .stall_banktimer_o(P``stall_banktimer), .stall_noreq_o(P``stall_noreq), .stall_zq_o(P``stall_zq), \
        .dbg_dir_flip_o(P``dbg_dir_flip), .dbg_dir_o(P``dbg_dir), .dbg_dir_cause_o(P``dbg_dir_cause), .dbg_dir_batch_o(P``dbg_dir_batch)

    // the two instances' outputs, one set per prefix (n_ = new, g_ = golden)

    wire n_wr_commit_valid, n_rd_issue_valid, n_wr_commit_cand, n_rd_issue_cand, n_cand_second;
    wire [PTRW-1:0] n_wr_commit_slot, n_rd_issue_slot;
    wire [BKW-1:0] n_cand_bank, n_evt_bank, n_cmd_bank;
    wire n_refresh_grant, n_zq_grant, n_maint_grant;
    wire n_evt_act, n_evt_rd, n_evt_wr, n_evt_pre, n_evt_ap;
    wire [RKW-1:0] n_evt_rank, n_cmd_rank;
    wire [ROW_WIDTH-1:0] n_evt_row, n_cmd_row;
    wire [COL_WIDTH-1:0] n_cmd_col;
    wire n_cmd_valid, n_cmd_timeout_pre, n_cmd_ap;
    wire [4:0] n_cmd_op;
    wire [MEW-1:0] n_cmd_extra;
    wire [31:0] n_stall_bp, n_stall_refresh, n_stall_turnaround, n_stall_tccd, n_stall_actlimit, n_stall_banktimer, n_stall_noreq, n_stall_zq;
    wire n_dbg_dir_flip, n_dbg_dir;
    wire [1:0] n_dbg_dir_cause;
    wire [7:0] n_dbg_dir_batch;
    assign n_all = {n_wr_commit_valid, n_wr_commit_slot, n_rd_issue_valid, n_rd_issue_slot, n_wr_commit_cand, n_rd_issue_cand, n_cand_bank, n_cand_second,
                     n_refresh_grant, n_zq_grant, n_maint_grant,
                     n_evt_act, n_evt_rd, n_evt_wr, n_evt_pre, n_evt_ap, n_evt_rank, n_evt_bank, n_evt_row,
                     n_cmd_valid, n_cmd_timeout_pre, n_cmd_op, n_cmd_rank, n_cmd_bank, n_cmd_row, n_cmd_col, n_cmd_ap, n_cmd_extra,
                     n_stall_bp, n_stall_refresh, n_stall_turnaround, n_stall_tccd, n_stall_actlimit, n_stall_banktimer, n_stall_noreq, n_stall_zq,
                     n_dbg_dir_flip, n_dbg_dir, n_dbg_dir_cause, n_dbg_dir_batch};
    wire g_wr_commit_valid, g_rd_issue_valid, g_wr_commit_cand, g_rd_issue_cand, g_cand_second;
    wire [PTRW-1:0] g_wr_commit_slot, g_rd_issue_slot;
    wire [BKW-1:0] g_cand_bank, g_evt_bank, g_cmd_bank;
    wire g_refresh_grant, g_zq_grant, g_maint_grant;
    wire g_evt_act, g_evt_rd, g_evt_wr, g_evt_pre, g_evt_ap;
    wire [RKW-1:0] g_evt_rank, g_cmd_rank;
    wire [ROW_WIDTH-1:0] g_evt_row, g_cmd_row;
    wire [COL_WIDTH-1:0] g_cmd_col;
    wire g_cmd_valid, g_cmd_timeout_pre, g_cmd_ap;
    wire [4:0] g_cmd_op;
    wire [MEW-1:0] g_cmd_extra;
    wire [31:0] g_stall_bp, g_stall_refresh, g_stall_turnaround, g_stall_tccd, g_stall_actlimit, g_stall_banktimer, g_stall_noreq, g_stall_zq;
    wire g_dbg_dir_flip, g_dbg_dir;
    wire [1:0] g_dbg_dir_cause;
    wire [7:0] g_dbg_dir_batch;
    assign g_all = {g_wr_commit_valid, g_wr_commit_slot, g_rd_issue_valid, g_rd_issue_slot, g_wr_commit_cand, g_rd_issue_cand, g_cand_bank, g_cand_second,
                     g_refresh_grant, g_zq_grant, g_maint_grant,
                     g_evt_act, g_evt_rd, g_evt_wr, g_evt_pre, g_evt_ap, g_evt_rank, g_evt_bank, g_evt_row,
                     g_cmd_valid, g_cmd_timeout_pre, g_cmd_op, g_cmd_rank, g_cmd_bank, g_cmd_row, g_cmd_col, g_cmd_ap, g_cmd_extra,
                     g_stall_bp, g_stall_refresh, g_stall_turnaround, g_stall_tccd, g_stall_actlimit, g_stall_banktimer, g_stall_noreq, g_stall_zq,
                     g_dbg_dir_flip, g_dbg_dir, g_dbg_dir_cause, g_dbg_dir_batch};

    mc_bank_pick #(.NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH),
                   .NUM_ENTRIES(NUM_ENTRIES), .LA(LA), .DIR_OWNS_ROWS(DIR_OWNS_ROWS), .DIR_HOLD_IDLE(DIR_HOLD_IDLE)) dut_new (
        `PICK_PORTS(n_)
    );
    mc_bank_pick_gold #(.NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH),
                        .NUM_ENTRIES(NUM_ENTRIES), .LA(LA), .DIR_OWNS_ROWS(DIR_OWNS_ROWS), .DIR_HOLD_IDLE(DIR_HOLD_IDLE)) dut_gold (
        `PICK_PORTS(g_)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // the command and its strobes by name (readable counterexamples), then
    // everything
    always @(posedge clk) if (rst_n) begin
        a_cmd_valid:  assert (n_cmd_valid  == g_cmd_valid);
        a_cmd_op:     assert (n_cmd_op     == g_cmd_op);
        a_cmd_bank:   assert (n_cmd_bank   == g_cmd_bank);
        a_cmd_row:    assert (n_cmd_row    == g_cmd_row);
        a_cmd_col:    assert (n_cmd_col    == g_cmd_col);
        a_cmd_ap:     assert (n_cmd_ap     == g_cmd_ap);
        a_wr_commit:  assert ({n_wr_commit_valid, n_wr_commit_slot} == {g_wr_commit_valid, g_wr_commit_slot});
        a_rd_issue:   assert ({n_rd_issue_valid, n_rd_issue_slot}   == {g_rd_issue_valid, g_rd_issue_slot});
        a_cand:       assert ({n_wr_commit_cand, n_rd_issue_cand, n_cand_bank, n_cand_second}
                              == {g_wr_commit_cand, g_rd_issue_cand, g_cand_bank, g_cand_second});
        a_evt:        assert ({n_evt_act, n_evt_rd, n_evt_wr, n_evt_pre, n_evt_ap, n_evt_bank, n_evt_row}
                              == {g_evt_act, g_evt_rd, g_evt_wr, g_evt_pre, g_evt_ap, g_evt_bank, g_evt_row});
        a_all:        assert (n_all == g_all);
    end
    // not vacuous: demand commands of every class fire, a column from the
    // second record (the pop shadow) and the background timeout close
    always @(posedge clk) if (rst_n) begin
        c_act:  cover (g_cmd_valid && g_cmd_op == 5'h01 && !g_cmd_timeout_pre && g_evt_act);
        c_rd:   cover (g_cmd_valid && g_cmd_op == 5'h02 && g_rd_issue_valid);
        c_wr:   cover (g_cmd_valid && g_cmd_op == 5'h04 && g_wr_commit_valid);
        c_pre:  cover (g_cmd_valid && g_cmd_op == 5'h06 && !g_cmd_timeout_pre && g_evt_pre);
        c_rd2:  cover (g_rd_issue_valid && g_cand_second);
        c_to:   cover (g_cmd_valid && g_cmd_timeout_pre);
        c_rda:  cover (g_cmd_valid && g_cmd_op == 5'h03);
    end
endmodule
