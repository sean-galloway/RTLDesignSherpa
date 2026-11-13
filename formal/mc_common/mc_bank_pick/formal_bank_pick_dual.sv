// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// mc_bank_pick DUAL_ISSUE row lane (memory-controllers MC-014): the word
// invariants the plane and the DFI command path rely on, on free inputs --
// the head records, the timers' readiness bits, the refresh / init /
// maintenance requests and the sink readiness are all unconstrained, so these
// hold for whatever the environment presents.
//
//   * one row command per word: the lane fires an ACT or a PRE, never both,
//     and only beside a main-lane COLUMN or an idle main lane -- never beside
//     a main ACT / PRE / REF / MRS / ZQ / init command or the timeout PRE;
//   * the two lanes never touch one bank in one word;
//   * the lane re-checks the live gate: an ACT only into a closed, act-ready
//     bank with tRRD / tFAW open; a PRE only on an open, pre-ready bank; and
//     only into a free slot (cmd_ready_i), with the runtime enable high.
//
// YOSYS-COMPATIBLE FORM: the DUT pre-flattened by sv2v (mc_head_rec_t as a
// 45-bit vector per bank, dram_op_e as [4:0]); immediate assertions.
`timescale 1ns / 1ps
module formal_bank_pick_dual #(
    parameter int NUM_BANKS   = 8,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int NUM_ENTRIES = 8,
    parameter int LA          = 2
) (
    input logic clk,
    input logic rst_n
);
    localparam int RKW  = 1;
    localparam int BKW  = $clog2(NUM_BANKS);
    localparam int PTRW = $clog2(NUM_ENTRIES);
    localparam int RECW = 45;
    localparam int MEW  = 1;
    // dram_op_e encodings (mc_common_pkg)
    localparam [4:0] OP_RD = 5'h02, OP_RDA = 5'h03, OP_WR = 5'h04, OP_WRA = 5'h05;

    (* anyseq *) reg [1:0]                 page_policy;
    (* anyseq *) reg                       dual_issue_en;
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

    wire                 cmd_valid, cmd_timeout_pre, cmd_ap;
    wire [4:0]           cmd_op;
    wire [RKW-1:0]       cmd_rank;
    wire [BKW-1:0]       cmd_bank, row2_bank;
    wire [ROW_WIDTH-1:0] cmd_row, row2_row;
    wire [COL_WIDTH-1:0] cmd_col;
    wire [MEW-1:0]       cmd_extra;
    wire                 row2_act, row2_pre;
    wire                 evt_act, evt_rd, evt_wr, evt_pre, evt_ap;
    wire [RKW-1:0]       evt_rank;
    wire [BKW-1:0]       evt_bank;
    wire [ROW_WIDTH-1:0] evt_row;

    mc_bank_pick #(.NUM_RANKS(1), .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH),
                   .NUM_ENTRIES(NUM_ENTRIES), .LA(LA), .DUAL_ISSUE(1'b1)) dut (
        .aclk(clk), .aresetn(rst_n), .page_policy_i(page_policy), .dual_issue_en_i(dual_issue_en),
        .ap_mode_en_i(ap_mode_en), .ap_close_i(ap_close), .ap_conflict_only_i(ap_conflict_only),
        .drain_close_ok_i(drain_close_ok), .timeout_pre_req_i(timeout_pre_req), .timeout_pre_bank_i(timeout_pre_bank),
        .wr_head_i(wr_head), .wr_head2_i(wr_head2), .rd_head_i(rd_head), .rd_head2_i(rd_head2),
        .wr_slot_row_i(wr_slot_row), .wr_slot_col_i(wr_slot_col), .rd_slot_row_i(rd_slot_row), .rd_slot_col_i(rd_slot_col),
        .wr_commit_ready_now_i(wr_commit_ready_now), .wr_commit_valid_o(), .wr_commit_slot_o(),
        .rd_issue_ready_i(rd_issue_ready), .rd_issue_valid_o(), .rd_issue_slot_o(),
        .wr_commit_cand_o(), .rd_issue_cand_o(), .cand_bank_o(), .cand_second_o(),
        .init_done_i(init_done), .init_cmd_valid_i(init_cmd_valid), .init_cmd_op_i(init_cmd_op),
        .init_cmd_bank_i(init_cmd_bank), .init_cmd_row_i(init_cmd_row),
        .refresh_req_i(refresh_req), .refresh_drain_i(refresh_drain), .refresh_kind_i(refresh_kind), .refresh_bank_i(refresh_bank),
        .refresh_grant_o(), .t_rfc_i(t_rfc), .t_rfc_pb_i(t_rfc_pb), .rd_ret_busy_i(rd_ret_busy),
        .zq_req_i(zq_req), .zq_grant_o(), .t_zqcs_i(t_zqcs),
        .maint_req_i(maint_req), .maint_grant_o(), .maint_op_i(maint_op), .maint_bank_i(maint_bank), .maint_row_i(maint_row),
        .maint_col_i(maint_col), .maint_extra_i(maint_extra), .maint_busy_i(maint_busy),
        .bank_act_ready_i(act_rdy), .bank_rdwr_ready_i(rdwr_rdy), .bank_pre_ready_i(pre_rdy),
        .bank_act_ready_la_i(act_la), .bank_rdwr_ready_la_i(rdwr_la), .bank_pre_ready_la_i(pre_la), .bank_row_active_i(row_active),
        .tfaw_ok_i(tfaw_ok), .trrd_ok_i(trrd_ok), .twtr_ok_i(twtr_ok), .trtw_ok_i(trtw_ok),
        .t_ccd_i(t_ccd), .t_rcd_i(t_rcd), .t_rp_i(t_rp), .t_wr_i(t_wr), .t_rtp_i(t_rtp), .dir_batch_max_i(dir_batch_max),
        .evt_act_o(evt_act), .evt_rd_o(evt_rd), .evt_wr_o(evt_wr), .evt_pre_o(evt_pre), .evt_ap_o(evt_ap),
        .evt_rank_o(evt_rank), .evt_bank_o(evt_bank), .evt_row_o(evt_row),
        .cmd_valid_o(cmd_valid), .cmd_timeout_pre_o(cmd_timeout_pre), .cmd_ready_i(cmd_ready), .cmd_op_o(cmd_op),
        .cmd_rank_o(cmd_rank), .cmd_bank_o(cmd_bank), .cmd_row_o(cmd_row), .cmd_col_o(cmd_col), .cmd_ap_o(cmd_ap), .cmd_extra_o(cmd_extra),
        .row2_act_o(row2_act), .row2_pre_o(row2_pre), .row2_bank_o(row2_bank), .row2_row_o(row2_row),
        .stall_bp_o(), .stall_refresh_o(), .stall_turnaround_o(), .stall_tccd_o(),
        .stall_actlimit_o(), .stall_banktimer_o(), .stall_noreq_o(), .stall_zq_o(),
        .dbg_dir_flip_o(), .dbg_dir_o(), .dbg_dir_cause_o(), .dbg_dir_batch_o()
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    wire lane_fire = row2_act || row2_pre;
    wire main_col  = cmd_valid && ((cmd_op == OP_RD) || (cmd_op == OP_RDA) || (cmd_op == OP_WR) || (cmd_op == OP_WRA));

    always @(posedge clk) if (rst_n) begin
        a_one_row:      assert (!(row2_act && row2_pre));
        a_enable:       assert (!lane_fire || dual_issue_en);
        a_slot:         assert (!lane_fire || cmd_ready);
        // beside a main-lane COLUMN only -- never alone (the 2026-11-12 cut:
        // the lane stays off the plane's command-valid cone), never beside a
        // main-lane row / override command (every non-column op is one),
        // never the timeout PRE
        a_beside_col:   assert (!lane_fire || main_col);
        a_no_main_act:  assert (!row2_act || !evt_act);
        a_no_main_pre:  assert (!lane_fire || !evt_pre);
        a_no_to_pre:    assert (!lane_fire || !cmd_timeout_pre);
        a_other_bank:   assert (!lane_fire || (row2_bank != cmd_bank));
        // the live gate, re-checked at the fire
        a_act_gate:     assert (!row2_act || (!row_active[row2_bank] && act_rdy[row2_bank] && tfaw_ok && trrd_ok));
        a_pre_gate:     assert (!row2_pre || (row_active[row2_bank] && pre_rdy[row2_bank]));
        // the main lane's own column / row rules are untouched by the lane
        a_main_act_gate: assert (!evt_act || (act_rdy[evt_bank] && tfaw_ok && trrd_ok));
    end

    // the lane does fire, both classes, beside a read and beside a write
    always @(posedge clk) if (rst_n) begin
        c_act_beside_col: cover (row2_act && main_col);
        c_pre_beside_col: cover (row2_pre && main_col);
        c_act_beside_rd:  cover (row2_act && cmd_valid && ((cmd_op == OP_RD) || (cmd_op == OP_RDA)));
        c_act_beside_wr:  cover (row2_act && cmd_valid && ((cmd_op == OP_WR) || (cmd_op == OP_WRA)));
    end
endmodule
