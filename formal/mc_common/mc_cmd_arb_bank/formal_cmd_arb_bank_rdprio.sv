// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// mc_cmd_arb_bank read-priority direction register (memory-controllers MC-024),
// HAS_RD_PRIO = 1 with the mode ON (rd_prio_en_i = 1) and the two knobs
// constant per run (static CSRs, anyconst), on free inputs -- the head
// records, the timers' readiness bits, refresh / init / maintenance and the
// sinks are unconstrained, as in the dual harness. The granite shape:
// DIR_OWNS_ROWS 1, DIR_HOLD_IDLE 8, the row lane built.
//
// Ports only (the core is flattened; nothing inside is visible), so the
// harness keeps its own copy of the starvation counter from the ports -- the
// write heads' vld bits and the write-column strobe evt_wr -- and the
// register's state from the debug outputs (dbg_dir_o = r_dir, the flip, its
// cause and the batch that ended). Both start at reset, so a bounded check
// from reset keeps them in step; the knobs are bounded small so the depth
// reaches every state of the counter's compare.
//
//   a_starve       a starved write head (the reference flag) with the bus on
//                  the reads and no write column this cycle turns the bus to
//                  the writes next cycle -- the starvation flip has priority
//                  over the drain and the cap;
//   a_cause3       a flip recorded as starvation (cause 3) had the reference
//                  flag set: the flip never comes from anything else;
//   a_no_read_cap  the bus never leaves the reads on the batch cap (cause 2):
//                  a read hold has no cap in this mode;
//   a_wr_cap_min   a write hold that ends on the cap ran at least wr_burst
//                  columns.
// Covers make each one non-vacuous: a starvation flip, a write cap flip at
// exactly wr_burst, a drain flip from the reads.
//
// YOSYS-COMPATIBLE FORM: the DUT pre-flattened by sv2v; immediate assertions.
`timescale 1ns / 1ps
module formal_cmd_arb_bank_rdprio #(
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

    // the two knobs: constant per run, small enough for the depth
    (* anyconst *) reg [11:0] wr_starve;
    (* anyconst *) reg [7:0]  wr_burst;
    always @(*) begin
        assume (wr_starve >= 12'd1 && wr_starve <= 12'd4);
        assume (wr_burst  >= 8'd1  && wr_burst  <= 8'd3);
    end

    wire       dir_flip, dir;
    wire [1:0] dir_cause;
    wire [7:0] dir_batch;

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

    mc_cmd_arb_bank #(.NUM_RANKS(1), .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH),
                   .NUM_ENTRIES(NUM_ENTRIES), .LA(LA), .DIR_OWNS_ROWS(1'b1), .DIR_HOLD_IDLE(8),
                   .HAS_RD_PRIO(1'b1), .DUAL_ISSUE(1'b1)) dut (
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
        .rd_prio_en_i(1'b1), .wr_starve_i(wr_starve), .wr_burst_i(wr_burst),
        .evt_act_o(evt_act), .evt_rd_o(evt_rd), .evt_wr_o(evt_wr), .evt_pre_o(evt_pre), .evt_ap_o(evt_ap),
        .evt_rank_o(evt_rank), .evt_bank_o(evt_bank), .evt_row_o(evt_row),
        .cmd_valid_o(cmd_valid), .cmd_timeout_pre_o(cmd_timeout_pre), .cmd_ready_i(cmd_ready), .cmd_op_o(cmd_op),
        .cmd_rank_o(cmd_rank), .cmd_bank_o(cmd_bank), .cmd_row_o(cmd_row), .cmd_col_o(cmd_col), .cmd_ap_o(cmd_ap), .cmd_extra_o(cmd_extra),
        .row2_act_o(row2_act), .row2_pre_o(row2_pre), .row2_bank_o(row2_bank), .row2_row_o(row2_row),
        .stall_bp_o(), .stall_refresh_o(), .stall_turnaround_o(), .stall_tccd_o(),
        .stall_actlimit_o(), .stall_banktimer_o(), .stall_noreq_o(), .stall_zq_o(),
        .dbg_dir_flip_o(dir_flip), .dbg_dir_o(dir), .dbg_dir_cause_o(dir_cause), .dbg_dir_batch_o(dir_batch)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    // ---- reference starvation counter, from the ports ----------------------
    reg f_wr_queued;
    integer b;
    always @(*) begin
        f_wr_queued = 1'b0;
        for (b = 0; b < NUM_BANKS; b = b + 1)
            if (wr_head[b*RECW + RECW-1]) f_wr_queued = 1'b1;     // mc_head_rec_t.vld, the MSB
    end
    reg [11:0] f_wait;
    reg        f_starved, f_starved_q;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_wait <= 12'd0; f_starved <= 1'b0; f_starved_q <= 1'b0;
        end else begin
            f_starved   <= (f_wait >= wr_starve);
            f_starved_q <= f_starved;
            if (evt_wr)                  f_wait <= 12'd0;
            else if (!f_wr_queued)       f_wait <= 12'd0;
            else if (f_wait != 12'hFFF)  f_wait <= f_wait + 12'd1;
        end
    end
    // last cycle's view, for the one-step properties
    reg f_dir_q, f_evt_wr_q, f_rst_q;
    always @(posedge clk) begin
        f_dir_q    <= dir;
        f_evt_wr_q <= evt_wr;
        f_rst_q    <= rst_n;
    end

    always @(posedge clk) if (rst_n && f_rst_q) begin
        a_starve:      assert (!(f_starved_q && !f_dir_q && !f_evt_wr_q) || dir);
        a_cause3:      assert (!(dir_flip && dir_cause == 2'd3) || f_starved_q);
        a_no_read_cap: assert (!(dir_flip && dir && dir_cause == 2'd2));
        a_wr_cap_min:  assert (!(dir_flip && !dir && dir_cause == 2'd2) || (dir_batch >= wr_burst));
    end
    always @(posedge clk) if (rst_n && f_rst_q) begin
        c_starve:   cover (dir_flip && dir && dir_cause == 2'd3);
        c_wr_cap:   cover (dir_flip && !dir && dir_cause == 2'd2 && dir_batch == wr_burst);
        c_rd_drain: cover (dir_flip && dir && dir_cause == 2'd1);
    end
endmodule
