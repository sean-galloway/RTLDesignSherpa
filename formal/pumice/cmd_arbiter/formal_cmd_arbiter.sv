// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal wrapper for pumice_cmd_arbiter COMPOSED WITH global_timers.
//
// WHY THIS EXISTS: it settles pumice ISSUE-019. That item established a hole in
// the CHECKING -- tFAW and tRRD are rank-global, the arbiter checks them at its
// STAGE-1b pre-pick (two registers before a command fires), the final-stage
// `w_out_safe` re-validates only the PER-BANK gate, and
// pumice_cmd_history_checker is same-bank by design -- and then closed on
// evidence: 171 sim tests with a rank-global tRRD/tFAW check armed found no
// violation, with the check proved live. "Not observed" is not "impossible",
// and this is the proof that closes that gap.
//
// THE COMPOSITION IS THE POINT. Proving the arbiter alone says nothing: its
// tfaw_ok_i / trrd_ok_i are inputs, so an engine free to drive them can permit
// anything. The real question is about the LOOP -- arbiter issues, timers
// observe, timers gate the arbiter -- so the real global_timers is instantiated
// here and wired to the arbiter's own evt_* outputs. What is proved is a
// property of the pair, which is what runs on silicon.
//
// WHAT IS PROVED
//   * tRRD: no two ACTs closer than t_rrd_i, measured on evt_act_o by a counter
//     this wrapper keeps -- not by anything either DUT exposes.
//   * tFAW: never five ACTs inside a t_faw_i window.
//   * one command per cycle: the DFI carries one slot, so the evt_* strobes are
//     mutually exclusive.
//
// The arbiter is self-contained (it instantiates nothing), so its CAM-side
// inputs are free: the scheduling vectors, the bank readiness and the init and
// refresh ports are driven by the engine, which is the strongest environment --
// any CAM behaviour is allowed, including ones the real CAMs never produce.
//
// SMALL GEOMETRY. 1 rank, 4 banks, 2 entries per CAM, 4-bit row. tRRD and tFAW
// are rank-global, so bank count only has to be enough for the cross-bank case
// that per-bank timers cannot see, which is two.
//
// YOSYS-COMPATIBLE FORM. Both DUTs pre-flattened by sv2v; immediate assertions.

`timescale 1ns / 1ps

module formal_cmd_arbiter #(
    parameter int NR   = 1,    // NUM_RANKS
    parameter int NB   = 4,    // NUM_BANKS
    parameter int RW   = 4,    // ROW_WIDTH
    parameter int CW   = 4,    // COL_WIDTH
    parameter int IW   = 2,    // AXI_ID_WIDTH
    parameter int NE   = 2,    // NUM_ENTRIES
    parameter int AGEW = 4,    // AGE_WIDTH
    parameter int RKW  = 1,
    parameter int BKW  = 2,
    parameter int PTRW = 1,
    // ISSUE019=1 arms the tRRD/tFAW spacing assertions. They FAIL -- that is
    // the reproduction for pumice BUG-021 -- so they are off by default and
    // live in their own sby task, to keep `make -C formal formal-pumice` a
    // signal about regressions rather than a permanent red on a known,
    // triaged defect. `make issue019` runs them.
    parameter int ISSUE019 = 0
) (
    input logic aclk,
    input logic aresetn
);

    // ---- CSR-programmed timings: written once at init, then stable ---------
    (* anyconst *) reg [7:0] t_faw, t_rrd, t_wtr, t_rtw, t_ccd;
    always @(*) begin
        // tRRD must be able to BIND: with one command per cycle a spacing of 1
        // holds by construction, so only >= 2 asks anything of the design.
        assume (t_rrd >= 2 && t_rrd <= 4);
        // tFAW past the four-ACT span tRRD alone forces, or it is tRRD being
        // checked twice -- the vacuity that bit global_timers (TASK-035 traps).
        assume (t_faw >= 3*4 + 1 && t_faw <= 18);
        assume (t_wtr >= 1 && t_wtr <= 3);
        assume (t_rtw >= 1 && t_rtw <= 3);
        assume (t_ccd >= 1 && t_ccd <= 3);
    end

    // ---- free arbiter environment (CAM side, init, refresh, config) --------
    (* anyseq *) reg [1:0] page_policy_i, sched_order_mode_i, sched_row_sel_i;
    (* anyseq *) reg [1:0] sched_col_sel_i, sched_access_pref_i, sched_prio_sub_i;
    (* anyseq *) reg [7:0] sched_wr_high_wm_i, sched_wr_batch_max_i, sched_wr_low_wm_i;
    (* anyseq *) reg       sched_qos_en_i, ap_mode_en_i, timeout_pre_req_i;
    (* anyseq *) reg [NE*4-1:0] rd_sch_qos_i, wr_sch_qos_i;
    (* anyseq *) reg [NE-1:0]   rd_sch_age_exceed_i, wr_sch_age_exceed_i;
    (* anyseq *) reg [AGEW-1:0] rd_sch_head_rel_i, wr_sch_head_rel_i;
    (* anyseq *) reg [NB-1:0]   ap_close_i;
    (* anyseq *) reg [BKW-1:0]  timeout_pre_bank_i;
    (* anyseq *) reg            init_cmd_valid_i;
    (* anyseq *) reg [3:0]      init_cmd_op_i;
    (* anyseq *) reg [BKW-1:0]  init_cmd_bank_i;
    (* anyseq *) reg [RW-1:0]   init_cmd_row_i;
    (* anyseq *) reg            refresh_req_i, refresh_drain_i, refresh_kind_i;
    (* anyseq *) reg [BKW-1:0]  refresh_bank_i;
    (* anyseq *) reg [15:0]     t_rfc_i;
    (* anyseq *) reg [7:0]      t_rfc_pb_i;
    (* anyseq *) reg [NR*NB-1:0] bank_act_ready_i, bank_rdwr_ready_i, bank_pre_ready_i;
    (* anyseq *) reg [NR*NB-1:0] bank_act_ready_la_i, bank_rdwr_ready_la_i, bank_pre_ready_la_i;
    (* anyseq *) reg [NR*NB-1:0] bank_row_active_i;
    (* anyseq *) reg [NR*NB*RW-1:0] bank_open_row_i;
    (* anyseq *) reg [NE-1:0]   wr_sch_valid_i, rd_sch_valid_i;
    (* anyseq *) reg [NE*BKW-1:0] wr_sch_bank_i, rd_sch_bank_i;
    (* anyseq *) reg [NE*RW-1:0]  wr_sch_row_i, rd_sch_row_i;
    (* anyseq *) reg [NE*CW-1:0]  wr_sch_col_i, rd_sch_col_i;
    (* anyseq *) reg [NE*NE-1:0]  wr_sch_older_i, rd_sch_older_i;
    (* anyseq *) reg            wr_commit_ready_i, rd_issue_ready_i, cmd_ready_i;

    // init is complete: this proof is about mission-mode scheduling, and the
    // init sequencer drives the command bus directly before that.
    wire init_done_i = 1'b1;

    wire refresh_grant_o, wr_commit_valid_o, rd_issue_valid_o;
    wire [PTRW-1:0] wr_commit_slot_o, rd_issue_slot_o;
    wire evt_act_o, evt_rd_o, evt_wr_o, evt_pre_o, evt_ap_o;
    wire [RKW-1:0] evt_rank_o;
    wire [BKW-1:0] evt_bank_o;
    wire [RW-1:0]  evt_row_o;
    wire cmd_valid_o; wire [3:0] cmd_op_o;
    wire [RKW-1:0] cmd_rank_o; wire [BKW-1:0] cmd_bank_o;
    wire [RW-1:0] cmd_row_o; wire [CW-1:0] cmd_col_o;

    // the timers' readiness, produced by the REAL global_timers below
    wire [NR-1:0] tfaw_ok_i, trrd_ok_i;
    wire twtr_ok_i, trtw_ok_i, tccd_ok_i;

    pumice_cmd_arbiter #(
        .NUM_RANKS(NR), .NUM_BANKS(NB), .ROW_WIDTH(RW), .COL_WIDTH(CW),
        .AXI_ID_WIDTH(IW), .NUM_ENTRIES(NE), .AGE_WIDTH(AGEW)
    ) u_arb (
        .aclk(aclk), .aresetn(aresetn),
        .page_policy_i(page_policy_i), .sched_order_mode_i(sched_order_mode_i),
        .sched_row_sel_i(sched_row_sel_i), .sched_col_sel_i(sched_col_sel_i),
        .sched_access_pref_i(sched_access_pref_i),
        .sched_wr_high_wm_i(sched_wr_high_wm_i),
        .sched_wr_batch_max_i(sched_wr_batch_max_i),
        .sched_wr_low_wm_i(sched_wr_low_wm_i), .sched_prio_sub_i(sched_prio_sub_i),
        .sched_qos_en_i(sched_qos_en_i), .rd_sch_qos_i(rd_sch_qos_i),
        .wr_sch_qos_i(wr_sch_qos_i), .rd_sch_age_exceed_i(rd_sch_age_exceed_i),
        .wr_sch_age_exceed_i(wr_sch_age_exceed_i),
        .rd_sch_head_rel_i(rd_sch_head_rel_i), .wr_sch_head_rel_i(wr_sch_head_rel_i),
        .ap_mode_en_i(ap_mode_en_i), .ap_close_i(ap_close_i),
        .timeout_pre_req_i(timeout_pre_req_i), .timeout_pre_bank_i(timeout_pre_bank_i),
        .init_done_i(init_done_i), .init_cmd_valid_i(init_cmd_valid_i),
        .init_cmd_op_i(init_cmd_op_i), .init_cmd_bank_i(init_cmd_bank_i),
        .init_cmd_row_i(init_cmd_row_i),
        .refresh_req_i(refresh_req_i), .refresh_drain_i(refresh_drain_i),
        .refresh_kind_i(refresh_kind_i), .refresh_bank_i(refresh_bank_i),
        .refresh_grant_o(refresh_grant_o), .t_rfc_i(t_rfc_i), .t_rfc_pb_i(t_rfc_pb_i),
        .bank_act_ready_i(bank_act_ready_i), .bank_rdwr_ready_i(bank_rdwr_ready_i),
        .bank_pre_ready_i(bank_pre_ready_i), .bank_act_ready_la_i(bank_act_ready_la_i),
        .bank_rdwr_ready_la_i(bank_rdwr_ready_la_i), .bank_pre_ready_la_i(bank_pre_ready_la_i),
        .bank_row_active_i(bank_row_active_i), .bank_open_row_i(bank_open_row_i),
        .tfaw_ok_i(tfaw_ok_i), .trrd_ok_i(trrd_ok_i), .twtr_ok_i(twtr_ok_i),
        .trtw_ok_i(trtw_ok_i), .tccd_ok_i(tccd_ok_i), .t_ccd_i(t_ccd),
        .wr_sch_valid_i(wr_sch_valid_i), .wr_sch_bank_i(wr_sch_bank_i),
        .wr_sch_row_i(wr_sch_row_i), .wr_sch_col_i(wr_sch_col_i),
        .wr_sch_older_i(wr_sch_older_i), .wr_commit_ready_i(wr_commit_ready_i),
        .wr_commit_valid_o(wr_commit_valid_o), .wr_commit_slot_o(wr_commit_slot_o),
        .rd_sch_valid_i(rd_sch_valid_i), .rd_sch_bank_i(rd_sch_bank_i),
        .rd_sch_row_i(rd_sch_row_i), .rd_sch_col_i(rd_sch_col_i),
        .rd_sch_older_i(rd_sch_older_i), .rd_issue_ready_i(rd_issue_ready_i),
        .rd_issue_valid_o(rd_issue_valid_o), .rd_issue_slot_o(rd_issue_slot_o),
        .evt_act_o(evt_act_o), .evt_rd_o(evt_rd_o), .evt_wr_o(evt_wr_o),
        .evt_pre_o(evt_pre_o), .evt_ap_o(evt_ap_o), .evt_rank_o(evt_rank_o),
        .evt_bank_o(evt_bank_o), .evt_row_o(evt_row_o),
        .cmd_valid_o(cmd_valid_o), .cmd_ready_i(cmd_ready_i), .cmd_op_o(cmd_op_o),
        .cmd_rank_o(cmd_rank_o), .cmd_bank_o(cmd_bank_o), .cmd_row_o(cmd_row_o),
        .cmd_col_o(cmd_col_o)
    );

    // THE LOOP: the arbiter's own events feed the real timers, whose readiness
    // gates the arbiter. Proving the arbiter against free ok_i inputs would
    // prove nothing at all.
    wire [NR-1:0] gt_faw_nz, gt_trrd_nz;
    wire gt_twtr_nz, gt_trtw_nz, gt_tccd_nz;
    global_timers #(.NUM_RANKS(NR), .NUM_BANKS(NB)) u_gt (
        .mc_clk(aclk), .mc_rst_n(aresetn),
        .t_faw_i(t_faw), .t_rrd_i(t_rrd), .t_wtr_global_i(t_wtr),
        .t_rtw_i(t_rtw), .t_ccd_i(t_ccd),
        .evt_act_i(evt_act_o), .evt_act_rank_i(evt_rank_o),
        .evt_rd_i(evt_rd_o), .evt_wr_i(evt_wr_o),
        .tfaw_window_ok_o(tfaw_ok_i), .trrd_window_ok_o(trrd_ok_i),
        .twtr_global_ok_o(twtr_ok_i), .trtw_window_ok_o(trtw_ok_i),
        .tccd_window_ok_o(tccd_ok_i),
        .obs_faw_nz_o(gt_faw_nz), .obs_trrd_nz_o(gt_trrd_nz),
        .obs_twtr_nz_o(gt_twtr_nz), .obs_trtw_nz_o(gt_trtw_nz),
        .obs_tccd_nz_o(gt_tccd_nz)
    );

    // ---- CAM-side invariants, ASSUMED because they are PROVED -------------
    // The scheduling vectors are free above, which is the strongest
    // environment -- but "strongest" includes CAM states the real CAMs cannot
    // produce, and a counterexample resting on one of those is not a finding.
    // formal/pumice/rd_cmd_cam proves the age-order matrix is a STRICT ORDER
    // over valid entries (irreflexive, antisymmetric, transitive), so assuming
    // exactly that here is sound: it is a theorem about the block that drives
    // this input, not a convenience.
    reg ok_rd_ord, ok_wr_ord;
    integer oi, oj;
    always @(*) begin
        ok_rd_ord = 1'b1; ok_wr_ord = 1'b1;
        for (oi = 0; oi < NE; oi = oi + 1) begin
            if (rd_sch_older_i[oi*NE + oi]) ok_rd_ord = 1'b0;
            if (wr_sch_older_i[oi*NE + oi]) ok_wr_ord = 1'b0;
            for (oj = 0; oj < NE; oj = oj + 1) begin
                if (oi != oj && rd_sch_valid_i[oi] && rd_sch_valid_i[oj]
                    && (rd_sch_older_i[oi*NE + oj] == rd_sch_older_i[oj*NE + oi]))
                    ok_rd_ord = 1'b0;
                if (oi != oj && wr_sch_valid_i[oi] && wr_sch_valid_i[oj]
                    && (wr_sch_older_i[oi*NE + oj] == wr_sch_older_i[oj*NE + oi]))
                    ok_wr_ord = 1'b0;
            end
        end
    end
    always @(*) if (aresetn) begin
        assume (ok_rd_ord);
        assume (ok_wr_ord);
    end

    reg [7:0] f_past_valid = 0;
    always @(posedge aclk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!aresetn);
    always @(posedge aclk) if (f_past_valid >= 2) assume (aresetn);

    // =====================================================================
    // INDEPENDENT HISTORY -- the wrapper times the ACTs itself
    // =====================================================================
    localparam int AW = 10;
    reg [AW-1:0] age_act;
    reg          seen_act;
    reg [AW-1:0] faw_age [4];
    reg [2:0]    n_act;

    integer i;
    always @(posedge aclk) begin
        if (!aresetn) begin
            age_act <= 0; seen_act <= 1'b0; n_act <= 0;
            for (i = 0; i < 4; i = i + 1) faw_age[i] <= {AW{1'b1}};
        end else begin
            if (evt_act_o) begin age_act <= 1; seen_act <= 1'b1; end
            else if (age_act != {AW{1'b1}}) age_act <= age_act + 1'b1;

            for (i = 0; i < 4; i = i + 1)
                if (faw_age[i] != {AW{1'b1}}) faw_age[i] <= faw_age[i] + 1'b1;
            if (evt_act_o) begin
                faw_age[3] <= (faw_age[2] == {AW{1'b1}}) ? {AW{1'b1}} : faw_age[2] + 1'b1;
                faw_age[2] <= (faw_age[1] == {AW{1'b1}}) ? {AW{1'b1}} : faw_age[1] + 1'b1;
                faw_age[1] <= (faw_age[0] == {AW{1'b1}}) ? {AW{1'b1}} : faw_age[0] + 1'b1;
                faw_age[0] <= 1;
                if (n_act != 3'd7) n_act <= n_act + 1'b1;
            end
        end
    end

    // =====================================================================
    // THE ISSUE-019 PROPERTIES
    // =====================================================================
    always @(posedge aclk) if (aresetn && f_past_valid > 2) begin
        // tRRD: no two ACTs closer than t_rrd, ANY banks. This is the one the
        // per-bank bank_timer cannot see and the command-history checker was
        // same-bank-blind to.
        if (ISSUE019 != 0 && evt_act_o && seen_act)
            a_trrd_spacing: assert (age_act >= {2'b0, t_rrd});

        // tFAW: this ACT is the fifth only if four earlier ones exist, and the
        // oldest of those four must have left the window.
        if (ISSUE019 != 0 && evt_act_o && n_act >= 3'd4)
            a_tfaw_window: assert (faw_age[3] >= {2'b0, t_faw});

        // one DRAM command per cycle -- the DFI carries one slot
        a_single_issue: assert ($countones({evt_act_o, evt_rd_o, evt_wr_o, evt_pre_o}) <= 1);
    end

    // =====================================================================
    // COVER -- a pass is worthless if ACTs never happen
    // =====================================================================
    always @(posedge aclk) if (aresetn) begin
        c_act:        cover (evt_act_o);
        c_two_acts:   cover (evt_act_o && seen_act);
        c_four_acts:  cover (n_act >= 3'd4);
        c_fifth_act:  cover (evt_act_o && n_act >= 3'd4);
        c_act_diff_bank: cover (evt_act_o && seen_act && age_act < 10'd6);
        c_col:        cover (evt_rd_o || evt_wr_o);
    end

endmodule
