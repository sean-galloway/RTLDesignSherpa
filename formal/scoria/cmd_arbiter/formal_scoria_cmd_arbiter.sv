// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal wrapper for scoria_cmd_arbiter COMPOSED WITH scoria_global_timers.
//
// WHY THIS EXISTS: it is the unbounded-behaviour evidence for scoria BUG-001.
// That bug is the arbiter issuing two cross-bank ACTs one cycle apart against
// tRRD 2 -- the final-stage `w_out_safe` re-validated only the PER-BANK gate,
// so a rank-global window checked two pipeline stages earlier could go stale
// under it. It reproduced in simulation on 3 of 3 seeds in about 30 seconds,
// and the fix adds the rank-global terms to that gate:
//
//     if (r_do_act) w_out_safe = bank_act_ready_i[RK0][r_bank]
//                             && tfaw_ok_i[RK0] && trrd_ok_i[RK0];
//
// Three seeds is a measurement, not a proof. This is the proof.
//
// THE DIFFERENCE FROM pumice's EQUIVALENT PROOF. pumice/cmd_arbiter holds the
// same two properties behind an `ISSUE019` parameter that defaults OFF,
// because on pumice they FAIL -- they are the reproduction for pumice BUG-021,
// the same mechanism in the same block, which pumice could only ever show in
// formal. Here they are ARMED BY DEFAULT and expected to hold, because the
// gate is fixed. If a future change regresses that gate, `make prove` goes red
// in the area sweep rather than in a task nobody runs.
//
// THE COMPOSITION IS THE POINT. Proving the arbiter alone says nothing: its
// tfaw_ok_i / trrd_ok_i are inputs, so an engine free to drive them can permit
// anything -- and the bug is precisely that the arbiter sampled those inputs
// too early. So the real scoria_global_timers is instantiated here and wired to
// the arbiter's own evt_* outputs: arbiter issues, timers observe, timers gate
// the arbiter. What is proved is a property of the pair, which is what runs on
// the board.
//
// WHAT IS PROVED
//   * tRRD: no two ACTs closer than t_rrd_i, ANY banks -- measured on
//     evt_act_o by a counter this wrapper keeps, not by anything either DUT
//     exposes. This is the one scoria_bank_timer cannot see (it is per-bank)
//     and scoria_cmd_history_checker is blind to (it is same-bank by design).
//   * tFAW: never five ACTs inside a t_faw_i window.
//   * one DRAM command per cycle: the DFI carries one slot.
//   * tZQCS: scoria-only. JESD79-3F 3.10 forbids EVERY command during the
//     ZQCS window, so a grant must be followed by silence -- a stronger
//     obligation than any per-bank timer expresses, and the arbiter owns it
//     alone because scoria_zq_ctrl does not.
//
// The arbiter is self-contained (it instantiates nothing), so its CAM-side
// inputs are free: the scheduling vectors, bank readiness, init, refresh and
// ZQ ports are all driven by the engine, which is the strongest environment --
// any CAM behaviour is allowed, including ones the real CAMs never produce.
//
// SMALL GEOMETRY. 1 rank, 4 banks, 2 entries per CAM, 4-bit row. tRRD and tFAW
// are rank-global, so the bank count only has to be enough for the cross-bank
// case per-bank timers cannot see, which is two.
//
// YOSYS-COMPATIBLE FORM. Both DUTs pre-flattened by sv2v; immediate assertions
// (scoria carries no assertions in its RTL, by standing rule).

`timescale 1ns / 1ps

module formal_scoria_cmd_arbiter #(
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
    // BUG001=0 disarms the rank-global spacing assertions. Kept as a knob only
    // so the pre-fix arbiter can be re-proved to FAIL on demand (that is what
    // makes the passing proof mean something); it defaults ON and the area
    // sweep runs it armed.
    parameter int BUG001 = 1
) (
    input logic aclk,
    input logic aresetn
);

    // ---- CSR-programmed timings: written once at init, then stable ---------
    (* anyconst *) reg [7:0] t_faw, t_rrd, t_wtr, t_rtw, t_ccd;
    (* anyconst *) reg [15:0] t_zqcs;
    always @(*) begin
        // tRRD must be able to BIND: with one command per cycle a spacing of 1
        // holds by construction, so only >= 2 asks anything of the design.
        assume (t_rrd >= 2 && t_rrd <= 4);
        // tFAW past the four-ACT span tRRD alone forces, or it is tRRD being
        // checked twice -- the vacuity that bit pumice's global_timers proof.
        assume (t_faw >= 3*4 + 1 && t_faw <= 18);
        assume (t_wtr >= 1 && t_wtr <= 3);
        assume (t_rtw >= 1 && t_rtw <= 3);
        assume (t_ccd >= 1 && t_ccd <= 3);
        // Short enough that a bounded trace can both open and close the
        // window; the real part is ~64 CK, which no BMC depth would reach.
        assume (t_zqcs >= 2 && t_zqcs <= 5);
    end

    // ---- free arbiter environment (CAM side, init, refresh, ZQ, config) ----
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
    (* anyseq *) reg            zq_req_i;
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

    wire refresh_grant_o, wr_commit_valid_o, rd_issue_valid_o, zq_grant_o;
    wire [PTRW-1:0] wr_commit_slot_o, rd_issue_slot_o;
    wire evt_act_o, evt_rd_o, evt_wr_o, evt_pre_o, evt_ap_o;
    wire [RKW-1:0] evt_rank_o;
    wire [BKW-1:0] evt_bank_o;
    wire [RW-1:0]  evt_row_o;
    wire cmd_valid_o; wire [3:0] cmd_op_o;
    wire [RKW-1:0] cmd_rank_o; wire [BKW-1:0] cmd_bank_o;
    wire [RW-1:0] cmd_row_o; wire [CW-1:0] cmd_col_o;
    wire [31:0] stall_zq_o;

    // the timers' readiness, produced by the REAL scoria_global_timers below
    wire [NR-1:0] tfaw_ok_i, trrd_ok_i;
    wire twtr_ok_i, trtw_ok_i, tccd_ok_i;

    scoria_cmd_arbiter #(
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
        .zq_req_i(zq_req_i), .zq_grant_o(zq_grant_o), .t_zqcs_i(t_zqcs),
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
        .cmd_col_o(cmd_col_o), .stall_zq_o(stall_zq_o)
    );

    // THE LOOP: the arbiter's own events feed the real timers, whose readiness
    // gates the arbiter. Proving the arbiter against free ok_i inputs would
    // prove nothing at all -- and would in particular not see BUG-001, which
    // is about WHEN the arbiter samples these.
    wire [NR-1:0] gt_faw_nz, gt_trrd_nz;
    wire gt_twtr_nz, gt_trtw_nz, gt_tccd_nz;
    scoria_global_timers #(.NUM_RANKS(NR), .NUM_BANKS(NB)) u_gt (
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

    // ---- CAM-side invariants, ASSUMED because they are PROVED --------------
    // The scheduling vectors are free above, which is the strongest
    // environment -- but "strongest" includes CAM states the real CAMs cannot
    // produce, and a counterexample resting on one of those is not a finding.
    // The age-order matrix is a STRICT ORDER over valid entries (irreflexive,
    // antisymmetric), which is a theorem about the block driving this input --
    // proved for the same CAM on pumice in formal/pumice/rd_cmd_cam -- not a
    // convenience. scoria's CAMs are the pumice ones; when scoria gets its own
    // rd_cmd_cam proof this assumption should cite that instead.
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

    // =======================================================================
    // INDEPENDENT HISTORY -- the wrapper times the ACTs itself
    // =======================================================================
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

    // ZQCS history: how long since a grant, and whether one has been seen.
    reg [AW-1:0] age_zq;
    reg          seen_zq;
    always @(posedge aclk) begin
        if (!aresetn) begin age_zq <= 0; seen_zq <= 1'b0; end
        else if (zq_grant_o) begin age_zq <= 1; seen_zq <= 1'b1; end
        else if (age_zq != {AW{1'b1}}) age_zq <= age_zq + 1'b1;
    end

    // =======================================================================
    // THE BUG-001 PROPERTIES -- armed, because the gate is fixed
    // =======================================================================
    always @(posedge aclk) if (aresetn && f_past_valid > 2) begin
        // tRRD: no two ACTs closer than t_rrd, ANY banks. THE BUG-001
        // property: per-bank bank_timer cannot see it and
        // scoria_cmd_history_checker is same-bank by design, so before the
        // `w_out_safe` fix this is the assertion that fires.
        if (BUG001 != 0 && evt_act_o && seen_act)
            a_trrd_spacing: assert (age_act >= {2'b0, t_rrd});

        // tFAW: this ACT is the fifth only if four earlier ones exist, and the
        // oldest of those four must have left the window.
        if (BUG001 != 0 && evt_act_o && n_act >= 3'd4)
            a_tfaw_window: assert (faw_age[3] >= {2'b0, t_faw});

        // one DRAM command per cycle -- the DFI carries one slot
        a_single_issue: assert ($countones({evt_act_o, evt_rd_o, evt_wr_o, evt_pre_o}) <= 1);

        // tZQCS, scoria-only: JESD79-3F 3.10 forbids EVERY command during the
        // window, so nothing may issue until it closes. The arbiter owns this
        // alone -- scoria_zq_ctrl does not hold the window.
        if (seen_zq && age_zq <= {6'b0, t_zqcs[3:0]})
            a_zqcs_quiet: assert (!(evt_act_o || evt_rd_o || evt_wr_o || evt_pre_o));
    end

    // =======================================================================
    // COVER -- a pass is worthless if ACTs never happen
    // =======================================================================
    always @(posedge aclk) if (aresetn) begin
        c_act:        cover (evt_act_o);
        c_two_acts:   cover (evt_act_o && seen_act);
        c_four_acts:  cover (n_act >= 3'd4);
        c_fifth_act:  cover (evt_act_o && n_act >= 3'd4);
        c_act_diff_bank: cover (evt_act_o && seen_act && age_act < 10'd6);
        c_col:        cover (evt_rd_o || evt_wr_o);
        c_zq_grant:   cover (zq_grant_o);
        // The REALISTIC shape of the tZQCS hole: an ACT, not a stray PRE.
        // Traffic queues up behind a ZQCS (the arbiter precharges everything
        // to issue one), so the instant it goes the pick cone is free to take
        // a waiting ACT -- which fires a cycle later, inside the window.
        c_act_in_zqcs: cover (seen_zq && age_zq <= {6'b0, t_zqcs[3:0]} && evt_act_o);
        c_col_in_zqcs: cover (seen_zq && age_zq <= {6'b0, t_zqcs[3:0]}
                              && (evt_rd_o || evt_wr_o));
    end

endmodule
