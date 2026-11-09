// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Equivalence harness: mc_bank_timer with ZF_REG = 1 (registered zero-detect,
// "within LA" and auto-precharge lookahead flags; memory-controllers MC-011,
// 2026-11-08) against the golden copy of the live-compare form, same inputs,
// every output compared every cycle. The flags are a retiming of the output
// compares across the counter register, so the two must agree on
// safe_*, safe_*_la, row_valid, open_row, state and the obs_* bits with no
// exception -- a single differing cycle is a behaviour change, not noise.
//
// Timings are CSR-programmed and static during traffic (the parent registers
// them; they are false paths on the board), so they are anyconst here, over
// the full counter range. The strobes are free, single-issue (one DRAM command
// per bank per cycle is the controller's contract and the parent's gating),
// and NOT gated by the readiness outputs: the equivalence must hold whatever
// the environment pushes, which is stronger than the spacing proof needs.
`timescale 1ns / 1ps
module formal_bank_timer_equiv #(
    parameter int ROW_WIDTH = 4,
    parameter int TW        = 8,
    parameter int LA        = 2,
    parameter bit LA_AP     = 1'b1,
    parameter bit SET_LAG   = 1'b1
) (
    input logic clk,
    input logic rst_n
);
    localparam integer LD = SET_LAG ? 2 : 1;

    (* anyconst *) reg [TW-1:0] t_rcd, t_rp, t_ras, t_rc, t_wr, t_rtp;
    (* anyseq *) reg set_act, set_rd, set_wr, set_pre, set_ap;
    (* anyseq *) reg [ROW_WIDTH-1:0] row;
    always @(*) assume ($countones({set_act, set_rd, set_wr, set_pre}) <= 1);

    function automatic [TW-1:0] f_ld(input [TW-1:0] t, input integer d);
        f_ld = (t <= d) ? {TW{1'b0}} : (t - d[TW-1:0]);
    endfunction
    wire [TW-1:0] ld_rcd = f_ld(t_rcd, LD), ld_ras = f_ld(t_ras, LD), ld_rc = f_ld(t_rc, LD);
    wire [TW-1:0] ld_rp  = f_ld(t_rp, LD),  ld_rp1 = f_ld(t_rp, 1);
    wire [TW-1:0] ld_rtp = f_ld(t_rtp, LD), ld_wr = f_ld(t_wr, LD);
    wire [TW-1:0] rtp_w1 = f_ld(t_rtp, 1), wr_w1 = f_ld(t_wr, 1), ras_w1 = f_ld(t_ras, 1);
    wire rtp_le1 = (t_rtp <= 1), wr_le1 = (t_wr <= 1);
    wire rcd_la = (t_rcd <= LA + 1), ras_la = (t_ras <= LA + 1), rc_la = (t_rc <= LA + 1);
    wire rp_la  = (t_rp  <= LA + 1), rtp_la = (t_rtp <= LA + 1), wr_la = (t_wr <= LA + 1);

    // outputs, new (n_) and golden (g_)
    wire n_safe_act, n_safe_rd, n_safe_wr, n_safe_pre, n_safe_act_la, n_safe_rdwr_la, n_safe_pre_la;
    wire n_row_valid, n_obs_rcd_nz, n_obs_preblk_nz, n_obs_ras_nz, n_obs_ap_pending;
    wire [ROW_WIDTH-1:0] n_open_row; wire [2:0] n_state;
    wire g_safe_act, g_safe_rd, g_safe_wr, g_safe_pre, g_safe_act_la, g_safe_rdwr_la, g_safe_pre_la;
    wire g_row_valid, g_obs_rcd_nz, g_obs_preblk_nz, g_obs_ras_nz, g_obs_ap_pending;
    wire [ROW_WIDTH-1:0] g_open_row; wire [2:0] g_state;

    mc_bank_timer #(.ROW_WIDTH(ROW_WIDTH), .TW(TW), .LA(LA), .LA_AP(LA_AP), .SET_LAG(SET_LAG), .ZF_REG(1'b1)) dut_new (
        .clk(clk), .rst_n(rst_n),
        .ld_rcd_i(ld_rcd), .ld_ras_i(ld_ras), .ld_rc_i(ld_rc), .ld_rp_i(ld_rp), .ld_rp1_i(ld_rp1),
        .ld_rtp_i(ld_rtp), .ld_wr_i(ld_wr), .t_rp_i(t_rp),
        .rtp_le1_i(rtp_le1), .wr_le1_i(wr_le1),
        .rcd_la_i(rcd_la), .ras_la_i(ras_la), .rc_la_i(rc_la), .rp_la_i(rp_la), .rtp_la_i(rtp_la), .wr_la_i(wr_la),
        .rtp_w1_i(rtp_w1), .wr_w1_i(wr_w1), .ras_w1_i(ras_w1),
        .set_act_i(set_act), .set_rd_i(set_rd), .set_wr_i(set_wr), .set_pre_i(set_pre), .set_ap_i(set_ap), .row_i(row),
        .safe_act_o(n_safe_act), .safe_rd_o(n_safe_rd), .safe_wr_o(n_safe_wr), .safe_pre_o(n_safe_pre),
        .safe_act_la_o(n_safe_act_la), .safe_rdwr_la_o(n_safe_rdwr_la), .safe_pre_la_o(n_safe_pre_la),
        .row_valid_o(n_row_valid), .open_row_o(n_open_row), .state_o(n_state),
        .obs_rcd_nz_o(n_obs_rcd_nz), .obs_preblk_nz_o(n_obs_preblk_nz), .obs_ras_nz_o(n_obs_ras_nz), .obs_ap_pending_o(n_obs_ap_pending)
    );
    mc_bank_timer_gold #(.ROW_WIDTH(ROW_WIDTH), .TW(TW), .LA(LA), .LA_AP(LA_AP), .SET_LAG(SET_LAG)) dut_gold (
        .clk(clk), .rst_n(rst_n),
        .ld_rcd_i(ld_rcd), .ld_ras_i(ld_ras), .ld_rc_i(ld_rc), .ld_rp_i(ld_rp), .ld_rp1_i(ld_rp1),
        .ld_rtp_i(ld_rtp), .ld_wr_i(ld_wr), .t_rp_i(t_rp),
        .rtp_le1_i(rtp_le1), .wr_le1_i(wr_le1),
        .rcd_la_i(rcd_la), .ras_la_i(ras_la), .rc_la_i(rc_la), .rp_la_i(rp_la), .rtp_la_i(rtp_la), .wr_la_i(wr_la),
        .rtp_w1_i(rtp_w1), .wr_w1_i(wr_w1), .ras_w1_i(ras_w1),
        .set_act_i(set_act), .set_rd_i(set_rd), .set_wr_i(set_wr), .set_pre_i(set_pre), .set_ap_i(set_ap), .row_i(row),
        .safe_act_o(g_safe_act), .safe_rd_o(g_safe_rd), .safe_wr_o(g_safe_wr), .safe_pre_o(g_safe_pre),
        .safe_act_la_o(g_safe_act_la), .safe_rdwr_la_o(g_safe_rdwr_la), .safe_pre_la_o(g_safe_pre_la),
        .row_valid_o(g_row_valid), .open_row_o(g_open_row), .state_o(g_state),
        .obs_rcd_nz_o(g_obs_rcd_nz), .obs_preblk_nz_o(g_obs_preblk_nz), .obs_ras_nz_o(g_obs_ras_nz), .obs_ap_pending_o(g_obs_ap_pending)
    );

    reg [7:0] f_past_valid = 0;
    always @(posedge clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!rst_n);
    always @(posedge clk) if (f_past_valid >= 2) assume (rst_n);

    always @(posedge clk) if (rst_n) begin
        a_safe_act:      assert (n_safe_act      == g_safe_act);
        a_safe_rd:       assert (n_safe_rd       == g_safe_rd);
        a_safe_wr:       assert (n_safe_wr       == g_safe_wr);
        a_safe_pre:      assert (n_safe_pre      == g_safe_pre);
        a_safe_act_la:   assert (n_safe_act_la   == g_safe_act_la);
        a_safe_rdwr_la:  assert (n_safe_rdwr_la  == g_safe_rdwr_la);
        a_safe_pre_la:   assert (n_safe_pre_la   == g_safe_pre_la);
        a_row_valid:     assert (n_row_valid     == g_row_valid);
        a_open_row:      assert (n_open_row      == g_open_row);
        a_state:         assert (n_state         == g_state);
        a_obs_rcd:       assert (n_obs_rcd_nz    == g_obs_rcd_nz);
        a_obs_preblk:    assert (n_obs_preblk_nz == g_obs_preblk_nz);
        a_obs_ras:       assert (n_obs_ras_nz    == g_obs_ras_nz);
        a_obs_ap:        assert (n_obs_ap_pending == g_obs_ap_pending);
    end
    // the proof is not vacuous: every class of command, and the lookahead
    // and the auto-precharge path, occur
    always @(posedge clk) if (rst_n) begin
        c_act:    cover (set_act && g_safe_act);
        c_ap_la:  cover (g_obs_ap_pending && g_safe_act_la && !g_safe_act);
        c_rd_la:  cover (g_safe_rdwr_la && !g_safe_rd);
        c_pre_la: cover (g_safe_pre_la && !g_safe_pre);
    end
endmodule
