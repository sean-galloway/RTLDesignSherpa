// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Equivalence harness: mc_global_timers with the tournament tFAW slot search
// (memory-controllers MC-011, 2026-11-08) against the golden copy of the
// serial walk it replaces, same free inputs, every output compared every
// cycle after reset. The search is a different circuit for the same
// function -- the lowest index among the smallest slot values, an excluded
// slot above every value, the serial walk's slot-0 default when nothing beats
// its 8'hFF starting minimum -- so the two must agree with no exception.
//
// The strobes are free per cycle and no spacing contract is assumed: the
// equivalence must hold for whatever the environment presents. The timings are
// CSR-programmed and static during traffic (false paths on the board), so they
// are anyconst, over their whole 8-bit range -- free per cycle they made the
// 32-step BMC intractable (the solver sat on step 23 for half an hour) for a
// case the hardware cannot present.
//
// YOSYS-COMPATIBLE FORM: both DUTs pre-flattened by sv2v; immediate assertions.
`timescale 1ns / 1ps
module formal_global_timers_equiv #(
    parameter int NUM_RANKS = 1,
    parameter int NUM_BANKS = 8
) (
    input logic mc_clk,
    input logic mc_rst_n
);
    (* anyconst *) reg [7:0] t_faw_i, t_rrd_i, t_wtr_global_i, t_rtw_i, t_ccd_i;
    (* anyseq *) reg       evt_act_i, evt_rd_i, evt_wr_i;
    wire [0:0] evt_act_rank_i = 1'b0;      // NUM_RANKS = 1

    // the two instances' outputs, one set per prefix (n_ = new, g_ = golden)

`define GT_PORTS(P) \
        .mc_clk(mc_clk), .mc_rst_n(mc_rst_n), \
        .t_faw_i(t_faw_i), .t_rrd_i(t_rrd_i), .t_wtr_global_i(t_wtr_global_i), .t_rtw_i(t_rtw_i), .t_ccd_i(t_ccd_i), \
        .evt_act_i(evt_act_i), .evt_act_rank_i(evt_act_rank_i), .evt_rd_i(evt_rd_i), .evt_wr_i(evt_wr_i), \
        .tfaw_window_ok_o(P``tfaw_ok), .trrd_window_ok_o(P``trrd_ok), .twtr_global_ok_o(P``twtr_ok), \
        .trtw_window_ok_o(P``trtw_ok), .tccd_window_ok_o(P``tccd_ok), \
        .obs_faw_nz_o(P``obs_faw_nz), .obs_trrd_nz_o(P``obs_trrd_nz), .obs_twtr_nz_o(P``obs_twtr_nz), \
        .obs_trtw_nz_o(P``obs_trtw_nz), .obs_tccd_nz_o(P``obs_tccd_nz), \
        .t_ccd_l_i(8'd0), .t_ccd_s_i(8'd0), .t_rrd_l_i(8'd0), .t_rrd_s_i(8'd0), \
        .evt_act_bg_i('0), .evt_col_bg_i('0), .cand_rank_i('0), .cand_bg_i('0), \
        .tccd_l_window_ok_o(P``tccd_l_ok), .tccd_s_window_ok_o(P``tccd_s_ok), \
        .trrd_l_window_ok_o(P``trrd_l_ok), .trrd_s_window_ok_o(P``trrd_s_ok)

    wire [NUM_RANKS-1:0] n_tfaw_ok, n_trrd_ok, n_obs_faw_nz, n_obs_trrd_nz;
    wire n_twtr_ok, n_trtw_ok, n_tccd_ok, n_obs_twtr_nz, n_obs_trtw_nz, n_obs_tccd_nz;
    wire n_tccd_l_ok, n_tccd_s_ok, n_trrd_l_ok, n_trrd_s_ok;
    wire [NUM_RANKS-1:0] g_tfaw_ok, g_trrd_ok, g_obs_faw_nz, g_obs_trrd_nz;
    wire g_twtr_ok, g_trtw_ok, g_tccd_ok, g_obs_twtr_nz, g_obs_trtw_nz, g_obs_tccd_nz;
    wire g_tccd_l_ok, g_tccd_s_ok, g_trrd_l_ok, g_trrd_s_ok;

    mc_global_timers      #(.NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS)) dut_new  ( `GT_PORTS(n_) );
    mc_global_timers_gold #(.NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS)) dut_gold ( `GT_PORTS(g_) );

    reg [7:0] f_past_valid = 0;
    always @(posedge mc_clk) f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!mc_rst_n);
    always @(posedge mc_clk) if (f_past_valid >= 2) assume (mc_rst_n);

    always @(posedge mc_clk) if (mc_rst_n) begin
        a_tfaw:  assert (n_tfaw_ok == g_tfaw_ok);
        a_trrd:  assert (n_trrd_ok == g_trrd_ok);
        a_twtr:  assert (n_twtr_ok == g_twtr_ok);
        a_trtw:  assert (n_trtw_ok == g_trtw_ok);
        a_tccd:  assert (n_tccd_ok == g_tccd_ok);
        a_obs:   assert ({n_obs_faw_nz, n_obs_trrd_nz, n_obs_twtr_nz, n_obs_trtw_nz, n_obs_tccd_nz}
                         == {g_obs_faw_nz, g_obs_trrd_nz, g_obs_twtr_nz, g_obs_trtw_nz, g_obs_tccd_nz});
        a_ls:    assert ({n_tccd_l_ok, n_tccd_s_ok, n_trrd_l_ok, n_trrd_s_ok}
                         == {g_tccd_l_ok, g_tccd_s_ok, g_trrd_l_ok, g_trrd_s_ok});
    end
    // not vacuous: the tFAW window closes and reopens, and four ACTs land
    // with unequal slot values (the search has to choose)
    reg [2:0] n_acts;
    always @(posedge mc_clk) if (!mc_rst_n) n_acts <= '0; else if (evt_act_i && n_acts != 3'd7) n_acts <= n_acts + 1'b1;
    always @(posedge mc_clk) if (mc_rst_n) begin
        c_faw_blocks: cover (!g_tfaw_ok[0] && n_acts >= 3'd4);
        c_faw_reopen: cover (g_tfaw_ok[0] && n_acts >= 3'd4 && $past(!g_tfaw_ok[0]));
    end
endmodule
