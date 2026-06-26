// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: command_scheduler_macro
// Purpose: "What command should we issue this cycle?" — bundles all
//          the decision-making layer of the controller core:
//          scheduler + per-bank/global timers + refresh + powerdown +
//          mode-register + init-sequencer.
//
// Boundaries:
//          * Host-AXI side  → CAM query (q_rank/bank/row), match
//                             vectors (wr/rd_match_*), snap_* metadata,
//                             mark-issued strobes (wr/rd_issued_*).
//          * DFI-cmd side   → cmd_* channel consumed by dfi_v21_interface_macro.
//          * Data-path side → cmd_op + cmd_wr_slot/rd_slot + live
//                             CL/CWL/BL/AL for data_path_macro.
//          * DFI status     → dfi_init_start_o (drives PHY init) and
//                             dfi_cke_o (per-rank clock enable).
//
// Status:  SKELETON wrapper — FUB bodies remain stubs.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module command_scheduler_macro
    import ddr2_lpddr2_pkg::*;
#(
    parameter int AXI_ID_WIDTH    = 4,
    parameter int NUM_RANKS       = 1,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int WR_CAM_DEPTH    = 16,
    parameter int RD_CAM_DEPTH    = 16,
    parameter int DFI_CS_WIDTH    = NUM_RANKS,
    parameter int PAGE_POLICY     = 32'(PAGE_POLICY_CLOSE),

    parameter int IW  = AXI_ID_WIDTH,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int RW  = ROW_WIDTH,
    parameter int CW  = COL_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int WSL = $clog2(WR_CAM_DEPTH),
    parameter int RSL = $clog2(RD_CAM_DEPTH)
) (
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,

    // ---- runtime config ----
    input  memtype_e                   memtype_i,
    input  logic [15:0]                t_refi_i,
    input  logic [7:0]                 t_rcd_i,
    input  logic [7:0]                 t_rp_i,
    input  logic [7:0]                 t_ras_i,
    input  logic [7:0]                 t_rc_i,
    input  logic [7:0]                 t_wr_i,
    input  logic [7:0]                 t_wtr_i,
    input  logic [7:0]                 t_rtp_i,
    input  logic [7:0]                 t_faw_i,
    input  logic [7:0]                 t_rrd_i,
    input  logic [15:0]                idle_threshold_i,
    input  logic                       enable_pde_i,
    input  logic                       enable_sref_i,

    // ---- CSR-style MR write port ----
    input  logic                       mr_we_i,
    input  logic [4:0]                 mr_index_i,
    input  logic [15:0]                mr_data_i,
    input  logic [RKW-1:0]             mr_rank_i,

    // ---- host CAM query (drive q_*; receive match vectors) ----
    output logic [RKW-1:0]             q_rank_o,
    output logic [BKW-1:0]             q_bank_o,
    output logic [RW-1:0]              q_row_o,
    input  logic [WR_CAM_DEPTH-1:0]    wr_match_pending_i,
    input  logic [WR_CAM_DEPTH-1:0]    wr_match_rowhit_i,
    input  logic [RD_CAM_DEPTH-1:0]    rd_match_pending_i,
    input  logic [RD_CAM_DEPTH-1:0]    rd_match_rowhit_i,

    // ---- CAM snapshot metadata (combinational from host) ----
    input  logic [WR_CAM_DEPTH-1:0][RKW-1:0] wr_snap_rank_i,
    input  logic [WR_CAM_DEPTH-1:0][BKW-1:0] wr_snap_bank_i,
    input  logic [WR_CAM_DEPTH-1:0][RW-1:0]  wr_snap_row_i,
    input  logic [WR_CAM_DEPTH-1:0][CW-1:0]  wr_snap_col_i,
    input  logic [WR_CAM_DEPTH-1:0][BLW-1:0] wr_snap_len_i,
    input  logic [WR_CAM_DEPTH-1:0][3:0]     wr_snap_qos_i,
    input  logic [RD_CAM_DEPTH-1:0][RKW-1:0] rd_snap_rank_i,
    input  logic [RD_CAM_DEPTH-1:0][BKW-1:0] rd_snap_bank_i,
    input  logic [RD_CAM_DEPTH-1:0][RW-1:0]  rd_snap_row_i,
    input  logic [RD_CAM_DEPTH-1:0][CW-1:0]  rd_snap_col_i,
    input  logic [RD_CAM_DEPTH-1:0][BLW-1:0] rd_snap_len_i,
    input  logic [RD_CAM_DEPTH-1:0][3:0]     rd_snap_qos_i,
    input  logic [RD_CAM_DEPTH-1:0][7:0]     rd_snap_age_i,

    // ---- mark-issued back to host CAMs ----
    output logic                       wr_issued_we_o,
    output logic [WSL-1:0]             wr_issued_slot_o,
    output logic                       rd_issued_we_o,
    output logic [RSL-1:0]             rd_issued_slot_o,

    // ---- chosen op (to dfi_v21_interface_macro AND data_path_macro) ----
    output logic                       cmd_valid_o,
    input  logic                       cmd_ready_i,
    output dram_op_e                   cmd_op_o,
    output logic [RKW-1:0]             cmd_rank_o,
    output logic [BKW-1:0]             cmd_bank_o,
    output logic [RW-1:0]              cmd_row_o,
    output logic [CW-1:0]              cmd_col_o,
    output logic [BLW-1:0]             cmd_len_o,
    output logic [WSL-1:0]             cmd_wr_slot_o,
    output logic [RSL-1:0]             cmd_rd_slot_o,

    // ---- live MR values (to data_path_macro + dfi_v21_interface_macro) ----
    output logic [3:0]                 cl_o,
    output logic [3:0]                 cwl_o,
    output logic [3:0]                 bl_o,
    output logic [3:0]                 al_o,

    // ---- DFI status (to dfi_v21_interface_macro / out of core) ----
    output logic                       dfi_init_start_o,
    input  logic                       dfi_init_complete_i,
    output logic [DFI_CS_WIDTH-1:0]    dfi_cke_o,

    // ---- top-level status ----
    output logic                       controller_idle_o,

    // ---- status feed (consumed by the CSR slave's STATUS register) ----
    output logic                       status_init_done_o,
    output logic                       status_init_busy_o,
    output logic [2:0]                 status_pdn_state_o,

    //=========================================================================
    // obs_* CSR readout — see docs/csr_obs_layout.md for the layout.
    // 7 32-bit words covering xbank_timers + global_timers + refresh_ctrl
    // + powerdown_ctrl. The axi_frontend_macro contributes its own
    // obs_words_o; the core_macro concatenates the two.
    //=========================================================================
    output logic [6:0][31:0]           obs_words_o
);

    //=========================================================================
    // Internal nets between scheduler and its supporting FUBs.
    //=========================================================================

    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                bank_act_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                bank_rdwr_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                bank_pre_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                bank_row_active;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][RW-1:0]        bank_open_row;
    bank_state_e [NUM_RANKS-1:0][NUM_BANKS-1:0]         bank_state_unused;
    logic [NUM_RANKS-1:0]                               tfaw_window_ok;
    logic [NUM_RANKS-1:0]                               trrd_window_ok_unused;
    logic                                               twtr_global_ok_unused;
    logic                                               trtw_window_ok_unused;
    logic                                               tccd_window_ok_unused;

    // ---- obs_* harvest wires (packed into obs_words_o at end of module) ----
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]  obs_xbank_act_nz;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]  obs_xbank_rdwr_nz;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]  obs_xbank_pre_nz;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]  obs_xbank_rc_nz;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]  obs_xbank_ras_nz;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]  obs_xbank_ap_pending;
    logic [NUM_RANKS-1:0]                 obs_gt_faw_nz;
    logic [NUM_RANKS-1:0]                 obs_gt_trrd_nz;
    logic                                 obs_gt_twtr_nz;
    logic                                 obs_gt_trtw_nz;
    logic                                 obs_gt_tccd_nz;
    logic [15:0]                          obs_refi_cnt;
    logic [3:0]                           obs_refi_drain_remaining;
    logic [$clog2(NUM_BANKS)-1:0]         obs_refi_bank_rotor;
    logic [15:0]                          obs_refi_grants_total;
    logic [2:0]                           obs_pdn_state;
    logic [15:0]                          obs_pdn_idle_cnt;
    logic [15:0]                          obs_pdn_grants_pde;
    logic [15:0]                          obs_pdn_grants_sr;

    logic                                               refresh_req;
    logic                                               refresh_grant;
    logic                                               pdn_req;
    logic                                               pdn_grant;
    logic                                               init_busy;
    logic                                               init_done;
    logic                                               mr_req;
    logic                                               mr_grant;

    logic                                               evt_act, evt_rd, evt_wr, evt_pre, evt_ap;
    logic [RKW-1:0]                                     evt_rank;
    logic [BKW-1:0]                                     evt_bank;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                predict_open;

    // init-sequencer MR stream
    logic                                               mr_seq_we;
    logic [4:0]                                         mr_seq_index;
    logic [15:0]                                        mr_seq_data;
    logic                                               zqcl_req;
    logic                                               zqcl_grant;

    // ZQCL handshake — until scheduler arbitrates ZQ ops, auto-grant.
    assign zqcl_grant = 1'b1;

    // MR-load mux: prefer init sequencer's stream, fall back to CSR
    logic                                               mr_load_we;
    logic [4:0]                                         mr_load_index;
    logic [15:0]                                        mr_load_data;
    assign mr_load_we    = mr_seq_we | mr_we_i;
    assign mr_load_index = mr_seq_we ? mr_seq_index : mr_index_i;
    assign mr_load_data  = mr_seq_we ? mr_seq_data  : mr_data_i;

    // Controller idle status — used by powerdown_ctrl and exposed for top.
    assign controller_idle_o = ~cmd_valid_o;

    // Unused MR live values from mode_register (kept for future wiring).
    logic [1:0] drv_strength_unused;
    logic [1:0] odt_unused;

    // Unused per-rank MR-request fields and timer outputs.
    logic [4:0]  mr_req_index_unused;
    logic [15:0] mr_req_data_unused;
    logic [3:0]  pending_refreshes_unused;
    // (legacy trrd_unused/twtr_unused/trtw_unused removed; see new
    //  per-rank _window_ok_unused declarations above)

    //=========================================================================
    // FUBs
    //=========================================================================

    scheduler #(
        .WR_CAM_DEPTH    (WR_CAM_DEPTH),
        .RD_CAM_DEPTH    (RD_CAM_DEPTH),
        .NUM_RANKS       (NUM_RANKS),
        .NUM_BANKS       (NUM_BANKS),
        .ROW_WIDTH       (RW),
        .COL_WIDTH       (CW),
        .BURST_LEN_WIDTH (BLW),
        .AXI_ID_WIDTH    (IW),
        .PAGE_POLICY     (PAGE_POLICY)
    ) u_scheduler (
        .mc_clk             (mc_clk),
        .mc_rst_n           (mc_rst_n),
        .q_rank_o           (q_rank_o),
        .q_bank_o           (q_bank_o),
        .q_row_o            (q_row_o),
        .wr_match_pending_i (wr_match_pending_i),
        .wr_match_rowhit_i  (wr_match_rowhit_i),
        .rd_match_pending_i (rd_match_pending_i),
        .rd_match_rowhit_i  (rd_match_rowhit_i),
        .wr_snap_rank_i     (wr_snap_rank_i),
        .wr_snap_bank_i     (wr_snap_bank_i),
        .wr_snap_row_i      (wr_snap_row_i),
        .wr_snap_col_i      (wr_snap_col_i),
        .wr_snap_len_i      (wr_snap_len_i),
        .wr_snap_qos_i      (wr_snap_qos_i),
        .rd_snap_rank_i     (rd_snap_rank_i),
        .rd_snap_bank_i     (rd_snap_bank_i),
        .rd_snap_row_i      (rd_snap_row_i),
        .rd_snap_col_i      (rd_snap_col_i),
        .rd_snap_len_i      (rd_snap_len_i),
        .rd_snap_qos_i      (rd_snap_qos_i),
        .rd_snap_age_i      (rd_snap_age_i),
        .wr_issued_we_o     (wr_issued_we_o),
        .wr_issued_slot_o   (wr_issued_slot_o),
        .rd_issued_we_o     (rd_issued_we_o),
        .rd_issued_slot_o   (rd_issued_slot_o),
        .bank_act_ready_i   (bank_act_ready),
        .bank_rdwr_ready_i  (bank_rdwr_ready),
        .bank_pre_ready_i   (bank_pre_ready),
        .bank_row_active_i  (bank_row_active),
        .bank_open_row_i    (bank_open_row),
        .tfaw_window_ok_i   (tfaw_window_ok),
        .predict_open_i     (predict_open),
        .refresh_req_i      (refresh_req),
        .refresh_grant_o    (refresh_grant),
        .pdn_req_i          (pdn_req),
        .pdn_grant_o        (pdn_grant),
        .init_busy_i        (init_busy),
        .mr_req_i           (mr_req),
        .mr_grant_o         (mr_grant),
        .cmd_valid_o        (cmd_valid_o),
        .cmd_ready_i        (cmd_ready_i),
        .cmd_op_o           (cmd_op_o),
        .cmd_rank_o         (cmd_rank_o),
        .cmd_bank_o         (cmd_bank_o),
        .cmd_row_o          (cmd_row_o),
        .cmd_col_o          (cmd_col_o),
        .cmd_len_o          (cmd_len_o),
        .cmd_wr_slot_o      (cmd_wr_slot_o),
        .cmd_rd_slot_o      (cmd_rd_slot_o),
        .evt_act_o          (evt_act),
        .evt_rd_o           (evt_rd),
        .evt_wr_o           (evt_wr),
        .evt_pre_o          (evt_pre),
        .evt_ap_o           (evt_ap),
        .evt_rank_o         (evt_rank),
        .evt_bank_o         (evt_bank)
    );

    xbank_timers #(
        .NUM_RANKS (NUM_RANKS),
        .NUM_BANKS (NUM_BANKS),
        .ROW_WIDTH (RW)
    ) u_xbank_timers (
        .mc_clk             (mc_clk),
        .mc_rst_n           (mc_rst_n),
        .t_rcd_i            (t_rcd_i),
        .t_rp_i             (t_rp_i),
        .t_ras_i            (t_ras_i),
        .t_rc_i             (t_rc_i),
        .t_wr_i             (t_wr_i),
        .t_wtr_i            (t_wtr_i),
        .t_rtp_i            (t_rtp_i),
        .evt_act_i          (evt_act),
        .evt_rd_i           (evt_rd),
        .evt_wr_i           (evt_wr),
        .evt_pre_i          (evt_pre),
        .evt_ap_i           (evt_ap),
        .evt_rank_i         (evt_rank),
        .evt_bank_i         (evt_bank),
        .evt_row_i          (cmd_row_o),
        .bank_act_ready_o   (bank_act_ready),
        .bank_rdwr_ready_o  (bank_rdwr_ready),
        .bank_pre_ready_o   (bank_pre_ready),
        .bank_row_active_o  (bank_row_active),
        .bank_open_row_o    (bank_open_row),
        .bank_state_o       (bank_state_unused),
        // obs_* — packed into obs_words_o below for CSR readout.
        .obs_state_o        (),  // bank state — too wide; not in obs words
        .obs_act_cnt_nz_o   (obs_xbank_act_nz),
        .obs_rdwr_cnt_nz_o  (obs_xbank_rdwr_nz),
        .obs_pre_cnt_nz_o   (obs_xbank_pre_nz),
        .obs_rc_cnt_nz_o    (obs_xbank_rc_nz),
        .obs_ras_cnt_nz_o   (obs_xbank_ras_nz),
        .obs_ap_pending_o   (obs_xbank_ap_pending)
    );

    global_timers #(
        .NUM_RANKS (NUM_RANKS),
        .NUM_BANKS (NUM_BANKS)
    ) u_global_timers (
        .mc_clk           (mc_clk),
        .mc_rst_n         (mc_rst_n),
        .t_faw_i          (t_faw_i),
        .t_rrd_i          (t_rrd_i),
        .t_wtr_global_i   (t_wtr_i),
        .t_rtw_i          (t_rtp_i),
        .t_ccd_i          (8'd4),    // typical DDR2/LPDDR2 tCCD
        .evt_act_i        (evt_act),
        .evt_act_rank_i   (evt_rank),
        .evt_rd_i         (evt_rd),
        .evt_wr_i         (evt_wr),
        .tfaw_window_ok_o (tfaw_window_ok),
        .trrd_window_ok_o (trrd_window_ok_unused),
        .twtr_global_ok_o (twtr_global_ok_unused),
        .trtw_window_ok_o (trtw_window_ok_unused),
        .tccd_window_ok_o (tccd_window_ok_unused),
        .obs_faw_nz_o     (obs_gt_faw_nz),
        .obs_trrd_nz_o    (obs_gt_trrd_nz),
        .obs_twtr_nz_o    (obs_gt_twtr_nz),
        .obs_trtw_nz_o    (obs_gt_trtw_nz),
        .obs_tccd_nz_o    (obs_gt_tccd_nz)
    );

    logic                       refresh_drain_active_unused;
    logic                       refresh_kind_unused;
    logic [$clog2(NUM_BANKS)-1:0] refresh_bank_unused;

    refresh_ctrl #(
        .NUM_BANKS (NUM_BANKS)
    ) u_refresh_ctrl (
        .mc_clk                  (mc_clk),
        .mc_rst_n                (mc_rst_n),
        .t_refi_i                (t_refi_i),
        .refresh_burst_i         (4'd1),
        .refpb_mode_i            (1'b0),    // REFab default; LPDDR2 driver picks REFpb
        .enable_i                (init_done),
        .refresh_req_o           (refresh_req),
        .refresh_grant_i         (refresh_grant),
        .pending_refreshes_o     (pending_refreshes_unused),
        .refresh_drain_active_o  (refresh_drain_active_unused),
        .refresh_kind_o          (refresh_kind_unused),
        .refresh_bank_o          (refresh_bank_unused),
        // obs_* — packed into obs_words_o below.
        .obs_refi_cnt_o          (obs_refi_cnt),
        .obs_drain_remaining_o   (obs_refi_drain_remaining),
        .obs_bank_rotor_o        (obs_refi_bank_rotor),
        .obs_grants_total_o      (obs_refi_grants_total)
    );

    logic pdn_kind_unused;
    logic sref_active_unused;

    powerdown_ctrl #(
        .NUM_RANKS (NUM_RANKS),
        .CS_WIDTH  (DFI_CS_WIDTH)
    ) u_powerdown_ctrl (
        .mc_clk           (mc_clk),
        .mc_rst_n         (mc_rst_n),
        .idle_threshold_i (idle_threshold_i),
        .enable_pde_i     (enable_pde_i),
        .enable_sref_i    (enable_sref_i),
        .controller_idle_i(controller_idle_o),
        .pdn_req_o        (pdn_req),
        .pdn_kind_o       (pdn_kind_unused),
        .pdn_grant_i      (pdn_grant),
        .sref_active_o    (sref_active_unused),
        .dfi_cke_o        (dfi_cke_o),
        // obs_* — packed into obs_words_o below.
        .obs_state_o      (obs_pdn_state),
        .obs_idle_cnt_o   (obs_pdn_idle_cnt),
        .obs_grants_pde_o (obs_pdn_grants_pde),
        .obs_grants_sr_o  (obs_pdn_grants_sr)
    );

    mode_register #(
        .NUM_RANKS (NUM_RANKS)
    ) u_mode_register (
        .mc_clk          (mc_clk),
        .mc_rst_n        (mc_rst_n),
        .memtype_i       (memtype_i),
        .mr_we_i         (mr_load_we),
        .mr_index_i      (mr_load_index),
        .mr_data_i       (mr_load_data),
        .mr_rank_i       (mr_rank_i),
        .mr_req_o        (mr_req),
        .mr_grant_i      (mr_grant),
        .mr_req_index_o  (mr_req_index_unused),
        .mr_req_data_o   (mr_req_data_unused),
        .mr_req_rank_o   (),
        .cl_o            (cl_o),
        .cwl_o           (cwl_o),
        .bl_o            (bl_o),
        .al_o            (al_o),
        .drv_strength_o  (drv_strength_unused),
        .odt_o           (odt_unused)
    );

    init_sequencer u_init_sequencer (
        .mc_clk              (mc_clk),
        .mc_rst_n            (mc_rst_n),
        .memtype_i           (memtype_i),
        .dfi_init_start_o    (dfi_init_start_o),
        .dfi_init_complete_i (dfi_init_complete_i),
        .mr_seq_we_o         (mr_seq_we),
        .mr_seq_index_o      (mr_seq_index),
        .mr_seq_data_o       (mr_seq_data),
        .zqcl_req_o          (zqcl_req),
        .zqcl_grant_i        (zqcl_grant),
        .init_busy_o         (init_busy),
        .init_done_o         (init_done)
    );

    //=========================================================================
    // HAPPY page predictor — informs the scheduler whether each bank's
    // next access is likely to row-hit. Only consulted when PAGE_POLICY
    // == HAPPY_HYBRID; tied-off otherwise (the scheduler ignores).
    //=========================================================================
    page_predictor #(
        .NUM_RANKS (NUM_RANKS),
        .NUM_BANKS (NUM_BANKS),
        .ROW_WIDTH (RW)
    ) u_page_predictor (
        .mc_clk         (mc_clk),
        .mc_rst_n       (mc_rst_n),
        .evt_act_i      (evt_act),
        .evt_rank_i     (evt_rank),
        .evt_bank_i     (evt_bank),
        .evt_row_i      (cmd_row_o),
        .predict_open_o (predict_open)
    );

    wire unused = |{ bank_state_unused, drv_strength_unused, odt_unused,
                     bl_o,
                     mr_req_index_unused, mr_req_data_unused,
                     pending_refreshes_unused,
                     trrd_window_ok_unused, twtr_global_ok_unused,
                     trtw_window_ok_unused, tccd_window_ok_unused };

    //=========================================================================
    // obs_* packing into CSR words. Layout (NUM_RANKS=1, NUM_BANKS=8):
    //
    //   WORD 0  refresh_ctrl pt1: {drain_rem[3:0], bank_rotor[2:0], 9'b0,
    //                              refi_cnt[15:0]}
    //   WORD 1  refresh_ctrl pt2: {16'b0, grants_total[15:0]}
    //   WORD 2  powerdown_ctrl pt1: {13'b0, idle_cnt[15:0], state[2:0]}
    //   WORD 3  powerdown_ctrl pt2: {grants_sr[15:0], grants_pde[15:0]}
    //   WORD 4  global_timers + xbank_ap_pending:
    //           {16'b0, ap_pending[7:0], tccd_nz, trtw_nz, twtr_nz,
    //            trrd_nz, faw_nz, 3'b0}
    //   WORD 5  xbank part1: {rc_nz[7:0], pre_nz[7:0], rdwr_nz[7:0],
    //                          act_nz[7:0]}
    //   WORD 6  xbank part2: {24'b0, ras_nz[7:0]}
    //
    // Multi-rank/bank scaling: extra ranks fan out across additional
    // words. For now NUM_RANKS=1 ⇒ tight packing.
    //=========================================================================
    always_comb begin
        // Layout: pad | drain_rem(4) | bank_rotor(BA_W) | refi_cnt(16).
        // pad_width = 32 - 4 - $clog2(NUM_BANKS) - 16 = 12 - BA_W.
        obs_words_o[0] = {{(12-$clog2(NUM_BANKS)){1'b0}},
                          obs_refi_drain_remaining,
                          obs_refi_bank_rotor,
                          obs_refi_cnt};
        obs_words_o[1] = {16'b0, obs_refi_grants_total};
        obs_words_o[2] = {13'b0, obs_pdn_idle_cnt, obs_pdn_state};
        obs_words_o[3] = {obs_pdn_grants_sr, obs_pdn_grants_pde};
        obs_words_o[4] = {16'b0, obs_xbank_ap_pending[0],
                          obs_gt_tccd_nz, obs_gt_trtw_nz, obs_gt_twtr_nz,
                          obs_gt_trrd_nz[0], obs_gt_faw_nz[0], 3'b0};
        obs_words_o[5] = {obs_xbank_rc_nz[0], obs_xbank_pre_nz[0],
                          obs_xbank_rdwr_nz[0], obs_xbank_act_nz[0]};
        obs_words_o[6] = {24'b0, obs_xbank_ras_nz[0]};
    end

    // Status feed: init_sequencer + powerdown_ctrl exposing what the
    // CSR slave's STATUS register needs to surface to software.
    assign status_init_done_o = init_done;
    assign status_init_busy_o = init_busy;
    assign status_pdn_state_o = obs_pdn_state;

endmodule : command_scheduler_macro
