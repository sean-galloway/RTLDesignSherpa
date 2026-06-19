// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: ddr2_lpddr2_core_macro
// Purpose: Middle-layer macro that sits between `axi_frontend_macro` and
//          the DFI v2.1 PHY. Bundles the scheduler, per-bank/global
//          timers, refresh, power-down, init/MR engines, and the DFI
//          formatter/packer. This is the wrapper — all bodies live in
//          their fub/<name>_fub.sv files.
//
// Boundaries:
//          * Host side  → wires that pair with `axi_frontend_macro`
//                         backend ports (q_rank/bank/row, match vectors,
//                         beat_pull, b_complete, rd_inject, etc.)
//          * Memory side → DFI v2.1 Control + Write Data + Read Data
//                         + Status + Update sub-interfaces (Training
//                         deferred to a follow-on macro).
//
// Status:  SKELETON — wiring + tie-offs only. FUBs are stubs.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module ddr2_lpddr2_core_macro
    import ddr2_lpddr2_pkg::*;
#(
    // ----- host-side parameters (must match axi_frontend_macro) -----
    parameter int AXI_ID_WIDTH    = 4,
    parameter int AXI_DATA_WIDTH  = 64,
    parameter int NUM_RANKS       = 1,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int W_BUF_DEPTH     = 128,
    parameter int W_BUF_PTR_WIDTH = $clog2(W_BUF_DEPTH),
    parameter int WR_CAM_DEPTH    = 16,
    parameter int RD_CAM_DEPTH    = 16,

    // ----- DFI v2.1 widths -----
    parameter int DFI_ADDR_WIDTH  = 14,
    parameter int DFI_BANK_WIDTH  = 3,
    parameter int DFI_CTRL_WIDTH  = 1,
    parameter int DFI_CS_WIDTH    = NUM_RANKS,
    parameter int DFI_DATA_WIDTH  = AXI_DATA_WIDTH,
    parameter int DFI_STRB_WIDTH  = DFI_DATA_WIDTH / 8,
    parameter int DFI_VALID_WIDTH = 1,
    parameter int DFI_EN_WIDTH    = 1,

    // ----- aliases -----
    parameter int IW  = AXI_ID_WIDTH,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int RW  = ROW_WIDTH,
    parameter int CW  = COL_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int WPW = W_BUF_PTR_WIDTH,
    parameter int WSL = $clog2(WR_CAM_DEPTH),
    parameter int RSL = $clog2(RD_CAM_DEPTH)
) (
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,

    // ----- runtime config (CSR-ish; could be APB later) -----
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

    // MR write port — APB/CSR-style
    input  logic                       mr_we_i,
    input  logic [4:0]                 mr_index_i,
    input  logic [15:0]                mr_data_i,
    input  logic [RKW-1:0]             mr_rank_i,

    //=========================================================================
    // HOST-SIDE — pairs with axi_frontend_macro backend ports
    //=========================================================================

    // CAM query (this macro drives, frontend responds combinationally)
    output logic [RKW-1:0]             q_rank_o,
    output logic [BKW-1:0]             q_bank_o,
    output logic [RW-1:0]              q_row_o,
    input  logic [WR_CAM_DEPTH-1:0]    wr_match_pending_i,
    input  logic [WR_CAM_DEPTH-1:0]    wr_match_rowhit_i,
    input  logic [RD_CAM_DEPTH-1:0]    rd_match_pending_i,
    input  logic [RD_CAM_DEPTH-1:0]    rd_match_rowhit_i,

    // CAM snapshot metadata (combinational from frontend)
    input  logic [WR_CAM_DEPTH-1:0][CW-1:0]  wr_snap_col_i,
    input  logic [WR_CAM_DEPTH-1:0][BLW-1:0] wr_snap_len_i,
    input  logic [RD_CAM_DEPTH-1:0][CW-1:0]  rd_snap_col_i,
    input  logic [RD_CAM_DEPTH-1:0][BLW-1:0] rd_snap_len_i,
    input  logic [RD_CAM_DEPTH-1:0][IW-1:0]  rd_snap_id_i,

    // mark-issued back to CAMs
    output logic                       wr_issued_we_o,
    output logic [WSL-1:0]             wr_issued_slot_o,
    output logic                       rd_issued_we_o,
    output logic [RSL-1:0]             rd_issued_slot_o,

    // w_buf pull (write data path side)
    output logic                       beat_pull_strb_o,
    output logic [WSL-1:0]             beat_pull_slot_o,
    input  logic [WPW-1:0]             beat_pull_ptr_i,
    input  logic [WPW-1:0]             beat_pull_strb_ptr_i,
    input  logic                       beat_pull_last_i,
    input  logic [DFI_DATA_WIDTH-1:0]  wbuf_rd_data_i,
    input  logic [DFI_STRB_WIDTH-1:0]  wbuf_rd_strb_i,

    // b_complete back to wr CAM
    output logic                       b_complete_strb_o,
    output logic [WSL-1:0]             b_complete_slot_o,

    // rd-beat strobe + rd_inject path (read data path side)
    output logic                       rd_beat_we_o,
    output logic [RSL-1:0]             rd_beat_slot_o,
    output logic                       rd_inject_valid_o,
    input  logic                       rd_inject_ready_i,
    output logic [IW-1:0]              rd_inject_id_o,
    output logic [DFI_DATA_WIDTH-1:0]  rd_inject_data_o,
    output logic                       rd_inject_last_o,

    //=========================================================================
    // MEMORY-SIDE — DFI v2.1
    //=========================================================================

    // Control Interface
    output logic [DFI_ADDR_WIDTH-1:0]  dfi_address_o,
    output logic [DFI_BANK_WIDTH-1:0]  dfi_bank_o,
    output logic [DFI_CTRL_WIDTH-1:0]  dfi_cas_n_o,
    output logic [DFI_CTRL_WIDTH-1:0]  dfi_ras_n_o,
    output logic [DFI_CTRL_WIDTH-1:0]  dfi_we_n_o,
    output logic [DFI_CS_WIDTH-1:0]    dfi_cs_n_o,
    output logic [DFI_CS_WIDTH-1:0]    dfi_cke_o,
    output logic [DFI_CS_WIDTH-1:0]    dfi_odt_o,

    // Write Data Interface
    output logic [DFI_DATA_WIDTH-1:0]  dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]  dfi_wrdata_mask_o,

    // Read Data Interface
    output logic [DFI_EN_WIDTH-1:0]    dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]  dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0] dfi_rddata_valid_i,

    // Status Interface
    output logic [DFI_CS_WIDTH-1:0]    dfi_dram_clk_disable_o,
    output logic                       dfi_init_start_o,
    input  logic                       dfi_init_complete_i,

    // Update Interface (MC-initiated; PHY-initiated deferred)
    output logic                       dfi_ctrlupd_req_o,
    input  logic                       dfi_ctrlupd_ack_i,
    input  logic                       dfi_phyupd_req_i,
    output logic                       dfi_phyupd_ack_o,
    input  logic [1:0]                 dfi_phyupd_type_i
);

    //=========================================================================
    // Internal nets
    //=========================================================================

    // scheduler ↔ timers
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                bank_act_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                bank_rdwr_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                bank_pre_ready;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                bank_row_active;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][RW-1:0]        bank_open_row;
    bank_state_e [NUM_RANKS-1:0][NUM_BANKS-1:0]         bank_state_unused;
    logic                                               tfaw_window_ok;

    // scheduler ↔ refresh / pdn / init / MR
    logic                                               refresh_req;
    logic                                               refresh_grant;
    logic                                               pdn_req;
    logic                                               pdn_grant;
    logic                                               init_busy;
    logic                                               init_done;
    logic                                               mr_req;
    logic                                               mr_grant;

    // scheduler → cmd_formatter
    logic                                               cmd_valid;
    logic                                               cmd_ready;
    dram_op_e                                           cmd_op;
    logic [RKW-1:0]                                     cmd_rank;
    logic [BKW-1:0]                                     cmd_bank;
    logic [RW-1:0]                                      cmd_row;
    logic [CW-1:0]                                      cmd_col;
    logic [BLW-1:0]                                     cmd_len;
    logic [WSL-1:0]                                     cmd_wr_slot;
    logic [RSL-1:0]                                     cmd_rd_slot;

    // scheduler → wr_beat_sequencer / rd_cl_aligner op handshakes
    // Wired directly off the scheduler's cmd channel for the skeleton —
    // a real implementation may split via an issue-fanout fub.
    logic                                               wr_op_valid;
    logic                                               wr_op_ready;
    logic                                               rd_op_valid;
    logic                                               rd_op_ready;

    // mode register live values
    logic [3:0]                                         cl_val;
    logic [3:0]                                         cwl_val;
    logic [3:0]                                         bl_val;
    logic [3:0]                                         al_val;
    logic [1:0]                                         drv_strength_val;
    logic [1:0]                                         odt_val;

    // mode register sequenced injection (from init_sequencer)
    logic                                               mr_seq_we;
    logic [4:0]                                         mr_seq_index;
    logic [15:0]                                        mr_seq_data;
    logic                                               zqcl_req;
    logic                                               zqcl_grant;

    // bank-event strobes
    logic                                               evt_act, evt_rd, evt_wr, evt_pre;
    logic [RKW-1:0]                                     evt_rank;
    logic [BKW-1:0]                                     evt_bank;

    // pre-pack DFI nets from cmd_formatter / wr_beat / rd_cl
    logic [DFI_ADDR_WIDTH-1:0]                          pre_dfi_address;
    logic [DFI_BANK_WIDTH-1:0]                          pre_dfi_bank;
    logic [DFI_CTRL_WIDTH-1:0]                          pre_dfi_cas_n;
    logic [DFI_CTRL_WIDTH-1:0]                          pre_dfi_ras_n;
    logic [DFI_CTRL_WIDTH-1:0]                          pre_dfi_we_n;
    logic [DFI_CS_WIDTH-1:0]                            pre_dfi_cs_n;
    logic [DFI_CS_WIDTH-1:0]                            pre_dfi_cke;
    logic [DFI_CS_WIDTH-1:0]                            pre_dfi_odt;
    logic [DFI_DATA_WIDTH-1:0]                          pre_dfi_wrdata;
    logic [DFI_EN_WIDTH-1:0]                            pre_dfi_wrdata_en;
    logic [DFI_STRB_WIDTH-1:0]                          pre_dfi_wrdata_mask;
    logic [DFI_EN_WIDTH-1:0]                            pre_dfi_rddata_en;

    // MR-load multiplex: prefer init sequencer's stream, fall back to CSR
    logic                                               mr_load_we;
    logic [4:0]                                         mr_load_index;
    logic [15:0]                                        mr_load_data;
    assign mr_load_we    = mr_seq_we | mr_we_i;
    assign mr_load_index = mr_seq_we ? mr_seq_index : mr_index_i;
    assign mr_load_data  = mr_seq_we ? mr_seq_data  : mr_data_i;

    // For the skeleton, wr/rd op handshakes are simple fanouts of the
    // scheduler's cmd channel; a real implementation will route based on
    // cmd_op (WR/WRA vs RD/RDA).
    assign wr_op_valid = cmd_valid && ((cmd_op == OP_WR) || (cmd_op == OP_WRA));
    assign rd_op_valid = cmd_valid && ((cmd_op == OP_RD) || (cmd_op == OP_RDA));
    assign cmd_ready   = wr_op_valid ? wr_op_ready
                       : rd_op_valid ? rd_op_ready
                                     : 1'b1;

    // rd_inject ID lookup — keyed off the active RD CAM slot at op issue.
    // For the skeleton this comes from rd_snap_id_i indexed by cmd_rd_slot;
    // the real implementation tracks this via the rd_cl_aligner's queue.
    logic [IW-1:0] rd_active_id;
    assign rd_active_id = rd_snap_id_i[cmd_rd_slot];

    //=========================================================================
    // FUB instantiations
    //=========================================================================

    scheduler_fub #(
        .WR_CAM_DEPTH    (WR_CAM_DEPTH),
        .RD_CAM_DEPTH    (RD_CAM_DEPTH),
        .NUM_RANKS       (NUM_RANKS),
        .NUM_BANKS       (NUM_BANKS),
        .ROW_WIDTH       (RW),
        .COL_WIDTH       (CW),
        .BURST_LEN_WIDTH (BLW),
        .AXI_ID_WIDTH    (IW)
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
        .wr_snap_col_i      (wr_snap_col_i),
        .wr_snap_len_i      (wr_snap_len_i),
        .rd_snap_col_i      (rd_snap_col_i),
        .rd_snap_len_i      (rd_snap_len_i),
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
        .refresh_req_i      (refresh_req),
        .refresh_grant_o    (refresh_grant),
        .pdn_req_i          (pdn_req),
        .pdn_grant_o        (pdn_grant),
        .init_busy_i        (init_busy),
        .mr_req_i           (mr_req),
        .mr_grant_o         (mr_grant),
        .cmd_valid_o        (cmd_valid),
        .cmd_ready_i        (cmd_ready),
        .cmd_op_o           (cmd_op),
        .cmd_rank_o         (cmd_rank),
        .cmd_bank_o         (cmd_bank),
        .cmd_row_o          (cmd_row),
        .cmd_col_o          (cmd_col),
        .cmd_len_o          (cmd_len),
        .cmd_wr_slot_o      (cmd_wr_slot),
        .cmd_rd_slot_o      (cmd_rd_slot),
        .evt_act_o          (evt_act),
        .evt_rd_o           (evt_rd),
        .evt_wr_o           (evt_wr),
        .evt_pre_o          (evt_pre),
        .evt_rank_o         (evt_rank),
        .evt_bank_o         (evt_bank)
    );

    xbank_timers_fub #(
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
        .evt_rank_i         (evt_rank),
        .evt_bank_i         (evt_bank),
        .evt_row_i          (cmd_row),
        .bank_act_ready_o   (bank_act_ready),
        .bank_rdwr_ready_o  (bank_rdwr_ready),
        .bank_pre_ready_o   (bank_pre_ready),
        .bank_row_active_o  (bank_row_active),
        .bank_open_row_o    (bank_open_row),
        .bank_state_o       (bank_state_unused)
    );

    logic trrd_unused, twtr_unused, trtw_unused;
    global_timers_fub #(
        .NUM_RANKS (NUM_RANKS),
        .NUM_BANKS (NUM_BANKS)
    ) u_global_timers (
        .mc_clk           (mc_clk),
        .mc_rst_n         (mc_rst_n),
        .t_faw_i          (t_faw_i),
        .t_rrd_i          (t_rrd_i),
        .t_wtr_global_i   (t_wtr_i),
        .t_rtw_i          (t_rtp_i),
        .evt_act_i        (evt_act),
        .evt_act_rank_i   (evt_rank),
        .evt_rd_i         (evt_rd),
        .evt_wr_i         (evt_wr),
        .tfaw_window_ok_o (tfaw_window_ok),
        .trrd_window_ok_o (trrd_unused),
        .twtr_global_ok_o (twtr_unused),
        .trtw_window_ok_o (trtw_unused)
    );

    logic [3:0] pending_refreshes_unused;
    refresh_ctrl_fub u_refresh_ctrl (
        .mc_clk              (mc_clk),
        .mc_rst_n            (mc_rst_n),
        .t_refi_i            (t_refi_i),
        .refresh_burst_i     (4'd1),
        .enable_i            (init_done),
        .refresh_req_o       (refresh_req),
        .refresh_grant_i     (refresh_grant),
        .pending_refreshes_o (pending_refreshes_unused)
    );

    powerdown_ctrl_fub #(
        .NUM_RANKS (NUM_RANKS),
        .CS_WIDTH  (DFI_CS_WIDTH)
    ) u_powerdown_ctrl (
        .mc_clk           (mc_clk),
        .mc_rst_n         (mc_rst_n),
        .idle_threshold_i (idle_threshold_i),
        .enable_pde_i     (enable_pde_i),
        .enable_sref_i    (enable_sref_i),
        .controller_idle_i(~cmd_valid),
        .pdn_req_o        (pdn_req),
        .pdn_grant_i      (pdn_grant),
        .dfi_cke_o        (pre_dfi_cke)
    );

    logic        mr_seq_we_unused;
    logic [4:0]  mr_seq_index_unused;
    logic [15:0] mr_seq_data_unused;
    mode_register_fub #(
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
        .mr_req_index_o  (mr_seq_index_unused),
        .mr_req_data_o   (mr_seq_data_unused),
        .mr_req_rank_o   (),
        .cl_o            (cl_val),
        .cwl_o           (cwl_val),
        .bl_o            (bl_val),
        .al_o            (al_val),
        .drv_strength_o  (drv_strength_val),
        .odt_o           (odt_val)
    );

    init_sequencer_fub u_init_sequencer (
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
    assign zqcl_grant = 1'b1;   // until the scheduler arbitrates ZQCL

    wr_beat_sequencer_fub #(
        .WR_CAM_DEPTH    (WR_CAM_DEPTH),
        .W_BUF_PTR_WIDTH (WPW),
        .BURST_LEN_WIDTH (BLW),
        .DFI_DATA_WIDTH  (DFI_DATA_WIDTH),
        .DFI_STRB_WIDTH  (DFI_STRB_WIDTH),
        .DFI_EN_WIDTH    (DFI_EN_WIDTH)
    ) u_wr_beat_sequencer (
        .mc_clk               (mc_clk),
        .mc_rst_n             (mc_rst_n),
        .cwl_i                (cwl_val),
        .op_valid_i           (wr_op_valid),
        .op_ready_o           (wr_op_ready),
        .op_slot_i            (cmd_wr_slot),
        .op_len_i             (cmd_len),
        .beat_pull_strb_o     (beat_pull_strb_o),
        .beat_pull_slot_o     (beat_pull_slot_o),
        .beat_pull_ptr_i      (beat_pull_ptr_i),
        .beat_pull_strb_ptr_i (beat_pull_strb_ptr_i),
        .beat_pull_last_i     (beat_pull_last_i),
        .wbuf_rd_data_i       (wbuf_rd_data_i),
        .wbuf_rd_strb_i       (wbuf_rd_strb_i),
        .dfi_wrdata_o         (pre_dfi_wrdata),
        .dfi_wrdata_en_o      (pre_dfi_wrdata_en),
        .dfi_wrdata_mask_o    (pre_dfi_wrdata_mask),
        .b_complete_strb_o    (b_complete_strb_o),
        .b_complete_slot_o    (b_complete_slot_o)
    );

    rd_cl_aligner_fub #(
        .RD_CAM_DEPTH    (RD_CAM_DEPTH),
        .AXI_ID_WIDTH    (IW),
        .BURST_LEN_WIDTH (BLW),
        .DFI_DATA_WIDTH  (DFI_DATA_WIDTH),
        .DFI_VALID_WIDTH (DFI_VALID_WIDTH),
        .DFI_EN_WIDTH    (DFI_EN_WIDTH)
    ) u_rd_cl_aligner (
        .mc_clk             (mc_clk),
        .mc_rst_n           (mc_rst_n),
        .cl_i               (cl_val),
        .al_i               (al_val),
        .op_valid_i         (rd_op_valid),
        .op_ready_o         (rd_op_ready),
        .op_slot_i          (cmd_rd_slot),
        .op_id_i            (rd_active_id),
        .op_len_i           (cmd_len),
        .dfi_rddata_en_o    (pre_dfi_rddata_en),
        .dfi_rddata_i       (dfi_rddata_i),
        .dfi_rddata_valid_i (dfi_rddata_valid_i),
        .rd_inject_valid_o  (rd_inject_valid_o),
        .rd_inject_ready_i  (rd_inject_ready_i),
        .rd_inject_id_o     (rd_inject_id_o),
        .rd_inject_data_o   (rd_inject_data_o),
        .rd_inject_last_o   (rd_inject_last_o),
        .rd_beat_we_o       (rd_beat_we_o),
        .rd_beat_slot_o     (rd_beat_slot_o)
    );

    dfi_cmd_formatter_fub #(
        .NUM_RANKS       (NUM_RANKS),
        .NUM_BANKS       (NUM_BANKS),
        .ROW_WIDTH       (RW),
        .COL_WIDTH       (CW),
        .BURST_LEN_WIDTH (BLW),
        .DFI_ADDR_WIDTH  (DFI_ADDR_WIDTH),
        .DFI_BANK_WIDTH  (DFI_BANK_WIDTH),
        .DFI_CTRL_WIDTH  (DFI_CTRL_WIDTH),
        .DFI_CS_WIDTH    (DFI_CS_WIDTH)
    ) u_dfi_cmd_formatter (
        .mc_clk        (mc_clk),
        .mc_rst_n      (mc_rst_n),
        .memtype_i     (memtype_i),
        .cmd_valid_i   (cmd_valid),
        .cmd_ready_o   (),
        .cmd_op_i      (cmd_op),
        .cmd_rank_i    (cmd_rank),
        .cmd_bank_i    (cmd_bank),
        .cmd_row_i     (cmd_row),
        .cmd_col_i     (cmd_col),
        .cmd_len_i     (cmd_len),
        .dfi_address_o (pre_dfi_address),
        .dfi_bank_o    (pre_dfi_bank),
        .dfi_cas_n_o   (pre_dfi_cas_n),
        .dfi_ras_n_o   (pre_dfi_ras_n),
        .dfi_we_n_o    (pre_dfi_we_n),
        .dfi_cs_n_o    (pre_dfi_cs_n),
        .dfi_odt_o     (pre_dfi_odt)
    );

    dfi_signal_pack_fub #(
        .NUM_RANKS       (NUM_RANKS),
        .DFI_ADDR_WIDTH  (DFI_ADDR_WIDTH),
        .DFI_BANK_WIDTH  (DFI_BANK_WIDTH),
        .DFI_CTRL_WIDTH  (DFI_CTRL_WIDTH),
        .DFI_CS_WIDTH    (DFI_CS_WIDTH),
        .DFI_DATA_WIDTH  (DFI_DATA_WIDTH),
        .DFI_STRB_WIDTH  (DFI_STRB_WIDTH),
        .DFI_VALID_WIDTH (DFI_VALID_WIDTH),
        .DFI_EN_WIDTH    (DFI_EN_WIDTH)
    ) u_dfi_signal_pack (
        .mc_clk                 (mc_clk),
        .mc_rst_n               (mc_rst_n),
        .i_address              (pre_dfi_address),
        .i_bank                 (pre_dfi_bank),
        .i_cas_n                (pre_dfi_cas_n),
        .i_ras_n                (pre_dfi_ras_n),
        .i_we_n                 (pre_dfi_we_n),
        .i_cs_n                 (pre_dfi_cs_n),
        .i_cke                  (pre_dfi_cke),
        .i_odt                  (pre_dfi_odt),
        .i_wrdata               (pre_dfi_wrdata),
        .i_wrdata_en            (pre_dfi_wrdata_en),
        .i_wrdata_mask          (pre_dfi_wrdata_mask),
        .i_rddata_en            (pre_dfi_rddata_en),
        .dfi_address_o          (dfi_address_o),
        .dfi_bank_o             (dfi_bank_o),
        .dfi_cas_n_o            (dfi_cas_n_o),
        .dfi_ras_n_o            (dfi_ras_n_o),
        .dfi_we_n_o             (dfi_we_n_o),
        .dfi_cs_n_o             (dfi_cs_n_o),
        .dfi_cke_o              (dfi_cke_o),
        .dfi_odt_o              (dfi_odt_o),
        .dfi_wrdata_o           (dfi_wrdata_o),
        .dfi_wrdata_en_o        (dfi_wrdata_en_o),
        .dfi_wrdata_mask_o      (dfi_wrdata_mask_o),
        .dfi_rddata_en_o        (dfi_rddata_en_o),
        .dfi_dram_clk_disable_o (dfi_dram_clk_disable_o)
    );

    // ----- Update interface — tied off until ctrl_update_fub lands -----
    assign dfi_ctrlupd_req_o = 1'b0;
    assign dfi_phyupd_ack_o  = 1'b0;

    wire unused = |{ bank_state_unused, drv_strength_val, odt_val, bl_val,
                     mr_seq_we_unused, mr_seq_index_unused, mr_seq_data_unused,
                     trrd_unused, twtr_unused, trtw_unused,
                     pending_refreshes_unused,
                     dfi_ctrlupd_ack_i, dfi_phyupd_req_i, dfi_phyupd_type_i };

endmodule : ddr2_lpddr2_core_macro
