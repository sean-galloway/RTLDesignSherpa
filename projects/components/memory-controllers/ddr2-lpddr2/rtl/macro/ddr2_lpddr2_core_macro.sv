// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: ddr2_lpddr2_core_macro
// Purpose: Mid-layer wrapper that sits between `axi_frontend_macro` and
//          the DFI v2.1 PHY. Thin top-level: instantiates the three
//          sub-macros and wires them to each other + to the boundary.
//
// Hierarchy:
//          ddr2_lpddr2_core_macro
//          ├── command_scheduler_macro   (7 FUBs — what to issue)
//          ├── data_path_macro           (2 FUBs — W/R beat sequencing)
//          └── dfi_v21_interface_macro   (2 FUBs — DFI v2.1 wire pack)
//
// Status:  SKELETON wrapper — FUB bodies remain stubs.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module ddr2_lpddr2_core_macro
    import ddr2_lpddr2_pkg::*;
#(
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
    parameter int PAGE_POLICY     = 32'(PAGE_POLICY_CLOSE),

    parameter int DRAM_BEAT_WIDTH = AXI_DATA_WIDTH,
    parameter int DFI_RATE        = 2,
    parameter int DRAM_STRB_WIDTH = DRAM_BEAT_WIDTH / 8,
    parameter int MAX_BURST_LEN   = 256,

    // Per-phase DFI widths (multi-phase bus widths are × DFI_RATE)
    parameter int DFI_ADDR_WIDTH  = 14,
    parameter int DFI_BANK_WIDTH  = 3,
    parameter int DFI_CTRL_WIDTH  = 1,
    parameter int DFI_CS_WIDTH    = NUM_RANKS,
    parameter int DFI_ADDR_BUS_W  = DFI_ADDR_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W  = DFI_BANK_WIDTH * DFI_RATE,
    parameter int DFI_CTRL_BUS_W  = DFI_CTRL_WIDTH * DFI_RATE,
    parameter int DFI_CS_BUS_W    = DFI_CS_WIDTH * DFI_RATE,
    parameter int DFI_DATA_WIDTH  = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DFI_STRB_WIDTH  = DFI_DATA_WIDTH / 8,
    parameter int DFI_VALID_WIDTH = 1,
    parameter int DFI_EN_WIDTH    = 1,

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

    input  logic                       mr_we_i,
    input  logic [4:0]                 mr_index_i,
    input  logic [15:0]                mr_data_i,
    input  logic [RKW-1:0]             mr_rank_i,

    // ---- PHY timing (DFI Initialization Status Register-derived) ----
    input  logic [7:0]                 t_phy_wrlat_i,
    input  logic [7:0]                 t_rddata_en_i,

    // ---- read ordering: 1 = strict issue order across IDs (v2 only) ----
    input  logic                       rd_in_order_i,

    //=========================================================================
    // HOST-SIDE — pairs with axi_frontend_macro backend ports
    //=========================================================================

    output logic [RKW-1:0]             q_rank_o,
    output logic [BKW-1:0]             q_bank_o,
    output logic [RW-1:0]              q_row_o,
    input  logic [WR_CAM_DEPTH-1:0]    wr_match_pending_i,
    input  logic [WR_CAM_DEPTH-1:0]    wr_match_rowhit_i,
    input  logic [RD_CAM_DEPTH-1:0]    rd_match_pending_i,
    input  logic [RD_CAM_DEPTH-1:0]    rd_match_rowhit_i,

    input  logic [WR_CAM_DEPTH-1:0][RKW-1:0] wr_snap_rank_i,
    input  logic [WR_CAM_DEPTH-1:0][BKW-1:0] wr_snap_bank_i,
    input  logic [WR_CAM_DEPTH-1:0][RW-1:0]  wr_snap_row_i,
    input  logic [WR_CAM_DEPTH-1:0][CW-1:0]  wr_snap_col_i,
    input  logic [WR_CAM_DEPTH-1:0][BLW-1:0] wr_snap_len_i,
    input  logic [RD_CAM_DEPTH-1:0][RKW-1:0] rd_snap_rank_i,
    input  logic [RD_CAM_DEPTH-1:0][BKW-1:0] rd_snap_bank_i,
    input  logic [RD_CAM_DEPTH-1:0][RW-1:0]  rd_snap_row_i,
    input  logic [RD_CAM_DEPTH-1:0][CW-1:0]  rd_snap_col_i,
    input  logic [RD_CAM_DEPTH-1:0][BLW-1:0] rd_snap_len_i,
    input  logic [RD_CAM_DEPTH-1:0][IW-1:0]  rd_snap_id_i,

    output logic                       wr_issued_we_o,
    output logic [WSL-1:0]             wr_issued_slot_o,
    output logic                       rd_issued_we_o,
    output logic [RSL-1:0]             rd_issued_slot_o,

    output logic                       beat_pull_strb_o,
    output logic [WSL-1:0]             beat_pull_slot_o,
    input  logic [WPW-1:0]             beat_pull_ptr_i,
    input  logic [WPW-1:0]             beat_pull_strb_ptr_i,
    input  logic                       beat_pull_last_i,
    // wbuf_rd_data is one DRAM beat at a time (axi_frontend's
    // wbuf_ext_rd port is a single-beat combinational read).
    input  logic [DRAM_BEAT_WIDTH-1:0] wbuf_rd_data_i,
    input  logic [DRAM_STRB_WIDTH-1:0] wbuf_rd_strb_i,

    output logic                       b_complete_strb_o,
    output logic [WSL-1:0]             b_complete_slot_o,

    output logic                       rd_beat_we_o,
    output logic [RSL-1:0]             rd_beat_slot_o,
    output logic                       rd_inject_valid_o,
    input  logic                       rd_inject_ready_i,
    output logic [IW-1:0]              rd_inject_id_o,
    // rd_inject is one DRAM beat per cycle to the axi_frontend R FSM.
    output logic [DRAM_BEAT_WIDTH-1:0] rd_inject_data_o,
    output logic                       rd_inject_last_o,

    //=========================================================================
    // MEMORY-SIDE — DFI v2.1
    //=========================================================================

    // Multi-phase DFI control bus (per-phase × DFI_RATE).
    output logic [DFI_ADDR_BUS_W-1:0]  dfi_address_o,
    output logic [DFI_BANK_BUS_W-1:0]  dfi_bank_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_cas_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_ras_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_we_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_cs_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_cke_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_odt_o,

    output logic [DFI_DATA_WIDTH-1:0]  dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]  dfi_wrdata_mask_o,

    output logic [DFI_EN_WIDTH-1:0]    dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]  dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0] dfi_rddata_valid_i,

    output logic [DFI_CS_BUS_W-1:0]    dfi_dram_clk_disable_o,
    output logic                       dfi_init_start_o,
    input  logic                       dfi_init_complete_i,

    output logic                       dfi_ctrlupd_req_o,
    input  logic                       dfi_ctrlupd_ack_i,
    input  logic                       dfi_phyupd_req_i,
    output logic                       dfi_phyupd_ack_o,
    input  logic [1:0]                 dfi_phyupd_type_i
);

    //=========================================================================
    // Inter-macro nets
    //=========================================================================

    // command_scheduler ↔ dfi_interface (cmd channel)
    logic                       cmd_valid;
    logic                       cmd_ready;
    dram_op_e                   cmd_op;
    logic [RKW-1:0]             cmd_rank;
    logic [BKW-1:0]             cmd_bank;
    logic [RW-1:0]              cmd_row;
    logic [CW-1:0]              cmd_col;
    logic [BLW-1:0]             cmd_len;
    logic [WSL-1:0]             cmd_wr_slot;
    logic [RSL-1:0]             cmd_rd_slot;

    // command_scheduler → data_path (live MR + CKE)
    logic [3:0]                 cl_val;
    logic [3:0]                 cwl_val;
    logic [3:0]                 bl_val;
    logic [3:0]                 al_val;
    logic [DFI_CS_WIDTH-1:0]    pre_dfi_cke;

    // wr / rd op fanout (top-level split based on cmd_op)
    logic                       wr_op_valid;
    logic                       wr_op_ready;
    logic                       rd_op_valid;
    logic                       rd_op_ready;
    logic [IW-1:0]              rd_op_id;

    assign wr_op_valid = cmd_valid && ((cmd_op == OP_WR) || (cmd_op == OP_WRA));
    assign rd_op_valid = cmd_valid && ((cmd_op == OP_RD) || (cmd_op == OP_RDA));

    // cmd_ready merges the active consumer's ready. For non-WR/RD ops
    // (NOP/ACT/PRE/REF/MRS/ZQCL/...) the dfi_interface alone gates it.
    logic dfi_cmd_ready;
    assign cmd_ready = wr_op_valid ? (wr_op_ready & dfi_cmd_ready)
                     : rd_op_valid ? (rd_op_ready & dfi_cmd_ready)
                                   : dfi_cmd_ready;

    // rd_op_id is looked up via rd_snap_id_i indexed by cmd_rd_slot
    // (the rd_cl_aligner will eventually keep its own slot→id tracker).
    assign rd_op_id = rd_snap_id_i[cmd_rd_slot];

    // data_path → dfi_interface (pre-pack data nets)
    logic [DFI_DATA_WIDTH-1:0]  pre_dfi_wrdata;
    logic [DFI_EN_WIDTH-1:0]    pre_dfi_wrdata_en;
    logic [DFI_STRB_WIDTH-1:0]  pre_dfi_wrdata_mask;
    logic [DFI_EN_WIDTH-1:0]    pre_dfi_rddata_en;

    logic                       controller_idle_unused;

    // obs_* CSR words from command_scheduler_macro (see docs/csr_obs_layout.md)
    logic [6:0][31:0]           cmd_obs_words;

    //=========================================================================
    // Sub-macros
    //=========================================================================

    command_scheduler_macro #(
        .AXI_ID_WIDTH    (IW),
        .NUM_RANKS       (NUM_RANKS),
        .NUM_BANKS       (NUM_BANKS),
        .ROW_WIDTH       (RW),
        .COL_WIDTH       (CW),
        .BURST_LEN_WIDTH (BLW),
        .WR_CAM_DEPTH    (WR_CAM_DEPTH),
        .RD_CAM_DEPTH    (RD_CAM_DEPTH),
        .DFI_CS_WIDTH    (DFI_CS_WIDTH),
        .PAGE_POLICY     (PAGE_POLICY)
    ) u_command_scheduler (
        .mc_clk              (mc_clk),
        .mc_rst_n            (mc_rst_n),
        .memtype_i           (memtype_i),
        .t_refi_i            (t_refi_i),
        .t_rcd_i             (t_rcd_i),
        .t_rp_i              (t_rp_i),
        .t_ras_i             (t_ras_i),
        .t_rc_i              (t_rc_i),
        .t_wr_i              (t_wr_i),
        .t_wtr_i             (t_wtr_i),
        .t_rtp_i             (t_rtp_i),
        .t_faw_i             (t_faw_i),
        .t_rrd_i             (t_rrd_i),
        .idle_threshold_i    (idle_threshold_i),
        .enable_pde_i        (enable_pde_i),
        .enable_sref_i       (enable_sref_i),
        .mr_we_i             (mr_we_i),
        .mr_index_i          (mr_index_i),
        .mr_data_i           (mr_data_i),
        .mr_rank_i           (mr_rank_i),
        .q_rank_o            (q_rank_o),
        .q_bank_o            (q_bank_o),
        .q_row_o             (q_row_o),
        .wr_match_pending_i  (wr_match_pending_i),
        .wr_match_rowhit_i   (wr_match_rowhit_i),
        .rd_match_pending_i  (rd_match_pending_i),
        .rd_match_rowhit_i   (rd_match_rowhit_i),
        .wr_snap_rank_i      (wr_snap_rank_i),
        .wr_snap_bank_i      (wr_snap_bank_i),
        .wr_snap_row_i       (wr_snap_row_i),
        .wr_snap_col_i       (wr_snap_col_i),
        .wr_snap_len_i       (wr_snap_len_i),
        .rd_snap_rank_i      (rd_snap_rank_i),
        .rd_snap_bank_i      (rd_snap_bank_i),
        .rd_snap_row_i       (rd_snap_row_i),
        .rd_snap_col_i       (rd_snap_col_i),
        .rd_snap_len_i       (rd_snap_len_i),
        .wr_issued_we_o      (wr_issued_we_o),
        .wr_issued_slot_o    (wr_issued_slot_o),
        .rd_issued_we_o      (rd_issued_we_o),
        .rd_issued_slot_o    (rd_issued_slot_o),
        .cmd_valid_o         (cmd_valid),
        .cmd_ready_i         (cmd_ready),
        .cmd_op_o            (cmd_op),
        .cmd_rank_o          (cmd_rank),
        .cmd_bank_o          (cmd_bank),
        .cmd_row_o           (cmd_row),
        .cmd_col_o           (cmd_col),
        .cmd_len_o           (cmd_len),
        .cmd_wr_slot_o       (cmd_wr_slot),
        .cmd_rd_slot_o       (cmd_rd_slot),
        .cl_o                (cl_val),
        .cwl_o               (cwl_val),
        .bl_o                (bl_val),
        .al_o                (al_val),
        .dfi_init_start_o    (dfi_init_start_o),
        .dfi_init_complete_i (dfi_init_complete_i),
        .dfi_cke_o           (pre_dfi_cke),
        .controller_idle_o   (controller_idle_unused),
        // obs_* — packed CSR readout words (F1 will route up to APB slave)
        .obs_words_o         (cmd_obs_words)
    );

    data_path_macro #(
        .AXI_ID_WIDTH    (IW),
        .WR_CAM_DEPTH    (WR_CAM_DEPTH),
        .RD_CAM_DEPTH    (RD_CAM_DEPTH),
        .W_BUF_PTR_WIDTH (WPW),
        .BURST_LEN_WIDTH (BLW),
        .DRAM_BEAT_WIDTH (DRAM_BEAT_WIDTH),
        .DFI_RATE        (DFI_RATE),
        .DFI_DATA_WIDTH  (DFI_DATA_WIDTH),
        .DRAM_STRB_WIDTH (DRAM_STRB_WIDTH),
        .DFI_STRB_WIDTH  (DFI_STRB_WIDTH),
        .DFI_VALID_WIDTH (DFI_VALID_WIDTH),
        .DFI_EN_WIDTH    (DFI_EN_WIDTH),
        .MAX_BURST_LEN   (MAX_BURST_LEN)
    ) u_data_path (
        .mc_clk                (mc_clk),
        .mc_rst_n              (mc_rst_n),
        .cl_i                  (cl_val),
        .cwl_i                 (cwl_val),
        .al_i                  (al_val),
        .t_phy_wrlat_i         (t_phy_wrlat_i),
        .t_rddata_en_i         (t_rddata_en_i),
        .rd_in_order_i         (rd_in_order_i),
        .wr_op_valid_i         (wr_op_valid),
        .wr_op_ready_o         (wr_op_ready),
        .wr_op_slot_i          (cmd_wr_slot),
        .wr_op_len_i           (cmd_len),
        .rd_op_valid_i         (rd_op_valid),
        .rd_op_ready_o         (rd_op_ready),
        .rd_op_slot_i          (cmd_rd_slot),
        .rd_op_id_i            (rd_op_id),
        .rd_op_len_i           (cmd_len),
        .beat_pull_strb_o      (beat_pull_strb_o),
        .beat_pull_slot_o      (beat_pull_slot_o),
        .beat_pull_ptr_i       (beat_pull_ptr_i),
        .beat_pull_strb_ptr_i  (beat_pull_strb_ptr_i),
        .beat_pull_last_i      (beat_pull_last_i),
        .wbuf_rd_data_i        (wbuf_rd_data_i),
        .wbuf_rd_strb_i        (wbuf_rd_strb_i),
        .b_complete_strb_o     (b_complete_strb_o),
        .b_complete_slot_o     (b_complete_slot_o),
        .rd_inject_valid_o     (rd_inject_valid_o),
        .rd_inject_ready_i     (rd_inject_ready_i),
        .rd_inject_id_o        (rd_inject_id_o),
        .rd_inject_data_o      (rd_inject_data_o),
        .rd_inject_last_o      (rd_inject_last_o),
        .rd_beat_we_o          (rd_beat_we_o),
        .rd_beat_slot_o        (rd_beat_slot_o),
        .pre_dfi_wrdata_o      (pre_dfi_wrdata),
        .pre_dfi_wrdata_en_o   (pre_dfi_wrdata_en),
        .pre_dfi_wrdata_mask_o (pre_dfi_wrdata_mask),
        .pre_dfi_rddata_en_o   (pre_dfi_rddata_en),
        .dfi_rddata_i          (dfi_rddata_i),
        .dfi_rddata_valid_i    (dfi_rddata_valid_i)
    );

    dfi_v21_interface_macro #(
        .NUM_RANKS       (NUM_RANKS),
        .NUM_BANKS       (NUM_BANKS),
        .ROW_WIDTH       (RW),
        .COL_WIDTH       (CW),
        .BURST_LEN_WIDTH (BLW),
        .DFI_RATE        (DFI_RATE),
        .DFI_ADDR_WIDTH  (DFI_ADDR_WIDTH),
        .DFI_BANK_WIDTH  (DFI_BANK_WIDTH),
        .DFI_CTRL_WIDTH  (DFI_CTRL_WIDTH),
        .DFI_CS_WIDTH    (DFI_CS_WIDTH),
        .DFI_DATA_WIDTH  (DFI_DATA_WIDTH),
        .DFI_STRB_WIDTH  (DFI_STRB_WIDTH),
        .DFI_EN_WIDTH    (DFI_EN_WIDTH)
    ) u_dfi_v21_interface (
        .mc_clk                 (mc_clk),
        .mc_rst_n               (mc_rst_n),
        .memtype_i              (memtype_i),
        .cmd_valid_i            (cmd_valid),
        .cmd_ready_o            (dfi_cmd_ready),
        .cmd_op_i               (cmd_op),
        .cmd_rank_i             (cmd_rank),
        .cmd_bank_i             (cmd_bank),
        .cmd_row_i              (cmd_row),
        .cmd_col_i              (cmd_col),
        .cmd_len_i              (cmd_len),
        .pre_dfi_wrdata_i       (pre_dfi_wrdata),
        .pre_dfi_wrdata_en_i    (pre_dfi_wrdata_en),
        .pre_dfi_wrdata_mask_i  (pre_dfi_wrdata_mask),
        .pre_dfi_rddata_en_i    (pre_dfi_rddata_en),
        .pre_dfi_cke_i          (pre_dfi_cke),
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

    // ---- Update interface — tied off until ctrl_update_fub lands ----
    assign dfi_ctrlupd_req_o = 1'b0;
    assign dfi_phyupd_ack_o  = 1'b0;

    wire unused = |{ controller_idle_unused, bl_val,
                     dfi_ctrlupd_ack_i, dfi_phyupd_req_i, dfi_phyupd_type_i,
                     cmd_obs_words };

endmodule : ddr2_lpddr2_core_macro
