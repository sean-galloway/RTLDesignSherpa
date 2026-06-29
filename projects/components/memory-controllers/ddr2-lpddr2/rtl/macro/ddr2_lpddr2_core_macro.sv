// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: ddr2_lpddr2_core_macro
// Purpose: AXI-to-DFI macro. Subsumes the AXI4 host-side frontend so the
//          boundary is AXI4 slave on the host side and DFI v2.1 master
//          on the memory side. CSR slave + reset/clock sit OUTSIDE this
//          macro at the ddr2_lpddr2_top level.
//
// Hierarchy:
//          ddr2_lpddr2_core_macro
//          ├── axi_frontend_macro        (AXI4 slave + addr_map + CAMs)
//          ├── command_scheduler_macro   (7 FUBs — what to issue)
//          ├── data_path_macro           (2 FUBs — W/R beat sequencing)
//          └── dfi_v21_interface_macro   (2 FUBs — DFI v2.1 wire pack)
//
//          Pre-2026-06-26: this macro started at the scheduler boundary
//          and exposed snap_*/match_*/issued/beat_pull/b_complete/rd_beat/
//          rd_inject/wbuf_rd ports for the frontend to drive. The
//          frontend was a peer at the top level. As of this commit,
//          the frontend is internal — the only host-side surface is the
//          AXI4 bus, matching the natural AXI-to-DFI partition.

`timescale 1ns / 1ps
`include "reset_defs.svh"

module ddr2_lpddr2_core_macro
    import ddr2_lpddr2_pkg::*;
#(
    // ---- AXI4 ----
    parameter int AXI_ADDR_WIDTH  = 32,
    parameter int AXI_DATA_WIDTH  = 64,
    parameter int AXI_ID_WIDTH    = 4,
    parameter int AXI_USER_WIDTH  = 8,
    parameter int AXI_STRB_WIDTH  = AXI_DATA_WIDTH / 8,

    // ---- DRAM topology ----
    parameter int NUM_RANKS       = 1,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int BURST_LEN_WIDTH = 8,

    // ---- buffer / CAM depths ----
    parameter int W_BUF_DEPTH     = 128,
    parameter int W_BUF_PTR_WIDTH = $clog2(W_BUF_DEPTH),
    parameter int WR_CAM_DEPTH    = 16,
    parameter int RD_CAM_DEPTH    = 16,
    parameter int PAGE_POLICY     = 32'(PAGE_POLICY_CLOSE),

    // ---- DRAM / DFI ----
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

    // Aliases
    parameter int AW  = AXI_ADDR_WIDTH,
    parameter int DW  = AXI_DATA_WIDTH,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int UW  = AXI_USER_WIDTH,
    parameter int SW  = AXI_STRB_WIDTH,
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

    // ========================================================================
    // CSR-driven configuration (was: split between frontend + core)
    // ========================================================================
    input  addr_map_scheme_e           scheme_active_i,
    input  logic [7:0]                 xor_seed_i,

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

    // ========================================================================
    // HOST-SIDE — AXI4 slave (was: snap/match/issued/beat_pull/b_complete/...
    // exposed for the now-internal frontend to drive)
    // ========================================================================
    input  logic [IW-1:0]              s_axi_awid,
    input  logic [AW-1:0]              s_axi_awaddr,
    input  logic [7:0]                 s_axi_awlen,
    input  logic [2:0]                 s_axi_awsize,
    input  logic [1:0]                 s_axi_awburst,
    input  logic                       s_axi_awlock,
    input  logic [3:0]                 s_axi_awcache,
    input  logic [2:0]                 s_axi_awprot,
    input  logic [3:0]                 s_axi_awqos,
    input  logic [3:0]                 s_axi_awregion,
    input  logic [UW-1:0]              s_axi_awuser,
    input  logic                       s_axi_awvalid,
    output logic                       s_axi_awready,

    input  logic [DW-1:0]              s_axi_wdata,
    input  logic [SW-1:0]              s_axi_wstrb,
    input  logic                       s_axi_wlast,
    input  logic [UW-1:0]              s_axi_wuser,
    input  logic                       s_axi_wvalid,
    output logic                       s_axi_wready,

    output logic [IW-1:0]              s_axi_bid,
    output logic [1:0]                 s_axi_bresp,
    output logic [UW-1:0]              s_axi_buser,
    output logic                       s_axi_bvalid,
    input  logic                       s_axi_bready,

    input  logic [IW-1:0]              s_axi_arid,
    input  logic [AW-1:0]              s_axi_araddr,
    input  logic [7:0]                 s_axi_arlen,
    input  logic [2:0]                 s_axi_arsize,
    input  logic [1:0]                 s_axi_arburst,
    input  logic                       s_axi_arlock,
    input  logic [3:0]                 s_axi_arcache,
    input  logic [2:0]                 s_axi_arprot,
    input  logic [3:0]                 s_axi_arqos,
    input  logic [3:0]                 s_axi_arregion,
    input  logic [UW-1:0]              s_axi_aruser,
    input  logic                       s_axi_arvalid,
    output logic                       s_axi_arready,

    output logic [IW-1:0]              s_axi_rid,
    output logic [DW-1:0]              s_axi_rdata,
    output logic [1:0]                 s_axi_rresp,
    output logic                       s_axi_rlast,
    output logic [UW-1:0]              s_axi_ruser,
    output logic                       s_axi_rvalid,
    input  logic                       s_axi_rready,

    // ========================================================================
    // MEMORY-SIDE — DFI v2.1
    // ========================================================================
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
    input  logic [1:0]                 dfi_phyupd_type_i,

    // ========================================================================
    // STATUS + obs feed (consumed by ddr2_lpddr2_csr_slave)
    // ========================================================================
    output logic                       status_init_done_o,
    output logic                       status_init_busy_o,
    output logic [2:0]                 status_pdn_state_o,

    // 7 scheduler words + 2 frontend axi_intake words = 9. Layout:
    //   obs_words_o[6:0] — command_scheduler_macro (existing)
    //   obs_words_o[8:7] — axi_frontend_macro      (newly internal)
    output logic [8:0][31:0]           obs_words_o
);

    //=========================================================================
    // Internal nets — frontend ↔ scheduler / data_path
    //=========================================================================

    // q_*/match_* (scheduler query → frontend CAM rowhit check)
    logic [RKW-1:0]                          w_q_rank;
    logic [BKW-1:0]                          w_q_bank;
    logic [RW-1:0]                           w_q_row;
    logic [WR_CAM_DEPTH-1:0]                 w_wr_match_pending;
    logic [WR_CAM_DEPTH-1:0]                 w_wr_match_rowhit;
    logic [RD_CAM_DEPTH-1:0]                 w_rd_match_pending;
    logic [RD_CAM_DEPTH-1:0]                 w_rd_match_rowhit;

    // CAM snapshots (frontend → scheduler)
    logic [WR_CAM_DEPTH-1:0][RKW-1:0]        w_wr_snap_rank;
    logic [WR_CAM_DEPTH-1:0][BKW-1:0]        w_wr_snap_bank;
    logic [WR_CAM_DEPTH-1:0][RW-1:0]         w_wr_snap_row;
    logic [WR_CAM_DEPTH-1:0][CW-1:0]         w_wr_snap_col;
    logic [WR_CAM_DEPTH-1:0][BLW-1:0]        w_wr_snap_len;
    logic [WR_CAM_DEPTH-1:0][3:0]            w_wr_snap_qos;
    logic [WR_CAM_DEPTH-1:0][7:0]            w_wr_snap_age;
    logic [RD_CAM_DEPTH-1:0][RKW-1:0]        w_rd_snap_rank;
    logic [RD_CAM_DEPTH-1:0][BKW-1:0]        w_rd_snap_bank;
    logic [RD_CAM_DEPTH-1:0][RW-1:0]         w_rd_snap_row;
    logic [RD_CAM_DEPTH-1:0][CW-1:0]         w_rd_snap_col;
    logic [RD_CAM_DEPTH-1:0][BLW-1:0]        w_rd_snap_len;
    logic [RD_CAM_DEPTH-1:0][3:0]            w_rd_snap_qos;
    logic [RD_CAM_DEPTH-1:0][IW-1:0]         w_rd_snap_id;
    logic [RD_CAM_DEPTH-1:0][7:0]            w_rd_snap_age;

    // mark-issued strobes (scheduler → frontend)
    logic                                    w_wr_issued_we;
    logic [WSL-1:0]                          w_wr_issued_slot;
    logic                                    w_rd_issued_we;
    logic [RSL-1:0]                          w_rd_issued_slot;

    // beat-pull (data_path → frontend wbuf)
    logic                                    w_beat_pull_strb;
    logic [WSL-1:0]                          w_beat_pull_slot;
    logic [WPW-1:0]                          w_beat_pull_ptr;
    logic [WPW-1:0]                          w_beat_pull_strb_ptr;
    logic                                    w_beat_pull_last;
    logic [DRAM_BEAT_WIDTH-1:0]              w_wbuf_rd_data;
    logic [DRAM_STRB_WIDTH-1:0]              w_wbuf_rd_strb;

    // b_complete (data_path → frontend wr_cmd_cam retire)
    logic                                    w_b_complete_strb;
    logic [WSL-1:0]                          w_b_complete_slot;

    // rd_beat / rd_inject (data_path → frontend R-emit)
    logic                                    w_rd_beat_we;
    logic [RSL-1:0]                          w_rd_beat_slot;
    logic                                    w_rd_inject_valid;
    logic                                    w_rd_inject_ready;
    logic [IW-1:0]                           w_rd_inject_id;
    logic [DRAM_BEAT_WIDTH-1:0]              w_rd_inject_data;
    logic                                    w_rd_inject_last;

    // entry-complete (frontend output for telemetry; unused at boundary)
    logic                                    w_wr_entry_complete;
    logic [WSL-1:0]                          w_wr_entry_complete_slot;
    logic [IW-1:0]                           w_wr_entry_complete_id;
    logic                                    w_rd_entry_complete;
    logic [RSL-1:0]                          w_rd_entry_complete_slot;
    logic [IW-1:0]                           w_rd_entry_complete_id;

    // frontend obs_words (axi_intake telemetry)
    logic [1:0][31:0]                        w_frontend_obs_words;

    //=========================================================================
    // Internal nets — scheduler ↔ data_path ↔ dfi_interface
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

    // rd_op_id is looked up via rd_snap_id indexed by cmd_rd_slot
    assign rd_op_id = w_rd_snap_id[cmd_rd_slot];

    // data_path → dfi_interface (pre-pack data nets)
    logic [DFI_DATA_WIDTH-1:0]  pre_dfi_wrdata;
    logic [DFI_EN_WIDTH-1:0]    pre_dfi_wrdata_en;
    logic [DFI_STRB_WIDTH-1:0]  pre_dfi_wrdata_mask;
    logic [DFI_EN_WIDTH-1:0]    pre_dfi_rddata_en;

    logic                       controller_idle_unused;

    // scheduler obs words
    logic [6:0][31:0]           cmd_obs_words;

    //=========================================================================
    // axi_frontend_macro (newly internal)
    //=========================================================================

    axi_frontend_macro #(
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .NUM_RANKS            (NUM_RANKS),
        .NUM_BANKS            (NUM_BANKS),
        .ROW_WIDTH            (ROW_WIDTH),
        .COL_WIDTH            (COL_WIDTH),
        .BURST_LEN_WIDTH      (BURST_LEN_WIDTH),
        .W_BUF_DEPTH          (W_BUF_DEPTH),
        .WR_CAM_DEPTH         (WR_CAM_DEPTH),
        .RD_CAM_DEPTH         (RD_CAM_DEPTH)
    ) u_axi_frontend (
        .mc_clk                     (mc_clk),
        .mc_rst_n                   (mc_rst_n),
        .scheme_active_i            (scheme_active_i),
        .xor_seed_i                 (xor_seed_i),

        .s_axi_awid                 (s_axi_awid),
        .s_axi_awaddr               (s_axi_awaddr),
        .s_axi_awlen                (s_axi_awlen),
        .s_axi_awsize               (s_axi_awsize),
        .s_axi_awburst              (s_axi_awburst),
        .s_axi_awlock               (s_axi_awlock),
        .s_axi_awcache              (s_axi_awcache),
        .s_axi_awprot               (s_axi_awprot),
        .s_axi_awqos                (s_axi_awqos),
        .s_axi_awregion             (s_axi_awregion),
        .s_axi_awuser               (s_axi_awuser),
        .s_axi_awvalid              (s_axi_awvalid),
        .s_axi_awready              (s_axi_awready),
        .s_axi_wdata                (s_axi_wdata),
        .s_axi_wstrb                (s_axi_wstrb),
        .s_axi_wlast                (s_axi_wlast),
        .s_axi_wuser                (s_axi_wuser),
        .s_axi_wvalid               (s_axi_wvalid),
        .s_axi_wready               (s_axi_wready),
        .s_axi_bid                  (s_axi_bid),
        .s_axi_bresp                (s_axi_bresp),
        .s_axi_buser                (s_axi_buser),
        .s_axi_bvalid               (s_axi_bvalid),
        .s_axi_bready               (s_axi_bready),
        .s_axi_arid                 (s_axi_arid),
        .s_axi_araddr               (s_axi_araddr),
        .s_axi_arlen                (s_axi_arlen),
        .s_axi_arsize               (s_axi_arsize),
        .s_axi_arburst              (s_axi_arburst),
        .s_axi_arlock               (s_axi_arlock),
        .s_axi_arcache              (s_axi_arcache),
        .s_axi_arprot               (s_axi_arprot),
        .s_axi_arqos                (s_axi_arqos),
        .s_axi_arregion             (s_axi_arregion),
        .s_axi_aruser               (s_axi_aruser),
        .s_axi_arvalid              (s_axi_arvalid),
        .s_axi_arready              (s_axi_arready),
        .s_axi_rid                  (s_axi_rid),
        .s_axi_rdata                (s_axi_rdata),
        .s_axi_rresp                (s_axi_rresp),
        .s_axi_rlast                (s_axi_rlast),
        .s_axi_ruser                (s_axi_ruser),
        .s_axi_rvalid               (s_axi_rvalid),
        .s_axi_rready               (s_axi_rready),

        // rd_inject from data_path's R-injection path
        .rd_inject_valid_i          (w_rd_inject_valid),
        .rd_inject_ready_o          (w_rd_inject_ready),
        .rd_inject_id_i             (w_rd_inject_id),
        .rd_inject_data_i           (w_rd_inject_data),
        .rd_inject_last_i           (w_rd_inject_last),

        .wbuf_ext_rd_data_o         (w_wbuf_rd_data),
        .wbuf_ext_rd_strb_o         (w_wbuf_rd_strb),

        .q_rank_i                   (w_q_rank),
        .q_bank_i                   (w_q_bank),
        .q_row_i                    (w_q_row),
        .wr_match_pending_o         (w_wr_match_pending),
        .wr_match_rowhit_o          (w_wr_match_rowhit),
        .rd_match_pending_o         (w_rd_match_pending),
        .rd_match_rowhit_o          (w_rd_match_rowhit),

        .wr_snap_rank_o             (w_wr_snap_rank),
        .wr_snap_bank_o             (w_wr_snap_bank),
        .wr_snap_row_o              (w_wr_snap_row),
        .wr_snap_col_o              (w_wr_snap_col),
        .wr_snap_len_o              (w_wr_snap_len),
        .wr_snap_qos_o              (w_wr_snap_qos),
        .wr_snap_age_o              (w_wr_snap_age),
        .rd_snap_rank_o             (w_rd_snap_rank),
        .rd_snap_bank_o             (w_rd_snap_bank),
        .rd_snap_row_o              (w_rd_snap_row),
        .rd_snap_col_o              (w_rd_snap_col),
        .rd_snap_len_o              (w_rd_snap_len),
        .rd_snap_qos_o              (w_rd_snap_qos),
        .rd_snap_id_o               (w_rd_snap_id),
        .rd_snap_age_o              (w_rd_snap_age),

        .wr_issued_we_i             (w_wr_issued_we),
        .wr_issued_slot_i           (w_wr_issued_slot),
        .rd_issued_we_i             (w_rd_issued_we),
        .rd_issued_slot_i           (w_rd_issued_slot),

        .beat_pull_strb_i           (w_beat_pull_strb),
        .beat_pull_slot_i           (w_beat_pull_slot),
        .beat_pull_ptr_o            (w_beat_pull_ptr),
        .beat_pull_strb_ptr_o       (w_beat_pull_strb_ptr),
        .beat_pull_last_o           (w_beat_pull_last),

        .b_complete_strb_i          (w_b_complete_strb),
        .b_complete_slot_i          (w_b_complete_slot),
        .wr_entry_complete_o        (w_wr_entry_complete),
        .wr_entry_complete_slot_o   (w_wr_entry_complete_slot),
        .wr_entry_complete_id_o     (w_wr_entry_complete_id),

        .rd_beat_we_i               (w_rd_beat_we),
        .rd_beat_slot_i             (w_rd_beat_slot),
        .rd_entry_complete_o        (w_rd_entry_complete),
        .rd_entry_complete_slot_o   (w_rd_entry_complete_slot),
        .rd_entry_complete_id_o     (w_rd_entry_complete_id),

        .dbg_intake_busy_o          (),
        .dbg_wr_cam_occ_o           (),
        .dbg_rd_cam_occ_o           (),
        .dbg_forward_hit_o          (),
        .dbg_forward_miss_o         (),
        .dbg_fwd_valid_o            (),
        .dbg_fwd_src_slot_o         (),
        .dbg_fwd_id_o               (),

        .obs_words_o                (w_frontend_obs_words)
    );

    //=========================================================================
    // command_scheduler_macro
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
        .q_rank_o            (w_q_rank),
        .q_bank_o            (w_q_bank),
        .q_row_o             (w_q_row),
        .wr_match_pending_i  (w_wr_match_pending),
        .wr_match_rowhit_i   (w_wr_match_rowhit),
        .rd_match_pending_i  (w_rd_match_pending),
        .rd_match_rowhit_i   (w_rd_match_rowhit),
        .wr_snap_rank_i      (w_wr_snap_rank),
        .wr_snap_bank_i      (w_wr_snap_bank),
        .wr_snap_row_i       (w_wr_snap_row),
        .wr_snap_col_i       (w_wr_snap_col),
        .wr_snap_len_i       (w_wr_snap_len),
        .wr_snap_qos_i       (w_wr_snap_qos),
        .wr_snap_age_i       (w_wr_snap_age),
        .rd_snap_rank_i      (w_rd_snap_rank),
        .rd_snap_bank_i      (w_rd_snap_bank),
        .rd_snap_row_i       (w_rd_snap_row),
        .rd_snap_col_i       (w_rd_snap_col),
        .rd_snap_len_i       (w_rd_snap_len),
        .rd_snap_qos_i       (w_rd_snap_qos),
        .rd_snap_age_i       (w_rd_snap_age),
        .wr_issued_we_o      (w_wr_issued_we),
        .wr_issued_slot_o    (w_wr_issued_slot),
        .rd_issued_we_o      (w_rd_issued_we),
        .rd_issued_slot_o    (w_rd_issued_slot),
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
        .status_init_done_o  (status_init_done_o),
        .status_init_busy_o  (status_init_busy_o),
        .status_pdn_state_o  (status_pdn_state_o),
        .obs_words_o         (cmd_obs_words)
    );

    // Combine 7 scheduler + 2 frontend obs words → 9 total at boundary
    assign obs_words_o = {w_frontend_obs_words, cmd_obs_words};

    //=========================================================================
    // data_path_macro
    //=========================================================================

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
        .bl_i                  (bl_val),
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
        .beat_pull_strb_o      (w_beat_pull_strb),
        .beat_pull_slot_o      (w_beat_pull_slot),
        .beat_pull_ptr_i       (w_beat_pull_ptr),
        .beat_pull_strb_ptr_i  (w_beat_pull_strb_ptr),
        .beat_pull_last_i      (w_beat_pull_last),
        .wbuf_rd_data_i        (w_wbuf_rd_data),
        .wbuf_rd_strb_i        (w_wbuf_rd_strb),
        .b_complete_strb_o     (w_b_complete_strb),
        .b_complete_slot_o     (w_b_complete_slot),
        .rd_inject_valid_o     (w_rd_inject_valid),
        .rd_inject_ready_i     (w_rd_inject_ready),
        .rd_inject_id_o        (w_rd_inject_id),
        .rd_inject_data_o      (w_rd_inject_data),
        .rd_inject_last_o      (w_rd_inject_last),
        .rd_beat_we_o          (w_rd_beat_we),
        .rd_beat_slot_o        (w_rd_beat_slot),
        .pre_dfi_wrdata_o      (pre_dfi_wrdata),
        .pre_dfi_wrdata_en_o   (pre_dfi_wrdata_en),
        .pre_dfi_wrdata_mask_o (pre_dfi_wrdata_mask),
        .pre_dfi_rddata_en_o   (pre_dfi_rddata_en),
        .dfi_rddata_i          (dfi_rddata_i),
        .dfi_rddata_valid_i    (dfi_rddata_valid_i)
    );

    //=========================================================================
    // dfi_v21_interface_macro
    //=========================================================================

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

    wire unused = |{ controller_idle_unused,
                     w_wr_entry_complete, w_wr_entry_complete_slot,
                     w_wr_entry_complete_id,
                     w_rd_entry_complete, w_rd_entry_complete_slot,
                     w_rd_entry_complete_id,
                     dfi_ctrlupd_ack_i, dfi_phyupd_req_i, dfi_phyupd_type_i };

endmodule : ddr2_lpddr2_core_macro
