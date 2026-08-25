// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_core_tb_top
// Purpose: Verification wrapper for the new pumice_core. Exposes the DFI pin
//          bus on internal `phy_dfi_*` nets so the CocoTBFramework DFISlavePHY
//          BFM (+ MemoryModel golden) binds by prefix, and presents the host
//          AXI + config + the two clocks (aclk / dfi_clk) as ports the TB drives.
`timescale 1ns / 1ps

module pumice_core_tb_top
    import pumice_pkg::*;
#(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int NUM_RANKS      = 1,
    parameter int NUM_BANKS      = 8,
    parameter int ROW_WIDTH      = 14,
    parameter int COL_WIDTH      = 10,
    parameter int DFI_RATE       = 2,
    parameter int DRAM_BEAT_WIDTH = 64,
    parameter int BL             = 8,
    parameter int NUM_ENTRIES    = 8,
    parameter int N_SRAM_SLOTS   = 8,
    parameter int CMD_HISTORY_EN = 0,  // -G from DV: arm the history scoreboard

    parameter int DW  = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int SW  = DW / 8,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int AW  = AXI_ADDR_WIDTH,
    parameter int PHW = (DFI_RATE > 1) ? $clog2(DFI_RATE) : 1,
    parameter int DFI_DATA_WIDTH = DW,
    parameter int DFI_STRB_WIDTH = DW / 8,
    parameter int DFI_EN_WIDTH   = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int DFI_ADDR_BUS_W = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W = $clog2(NUM_BANKS) * DFI_RATE,
    parameter int DFI_CTRL_BUS_W = 1 * DFI_RATE,
    parameter int DFI_CS_BUS_W   = NUM_RANKS * DFI_RATE
) (
    input  logic aclk, aresetn, dfi_clk, dfi_rstn,
    // config
    input  memtype_e         memtype_i,
    input  page_policy_e     page_policy_i,
    // Runtime page-policy pins (PUMICE-006); unconnected => 0 => legacy.
    input  logic [2:0]       page_mode_i,
    input  logic             page_scope_i,
    input  logic [7:0]       page_tr_init_i,
    input  logic [7:0]       page_tr_min_i,
    input  logic [7:0]       page_tr_max_i,
    input  logic [7:0]       page_tr_step_i,
    input  logic [3:0]       page_mc_high_i,
    input  logic [3:0]       page_mc_low_i,
    input  logic [3:0]       page_mc_init_i,
    input  logic [15:0]      page_check_ivl_i,
    input  logic [7:0]       page_rbl_thresh_i,
    input  logic [1:0]       page_rbl_ways_i,
    input  logic [3:0]       page_rbl_sets_i,
    input  logic [15:0]      page_rbl_ivl_i,
    input  logic [4:0]       bank_lsb_i,
    input  logic             hash_en_i,
    input  logic [7:0]       hash_seed_i,
    input  logic [7:0]       t_rcd_i, t_rp_i, t_ras_i, t_rc_i, t_wr_i, t_rtp_i,
    input  logic [7:0]       t_faw_i, t_rrd_i, t_wtr_i, t_rtw_i, t_ccd_i,
    input  logic [15:0]      t_refi_i,
    input  logic [15:0]      t_rfc_i,
    input  logic [3:0]       refresh_burst_i,
    input  logic [15:0]      t_init_wait_i, t_dll_wait_i,
    input  logic [7:0]       t_mrd_wait_i, t_rp_wait_i, t_rfc_wait_i,
    input  logic [PHW-1:0]   rd_phase_i, wr_phase_i,
    input  logic [7:0]       t_phy_wrlat_i, t_rddata_en_i,
    output logic [3:0]       cl_o, cwl_o, bl_o,
    output logic             init_done_o,
    // host AXI
    input  logic [IW-1:0]  s_axi_awid,   input logic [AW-1:0] s_axi_awaddr,
    input  logic [7:0]     s_axi_awlen,  input logic [2:0]    s_axi_awsize,
    input  logic [1:0]     s_axi_awburst,input logic          s_axi_awlock,
    input  logic [3:0]     s_axi_awcache,input logic [2:0]    s_axi_awprot,
    input  logic [3:0]     s_axi_awqos,  input logic [3:0]    s_axi_awregion,
    input  logic           s_axi_awuser, input logic          s_axi_awvalid,
    output logic           s_axi_awready,
    input  logic [DW-1:0]  s_axi_wdata,  input logic [SW-1:0] s_axi_wstrb,
    input  logic           s_axi_wlast,  input logic          s_axi_wuser,
    input  logic           s_axi_wvalid, output logic         s_axi_wready,
    output logic [IW-1:0]  s_axi_bid,    output logic [1:0]   s_axi_bresp,
    output logic           s_axi_buser,  output logic         s_axi_bvalid,
    input  logic           s_axi_bready,
    input  logic [IW-1:0]  s_axi_arid,   input logic [AW-1:0] s_axi_araddr,
    input  logic [7:0]     s_axi_arlen,  input logic [2:0]    s_axi_arsize,
    input  logic [1:0]     s_axi_arburst,input logic          s_axi_arlock,
    input  logic [3:0]     s_axi_arcache,input logic [2:0]    s_axi_arprot,
    input  logic [3:0]     s_axi_arqos,  input logic [3:0]    s_axi_arregion,
    input  logic           s_axi_aruser, input logic          s_axi_arvalid,
    output logic           s_axi_arready,
    output logic [IW-1:0]  s_axi_rid,    output logic [DW-1:0] s_axi_rdata,
    output logic [1:0]     s_axi_rresp,  output logic          s_axi_rlast,
    output logic           s_axi_ruser,  output logic          s_axi_rvalid,
    input  logic           s_axi_rready
);

    // ---- phy_dfi_* nets the DFISlavePHY BFM binds to (prefix phy_dfi) ----
    logic [DFI_ADDR_BUS_W-1:0]  phy_dfi_address;
    logic [DFI_BANK_BUS_W-1:0]  phy_dfi_bank;
    logic [DFI_CTRL_BUS_W-1:0]  phy_dfi_cas_n, phy_dfi_ras_n, phy_dfi_we_n;
    logic [DFI_CS_BUS_W-1:0]    phy_dfi_cs_n, phy_dfi_odt;
    logic [DFI_DATA_WIDTH-1:0]  phy_dfi_wrdata;
    logic [DFI_EN_WIDTH-1:0]    phy_dfi_wrdata_en;
    logic [DFI_STRB_WIDTH-1:0]  phy_dfi_wrdata_mask;
    logic [DFI_EN_WIDTH-1:0]    phy_dfi_rddata_en;
    logic [DFI_DATA_WIDTH-1:0]  phy_dfi_rddata;         // BFM drives
    logic [DFI_VALID_WIDTH-1:0] phy_dfi_rddata_valid;   // BFM drives
    logic                       phy_dfi_init_start;
    logic                       phy_dfi_init_complete;  // BFM drives
    // signals the BFM's _signals list expects (tied / unused here)
    logic                       phy_dfi_error, phy_dfi_error_info, phy_dfi_crc_alert;
    logic                       phy_dfi_ctrlupd_req, phy_dfi_ctrlupd_ack;
    logic                       phy_dfi_phyupd_req, phy_dfi_phyupd_ack;
    logic [1:0]                 phy_dfi_phyupd_type;
    logic                       phy_dfi_disconnect_req;
    logic                       phy_dfi_freq_change_req, phy_dfi_freq_change_ack;
    logic                       phy_dfi_parity_check, phy_dfi_phymstr_req;
    logic                       phy_dfi_training_active, phy_dfi_training_phase;
    logic [DFI_CS_BUS_W-1:0]    phy_dfi_cke, phy_dfi_dram_clk_disable;

    assign phy_dfi_error           = 1'b0;
    assign phy_dfi_error_info      = 1'b0;
    assign phy_dfi_crc_alert       = 1'b0;
    assign phy_dfi_ctrlupd_req     = 1'b0;
    assign phy_dfi_ctrlupd_ack     = 1'b0;
    assign phy_dfi_phyupd_req      = 1'b0;
    assign phy_dfi_phyupd_ack      = 1'b0;
    assign phy_dfi_phyupd_type     = 2'b0;
    assign phy_dfi_disconnect_req  = 1'b0;
    assign phy_dfi_freq_change_req = 1'b0;
    assign phy_dfi_freq_change_ack = 1'b0;
    assign phy_dfi_parity_check    = 1'b0;
    assign phy_dfi_phymstr_req     = 1'b0;
    assign phy_dfi_training_active = 1'b0;
    assign phy_dfi_training_phase  = 1'b0;
    assign phy_dfi_cke             = '1;
    assign phy_dfi_dram_clk_disable = '0;

    pumice_core #(
        .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW), .NUM_RANKS(NUM_RANKS),
        .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH),
        .DFI_RATE(DFI_RATE), .DRAM_BEAT_WIDTH(DRAM_BEAT_WIDTH), .BL(BL),
        .NUM_ENTRIES(NUM_ENTRIES), .N_SRAM_SLOTS(N_SRAM_SLOTS),
        .CMD_HISTORY_EN(CMD_HISTORY_EN)
    ) u_core (
        .aclk(aclk), .aresetn(aresetn), .dfi_clk(dfi_clk), .dfi_rstn(dfi_rstn),
        .memtype_i(memtype_i), .page_policy_i(page_policy_i),
        .page_mode_i(page_mode_i), .page_scope_i(page_scope_i),
        .page_tr_init_i(page_tr_init_i), .page_tr_min_i(page_tr_min_i),
        .page_tr_max_i(page_tr_max_i), .page_tr_step_i(page_tr_step_i),
        .page_mc_high_i(page_mc_high_i), .page_mc_low_i(page_mc_low_i),
        .page_mc_init_i(page_mc_init_i), .page_check_ivl_i(page_check_ivl_i),
        .page_rbl_thresh_i(page_rbl_thresh_i), .page_rbl_ways_i(page_rbl_ways_i),
        .page_rbl_sets_i(page_rbl_sets_i), .page_rbl_ivl_i(page_rbl_ivl_i),
        .stat_page_hit_o(), .stat_page_miss_o(), .stat_page_empty_o(),
        .stat_act_o(), .stat_pre_o(), .stat_ref_o(),
        // CSR-backed MR values at their RDL resets (MR0 0x0433 = BL8/CL3/tWR3);
        // no runtime MR retune in this TB, init_restart tied off.
        .mr0_i(16'h0433), .mr1_i(16'h0000), .mr2_i(16'h0000), .mr3_i(16'h0000),
        .init_restart_i(1'b0),
        .bank_lsb_i(bank_lsb_i), .hash_en_i(hash_en_i), .hash_seed_i(hash_seed_i),
        .t_rcd_i(t_rcd_i), .t_rp_i(t_rp_i), .t_ras_i(t_ras_i), .t_rc_i(t_rc_i),
        .t_wr_i(t_wr_i), .t_rtp_i(t_rtp_i), .t_faw_i(t_faw_i), .t_rrd_i(t_rrd_i),
        .t_wtr_i(t_wtr_i), .t_rtw_i(t_rtw_i), .t_ccd_i(t_ccd_i),
        .t_refi_i(t_refi_i), .t_rfc_i(t_rfc_i), .refresh_burst_i(refresh_burst_i),
        .t_init_wait_i(t_init_wait_i), .t_dll_wait_i(t_dll_wait_i),
        .t_mrd_wait_i(t_mrd_wait_i), .t_rp_wait_i(t_rp_wait_i), .t_rfc_wait_i(t_rfc_wait_i),
        .rd_phase_i(rd_phase_i), .wr_phase_i(wr_phase_i),
        .t_phy_wrlat_i(t_phy_wrlat_i), .t_rddata_en_i(t_rddata_en_i),
        // gear_i = log2(DFI_RATE) so the ACTIVE DFI rate == the build DFI_RATE
        // (full rate, all phases active) — bit-identical to the pre-gear
        // behavior. bl_i = build BL so the runtime sub-DFI-word framing matches
        // the compile geometry.
        .gear_i(2'($clog2(DFI_RATE))),
        .bl_i(4'(BL)),
        .cl_o(cl_o), .cwl_o(cwl_o), .bl_o(bl_o), .init_done_o(init_done_o),
        .s_axi_awid(s_axi_awid), .s_axi_awaddr(s_axi_awaddr), .s_axi_awlen(s_axi_awlen),
        .s_axi_awsize(s_axi_awsize), .s_axi_awburst(s_axi_awburst), .s_axi_awlock(s_axi_awlock),
        .s_axi_awcache(s_axi_awcache), .s_axi_awprot(s_axi_awprot), .s_axi_awqos(s_axi_awqos),
        .s_axi_awregion(s_axi_awregion), .s_axi_awuser(s_axi_awuser),
        .s_axi_awvalid(s_axi_awvalid), .s_axi_awready(s_axi_awready),
        .s_axi_wdata(s_axi_wdata), .s_axi_wstrb(s_axi_wstrb), .s_axi_wlast(s_axi_wlast),
        .s_axi_wuser(s_axi_wuser), .s_axi_wvalid(s_axi_wvalid), .s_axi_wready(s_axi_wready),
        .s_axi_bid(s_axi_bid), .s_axi_bresp(s_axi_bresp), .s_axi_buser(s_axi_buser),
        .s_axi_bvalid(s_axi_bvalid), .s_axi_bready(s_axi_bready),
        .s_axi_arid(s_axi_arid), .s_axi_araddr(s_axi_araddr), .s_axi_arlen(s_axi_arlen),
        .s_axi_arsize(s_axi_arsize), .s_axi_arburst(s_axi_arburst), .s_axi_arlock(s_axi_arlock),
        .s_axi_arcache(s_axi_arcache), .s_axi_arprot(s_axi_arprot), .s_axi_arqos(s_axi_arqos),
        .s_axi_arregion(s_axi_arregion), .s_axi_aruser(s_axi_aruser),
        .s_axi_arvalid(s_axi_arvalid), .s_axi_arready(s_axi_arready),
        .s_axi_rid(s_axi_rid), .s_axi_rdata(s_axi_rdata), .s_axi_rresp(s_axi_rresp),
        .s_axi_rlast(s_axi_rlast), .s_axi_ruser(s_axi_ruser),
        .s_axi_rvalid(s_axi_rvalid), .s_axi_rready(s_axi_rready),
        // DFI pin bus -> phy_dfi_* nets
        .dfi_address_o(phy_dfi_address), .dfi_bank_o(phy_dfi_bank),
        .dfi_cas_n_o(phy_dfi_cas_n), .dfi_ras_n_o(phy_dfi_ras_n), .dfi_we_n_o(phy_dfi_we_n),
        .dfi_cs_n_o(phy_dfi_cs_n), .dfi_odt_o(phy_dfi_odt),
        .dfi_wrdata_o(phy_dfi_wrdata), .dfi_wrdata_en_o(phy_dfi_wrdata_en),
        .dfi_wrdata_mask_o(phy_dfi_wrdata_mask),
        .dfi_rddata_en_o(phy_dfi_rddata_en), .dfi_rddata_i(phy_dfi_rddata),
        .dfi_rddata_valid_i(phy_dfi_rddata_valid),
        .dfi_init_start_o(phy_dfi_init_start), .dfi_init_complete_i(phy_dfi_init_complete)
    );

    // ---- fine-grained per-bank command-history scoreboard (standalone) ------
    // Taps the scheduler's issued abstract-command stream (aclk domain) and
    // audits JEDEC same-bank sequencing the COARSE bank-timer readiness misses —
    // e.g. a REFab granted while a bank row is still OPEN (ACT with no PRE), the
    // registered-feedback refresh-collision hazard. Sequencing checks only;
    // pair with the DFI-read data check for de-interleave/skew defects.
    pumice_cmd_history_checker #(
        .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS), .DEPTH(32),
        // JEDEC same-bank windows (match the tb _cfg timings): catches a column
        // op issued too soon after ACT (tRCD) etc. — e.g. a refresh-disturbed
        // ACT->RDA spacing.
        .T_RCD(3), .T_RP(3), .T_RAS(4), .T_RFC(8),
        // global turnaround windows — must match the tb _cfg t_wtr/t_rtw
        .T_WTR(2), .T_RTW(2)
    ) u_cmd_history (
        .clk        (aclk),
        .rst_n      (aresetn),
        .cmd_valid_i(u_core.w_cmd_v),
        .cmd_op_i   (u_core.w_cmd_op),
        .cmd_rank_i (u_core.w_cmd_rank),
        .cmd_bank_i (u_core.w_cmd_bank)
    );

    // ---- param-gated DFI read-return scoreboard (data-path debug tooling) ----
    // Reconciles reads ISSUED (scheduler OP_RD/OP_RDA) vs DATA RETURNED on the DFI
    // read path, correlated with refresh — catches the refresh-drain read-data
    // loss (drop / zero-return) the command scoreboard can't see. DEBUG_EN=0
    // synthesizes it away; the dbg_* counters are CSR-ready for on-silicon use.
    logic [15:0] w_dbg_rd_issued, w_dbg_rd_returned, w_dbg_rd_drops,
                 w_dbg_rd_zero,   w_dbg_rd_ref_inflight;
    logic        w_dbg_rd_error;
    pumice_dfi_rd_return_checker #(
        .DEBUG_EN(1), .DW(DW), .TIMEOUT(512), .REF_WINDOW(64)
    ) u_rd_return_chk (
        .clk        (aclk),
        .rst_n      (aresetn),
        .dbg_clear_i(1'b0),
        .cmd_valid_i(u_core.w_cmd_v),
        .cmd_op_i   (u_core.w_cmd_op),
        .ret_valid_i(u_core.w_ret_v),
        .ret_last_i (u_core.w_ret_last),
        .ret_data_i (u_core.w_ret_data),
        .dbg_reads_issued_o  (w_dbg_rd_issued),
        .dbg_reads_returned_o(w_dbg_rd_returned),
        .dbg_drops_o         (w_dbg_rd_drops),
        .dbg_zero_returns_o  (w_dbg_rd_zero),
        .dbg_ref_inflight_o  (w_dbg_rd_ref_inflight),
        .dbg_error_o         (w_dbg_rd_error)
    );

endmodule : pumice_core_tb_top
