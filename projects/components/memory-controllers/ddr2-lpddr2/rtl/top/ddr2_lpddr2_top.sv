// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: ddr2_lpddr2_top
// Purpose: Top-level wrapper that integrates the three macros into a
//          complete DDR2/LPDDR2 memory controller:
//
//            ddr2_lpddr2_top
//              ├── axi_frontend_macro        (AXI4 host → CAMs)
//              ├── ddr2_lpddr2_core_macro    (scheduler + datapath + DFI)
//              └── ddr2_lpddr2_csr_slave     (APB CSR + cfg projection)
//
// External ports:
//   - AXI4 slave (s_axi_*) on mc_clk
//   - APB slave (s_apb_*) on pclk (independent clock — CDC inside slave)
//   - DFI master to PHY on mc_clk
//
// Internal nets connect the three macros via the snap / handshake buses
// already designed at the macro boundaries.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module ddr2_lpddr2_top
    import ddr2_lpddr2_pkg::*;
#(
    // AXI4 host
    parameter int AXI_ADDR_WIDTH   = 32,
    parameter int AXI_DATA_WIDTH   = 64,
    parameter int AXI_ID_WIDTH     = 4,
    // AXI USER channel — 8 bits is the typical SoC convention. The side-table
    // captures awuser/aruser per ID and echoes them on B/R per AXI4.
    parameter int AXI_USER_WIDTH   = 8,
    parameter int AXI_STRB_WIDTH   = AXI_DATA_WIDTH / 8,
    parameter int BURST_LEN_WIDTH  = 8,

    // APB CSR
    parameter int APB_ADDR_WIDTH   = 12,
    parameter int APB_DATA_WIDTH   = 32,
    parameter int APB_STRB_WIDTH   = APB_DATA_WIDTH / 8,
    parameter int APB_PROT_WIDTH   = 3,

    // DRAM topology
    parameter int NUM_RANKS        = 1,
    parameter int NUM_BANKS        = 8,
    parameter int ROW_WIDTH        = 14,
    parameter int COL_WIDTH        = 10,

    // CAM depths
    parameter int WR_CAM_DEPTH     = 16,
    parameter int RD_CAM_DEPTH     = 16,

    // w_buf
    parameter int W_BUF_DEPTH      = 128,
    parameter int W_BUF_PTR_WIDTH  = $clog2(W_BUF_DEPTH),

    // DFI
    parameter int DFI_RATE         = 2,
    parameter int DRAM_BEAT_WIDTH  = AXI_DATA_WIDTH,
    parameter int DRAM_STRB_WIDTH  = AXI_STRB_WIDTH,
    parameter int DFI_DATA_WIDTH   = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DFI_STRB_WIDTH   = DRAM_STRB_WIDTH * DFI_RATE,
    parameter int DFI_EN_WIDTH     = DFI_RATE,
    parameter int DFI_VALID_WIDTH  = DFI_RATE,
    parameter int DFI_ADDR_BUS_W   = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W   = $clog2(NUM_BANKS) * DFI_RATE,
    parameter int DFI_CTRL_BUS_W   = 1 * DFI_RATE,
    parameter int DFI_CS_BUS_W     = NUM_RANKS * DFI_RATE,
    parameter int DFI_CS_WIDTH     = NUM_RANKS,

    parameter int PAGE_POLICY     = 32'(PAGE_POLICY_CLOSE),
    parameter int MAX_BURST_LEN    = 8,

    // ---- derived ----
    parameter int IW  = AXI_ID_WIDTH,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int RW  = ROW_WIDTH,
    parameter int CW  = COL_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int WSL = $clog2(WR_CAM_DEPTH),
    parameter int RSL = $clog2(RD_CAM_DEPTH),
    parameter int WPW = W_BUF_PTR_WIDTH
) (
    // Clocks + resets
    input  logic                          mc_clk,
    input  logic                          mc_rst_n,
    input  logic                          pclk,
    input  logic                          presetn,

    //=========================================================================
    // AXI4 slave (host)
    //=========================================================================
    input  logic [IW-1:0]                 s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_axi_awaddr,
    input  logic [7:0]                    s_axi_awlen,
    input  logic [2:0]                    s_axi_awsize,
    input  logic [1:0]                    s_axi_awburst,
    input  logic                          s_axi_awlock,
    input  logic [3:0]                    s_axi_awcache,
    input  logic [2:0]                    s_axi_awprot,
    input  logic [3:0]                    s_axi_awqos,
    input  logic [3:0]                    s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_awuser,
    input  logic                          s_axi_awvalid,
    output logic                          s_axi_awready,
    input  logic [AXI_DATA_WIDTH-1:0]     s_axi_wdata,
    input  logic [AXI_STRB_WIDTH-1:0]     s_axi_wstrb,
    input  logic                          s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_wuser,
    input  logic                          s_axi_wvalid,
    output logic                          s_axi_wready,
    output logic [IW-1:0]                 s_axi_bid,
    output logic [1:0]                    s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_buser,
    output logic                          s_axi_bvalid,
    input  logic                          s_axi_bready,
    input  logic [IW-1:0]                 s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_axi_araddr,
    input  logic [7:0]                    s_axi_arlen,
    input  logic [2:0]                    s_axi_arsize,
    input  logic [1:0]                    s_axi_arburst,
    input  logic                          s_axi_arlock,
    input  logic [3:0]                    s_axi_arcache,
    input  logic [2:0]                    s_axi_arprot,
    input  logic [3:0]                    s_axi_arqos,
    input  logic [3:0]                    s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_aruser,
    input  logic                          s_axi_arvalid,
    output logic                          s_axi_arready,
    output logic [IW-1:0]                 s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]     s_axi_rdata,
    output logic [1:0]                    s_axi_rresp,
    output logic                          s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_ruser,
    output logic                          s_axi_rvalid,
    input  logic                          s_axi_rready,

    //=========================================================================
    // APB slave (CSR)
    //=========================================================================
    input  logic                          s_apb_PSEL,
    input  logic                          s_apb_PENABLE,
    output logic                          s_apb_PREADY,
    input  logic [APB_ADDR_WIDTH-1:0]     s_apb_PADDR,
    input  logic                          s_apb_PWRITE,
    input  logic [APB_DATA_WIDTH-1:0]     s_apb_PWDATA,
    input  logic [APB_STRB_WIDTH-1:0]     s_apb_PSTRB,
    input  logic [APB_PROT_WIDTH-1:0]     s_apb_PPROT,
    output logic [APB_DATA_WIDTH-1:0]     s_apb_PRDATA,
    output logic                          s_apb_PSLVERR,

    //=========================================================================
    // DFI master (PHY-facing)
    //=========================================================================
    output logic [DFI_ADDR_BUS_W-1:0]     dfi_address_o,
    output logic [DFI_BANK_BUS_W-1:0]     dfi_bank_o,
    output logic [DFI_CTRL_BUS_W-1:0]     dfi_cas_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]     dfi_ras_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]     dfi_we_n_o,
    output logic [DFI_CS_BUS_W-1:0]       dfi_cs_n_o,
    output logic [DFI_CS_BUS_W-1:0]       dfi_cke_o,
    output logic [DFI_CS_BUS_W-1:0]       dfi_odt_o,
    output logic [DFI_DATA_WIDTH-1:0]     dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]       dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]     dfi_wrdata_mask_o,
    output logic [DFI_EN_WIDTH-1:0]       dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]     dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0]    dfi_rddata_valid_i,
    output logic [DFI_CS_BUS_W-1:0]       dfi_dram_clk_disable_o,
    output logic                          dfi_init_start_o,
    input  logic                          dfi_init_complete_i,
    output logic                          dfi_ctrlupd_req_o,
    input  logic                          dfi_ctrlupd_ack_i,
    input  logic                          dfi_phyupd_req_i,
    output logic                          dfi_phyupd_ack_o,
    input  logic [1:0]                    dfi_phyupd_type_i,

    //=========================================================================
    // External run-time controls (carry parameters not yet in CSR map)
    //=========================================================================
    input  memtype_e                      memtype_i,
    input  logic [7:0]                    t_phy_wrlat_i,
    input  logic [7:0]                    t_rddata_en_i,
    input  logic                          rd_in_order_i,
    input  logic [3:0]                    cap_lookahead_max_i,
    input  logic [3:0]                    cap_synth_mask_i
);

    //=========================================================================
    // CSR ↔ core nets
    //=========================================================================
    // CFG outputs from slave → core
    logic                                 cfg_init_start;
    logic                                 cfg_init_force_restart;
    logic                                 cfg_pwr_req_low_power;
    logic                                 cfg_pwr_req_dpd;
    logic                                 cfg_pwr_req_active;
    logic                                 cfg_pwr_req_self_refresh;
    logic                                 cfg_soft_reset;
    logic [7:0]                           cfg_t_rc, cfg_t_rcd, cfg_t_rp, cfg_t_ras;
    logic [15:0]                          cfg_t_rfc, cfg_t_refi;
    logic [7:0]                           cfg_t_rrd, cfg_t_faw, cfg_t_wtr, cfg_t_ccd;
    logic [7:0]                           cfg_cl, cfg_cwl, cfg_t_wr, cfg_t_rfcpb;
    logic [15:0]                          cfg_mr0, cfg_mr1, cfg_mr2, cfg_mr3;
    logic [7:0]                           cfg_pasr_banks_rank0, cfg_pasr_segs_rank0;
    logic [3:0]                           cfg_lookahead_active;
    logic                                 cfg_force_inorder, cfg_happy_enable;
    logic [7:0]                           cfg_age_max_runtime, cfg_txn_queue_high_water;
    logic [1:0]                           cfg_refpb_policy_or, cfg_page_policy_or;
    logic [3:0]                           cfg_refresh_defer_active;
    logic [15:0]                          cfg_zqcs_freq_hz;
    logic [1:0]                           cfg_addr_map_scheme_or;
    logic [3:0]                           cfg_zq_retries;
    logic [7:0]                           cfg_init_timeout_ms;
    logic [15:0]                          cfg_warmup_cycles;
    logic [7:0]                           cfg_hysteresis;

    // STATUS inputs from core → slave
    logic                                 core_init_done;
    logic                                 core_init_busy;
    logic [2:0]                           core_pdn_state;

    // obs_words consolidation: core_macro now emits all 9 (7 scheduler + 2
    // frontend, frontend was absorbed into core_macro on 2026-06-26).
    logic [8:0][31:0]                     all_obs_words;

    //=========================================================================
    // Address-map scheme — CSR-driven, passed through to core_macro.
    // Map 2'b01/10/11 → ROW_MAJOR/BANK_INTERLEAVE/XOR_HASH; 2'b00 falls
    // back to ROW_MAJOR.
    //=========================================================================
    addr_map_scheme_e w_scheme_active;
    always_comb begin
        unique case (cfg_addr_map_scheme_or)
            2'b01:   w_scheme_active = ADDR_MAP_ROW_MAJOR;
            2'b10:   w_scheme_active = ADDR_MAP_BANK_INTERLEAVE;
            2'b11:   w_scheme_active = ADDR_MAP_XOR_HASH;
            default: w_scheme_active = ADDR_MAP_ROW_MAJOR;
        endcase
    end

    //=========================================================================
    // ddr2_lpddr2_core_macro — the AXI-to-DFI mid-layer. As of
    // 2026-06-26 this absorbed axi_frontend_macro, so AXI ports now
    // attach directly here.
    //=========================================================================
    ddr2_lpddr2_core_macro #(
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .AXI_USER_WIDTH     (AXI_USER_WIDTH),
        .NUM_RANKS          (NUM_RANKS),
        .NUM_BANKS          (NUM_BANKS),
        .ROW_WIDTH          (ROW_WIDTH),
        .COL_WIDTH          (COL_WIDTH),
        .BURST_LEN_WIDTH    (BURST_LEN_WIDTH),
        .W_BUF_DEPTH        (W_BUF_DEPTH),
        .WR_CAM_DEPTH       (WR_CAM_DEPTH),
        .RD_CAM_DEPTH       (RD_CAM_DEPTH),
        .W_BUF_PTR_WIDTH    (W_BUF_PTR_WIDTH),
        .DRAM_BEAT_WIDTH    (DRAM_BEAT_WIDTH),
        .DFI_RATE           (DFI_RATE),
        .DFI_DATA_WIDTH     (DFI_DATA_WIDTH),
        .DRAM_STRB_WIDTH    (DRAM_STRB_WIDTH),
        .DFI_STRB_WIDTH     (DFI_STRB_WIDTH),
        .DFI_VALID_WIDTH    (DFI_VALID_WIDTH),
        .DFI_EN_WIDTH       (DFI_EN_WIDTH),
        .DFI_CS_WIDTH       (DFI_CS_WIDTH),
        .MAX_BURST_LEN      (MAX_BURST_LEN),
        .PAGE_POLICY        (PAGE_POLICY)
    ) u_core (
        .mc_clk              (mc_clk),
        .mc_rst_n            (mc_rst_n),

        // Address-map scheme (CSR-driven, previously into the frontend)
        .scheme_active_i     (w_scheme_active),
        .xor_seed_i          (8'h0),

        // run-time config (CSR slave-driven, with externs for what CSR doesn't cover)
        .memtype_i           (memtype_i),
        .t_refi_i            (cfg_t_refi),
        .t_rcd_i             (cfg_t_rcd),
        .t_rp_i              (cfg_t_rp),
        .t_ras_i             (cfg_t_ras),
        .t_rc_i              (cfg_t_rc),
        .t_wr_i              (cfg_t_wr),
        .t_wtr_i             (cfg_t_wtr),
        .t_rtp_i             (8'd4),   // not yet in CSR map
        .t_faw_i             (cfg_t_faw),
        .t_rrd_i             (cfg_t_rrd),
        .idle_threshold_i    (16'd64), // not yet in CSR map
        .enable_pde_i        (cfg_pwr_req_low_power),
        .enable_sref_i       (cfg_pwr_req_self_refresh),

        .mr_we_i             (1'b0),   // CSR-driven MR loads handled inside init_seq
        .mr_index_i          (5'h0),
        .mr_data_i           (16'h0),
        .mr_rank_i           ('0),

        .t_phy_wrlat_i       (t_phy_wrlat_i),
        .t_rddata_en_i       (t_rddata_en_i),
        .rd_in_order_i       (rd_in_order_i),

        // AXI4 slave host port
        .s_axi_awid          (s_axi_awid),
        .s_axi_awaddr        (s_axi_awaddr),
        .s_axi_awlen         (s_axi_awlen),
        .s_axi_awsize        (s_axi_awsize),
        .s_axi_awburst       (s_axi_awburst),
        .s_axi_awlock        (s_axi_awlock),
        .s_axi_awcache       (s_axi_awcache),
        .s_axi_awprot        (s_axi_awprot),
        .s_axi_awqos         (s_axi_awqos),
        .s_axi_awregion      (s_axi_awregion),
        .s_axi_awuser        (s_axi_awuser),
        .s_axi_awvalid       (s_axi_awvalid),
        .s_axi_awready       (s_axi_awready),
        .s_axi_wdata         (s_axi_wdata),
        .s_axi_wstrb         (s_axi_wstrb),
        .s_axi_wlast         (s_axi_wlast),
        .s_axi_wuser         (s_axi_wuser),
        .s_axi_wvalid        (s_axi_wvalid),
        .s_axi_wready        (s_axi_wready),
        .s_axi_bid           (s_axi_bid),
        .s_axi_bresp         (s_axi_bresp),
        .s_axi_buser         (s_axi_buser),
        .s_axi_bvalid        (s_axi_bvalid),
        .s_axi_bready        (s_axi_bready),
        .s_axi_arid          (s_axi_arid),
        .s_axi_araddr        (s_axi_araddr),
        .s_axi_arlen         (s_axi_arlen),
        .s_axi_arsize        (s_axi_arsize),
        .s_axi_arburst       (s_axi_arburst),
        .s_axi_arlock        (s_axi_arlock),
        .s_axi_arcache       (s_axi_arcache),
        .s_axi_arprot        (s_axi_arprot),
        .s_axi_arqos         (s_axi_arqos),
        .s_axi_arregion      (s_axi_arregion),
        .s_axi_aruser        (s_axi_aruser),
        .s_axi_arvalid       (s_axi_arvalid),
        .s_axi_arready       (s_axi_arready),
        .s_axi_rid           (s_axi_rid),
        .s_axi_rdata         (s_axi_rdata),
        .s_axi_rresp         (s_axi_rresp),
        .s_axi_rlast         (s_axi_rlast),
        .s_axi_ruser         (s_axi_ruser),
        .s_axi_rvalid        (s_axi_rvalid),
        .s_axi_rready        (s_axi_rready),

        // DFI
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
        .dfi_rddata_i           (dfi_rddata_i),
        .dfi_rddata_valid_i     (dfi_rddata_valid_i),
        .dfi_dram_clk_disable_o (dfi_dram_clk_disable_o),
        .dfi_init_start_o       (dfi_init_start_o),
        .dfi_init_complete_i    (dfi_init_complete_i),
        .dfi_ctrlupd_req_o      (dfi_ctrlupd_req_o),
        .dfi_ctrlupd_ack_i      (dfi_ctrlupd_ack_i),
        .dfi_phyupd_req_i       (dfi_phyupd_req_i),
        .dfi_phyupd_ack_o       (dfi_phyupd_ack_o),
        .dfi_phyupd_type_i      (dfi_phyupd_type_i),

        // status + obs
        .status_init_done_o     (core_init_done),
        .status_init_busy_o     (core_init_busy),
        .status_pdn_state_o     (core_pdn_state),
        .obs_words_o            (all_obs_words)
    );

    //=========================================================================
    // ddr2_lpddr2_csr_slave
    //=========================================================================
    // Per-bank / system obs feeds are not yet generated by the core; tie to 0
    // so the readback registers report 0 until perf-monitor counters land.
    logic [7:0][31:0] zero_per_bank;
    logic [3:0][31:0] zero_defer_hist;
    assign zero_per_bank   = '{default:'0};
    assign zero_defer_hist = '{default:'0};

    ddr2_lpddr2_csr_slave #(
        .APB_ADDR_WIDTH (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH (APB_DATA_WIDTH)
    ) u_csr (
        .mc_clk                     (mc_clk),
        .mc_rst_n                   (mc_rst_n),
        .pclk                       (pclk),
        .presetn                    (presetn),

        .s_apb_PSEL                 (s_apb_PSEL),
        .s_apb_PENABLE              (s_apb_PENABLE),
        .s_apb_PREADY               (s_apb_PREADY),
        .s_apb_PADDR                (s_apb_PADDR),
        .s_apb_PWRITE               (s_apb_PWRITE),
        .s_apb_PWDATA               (s_apb_PWDATA),
        .s_apb_PSTRB                (s_apb_PSTRB),
        .s_apb_PPROT                (s_apb_PPROT),
        .s_apb_PRDATA               (s_apb_PRDATA),
        .s_apb_PSLVERR              (s_apb_PSLVERR),

        .cfg_init_start_o           (cfg_init_start),
        .cfg_init_force_restart_o   (cfg_init_force_restart),
        .cfg_pwr_req_low_power_o    (cfg_pwr_req_low_power),
        .cfg_pwr_req_dpd_o          (cfg_pwr_req_dpd),
        .cfg_pwr_req_active_o       (cfg_pwr_req_active),
        .cfg_pwr_req_self_refresh_o (cfg_pwr_req_self_refresh),
        .cfg_soft_reset_o           (cfg_soft_reset),
        .cfg_t_rc_o                 (cfg_t_rc),
        .cfg_t_rcd_o                (cfg_t_rcd),
        .cfg_t_rp_o                 (cfg_t_rp),
        .cfg_t_ras_o                (cfg_t_ras),
        .cfg_t_rfc_o                (cfg_t_rfc),
        .cfg_t_refi_o               (cfg_t_refi),
        .cfg_t_rrd_o                (cfg_t_rrd),
        .cfg_t_faw_o                (cfg_t_faw),
        .cfg_t_wtr_o                (cfg_t_wtr),
        .cfg_t_ccd_o                (cfg_t_ccd),
        .cfg_cl_o                   (cfg_cl),
        .cfg_cwl_o                  (cfg_cwl),
        .cfg_t_wr_o                 (cfg_t_wr),
        .cfg_t_rfcpb_o              (cfg_t_rfcpb),
        .cfg_mr0_o                  (cfg_mr0),
        .cfg_mr1_o                  (cfg_mr1),
        .cfg_mr2_o                  (cfg_mr2),
        .cfg_mr3_o                  (cfg_mr3),
        .cfg_pasr_banks_rank0_o     (cfg_pasr_banks_rank0),
        .cfg_pasr_segs_rank0_o      (cfg_pasr_segs_rank0),
        .cfg_lookahead_active_o     (cfg_lookahead_active),
        .cfg_force_inorder_o        (cfg_force_inorder),
        .cfg_happy_enable_o         (cfg_happy_enable),
        .cfg_age_max_runtime_o      (cfg_age_max_runtime),
        .cfg_txn_queue_high_water_o (cfg_txn_queue_high_water),
        .cfg_refpb_policy_or_o      (cfg_refpb_policy_or),
        .cfg_page_policy_or_o       (cfg_page_policy_or),
        .cfg_refresh_defer_active_o (cfg_refresh_defer_active),
        .cfg_zqcs_freq_hz_o         (cfg_zqcs_freq_hz),
        .cfg_addr_map_scheme_or_o   (cfg_addr_map_scheme_or),
        .cfg_zq_retries_o           (cfg_zq_retries),
        .cfg_init_timeout_ms_o      (cfg_init_timeout_ms),
        .cfg_warmup_cycles_o        (cfg_warmup_cycles),
        .cfg_hysteresis_o           (cfg_hysteresis),

        // status feed back
        .status_init_done_i         (core_init_done),
        .status_init_error_i        (1'b0),                 // not yet sourced
        .status_power_state_i       ({1'b0, core_pdn_state}),
        .status_pasr_active_i       (|cfg_pasr_banks_rank0),
        .status_init_step_dbg_i     (8'h0),                 // not yet sourced
        .status_version_match_i     (1'b1),
        .status_history_i           (32'h0),                // not yet sourced
        .status_temp_class_rank0_i  (2'b00),
        .cap_lookahead_max_i        (cap_lookahead_max_i),
        .cap_synth_mask_i           (cap_synth_mask_i),

        // obs feeds
        .obs_words_i                (all_obs_words),
        .obs_row_hit_i              (zero_per_bank),
        .obs_ref_latency_i          (zero_per_bank),
        .obs_txn_queue_depth_max_i  (32'h0),
        .obs_txn_queue_depth_avg_i  (32'h0),
        .obs_refresh_pending_max_i  (32'h0),
        .obs_refresh_defer_hist_i   (zero_defer_hist),
        .obs_page_pred_accuracy_i   (32'h0),
        .obs_axi_r_latency_avg_i    (32'h0),
        .obs_axi_r_latency_p99_i    (32'h0),
        .obs_axi_w_latency_avg_i    (32'h0)
    );

    // Lint silencers for runtime overrides not yet consumed by the core.
    wire unused_top = |{ cfg_init_start, cfg_init_force_restart, cfg_pwr_req_dpd,
                         cfg_pwr_req_active, cfg_soft_reset,
                         cfg_t_rfc, cfg_t_ccd, cfg_cl, cfg_cwl, cfg_t_rfcpb,
                         cfg_mr0, cfg_mr1, cfg_mr2, cfg_mr3,
                         cfg_pasr_segs_rank0,
                         cfg_lookahead_active, cfg_force_inorder, cfg_happy_enable,
                         cfg_age_max_runtime, cfg_txn_queue_high_water,
                         cfg_refpb_policy_or, cfg_page_policy_or,
                         cfg_refresh_defer_active, cfg_zqcs_freq_hz,
                         cfg_zq_retries, cfg_init_timeout_ms,
                         cfg_warmup_cycles, cfg_hysteresis };

endmodule : ddr2_lpddr2_top
