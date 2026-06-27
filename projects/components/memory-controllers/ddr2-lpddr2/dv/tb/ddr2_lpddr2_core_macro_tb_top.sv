// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Cocotb-side TB wrapper around ddr2_lpddr2_core_macro. Exposes the
// AXI4 host port as toplevel ports (BFM-driven) and aliases the DFI
// bus to `phy_dfi_*` for the CocoTBFramework DFISlavePHY BFM. CSR
// configuration is replaced with direct cfg input ports — the TB
// drives them at reset.
//
// This is the "AXI-to-DFI macro" test env requested 2026-06-26.

`timescale 1ns / 1ps

module ddr2_lpddr2_core_macro_tb_top
    import ddr2_lpddr2_pkg::*;
#(
    parameter int AXI_ADDR_WIDTH   = 32,
    parameter int AXI_DATA_WIDTH   = 64,
    parameter int AXI_ID_WIDTH     = 4,
    parameter int AXI_USER_WIDTH   = 8,
    parameter int AXI_STRB_WIDTH   = AXI_DATA_WIDTH / 8,

    parameter int NUM_RANKS        = 1,
    parameter int NUM_BANKS        = 8,
    parameter int ROW_WIDTH        = 14,
    parameter int COL_WIDTH        = 10,
    parameter int PAGE_POLICY      = 1,

    parameter int DFI_RATE         = 2,
    parameter int DFI_DATA_WIDTH   = AXI_DATA_WIDTH * DFI_RATE,
    parameter int DFI_STRB_WIDTH   = AXI_STRB_WIDTH * DFI_RATE,
    parameter int DFI_EN_WIDTH     = DFI_RATE,
    parameter int DFI_VALID_WIDTH  = DFI_RATE,
    parameter int DFI_ADDR_BUS_W   = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W   = $clog2(NUM_BANKS) * DFI_RATE,
    parameter int DFI_CTRL_BUS_W   = 1 * DFI_RATE,
    parameter int DFI_CS_BUS_W     = NUM_RANKS * DFI_RATE
) (
    input  logic                           mc_clk,
    input  logic                           mc_rst_n,

    // ---- direct cfg surface (no CSR) ----
    input  memtype_e                       memtype_i,
    input  logic [15:0]                    t_refi_i,
    input  logic [7:0]                     t_rcd_i,
    input  logic [7:0]                     t_rp_i,
    input  logic [7:0]                     t_ras_i,
    input  logic [7:0]                     t_rc_i,
    input  logic [7:0]                     t_wr_i,
    input  logic [7:0]                     t_wtr_i,
    input  logic [7:0]                     t_rtp_i,
    input  logic [7:0]                     t_faw_i,
    input  logic [7:0]                     t_rrd_i,
    input  logic                           enable_pde_i,
    input  logic                           enable_sref_i,
    input  logic [7:0]                     t_phy_wrlat_i,
    input  logic [7:0]                     t_rddata_en_i,
    input  logic                           rd_in_order_i,

    // ---- AXI4 slave port ----
    input  logic [AXI_ID_WIDTH-1:0]        s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]      s_axi_awaddr,
    input  logic [7:0]                     s_axi_awlen,
    input  logic [2:0]                     s_axi_awsize,
    input  logic [1:0]                     s_axi_awburst,
    input  logic                           s_axi_awlock,
    input  logic [3:0]                     s_axi_awcache,
    input  logic [2:0]                     s_axi_awprot,
    input  logic [3:0]                     s_axi_awqos,
    input  logic [3:0]                     s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]      s_axi_awuser,
    input  logic                           s_axi_awvalid,
    output logic                           s_axi_awready,

    input  logic [AXI_DATA_WIDTH-1:0]      s_axi_wdata,
    input  logic [AXI_STRB_WIDTH-1:0]      s_axi_wstrb,
    input  logic                           s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]      s_axi_wuser,
    input  logic                           s_axi_wvalid,
    output logic                           s_axi_wready,

    output logic [AXI_ID_WIDTH-1:0]        s_axi_bid,
    output logic [1:0]                     s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]      s_axi_buser,
    output logic                           s_axi_bvalid,
    input  logic                           s_axi_bready,

    input  logic [AXI_ID_WIDTH-1:0]        s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]      s_axi_araddr,
    input  logic [7:0]                     s_axi_arlen,
    input  logic [2:0]                     s_axi_arsize,
    input  logic [1:0]                     s_axi_arburst,
    input  logic                           s_axi_arlock,
    input  logic [3:0]                     s_axi_arcache,
    input  logic [2:0]                     s_axi_arprot,
    input  logic [3:0]                     s_axi_arqos,
    input  logic [3:0]                     s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]      s_axi_aruser,
    input  logic                           s_axi_arvalid,
    output logic                           s_axi_arready,

    output logic [AXI_ID_WIDTH-1:0]        s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]      s_axi_rdata,
    output logic [1:0]                     s_axi_rresp,
    output logic                           s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]      s_axi_ruser,
    output logic                           s_axi_rvalid,
    input  logic                           s_axi_rready,

    // ---- status visibility ----
    output logic                           status_init_done,
    output logic                           status_init_busy
);

    // DFI bus — internal nets exposed under the phy_dfi_* names the
    // DFISlavePHY BFM auto-discovers. The BFM reaches in via cocotb-bus
    // hierarchy; no per-DUT plumbing.
    logic [DFI_ADDR_BUS_W-1:0]   phy_dfi_address;
    logic [DFI_BANK_BUS_W-1:0]   phy_dfi_bank;
    logic [DFI_CTRL_BUS_W-1:0]   phy_dfi_cas_n;
    logic [DFI_CTRL_BUS_W-1:0]   phy_dfi_ras_n;
    logic [DFI_CTRL_BUS_W-1:0]   phy_dfi_we_n;
    logic [DFI_CS_BUS_W-1:0]     phy_dfi_cs_n;
    logic [DFI_CS_BUS_W-1:0]     phy_dfi_cke;
    logic [DFI_CS_BUS_W-1:0]     phy_dfi_odt;
    logic [DFI_DATA_WIDTH-1:0]   phy_dfi_wrdata;
    logic [DFI_EN_WIDTH-1:0]     phy_dfi_wrdata_en;
    logic [DFI_STRB_WIDTH-1:0]   phy_dfi_wrdata_mask;
    logic [DFI_EN_WIDTH-1:0]     phy_dfi_rddata_en;
    logic [DFI_DATA_WIDTH-1:0]   phy_dfi_rddata;
    logic [DFI_VALID_WIDTH-1:0]  phy_dfi_rddata_valid;
    logic [DFI_CS_BUS_W-1:0]     phy_dfi_dram_clk_disable;
    logic                        phy_dfi_init_start;
    logic                        phy_dfi_init_complete;
    logic                        phy_dfi_ctrlupd_req;
    logic                        phy_dfi_ctrlupd_ack;
    logic                        phy_dfi_phyupd_req;
    logic                        phy_dfi_phyupd_ack;
    logic [1:0]                  phy_dfi_phyupd_type;

    // BFM-driven helper signals (v3+/v4+ DFI extension surface). Declared
    // here only so DFISlavePHY can drive them; not consumed by the DUT.
    logic                        phy_dfi_error;
    logic                        phy_dfi_error_info;
    logic                        phy_dfi_crc_alert;
    logic                        phy_dfi_training_active;
    logic                        phy_dfi_training_phase;
    logic                        phy_dfi_parity_check;
    logic                        phy_dfi_freq_change_ack;
    logic                        phy_dfi_freq_change_req;
    logic                        phy_dfi_disconnect_req;
    logic                        phy_dfi_phymstr_req;

    wire unused = |{ phy_dfi_error, phy_dfi_error_info, phy_dfi_crc_alert,
                     phy_dfi_training_active, phy_dfi_training_phase,
                     phy_dfi_parity_check, phy_dfi_freq_change_ack,
                     phy_dfi_freq_change_req, phy_dfi_disconnect_req,
                     phy_dfi_phymstr_req };

    // Default scheme: ROW_MAJOR. xor_seed=0.
    addr_map_scheme_e w_scheme_active;
    assign w_scheme_active = ADDR_MAP_ROW_MAJOR;

    ddr2_lpddr2_core_macro #(
        .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .AXI_USER_WIDTH  (AXI_USER_WIDTH),
        .NUM_RANKS       (NUM_RANKS),
        .NUM_BANKS       (NUM_BANKS),
        .ROW_WIDTH       (ROW_WIDTH),
        .COL_WIDTH       (COL_WIDTH),
        .PAGE_POLICY     (PAGE_POLICY),
        .DFI_RATE        (DFI_RATE),
        .DFI_DATA_WIDTH  (DFI_DATA_WIDTH),
        .DFI_STRB_WIDTH  (DFI_STRB_WIDTH),
        .DFI_EN_WIDTH    (DFI_EN_WIDTH),
        .DFI_VALID_WIDTH (DFI_VALID_WIDTH),
        .DFI_CS_WIDTH    (NUM_RANKS)
    ) u_dut (
        .mc_clk                 (mc_clk),
        .mc_rst_n               (mc_rst_n),
        .scheme_active_i        (w_scheme_active),
        .xor_seed_i             (8'h0),

        .memtype_i              (memtype_i),
        .t_refi_i               (t_refi_i),
        .t_rcd_i                (t_rcd_i),
        .t_rp_i                 (t_rp_i),
        .t_ras_i                (t_ras_i),
        .t_rc_i                 (t_rc_i),
        .t_wr_i                 (t_wr_i),
        .t_wtr_i                (t_wtr_i),
        .t_rtp_i                (t_rtp_i),
        .t_faw_i                (t_faw_i),
        .t_rrd_i                (t_rrd_i),
        .idle_threshold_i       (16'd64),
        .enable_pde_i           (enable_pde_i),
        .enable_sref_i          (enable_sref_i),
        .mr_we_i                (1'b0),
        .mr_index_i             (5'h0),
        .mr_data_i              (16'h0),
        .mr_rank_i              ('0),
        .t_phy_wrlat_i          (t_phy_wrlat_i),
        .t_rddata_en_i          (t_rddata_en_i),
        .rd_in_order_i          (rd_in_order_i),

        .s_axi_awid             (s_axi_awid),
        .s_axi_awaddr           (s_axi_awaddr),
        .s_axi_awlen            (s_axi_awlen),
        .s_axi_awsize           (s_axi_awsize),
        .s_axi_awburst          (s_axi_awburst),
        .s_axi_awlock           (s_axi_awlock),
        .s_axi_awcache          (s_axi_awcache),
        .s_axi_awprot           (s_axi_awprot),
        .s_axi_awqos            (s_axi_awqos),
        .s_axi_awregion         (s_axi_awregion),
        .s_axi_awuser           (s_axi_awuser),
        .s_axi_awvalid          (s_axi_awvalid),
        .s_axi_awready          (s_axi_awready),
        .s_axi_wdata            (s_axi_wdata),
        .s_axi_wstrb            (s_axi_wstrb),
        .s_axi_wlast            (s_axi_wlast),
        .s_axi_wuser            (s_axi_wuser),
        .s_axi_wvalid           (s_axi_wvalid),
        .s_axi_wready           (s_axi_wready),
        .s_axi_bid              (s_axi_bid),
        .s_axi_bresp            (s_axi_bresp),
        .s_axi_buser            (s_axi_buser),
        .s_axi_bvalid           (s_axi_bvalid),
        .s_axi_bready           (s_axi_bready),
        .s_axi_arid             (s_axi_arid),
        .s_axi_araddr           (s_axi_araddr),
        .s_axi_arlen            (s_axi_arlen),
        .s_axi_arsize           (s_axi_arsize),
        .s_axi_arburst          (s_axi_arburst),
        .s_axi_arlock           (s_axi_arlock),
        .s_axi_arcache          (s_axi_arcache),
        .s_axi_arprot           (s_axi_arprot),
        .s_axi_arqos            (s_axi_arqos),
        .s_axi_arregion         (s_axi_arregion),
        .s_axi_aruser           (s_axi_aruser),
        .s_axi_arvalid          (s_axi_arvalid),
        .s_axi_arready          (s_axi_arready),
        .s_axi_rid              (s_axi_rid),
        .s_axi_rdata            (s_axi_rdata),
        .s_axi_rresp            (s_axi_rresp),
        .s_axi_rlast            (s_axi_rlast),
        .s_axi_ruser            (s_axi_ruser),
        .s_axi_rvalid           (s_axi_rvalid),
        .s_axi_rready           (s_axi_rready),

        .dfi_address_o          (phy_dfi_address),
        .dfi_bank_o             (phy_dfi_bank),
        .dfi_cas_n_o            (phy_dfi_cas_n),
        .dfi_ras_n_o            (phy_dfi_ras_n),
        .dfi_we_n_o             (phy_dfi_we_n),
        .dfi_cs_n_o             (phy_dfi_cs_n),
        .dfi_cke_o              (phy_dfi_cke),
        .dfi_odt_o              (phy_dfi_odt),
        .dfi_wrdata_o           (phy_dfi_wrdata),
        .dfi_wrdata_en_o        (phy_dfi_wrdata_en),
        .dfi_wrdata_mask_o      (phy_dfi_wrdata_mask),
        .dfi_rddata_en_o        (phy_dfi_rddata_en),
        .dfi_rddata_i           (phy_dfi_rddata),
        .dfi_rddata_valid_i     (phy_dfi_rddata_valid),
        .dfi_dram_clk_disable_o (phy_dfi_dram_clk_disable),
        .dfi_init_start_o       (phy_dfi_init_start),
        .dfi_init_complete_i    (phy_dfi_init_complete),
        .dfi_ctrlupd_req_o      (phy_dfi_ctrlupd_req),
        .dfi_ctrlupd_ack_i      (phy_dfi_ctrlupd_ack),
        .dfi_phyupd_req_i       (phy_dfi_phyupd_req),
        .dfi_phyupd_ack_o       (phy_dfi_phyupd_ack),
        .dfi_phyupd_type_i      (phy_dfi_phyupd_type),

        .status_init_done_o     (status_init_done),
        .status_init_busy_o     (status_init_busy),
        .status_pdn_state_o     (),
        .obs_words_o            ()
    );

endmodule : ddr2_lpddr2_core_macro_tb_top
