// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Cocotb-side testbench wrapper around ddr2_lpddr2_top.
//
// Purpose: expose the DUT's DFI bus under the signal naming the
// CocoTBFramework DFISlavePHY BFM expects (`phy_dfi_*`). The BFM
// hard-codes its bus prefix to `phy_dfi`, so this thin alias module
// keeps both sides clean: the DUT stays vendor-agnostic with `dfi_*`
// ports, and the BFM auto-binds with no per-DUT plumbing.
//
// All phy_dfi_* signals are *internal logic nets*, not ports —
// cocotb-bus + Verilator (--public-flat-rw) lets the BFM read/write
// them directly through the toplevel hierarchy. The wrapper carries
// AXI4 + APB as ports because those are driven by cocotb-side BFMs
// that expect ports.

`timescale 1ns / 1ps

module ddr2_lpddr2_top_tb_top
    import ddr2_lpddr2_pkg::*;
#(
    parameter int AXI_ADDR_WIDTH   = 32,
    parameter int AXI_DATA_WIDTH   = 64,
    parameter int AXI_ID_WIDTH     = 4,
    parameter int AXI_USER_WIDTH   = 8,
    parameter int AXI_STRB_WIDTH   = AXI_DATA_WIDTH / 8,

    parameter int APB_ADDR_WIDTH   = 12,
    parameter int APB_DATA_WIDTH   = 32,
    parameter int APB_STRB_WIDTH   = APB_DATA_WIDTH / 8,
    parameter int APB_PROT_WIDTH   = 3,

    parameter int NUM_RANKS        = 1,
    parameter int NUM_BANKS        = 8,
    parameter int ROW_WIDTH        = 14,
    parameter int COL_WIDTH        = 10,

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
    input  logic                          mc_clk,
    input  logic                          mc_rst_n,
    input  logic                          pclk,
    input  logic                          presetn,

    // ----- AXI4 slave (host) -------------------------------------------
    input  logic [AXI_ID_WIDTH-1:0]       s_axi_awid,
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
    output logic [AXI_ID_WIDTH-1:0]       s_axi_bid,
    output logic [1:0]                    s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_buser,
    output logic                          s_axi_bvalid,
    input  logic                          s_axi_bready,
    input  logic [AXI_ID_WIDTH-1:0]       s_axi_arid,
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
    output logic [AXI_ID_WIDTH-1:0]       s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]     s_axi_rdata,
    output logic [1:0]                    s_axi_rresp,
    output logic                          s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_ruser,
    output logic                          s_axi_rvalid,
    input  logic                          s_axi_rready,

    // ----- APB slave (CSR) ---------------------------------------------
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

    // ----- Externs (not yet in CSR map) --------------------------------
    input  memtype_e                      memtype_i,
    input  logic [7:0]                    t_phy_wrlat_i,
    input  logic [7:0]                    t_rddata_en_i,
    input  logic                          rd_in_order_i,
    input  logic [3:0]                    cap_lookahead_max_i,
    input  logic [3:0]                    cap_synth_mask_i
);

    //=========================================================================
    // PHY-side DFI bus — exposed as internal `phy_dfi_*` nets so the
    // DFISlavePHY BFM auto-binds with prefix=phy_dfi.
    //
    // Some signals (init_complete, phyupd_type) are NOT driven by the
    // BFM and need to be driven by the cocotb test directly. Verilator
    // with --public-flat-rw makes that legal — internal nets are
    // writable from the simulator side.
    //=========================================================================

    // MC-driven (DUT outputs) ----------------------------------------------
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
    logic [DFI_CS_BUS_W-1:0]     phy_dfi_dram_clk_disable;
    logic                        phy_dfi_init_start;
    logic                        phy_dfi_ctrlupd_req;
    logic                        phy_dfi_phyupd_ack;

    // PHY-driven (BFM-owned) inputs to the DUT -----------------------------
    logic [DFI_DATA_WIDTH-1:0]   phy_dfi_rddata;
    logic [DFI_VALID_WIDTH-1:0]  phy_dfi_rddata_valid;
    logic                        phy_dfi_init_complete;
    logic                        phy_dfi_ctrlupd_ack;
    logic                        phy_dfi_phyupd_req;
    logic [1:0]                  phy_dfi_phyupd_type;

    // v3+ signals — BFM bumps them in __init__ + the v2.1 behavior
    // samples freq_change_req every cycle. Keep declared so the BFM's
    // cocotb-bus binding succeeds; not wired to the DUT.
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

    //=========================================================================
    // DUT
    //=========================================================================
    ddr2_lpddr2_top #(
        .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH),
        .APB_ADDR_WIDTH (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH (APB_DATA_WIDTH),
        .NUM_RANKS      (NUM_RANKS),
        .NUM_BANKS      (NUM_BANKS),
        .ROW_WIDTH      (ROW_WIDTH),
        .COL_WIDTH      (COL_WIDTH),
        .DFI_RATE       (DFI_RATE)
    ) u_dut (
        .mc_clk         (mc_clk),
        .mc_rst_n       (mc_rst_n),
        .pclk           (pclk),
        .presetn        (presetn),

        .s_axi_awid     (s_axi_awid),
        .s_axi_awaddr   (s_axi_awaddr),
        .s_axi_awlen    (s_axi_awlen),
        .s_axi_awsize   (s_axi_awsize),
        .s_axi_awburst  (s_axi_awburst),
        .s_axi_awlock   (s_axi_awlock),
        .s_axi_awcache  (s_axi_awcache),
        .s_axi_awprot   (s_axi_awprot),
        .s_axi_awqos    (s_axi_awqos),
        .s_axi_awregion (s_axi_awregion),
        .s_axi_awuser   (s_axi_awuser),
        .s_axi_awvalid  (s_axi_awvalid),
        .s_axi_awready  (s_axi_awready),
        .s_axi_wdata    (s_axi_wdata),
        .s_axi_wstrb    (s_axi_wstrb),
        .s_axi_wlast    (s_axi_wlast),
        .s_axi_wuser    (s_axi_wuser),
        .s_axi_wvalid   (s_axi_wvalid),
        .s_axi_wready   (s_axi_wready),
        .s_axi_bid      (s_axi_bid),
        .s_axi_bresp    (s_axi_bresp),
        .s_axi_buser    (s_axi_buser),
        .s_axi_bvalid   (s_axi_bvalid),
        .s_axi_bready   (s_axi_bready),
        .s_axi_arid     (s_axi_arid),
        .s_axi_araddr   (s_axi_araddr),
        .s_axi_arlen    (s_axi_arlen),
        .s_axi_arsize   (s_axi_arsize),
        .s_axi_arburst  (s_axi_arburst),
        .s_axi_arlock   (s_axi_arlock),
        .s_axi_arcache  (s_axi_arcache),
        .s_axi_arprot   (s_axi_arprot),
        .s_axi_arqos    (s_axi_arqos),
        .s_axi_arregion (s_axi_arregion),
        .s_axi_aruser   (s_axi_aruser),
        .s_axi_arvalid  (s_axi_arvalid),
        .s_axi_arready  (s_axi_arready),
        .s_axi_rid      (s_axi_rid),
        .s_axi_rdata    (s_axi_rdata),
        .s_axi_rresp    (s_axi_rresp),
        .s_axi_rlast    (s_axi_rlast),
        .s_axi_ruser    (s_axi_ruser),
        .s_axi_rvalid   (s_axi_rvalid),
        .s_axi_rready   (s_axi_rready),

        .s_apb_PSEL     (s_apb_PSEL),
        .s_apb_PENABLE  (s_apb_PENABLE),
        .s_apb_PREADY   (s_apb_PREADY),
        .s_apb_PADDR    (s_apb_PADDR),
        .s_apb_PWRITE   (s_apb_PWRITE),
        .s_apb_PWDATA   (s_apb_PWDATA),
        .s_apb_PSTRB    (s_apb_PSTRB),
        .s_apb_PPROT    (s_apb_PPROT),
        .s_apb_PRDATA   (s_apb_PRDATA),
        .s_apb_PSLVERR  (s_apb_PSLVERR),

        // DFI alias — DUT dfi_* ↔ phy_dfi_* (PHY-side BFM naming)
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

        .memtype_i              (memtype_i),
        .t_phy_wrlat_i          (t_phy_wrlat_i),
        .t_rddata_en_i          (t_rddata_en_i),
        .rd_in_order_i          (rd_in_order_i),
        .cap_lookahead_max_i    (cap_lookahead_max_i),
        .cap_synth_mask_i       (cap_synth_mask_i)
    );

    // Silence Verilator's unused-output warnings for unused phy_dfi_* lines.
    wire unused = |{ phy_dfi_error, phy_dfi_error_info, phy_dfi_crc_alert,
                     phy_dfi_training_active, phy_dfi_training_phase,
                     phy_dfi_parity_check, phy_dfi_freq_change_ack,
                     phy_dfi_freq_change_req, phy_dfi_disconnect_req,
                     phy_dfi_phymstr_req,
                     phy_dfi_init_start, phy_dfi_dram_clk_disable,
                     phy_dfi_ctrlupd_req, phy_dfi_phyupd_ack };

endmodule : ddr2_lpddr2_top_tb_top
