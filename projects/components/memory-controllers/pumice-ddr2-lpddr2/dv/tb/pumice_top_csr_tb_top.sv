// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: pumice_top_csr_tb_top
// Purpose: Verification wrapper for the new pumice_top (core + PeakRDL CSR).
//          Exposes the DFI pin bus on phy_dfi_* nets for DFISlavePHY, and the
//          register cpuif + host AXI + clocks as ports the TB drives.
`timescale 1ns / 1ps

module pumice_top_csr_tb_top
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

    parameter int DW  = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int SW  = DW / 8,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int AW  = AXI_ADDR_WIDTH,
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
    input  logic         s_cpuif_req, s_cpuif_req_is_wr,
    input  logic [11:0]  s_cpuif_addr,
    input  logic [31:0]  s_cpuif_wr_data, s_cpuif_wr_biten,
    output logic         s_cpuif_req_stall_wr, s_cpuif_req_stall_rd,
    output logic         s_cpuif_rd_ack, s_cpuif_rd_err,
    output logic [31:0]  s_cpuif_rd_data,
    output logic         s_cpuif_wr_ack, s_cpuif_wr_err,
    output logic         init_done_o,
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
    logic [DFI_ADDR_BUS_W-1:0]  phy_dfi_address;
    logic [DFI_BANK_BUS_W-1:0]  phy_dfi_bank;
    logic [DFI_CTRL_BUS_W-1:0]  phy_dfi_cas_n, phy_dfi_ras_n, phy_dfi_we_n;
    logic [DFI_CS_BUS_W-1:0]    phy_dfi_cs_n, phy_dfi_odt;
    logic [DFI_DATA_WIDTH-1:0]  phy_dfi_wrdata;
    logic [DFI_EN_WIDTH-1:0]    phy_dfi_wrdata_en;
    logic [DFI_STRB_WIDTH-1:0]  phy_dfi_wrdata_mask;
    logic [DFI_EN_WIDTH-1:0]    phy_dfi_rddata_en;
    logic [DFI_DATA_WIDTH-1:0]  phy_dfi_rddata;
    logic [DFI_VALID_WIDTH-1:0] phy_dfi_rddata_valid;
    logic                       phy_dfi_init_start, phy_dfi_init_complete;
    logic phy_dfi_error, phy_dfi_error_info, phy_dfi_crc_alert;
    logic phy_dfi_ctrlupd_req, phy_dfi_ctrlupd_ack, phy_dfi_phyupd_req, phy_dfi_phyupd_ack;
    logic [1:0] phy_dfi_phyupd_type;
    logic phy_dfi_disconnect_req, phy_dfi_freq_change_req, phy_dfi_freq_change_ack;
    logic phy_dfi_parity_check, phy_dfi_phymstr_req, phy_dfi_training_active, phy_dfi_training_phase;
    logic [DFI_CS_BUS_W-1:0] phy_dfi_cke, phy_dfi_dram_clk_disable;
    assign phy_dfi_error=0; assign phy_dfi_error_info=0; assign phy_dfi_crc_alert=0;
    assign phy_dfi_ctrlupd_req=0; assign phy_dfi_ctrlupd_ack=0; assign phy_dfi_phyupd_req=0;
    assign phy_dfi_phyupd_ack=0; assign phy_dfi_phyupd_type=0; assign phy_dfi_disconnect_req=0;
    assign phy_dfi_freq_change_req=0; assign phy_dfi_freq_change_ack=0; assign phy_dfi_parity_check=0;
    assign phy_dfi_phymstr_req=0; assign phy_dfi_training_active=0; assign phy_dfi_training_phase=0;
    assign phy_dfi_cke='1; assign phy_dfi_dram_clk_disable=0;

    pumice_top #(
        .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW), .NUM_RANKS(NUM_RANKS),
        .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH),
        .DFI_RATE(DFI_RATE), .DRAM_BEAT_WIDTH(DRAM_BEAT_WIDTH), .BL(BL),
        .NUM_ENTRIES(NUM_ENTRIES), .N_SRAM_SLOTS(N_SRAM_SLOTS)
    ) u_top (
        .aclk(aclk), .aresetn(aresetn), .dfi_clk(dfi_clk), .dfi_rstn(dfi_rstn),
        .s_cpuif_req(s_cpuif_req), .s_cpuif_req_is_wr(s_cpuif_req_is_wr),
        .s_cpuif_addr(s_cpuif_addr), .s_cpuif_wr_data(s_cpuif_wr_data),
        .s_cpuif_wr_biten(s_cpuif_wr_biten),
        .s_cpuif_req_stall_wr(s_cpuif_req_stall_wr), .s_cpuif_req_stall_rd(s_cpuif_req_stall_rd),
        .s_cpuif_rd_ack(s_cpuif_rd_ack), .s_cpuif_rd_err(s_cpuif_rd_err),
        .s_cpuif_rd_data(s_cpuif_rd_data),
        .s_cpuif_wr_ack(s_cpuif_wr_ack), .s_cpuif_wr_err(s_cpuif_wr_err),
        .init_done_o(init_done_o),
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
        .dfi_address_o(phy_dfi_address), .dfi_bank_o(phy_dfi_bank),
        .dfi_cas_n_o(phy_dfi_cas_n), .dfi_ras_n_o(phy_dfi_ras_n), .dfi_we_n_o(phy_dfi_we_n),
        .dfi_cs_n_o(phy_dfi_cs_n), .dfi_odt_o(phy_dfi_odt),
        .dfi_wrdata_o(phy_dfi_wrdata), .dfi_wrdata_en_o(phy_dfi_wrdata_en),
        .dfi_wrdata_mask_o(phy_dfi_wrdata_mask),
        .dfi_rddata_en_o(phy_dfi_rddata_en), .dfi_rddata_i(phy_dfi_rddata),
        .dfi_rddata_valid_i(phy_dfi_rddata_valid),
        .dfi_init_start_o(phy_dfi_init_start), .dfi_init_complete_i(phy_dfi_init_complete)
    );
endmodule : pumice_top_csr_tb_top
