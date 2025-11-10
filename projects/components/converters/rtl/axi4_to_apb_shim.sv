// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_to_apb_shim
// Purpose: Axi4 To Apb Shim module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axi4_to_apb_shim #(
    parameter int DEPTH_AW          = 2,
    parameter int DEPTH_W           = 4,
    parameter int DEPTH_B           = 2,
    parameter int DEPTH_AR          = 2,
    parameter int DEPTH_R           = 4,
    parameter int SIDE_DEPTH        = 4,
    parameter int APB_CMD_DEPTH     = 4,
    parameter int APB_RSP_DEPTH     = 4,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int APB_ADDR_WIDTH    = 32,
    parameter int APB_DATA_WIDTH    = 32,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,
    parameter int APB_WSTRB_WIDTH   = APB_DATA_WIDTH / 8,
    // Declare parameters for short-hand notation
    parameter int AW                = AXI_ADDR_WIDTH,
    parameter int DW                = AXI_DATA_WIDTH,
    parameter int IW                = AXI_ID_WIDTH,
    parameter int UW                = AXI_USER_WIDTH,
    parameter int SW                = AXI_DATA_WIDTH / 8,
    parameter int APBAW             = APB_ADDR_WIDTH,
    parameter int APBDW             = APB_DATA_WIDTH,
    parameter int APBSW             = APB_DATA_WIDTH / 8,
    parameter int AXI2APBRATIO      = DW / APBDW,
    parameter int AWSize            = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int WSize             = DW+SW+1+UW,
    parameter int BSize             = IW+2+UW,
    parameter int ARSize            = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int RSize             = IW+DW+2+1+UW,
    parameter int APBCmdWidth       = APBAW + APBDW + APBSW + 3 + 1 + 1 + 1,
    parameter int APBRspWidth       = APBDW + 1 + 1 + 1,
    parameter int SideSize          = 1+IW+2+1+UW
) (
    // Clock and Reset
    input  logic                          aclk,
    input  logic                          aresetn,
    input  logic                          pclk,
    input  logic                          presetn,

    // Write address channel (AW)
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

    // Write data channel (W)
    input  logic [AXI_DATA_WIDTH-1:0]     s_axi_wdata,
    input  logic [AXI_WSTRB_WIDTH-1:0]    s_axi_wstrb,
    input  logic                          s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_wuser,
    input  logic                          s_axi_wvalid,
    output logic                          s_axi_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]       s_axi_bid,
    output logic [1:0]                    s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_buser,
    output logic                          s_axi_bvalid,
    input  logic                          s_axi_bready,

    // Read address channel (AR)
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

    // Read data channel (R)
    output logic [AXI_ID_WIDTH-1:0]       s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]     s_axi_rdata,
    output logic [1:0]                    s_axi_rresp,
    output logic                          s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_ruser,
    output logic                          s_axi_rvalid,
    input  logic                          s_axi_rready,

    // APB Master Interface (Outputs)
    output logic                          m_apb_PSEL,
    output logic [APB_ADDR_WIDTH-1:0]     m_apb_PADDR,
    output logic                          m_apb_PENABLE,
    output logic                          m_apb_PWRITE,
    output logic [APB_DATA_WIDTH-1:0]     m_apb_PWDATA,
    output logic [APB_WSTRB_WIDTH-1:0]    m_apb_PSTRB,
    output logic [2:0]                    m_apb_PPROT,

    // APB Master Interface (Inputs)
    input  logic [APB_DATA_WIDTH-1:0]     m_apb_PRDATA,
    input  logic                          m_apb_PREADY,
    input  logic                          m_apb_PSLVERR
);

    // AXI Skid interface signals
    logic [AWSize-1:0]                r_s_axi_aw_pkt;
    logic [3:0]                       r_s_axi_aw_count;
    logic                             r_s_axi_awvalid;
    logic                             w_s_axi_awready;
    logic [WSize-1:0]                 r_s_axi_w_pkt;
    logic                             r_s_axi_wvalid;
    logic                             w_s_axi_wready;
    logic [BSize-1:0]                 r_s_axi_b_pkt;
    logic                             w_s_axi_bvalid;
    logic                             r_s_axi_bready;
    logic [ARSize-1:0]                r_s_axi_ar_pkt;
    logic [3:0]                       r_s_axi_ar_count;
    logic                             r_s_axi_arvalid;
    logic                             w_s_axi_arready;
    logic [RSize-1:0]                 r_s_axi_r_pkt;
    logic                             w_s_axi_rvalid;
    logic                             r_s_axi_rready;

    // APB Master Interface
    // Command Packet
    logic                      w_cmd_valid;
    logic                      r_cmd_ready;
    logic [APBCmdWidth-1:0]    r_cmd_data;
    logic                      w_cmd_valid_apb;
    logic                      r_cmd_ready_apb;
    logic [APBCmdWidth-1:0]    r_cmd_data_apb;

    // Read Return interface
    logic                      r_rsp_valid;
    logic                      w_rsp_ready;
    logic [APBRspWidth-1:0]    r_rsp_data;
    logic                      r_rsp_valid_apb;
    logic                      w_rsp_ready_apb;
    logic [APBRspWidth-1:0]    r_rsp_data_apb;

    // Instantiate the axi4_slave_stub
    axi4_slave_stub #                   (
        .SKID_DEPTH_AW            (DEPTH_AW),
        .SKID_DEPTH_W             (DEPTH_W),
        .SKID_DEPTH_B             (DEPTH_B),
        .SKID_DEPTH_AR            (DEPTH_AR),
        .SKID_DEPTH_R             (DEPTH_R),
        .AXI_ID_WIDTH             (IW),
        .AXI_ADDR_WIDTH           (AW),
        .AXI_DATA_WIDTH           (DW),
        .AXI_USER_WIDTH           (UW)
    ) axi_slave_stub_inst         (
        .aclk                     (aclk),
        .aresetn                  (aresetn),
        // Write address channel  (AW)
        .s_axi_awid               (s_axi_awid),
        .s_axi_awaddr             (s_axi_awaddr),
        .s_axi_awlen              (s_axi_awlen),
        .s_axi_awsize             (s_axi_awsize),
        .s_axi_awburst            (s_axi_awburst),
        .s_axi_awlock             (s_axi_awlock),
        .s_axi_awcache            (s_axi_awcache),
        .s_axi_awprot             (s_axi_awprot),
        .s_axi_awqos              (s_axi_awqos),
        .s_axi_awregion           (s_axi_awregion),
        .s_axi_awuser             (s_axi_awuser),
        .s_axi_awvalid            (s_axi_awvalid),
        .s_axi_awready            (s_axi_awready),
        // Write data channel     (W)
        .s_axi_wdata              (s_axi_wdata),
        .s_axi_wstrb              (s_axi_wstrb),
        .s_axi_wlast              (s_axi_wlast),
        .s_axi_wuser              (s_axi_wuser),
        .s_axi_wvalid             (s_axi_wvalid),
        .s_axi_wready             (s_axi_wready),
        // Write response channel (B)
        .s_axi_bid                (s_axi_bid),
        .s_axi_bresp              (s_axi_bresp),
        .s_axi_buser              (s_axi_buser),
        .s_axi_bvalid             (s_axi_bvalid),
        .s_axi_bready             (s_axi_bready),
        // Read address channel   (AR)
        .s_axi_arid               (s_axi_arid),
        .s_axi_araddr             (s_axi_araddr),
        .s_axi_arlen              (s_axi_arlen),
        .s_axi_arsize             (s_axi_arsize),
        .s_axi_arburst            (s_axi_arburst),
        .s_axi_arlock             (s_axi_arlock),
        .s_axi_arcache            (s_axi_arcache),
        .s_axi_arprot             (s_axi_arprot),
        .s_axi_arqos              (s_axi_arqos),
        .s_axi_arregion           (s_axi_arregion),
        .s_axi_aruser             (s_axi_aruser),
        .s_axi_arvalid            (s_axi_arvalid),
        .s_axi_arready            (s_axi_arready),
        // Read data channel      (R)
        .s_axi_rid                (s_axi_rid),
        .s_axi_rdata              (s_axi_rdata),
        .s_axi_rresp              (s_axi_rresp),
        .s_axi_rlast              (s_axi_rlast),
        .s_axi_ruser              (s_axi_ruser),
        .s_axi_rvalid             (s_axi_rvalid),
        .s_axi_rready             (s_axi_rready),
        // Stub Outputs/Inputs
        // AW interface
        .fub_axi_awvalid          (r_s_axi_awvalid),
        .fub_axi_awready          (w_s_axi_awready),
        .fub_axi_aw_count         (r_s_axi_aw_count),
        .fub_axi_aw_pkt           (r_s_axi_aw_pkt),
        // W interface
        .fub_axi_wvalid           (r_s_axi_wvalid),
        .fub_axi_wready           (w_s_axi_wready),
        .fub_axi_w_pkt            (r_s_axi_w_pkt),
        // B interface
        .fub_axi_bvalid           (w_s_axi_bvalid),
        .fub_axi_bready           (r_s_axi_bready),
        .fub_axi_b_pkt            (r_s_axi_b_pkt),
        // AR interface
        .fub_axi_arvalid          (r_s_axi_arvalid),
        .fub_axi_arready          (w_s_axi_arready),
        .fub_axi_ar_count         (r_s_axi_ar_count),
        .fub_axi_ar_pkt           (r_s_axi_ar_pkt),
        // R interface
        .fub_axi_rvalid           (w_s_axi_rvalid),
        .fub_axi_rready           (r_s_axi_rready),
        .fub_axi_r_pkt            (r_s_axi_r_pkt)
    );

    // Instantiate the AXI to APB conversion module
    axi4_to_apb_convert #(
        .SIDE_DEPTH         (SIDE_DEPTH),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH     (AXI_USER_WIDTH),
        .APB_ADDR_WIDTH     (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH     (APB_DATA_WIDTH),
        .AXI_WSTRB_WIDTH    (AXI_WSTRB_WIDTH),
        .APB_WSTRB_WIDTH    (APB_WSTRB_WIDTH)
    ) axi4_to_apb_convert_inst (
        .aclk                 (aclk),
        .aresetn              (aresetn),
        .r_s_axi_aw_pkt       (r_s_axi_aw_pkt),
        .r_s_axi_aw_count     (r_s_axi_aw_count),
        .r_s_axi_awvalid      (r_s_axi_awvalid),
        .w_s_axi_awready      (w_s_axi_awready),
        .r_s_axi_w_pkt        (r_s_axi_w_pkt),
        .r_s_axi_wvalid       (r_s_axi_wvalid),
        .w_s_axi_wready       (w_s_axi_wready),
        .r_s_axi_b_pkt        (r_s_axi_b_pkt),
        .w_s_axi_bvalid       (w_s_axi_bvalid),
        .r_s_axi_bready       (r_s_axi_bready),
        .r_s_axi_ar_pkt       (r_s_axi_ar_pkt),
        .r_s_axi_ar_count     (r_s_axi_ar_count),
        .r_s_axi_arvalid      (r_s_axi_arvalid),
        .w_s_axi_arready      (w_s_axi_arready),
        .r_s_axi_r_pkt        (r_s_axi_r_pkt),
        .w_s_axi_rvalid       (w_s_axi_rvalid),
        .r_s_axi_rready       (r_s_axi_rready),
        .w_cmd_valid          (w_cmd_valid),
        .r_cmd_ready          (r_cmd_ready),
        .r_cmd_data           (r_cmd_data),
        .r_rsp_valid          (r_rsp_valid),
        .w_rsp_ready          (w_rsp_ready),
        .r_rsp_data           (r_rsp_data)
    );

    cdc_handshake #(
        .DATA_WIDTH(APBCmdWidth)
    ) u_cmd_cdc_handshake (
        .clk_src         (aclk),
        .rst_src_n       (aresetn),
        .src_valid       (w_cmd_valid),
        .src_ready       (r_cmd_ready),
        .src_data        (r_cmd_data),

        .clk_dst         (pclk),
        .rst_dst_n       (presetn),
        .dst_valid       (w_cmd_valid_apb),
        .dst_ready       (r_cmd_ready_apb),
        .dst_data        (r_cmd_data_apb)
    );

    cdc_handshake #(
        .DATA_WIDTH(APBRspWidth)
    ) u_rsp_cdc_handshake (
        .clk_src         (pclk),
        .rst_src_n       (presetn),
        .src_valid       (r_rsp_valid_apb),
        .src_ready       (w_rsp_ready_apb),
        .src_data        (r_rsp_data_apb),

        .clk_dst         (aclk),
        .rst_dst_n       (aresetn),
        .dst_valid       (r_rsp_valid),
        .dst_ready       (w_rsp_ready),
        .dst_data        (r_rsp_data)
    );


    // Instantiate the APB Master interface
    apb_master_stub # (
        .CMD_DEPTH        (APB_CMD_DEPTH),
        .RSP_DEPTH        (APB_RSP_DEPTH),
        .DATA_WIDTH       (APBDW),
        .ADDR_WIDTH       (APBAW),
        .STRB_WIDTH       (APBSW),       // DATA_WIDTH / 8
        .CMD_PACKET_WIDTH (APBCmdWidth), // ADDR_WIDTH + DATA_WIDTH + STRB_WIDTH + 4
        .RESP_PACKET_WIDTH(APBRspWidth)  // DATA_WIDTH + 2
    ) apb_master_inst     (
        .pclk             (pclk),
        .presetn          (presetn),
        .m_apb_PSEL       (m_apb_PSEL),
        .m_apb_PENABLE    (m_apb_PENABLE),
        .m_apb_PADDR      (m_apb_PADDR),
        .m_apb_PWRITE     (m_apb_PWRITE),
        .m_apb_PWDATA     (m_apb_PWDATA),
        .m_apb_PSTRB      (m_apb_PSTRB),
        .m_apb_PPROT      (m_apb_PPROT),
        .m_apb_PRDATA     (m_apb_PRDATA),
        .m_apb_PSLVERR    (m_apb_PSLVERR),
        .m_apb_PREADY     (m_apb_PREADY),
        .cmd_valid        (w_cmd_valid_apb),
        .cmd_ready        (r_cmd_ready_apb),
        .cmd_data         (r_cmd_data_apb),
        .rsp_valid        (r_rsp_valid_apb),
        .rsp_ready        (w_rsp_ready_apb),
        .rsp_data         (r_rsp_data_apb)
    );

endmodule : axi4_to_apb_shim
