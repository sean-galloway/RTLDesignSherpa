// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_master_wr
// Purpose: Axi Master Wr module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axi_master_wr
#(
     // Error Packet Identifiers
    parameter int UNIT_ID            = 99,
    parameter int AGENT_ID           = 99,

    // AXI parameters
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Channel parameter
    parameter int CHANNELS          = 16,

    // Skid buffer depths
    parameter int SKID_DEPTH_AW     = 2,
    parameter int SKID_DEPTH_W      = 4,
    parameter int SKID_DEPTH_B      = 2,

    // FIFO parameters
    parameter int SPLIT_FIFO_DEPTH  = 2,
    parameter int ERROR_FIFO_DEPTH  = 2,
    parameter int ADDR_FIFO_DEPTH   = 4,     // Depth of address tracking FIFO

    // Derived parameters
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int AWSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int WSize    = DW+(DW/8)+1+UW,
    parameter int BSize    = IW+2+UW
)
(
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Alignment mask signal (12-bit)
    input  logic [11:0]                alignment_mask,

    // Timer configs
    input  logic [3:0]               i_cfg_freq_sel, // Frequency selection (configurable)
    input  logic [3:0]               i_cfg_addr_cnt, // ADDR match for a timeout
    input  logic [3:0]               i_cfg_data_cnt, // DATA match for a timeout
    input  logic [3:0]               i_cfg_resp_cnt, // RESP match for a timeout

    // Slave AXI Interface (Input Side)
    // Write address channel (AW)
    input  logic [IW-1:0]              fub_awid,
    input  logic [AW-1:0]              fub_awaddr,
    input  logic [7:0]                 fub_awlen,
    input  logic [2:0]                 fub_awsize,
    input  logic [1:0]                 fub_awburst,
    input  logic                       fub_awlock,
    input  logic [3:0]                 fub_awcache,
    input  logic [2:0]                 fub_awprot,
    input  logic [3:0]                 fub_awqos,
    input  logic [3:0]                 fub_awregion,
    input  logic [UW-1:0]              fub_awuser,
    input  logic                       fub_awvalid,
    output logic                       fub_awready,

    // Write data channel (W)
    input  logic [DW-1:0]              fub_wdata,
    input  logic [DW/8-1:0]            fub_wstrb,
    input  logic                       fub_wlast,
    input  logic [UW-1:0]              fub_wuser,
    input  logic                       fub_wvalid,
    output logic                       fub_wready,

    // Write response channel (B)
    output logic [AXI_ID_WIDTH-1:0]    fub_bid,
    output logic [1:0]                 fub_bresp,
    output logic [AXI_USER_WIDTH-1:0]  fub_buser,
    output logic                       fub_bvalid,
    input  logic                       fub_bready,

    // Master AXI Interface (Output Side)
    // Write address channel (AW)
    output logic [IW-1:0]              m_axi_awid,
    output logic [AW-1:0]              m_axi_awaddr,
    output logic [7:0]                 m_axi_awlen,
    output logic [2:0]                 m_axi_awsize,
    output logic [1:0]                 m_axi_awburst,
    output logic                       m_axi_awlock,
    output logic [3:0]                 m_axi_awcache,
    output logic [2:0]                 m_axi_awprot,
    output logic [3:0]                 m_axi_awqos,
    output logic [3:0]                 m_axi_awregion,
    output logic [UW-1:0]              m_axi_awuser,
    output logic                       m_axi_awvalid,
    input  logic                       m_axi_awready,

    // Write data channel (W)
    output logic [DW-1:0]              m_axi_wdata,
    output logic [DW/8-1:0]            m_axi_wstrb,
    output logic                       m_axi_wlast,
    output logic [UW-1:0]              m_axi_wuser,
    output logic                       m_axi_wvalid,
    input  logic                       m_axi_wready,

    // Write response channel (B)
    input  logic [IW-1:0]              m_axi_bid,
    input  logic [1:0]                 m_axi_bresp,
    input  logic [UW-1:0]              m_axi_buser,
    input  logic                       m_axi_bvalid,
    output logic                       m_axi_bready,

    // Output split information with FIFO interface
    output logic [AW-1:0]              fub_split_addr,
    output logic [IW-1:0]              fub_split_id,
    output logic [7:0]                 fub_split_cnt,
    output logic                       fub_split_valid,
    input  logic                       fub_split_ready,

    // Error outputs with FIFO interface
    output logic [7:0]                 fub_error_type,
    output logic [AW-1:0]              fub_error_addr,
    output logic [IW-1:0]              fub_error_id,
    output logic [7:0]                 fub_error_unit_id,
    output logic [7:0]                 fub_error_agent_id,
    output logic                       fub_error_valid,
    input  logic                       fub_error_ready,

    // A cycle is in flight
    output logic                       o_busy

);

    // Internal connections between splitter and error monitor/skid buffer
    logic [IW-1:0]              int_awid;
    logic [AW-1:0]              int_awaddr;
    logic [7:0]                 int_awlen;
    logic [2:0]                 int_awsize;
    logic [1:0]                 int_awburst;
    logic                       int_awlock;
    logic [3:0]                 int_awcache;
    logic [2:0]                 int_awprot;
    logic [3:0]                 int_awqos;
    logic [3:0]                 int_awregion;
    logic [UW-1:0]              int_awuser;
    logic                       int_awvalid;
    logic                       int_awready;

    logic [DW-1:0]              int_wdata;
    logic [DW/8-1:0]            int_wstrb;
    logic                       int_wlast;
    logic [UW-1:0]              int_wuser;
    logic                       int_wvalid;
    logic                       int_wready;

    logic [IW-1:0]              int_bid;
    logic [1:0]                 int_bresp;
    logic [UW-1:0]              int_buser;
    logic                       int_bvalid;
    logic                       int_bready;

    // SKID buffer connections
    logic [3:0]                 int_aw_count;
    logic [AWSize-1:0]          int_aw_pkt;
    logic                       int_skid_awvalid;
    logic                       int_skid_awready;

    logic [3:0]                 int_w_count;
    logic [WSize-1:0]           int_w_pkt;
    logic                       int_skid_wvalid;
    logic                       int_skid_wready;

    logic [3:0]                 int_b_count;
    logic [BSize-1:0]           int_b_pkt;
    logic                       int_skid_bvalid;
    logic                       int_skid_bready;

    // Flow control signal
    logic                      int_block_ready;

    // Instantiate AXI write master splitter with FIFO interface
    axi_master_wr_splitter #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .SPLIT_FIFO_DEPTH     (SPLIT_FIFO_DEPTH)
    ) i_axi_master_wr_splitter (
        .aclk                 (aclk),
        .aresetn              (aresetn),
        .alignment_mask       (alignment_mask),

        .block_ready          (int_block_ready),

        // Slave interface (input)
        .fub_awid             (fub_awid),
        .fub_awaddr           (fub_awaddr),
        .fub_awlen            (fub_awlen),
        .fub_awsize           (fub_awsize),
        .fub_awburst          (fub_awburst),
        .fub_awlock           (fub_awlock),
        .fub_awcache          (fub_awcache),
        .fub_awprot           (fub_awprot),
        .fub_awqos            (fub_awqos),
        .fub_awregion         (fub_awregion),
        .fub_awuser           (fub_awuser),
        .fub_awvalid          (fub_awvalid),
        .fub_awready          (fub_awready),

        .fub_wdata            (fub_wdata),
        .fub_wstrb            (fub_wstrb),
        .fub_wlast            (fub_wlast),
        .fub_wuser            (fub_wuser),
        .fub_wvalid           (fub_wvalid),
        .fub_wready           (fub_wready),

        .fub_bid              (fub_bid),
        .fub_bresp            (fub_bresp),
        .fub_buser            (fub_buser),
        .fub_bvalid           (fub_bvalid),
        .fub_bready           (fub_bready),

        // Master interface (to error monitor)
        .m_axi_awid           (int_awid),
        .m_axi_awaddr         (int_awaddr),
        .m_axi_awlen          (int_awlen),
        .m_axi_awsize         (int_awsize),
        .m_axi_awburst        (int_awburst),
        .m_axi_awlock         (int_awlock),
        .m_axi_awcache        (int_awcache),
        .m_axi_awprot         (int_awprot),
        .m_axi_awqos          (int_awqos),
        .m_axi_awregion       (int_awregion),
        .m_axi_awuser         (int_awuser),
        .m_axi_awvalid        (int_awvalid),
        .m_axi_awready        (int_awready),

        .m_axi_wdata          (int_wdata),
        .m_axi_wstrb          (int_wstrb),
        .m_axi_wlast          (int_wlast),
        .m_axi_wuser          (int_wuser),
        .m_axi_wvalid         (int_wvalid),
        .m_axi_wready         (int_wready),

        .m_axi_bid            (int_bid),
        .m_axi_bresp          (int_bresp),
        .m_axi_buser          (int_buser),
        .m_axi_bvalid         (int_bvalid),
        .m_axi_bready         (int_bready),

        // Split information with FIFO interface
        .fub_split_addr       (fub_split_addr),
        .fub_split_id         (fub_split_id),
        .fub_split_cnt        (fub_split_cnt),
        .fub_split_valid      (fub_split_valid),
        .fub_split_ready      (fub_split_ready)
    );

    // Instantiate base error monitor module directly
    axi_errmon_base #(
        .UNIT_ID(UNIT_ID),
        .AGENT_ID(AGENT_ID),
        .CHANNELS(CHANNELS),
        .ADDR_WIDTH(AXI_ADDR_WIDTH),
        .ID_WIDTH(AXI_ID_WIDTH),
        .ERROR_FIFO_DEPTH(ERROR_FIFO_DEPTH),
        .ADDR_FIFO_DEPTH(ADDR_FIFO_DEPTH),
        .IS_READ(0),                // This is a write monitor
        .IS_AXI(1)                  // Full AXI (not AXI-Lite)
    ) i_axi_errmon_base (
        .aclk                 (aclk),
        .aresetn              (aresetn),

        // Configs
        .i_cfg_freq_sel       (i_cfg_freq_sel),
        .i_cfg_addr_cnt       (i_cfg_addr_cnt),
        .i_cfg_data_cnt       (i_cfg_data_cnt),
        .i_cfg_resp_cnt       (i_cfg_resp_cnt),

        // Address channel signals
        .i_addr_addr          (fub_awaddr),
        .i_addr_id            (fub_awid),
        .i_addr_valid         (fub_awvalid),
        .i_addr_ready         (fub_awready),

        // Data channel signals
        .i_data_id            ('b0),
        .i_data_last          (fub_wlast),
        .i_data_resp          ('b0),
        .i_data_valid         (fub_wvalid),
        .i_data_ready         (fub_wready),

        // Response channel signals
        .i_resp_id            (fub_bid),
        .i_resp               (fub_bresp),
        .i_resp_valid         (fub_bvalid),
        .i_resp_ready         (fub_bready),

        // Error outputs
        .o_error_valid        (fub_error_valid),
        .i_error_ready        (fub_error_ready),
        .o_error_type         (fub_error_type),
        .o_error_addr         (fub_error_addr),
        .o_error_id           (fub_error_id),
        .o_error_unit_id      (fub_error_unit_id),
        .o_error_agent_id     (fub_error_agent_id),

        // Flow control
        .o_block_ready        (int_block_ready),
        .o_busy               (o_busy)
    );

    // Instantiate AW Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AW),
        .DATA_WIDTH(AWSize)
    ) i_aw_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_awvalid),
        .o_wr_ready               (int_awready),
        .i_wr_data                (
            {int_awid, int_awaddr, int_awlen, int_awsize,
            int_awburst, int_awlock, int_awcache, int_awprot,
            int_awqos, int_awregion, int_awuser}),
        .o_rd_valid               (int_skid_awvalid),
        .i_rd_ready               (int_skid_awready),
        .o_rd_count               (int_aw_count),
        .o_rd_data                (int_aw_pkt),
        .ow_count                 ()
    );

    // Unpack AW signals from SKID buffer
    assign {m_axi_awid, m_axi_awaddr, m_axi_awlen, m_axi_awsize, m_axi_awburst,
            m_axi_awlock, m_axi_awcache, m_axi_awprot, m_axi_awqos,
            m_axi_awregion, m_axi_awuser} = int_aw_pkt;
    assign m_axi_awvalid = int_skid_awvalid;
    assign int_skid_awready = m_axi_awready;

    // Instantiate W Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_W),
        .DATA_WIDTH(WSize)
    ) i_w_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_wvalid),
        .o_wr_ready               (int_wready),
        .i_wr_data                (
            {int_wdata, int_wstrb, int_wlast, int_wuser}),
        .o_rd_valid               (int_skid_wvalid),
        .i_rd_ready               (int_skid_wready),
        .o_rd_count               (int_w_count),
        .o_rd_data                (int_w_pkt),
        .ow_count                 ()

    );

    // Unpack W signals from SKID buffer
    assign {m_axi_wdata, m_axi_wstrb, m_axi_wlast, m_axi_wuser} = int_w_pkt;
    assign m_axi_wvalid = int_skid_wvalid;
    assign int_skid_wready = m_axi_wready;

    // Instantiate B channel for write response back to splitter
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_B),
        .DATA_WIDTH(BSize)
    ) i_b_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (m_axi_bvalid),
        .o_wr_ready               (m_axi_bready),
        .i_wr_data                ({m_axi_bid, m_axi_bresp, m_axi_buser}),
        .o_rd_valid               (int_bvalid),
        .i_rd_ready               (int_bready),
        .o_rd_count               (int_b_count),
        .o_rd_data                ({int_bid, int_bresp, int_buser}),
        .ow_count                 ()
    );

endmodule : axi_master_wr