// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_master_rd
// Purpose: Axi Master Rd module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module axi_master_rd
#(
    // Error Packet Identifiers
    parameter int UNIT_ID            = 99,
    parameter int AGENT_ID           = 99,

    // AXI parameters
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_USER_WIDTH    = 1,

    // Channel parameter
    parameter int CHANNELS          = 16,

    // Skid buffer depths
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,

    // FIFO parameters
    parameter int SPLIT_FIFO_DEPTH  = 2,
    parameter int ERROR_FIFO_DEPTH  = 2,
    parameter int ADDR_FIFO_DEPTH   = 4,    // Depth of address tracking FIFO

    // Derived parameters
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW,
    parameter int RSize    = IW+DW+2+1+UW
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
    // Read address channel (AR)
    input  logic [IW-1:0]              fub_arid,
    input  logic [AW-1:0]              fub_araddr,
    input  logic [7:0]                 fub_arlen,
    input  logic [2:0]                 fub_arsize,
    input  logic [1:0]                 fub_arburst,
    input  logic                       fub_arlock,
    input  logic [3:0]                 fub_arcache,
    input  logic [2:0]                 fub_arprot,
    input  logic [3:0]                 fub_arqos,
    input  logic [3:0]                 fub_arregion,
    input  logic [UW-1:0]              fub_aruser,
    input  logic                       fub_arvalid,
    output logic                       fub_arready,

    // Read data channel (R)
    output logic [IW-1:0]              fub_rid,
    output logic [DW-1:0]              fub_rdata,
    output logic [1:0]                 fub_rresp,
    output logic                       fub_rlast,
    output logic [UW-1:0]              fub_ruser,
    output logic                       fub_rvalid,
    input  logic                       fub_rready,

    // Master AXI Interface (Output Side)
    // Read address channel (AR)
    output logic [IW-1:0]              m_axi_arid,
    output logic [AW-1:0]              m_axi_araddr,
    output logic [7:0]                 m_axi_arlen,
    output logic [2:0]                 m_axi_arsize,
    output logic [1:0]                 m_axi_arburst,
    output logic                       m_axi_arlock,
    output logic [3:0]                 m_axi_arcache,
    output logic [2:0]                 m_axi_arprot,
    output logic [3:0]                 m_axi_arqos,
    output logic [3:0]                 m_axi_arregion,
    output logic [UW-1:0]              m_axi_aruser,
    output logic                       m_axi_arvalid,
    input  logic                       m_axi_arready,

    // Read data channel (R)
    input  logic [IW-1:0]              m_axi_rid,
    input  logic [DW-1:0]              m_axi_rdata,
    input  logic [1:0]                 m_axi_rresp,
    input  logic                       m_axi_rlast,
    input  logic [UW-1:0]              m_axi_ruser,
    input  logic                       m_axi_rvalid,
    output logic                       m_axi_rready,

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
    logic [IW-1:0]              int_arid;
    logic [AW-1:0]              int_araddr;
    logic [7:0]                 int_arlen;
    logic [2:0]                 int_arsize;
    logic [1:0]                 int_arburst;
    logic                       int_arlock;
    logic [3:0]                 int_arcache;
    logic [2:0]                 int_arprot;
    logic [3:0]                 int_arqos;
    logic [3:0]                 int_arregion;
    logic [UW-1:0]              int_aruser;
    logic                       int_arvalid;
    logic                       int_arready;

    logic [IW-1:0]              int_rid;
    logic [DW-1:0]              int_rdata;
    logic [1:0]                 int_rresp;
    logic                       int_rlast;
    logic [UW-1:0]              int_ruser;
    logic                       int_rvalid;
    logic                       int_rready;

    // SKID buffer connections
    logic [3:0]                int_ar_count;
    logic [ARSize-1:0]         int_ar_pkt;
    logic                      int_skid_arvalid;
    logic                      int_skid_arready;

    logic [3:0]                int_r_count;
    logic [RSize-1:0]          int_r_pkt;
    logic                      int_skid_rvalid;
    logic                      int_skid_rready;

    // Flow control signal
    logic                      int_block_ready;

    // Instantiate AXI read master splitter with FIFO interface
    axi_master_rd_splitter #(
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH       (AXI_DATA_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        .SPLIT_FIFO_DEPTH     (SPLIT_FIFO_DEPTH)
    ) i_axi_master_rd_splitter (
        .aclk                 (aclk),
        .aresetn              (aresetn),
        .alignment_mask       (alignment_mask),

        .block_ready          (int_block_ready),

        // Slave interface (input)
        .fub_arid             (fub_arid),
        .fub_araddr           (fub_araddr),
        .fub_arlen            (fub_arlen),
        .fub_arsize           (fub_arsize),
        .fub_arburst          (fub_arburst),
        .fub_arlock           (fub_arlock),
        .fub_arcache          (fub_arcache),
        .fub_arprot           (fub_arprot),
        .fub_arqos            (fub_arqos),
        .fub_arregion         (fub_arregion),
        .fub_aruser           (fub_aruser),
        .fub_arvalid          (fub_arvalid),
        .fub_arready          (fub_arready),

        .fub_rid              (fub_rid),
        .fub_rdata            (fub_rdata),
        .fub_rresp            (fub_rresp),
        .fub_rlast            (fub_rlast),
        .fub_ruser            (fub_ruser),
        .fub_rvalid           (fub_rvalid),
        .fub_rready           (fub_rready),

        // Master interface (to error monitor)
        .m_axi_arid           (int_arid),
        .m_axi_araddr         (int_araddr),
        .m_axi_arlen          (int_arlen),
        .m_axi_arsize         (int_arsize),
        .m_axi_arburst        (int_arburst),
        .m_axi_arlock         (int_arlock),
        .m_axi_arcache        (int_arcache),
        .m_axi_arprot         (int_arprot),
        .m_axi_arqos          (int_arqos),
        .m_axi_arregion       (int_arregion),
        .m_axi_aruser         (int_aruser),
        .m_axi_arvalid        (int_arvalid),
        .m_axi_arready        (int_arready),

        .m_axi_rid            (int_rid),
        .m_axi_rdata          (int_rdata),
        .m_axi_rresp          (int_rresp),
        .m_axi_rlast          (int_rlast),
        .m_axi_ruser          (int_ruser),
        .m_axi_rvalid         (int_rvalid),
        .m_axi_rready         (int_rready),

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
        .IS_READ(1),              // This is a read monitor
        .IS_AXI(1)                // Full AXI (not AXI-Lite)
    ) i_axi_errmon_base (
        .aclk                 (aclk),
        .aresetn              (aresetn),

        // Configs
        .i_cfg_freq_sel       (i_cfg_freq_sel),
        .i_cfg_addr_cnt       (i_cfg_addr_cnt),
        .i_cfg_data_cnt       (i_cfg_data_cnt),
        .i_cfg_resp_cnt       (i_cfg_resp_cnt),

        // Address channel signals
        .i_addr_addr          (fub_araddr),
        .i_addr_id            (fub_arid),
        .i_addr_valid         (fub_arvalid),
        .i_addr_ready         (fub_arready),

        // Data channel signals
        .i_data_id            (fub_rid),
        .i_data_last          (fub_rlast),
        .i_data_resp          (fub_rresp),
        .i_data_valid         (fub_rvalid),
        .i_data_ready         (fub_rready),

        // Response channel signals (unused for read)
        .i_resp_id            ('b0),
        .i_resp               ('b0),
        .i_resp_valid         (1'b0),
        .i_resp_ready         (1'b0),

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

    // Instantiate AR Skid Buffer
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_AR),
        .DATA_WIDTH(ARSize)
    ) i_ar_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (int_arvalid),
        .o_wr_ready               (int_arready),
        .i_wr_data                (
            {int_arid, int_araddr, int_arlen, int_arsize,
            int_arburst, int_arlock, int_arcache, int_arprot,
            int_arqos, int_arregion, int_aruser}),
        .o_rd_valid               (int_skid_arvalid),
        .i_rd_ready               (int_skid_arready),
        .o_rd_count               (int_ar_count),
        .o_rd_data                (int_ar_pkt),
        .ow_count()
    );

    // Unpack AR signals from SKID buffer
    assign {m_axi_arid, m_axi_araddr, m_axi_arlen, m_axi_arsize, m_axi_arburst,
            m_axi_arlock, m_axi_arcache, m_axi_arprot, m_axi_arqos,
            m_axi_arregion, m_axi_aruser} = int_ar_pkt;
    assign m_axi_arvalid = int_skid_arvalid;
    assign int_skid_arready = m_axi_arready;

    // Instantiate R channel for read data back to splitter
    gaxi_skid_buffer #(
        .DEPTH(SKID_DEPTH_R),
        .DATA_WIDTH(RSize)
    ) i_r_channel (
        .i_axi_aclk               (aclk),
        .i_axi_aresetn            (aresetn),
        .i_wr_valid               (m_axi_rvalid),
        .o_wr_ready               (m_axi_rready),
        .i_wr_data                ({m_axi_rid, m_axi_rdata, m_axi_rresp, m_axi_rlast, m_axi_ruser}),
        .o_rd_valid               (int_rvalid),
        .i_rd_ready               (int_rready),
        .o_rd_count               (int_r_count),
        .o_rd_data                ({int_rid, int_rdata, int_rresp, int_rlast, int_ruser}),
        .ow_count()
    );

endmodule : axi_master_rd
