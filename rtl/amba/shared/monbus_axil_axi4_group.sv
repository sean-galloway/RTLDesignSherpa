// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: monbus_axil_axi4_group
// Purpose: AXIL-slave-read + AXI4-master-write wrapper for monbus_group_core.
//
//   Slave-read leaf:   axil4_slave_rd  (single-beat). Wrapper bridges its
//                      AXIL FUB into the core's AXI4-shaped read FUB by
//                      supplying arid=0 / arlen=0 / arsize=3 / arburst=INCR.
//
//   Master-write leaf: axi4_master_wr  (burst). Core's MAX_BURST_BEATS
//                      can be up to 256 (default 64). The core's
//                      AXI4-shaped write FUB drives the leaf's FUB
//                      mostly straight through; the AXI4 fields the
//                      core does not produce (awlock / awcache / awqos /
//                      awregion / awuser / wuser) are tied to safe
//                      defaults at the leaf boundary.
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

module monbus_axil_axi4_group
    import monitor_common_pkg::*;
#(
    parameter int FIFO_DEPTH_ERR       = 64,
    parameter int FIFO_DEPTH_WRITE     = 96,
    parameter int ADDR_WIDTH           = 32,
    parameter int AXI_ID_WIDTH         = 8,    // master write id
    parameter int AXI_USER_WIDTH       = 1,
    parameter int MAX_BURST_BEATS      = 64,   // master-write max beats/burst
    parameter int FLUSH_TIMEOUT_CYCLES = 1024,
    parameter int NUM_PROTOCOLS        = 3,
    parameter int USE_COMPRESSION      = 0,
    parameter int SKID_DEPTH_AR        = 2,
    parameter int SKID_DEPTH_R         = 4,
    parameter int SKID_DEPTH_AW        = 2,
    parameter int SKID_DEPTH_W         = 4,
    parameter int SKID_DEPTH_B         = 2
) (
    input  logic                          axi_aclk,
    input  logic                          axi_aresetn,

    input  logic                          monbus_valid,
    output logic                          monbus_ready,
    input  monitor_packet_t               monbus_packet,
    input  monbus_timestamp_t             monbus_timestamp,

    output monbus_timestamp_t             mon_time_out,

    // ----- AXIL slave read (err FIFO drain) -----
    input  logic                          s_axil_arvalid,
    output logic                          s_axil_arready,
    input  logic [ADDR_WIDTH-1:0]         s_axil_araddr,
    input  logic [2:0]                    s_axil_arprot,

    output logic                          s_axil_rvalid,
    input  logic                          s_axil_rready,
    output logic [63:0]                   s_axil_rdata,
    output logic [1:0]                    s_axil_rresp,

    // ----- AXI4 master write (burst bulk capture) -----
    output logic [AXI_ID_WIDTH-1:0]       m_axi_awid,
    output logic [ADDR_WIDTH-1:0]         m_axi_awaddr,
    output logic [7:0]                    m_axi_awlen,
    output logic [2:0]                    m_axi_awsize,
    output logic [1:0]                    m_axi_awburst,
    output logic                          m_axi_awlock,
    output logic [3:0]                    m_axi_awcache,
    output logic [2:0]                    m_axi_awprot,
    output logic [3:0]                    m_axi_awqos,
    output logic [3:0]                    m_axi_awregion,
    output logic [AXI_USER_WIDTH-1:0]     m_axi_awuser,
    output logic                          m_axi_awvalid,
    input  logic                          m_axi_awready,

    output logic [63:0]                   m_axi_wdata,
    output logic [7:0]                    m_axi_wstrb,
    output logic                          m_axi_wlast,
    output logic [AXI_USER_WIDTH-1:0]     m_axi_wuser,
    output logic                          m_axi_wvalid,
    input  logic                          m_axi_wready,

    input  logic [AXI_ID_WIDTH-1:0]       m_axi_bid,
    input  logic [1:0]                    m_axi_bresp,
    input  logic [AXI_USER_WIDTH-1:0]     m_axi_buser,
    input  logic                          m_axi_bvalid,
    output logic                          m_axi_bready,

    output logic                          irq_out,

    input  logic [ADDR_WIDTH-1:0]         cfg_base_addr,
    input  logic [ADDR_WIDTH-1:0]         cfg_limit_addr,
    input  logic [15:0]                   cfg_flush_watermark,

    // Per-protocol filter masks (same shape as the AXIL variant)
    input  logic [15:0]                   cfg_axi_pkt_mask,
    input  logic [15:0]                   cfg_axi_err_select,
    input  logic [15:0]                   cfg_axi_error_mask,
    input  logic [15:0]                   cfg_axi_timeout_mask,
    input  logic [15:0]                   cfg_axi_compl_mask,
    input  logic [15:0]                   cfg_axi_thresh_mask,
    input  logic [15:0]                   cfg_axi_perf_mask,
    input  logic [15:0]                   cfg_axi_addr_mask,
    input  logic [15:0]                   cfg_axi_debug_mask,
    input  logic [15:0]                   cfg_axis_pkt_mask,
    input  logic [15:0]                   cfg_axis_err_select,
    input  logic [15:0]                   cfg_axis_error_mask,
    input  logic [15:0]                   cfg_axis_timeout_mask,
    input  logic [15:0]                   cfg_axis_compl_mask,
    input  logic [15:0]                   cfg_axis_credit_mask,
    input  logic [15:0]                   cfg_axis_channel_mask,
    input  logic [15:0]                   cfg_axis_stream_mask,
    input  logic [15:0]                   cfg_core_pkt_mask,
    input  logic [15:0]                   cfg_core_err_select,
    input  logic [15:0]                   cfg_core_error_mask,
    input  logic [15:0]                   cfg_core_timeout_mask,
    input  logic [15:0]                   cfg_core_compl_mask,
    input  logic [15:0]                   cfg_core_thresh_mask,
    input  logic [15:0]                   cfg_core_perf_mask,
    input  logic [15:0]                   cfg_core_debug_mask,

    output logic                          err_fifo_full,
    output logic                          write_fifo_full,
    output logic [15:0]                   err_fifo_count,
    output logic [15:0]                   write_fifo_count,

    output logic [31:0]                   mon_compressor_stat_tier1_a,
    output logic [31:0]                   mon_compressor_stat_tier1_b,
    output logic [31:0]                   mon_compressor_stat_tier1_c,
    output logic [31:0]                   mon_compressor_stat_tier0,
    output logic [31:0]                   mon_compressor_stat_cam_miss,
    output logic [31:0]                   mon_compressor_stat_delta_ts_ovf,
    output logic [31:0]                   mon_compressor_stat_event_data_ovf,
    output logic [31:0]                   mon_compressor_stat_ed_delta_ovf
);

    // Slave-read FUB nets (AXIL leaf <-> wrapper bridge -> core)
    logic [ADDR_WIDTH-1:0]   axil_rd_fub_araddr;
    /* verilator lint_off UNUSED */
    logic [2:0]              axil_rd_fub_arprot;
    /* verilator lint_on UNUSED */
    logic                    axil_rd_fub_arvalid;
    logic                    axil_rd_fub_arready;
    logic [63:0]             axil_rd_fub_rdata;
    logic [1:0]              axil_rd_fub_rresp;
    logic                    axil_rd_fub_rvalid;
    logic                    axil_rd_fub_rready;

    // Master-write FUB nets (core -> wrapper bridge -> AXI4 leaf)
    logic [AXI_ID_WIDTH-1:0] axi_wr_fub_awid;
    logic [ADDR_WIDTH-1:0]   axi_wr_fub_awaddr;
    logic [7:0]              axi_wr_fub_awlen;
    logic [2:0]              axi_wr_fub_awsize;
    logic [1:0]              axi_wr_fub_awburst;
    logic                    axi_wr_fub_awvalid;
    logic                    axi_wr_fub_awready;
    logic [63:0]             axi_wr_fub_wdata;
    logic [7:0]              axi_wr_fub_wstrb;
    logic                    axi_wr_fub_wlast;
    logic                    axi_wr_fub_wvalid;
    logic                    axi_wr_fub_wready;
    logic [AXI_ID_WIDTH-1:0] axi_wr_fub_bid;
    logic [1:0]              axi_wr_fub_bresp;
    logic                    axi_wr_fub_bvalid;
    logic                    axi_wr_fub_bready;

    /* verilator lint_off UNUSED */
    logic                    core_s_rlast_unused;
    logic [0:0]              core_s_rid_unused;
    logic [AXI_ID_WIDTH-1:0] _unused_bid = axi_wr_fub_bid;
    logic [AXI_USER_WIDTH-1:0] _unused_buser = m_axi_buser;
    /* verilator lint_on UNUSED */

    // ==================================================================
    // AXIL slave read leaf
    // ==================================================================
    axil4_slave_rd #(
        .AXIL_ADDR_WIDTH (ADDR_WIDTH),
        .AXIL_DATA_WIDTH (64),
        .SKID_DEPTH_AR   (SKID_DEPTH_AR),
        .SKID_DEPTH_R    (SKID_DEPTH_R)
    ) u_axil_rd (
        .aclk           (axi_aclk),
        .aresetn        (axi_aresetn),

        .s_axil_araddr  (s_axil_araddr),
        .s_axil_arprot  (s_axil_arprot),
        .s_axil_arvalid (s_axil_arvalid),
        .s_axil_arready (s_axil_arready),
        .s_axil_rdata   (s_axil_rdata),
        .s_axil_rresp   (s_axil_rresp),
        .s_axil_rvalid  (s_axil_rvalid),
        .s_axil_rready  (s_axil_rready),

        .fub_araddr     (axil_rd_fub_araddr),
        .fub_arprot     (axil_rd_fub_arprot),
        .fub_arvalid    (axil_rd_fub_arvalid),
        .fub_arready    (axil_rd_fub_arready),
        .fub_rdata      (axil_rd_fub_rdata),
        .fub_rresp      (axil_rd_fub_rresp),
        .fub_rvalid     (axil_rd_fub_rvalid),
        .fub_rready     (axil_rd_fub_rready),

        .busy           ()
    );

    // ==================================================================
    // AXI4 master write leaf
    //
    //   The core only drives awid/awaddr/awlen/awsize/awburst and
    //   wdata/wstrb/wlast/wvalid (no awlock/awcache/awqos/awregion/
    //   awuser/wuser). Those are tied to safe defaults at the leaf's
    //   FUB inputs.
    // ==================================================================
    axi4_master_wr #(
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH  (ADDR_WIDTH),
        .AXI_DATA_WIDTH  (64),
        .AXI_USER_WIDTH  (AXI_USER_WIDTH),
        .SKID_DEPTH_AW   (SKID_DEPTH_AW),
        .SKID_DEPTH_W    (SKID_DEPTH_W),
        .SKID_DEPTH_B    (SKID_DEPTH_B)
    ) u_axi4_wr (
        .aclk             (axi_aclk),
        .aresetn          (axi_aresetn),

        .fub_axi_awid     (axi_wr_fub_awid),
        .fub_axi_awaddr   (axi_wr_fub_awaddr),
        .fub_axi_awlen    (axi_wr_fub_awlen),
        .fub_axi_awsize   (axi_wr_fub_awsize),
        .fub_axi_awburst  (axi_wr_fub_awburst),
        .fub_axi_awlock   (1'b0),
        .fub_axi_awcache  (4'b0010),         // Normal Non-cacheable Bufferable
        .fub_axi_awprot   (3'b000),
        .fub_axi_awqos    (4'b0000),
        .fub_axi_awregion (4'b0000),
        .fub_axi_awuser   ({AXI_USER_WIDTH{1'b0}}),
        .fub_axi_awvalid  (axi_wr_fub_awvalid),
        .fub_axi_awready  (axi_wr_fub_awready),

        .fub_axi_wdata    (axi_wr_fub_wdata),
        .fub_axi_wstrb    (axi_wr_fub_wstrb),
        .fub_axi_wlast    (axi_wr_fub_wlast),
        .fub_axi_wuser    ({AXI_USER_WIDTH{1'b0}}),
        .fub_axi_wvalid   (axi_wr_fub_wvalid),
        .fub_axi_wready   (axi_wr_fub_wready),

        .fub_axi_bid      (axi_wr_fub_bid),
        .fub_axi_bresp    (axi_wr_fub_bresp),
        .fub_axi_buser    (),
        .fub_axi_bvalid   (axi_wr_fub_bvalid),
        .fub_axi_bready   (axi_wr_fub_bready),

        .m_axi_awid       (m_axi_awid),
        .m_axi_awaddr     (m_axi_awaddr),
        .m_axi_awlen      (m_axi_awlen),
        .m_axi_awsize     (m_axi_awsize),
        .m_axi_awburst    (m_axi_awburst),
        .m_axi_awlock     (m_axi_awlock),
        .m_axi_awcache    (m_axi_awcache),
        .m_axi_awprot     (m_axi_awprot),
        .m_axi_awqos      (m_axi_awqos),
        .m_axi_awregion   (m_axi_awregion),
        .m_axi_awuser     (m_axi_awuser),
        .m_axi_awvalid    (m_axi_awvalid),
        .m_axi_awready    (m_axi_awready),

        .m_axi_wdata      (m_axi_wdata),
        .m_axi_wstrb      (m_axi_wstrb),
        .m_axi_wlast      (m_axi_wlast),
        .m_axi_wuser      (m_axi_wuser),
        .m_axi_wvalid     (m_axi_wvalid),
        .m_axi_wready     (m_axi_wready),

        .m_axi_bid        (m_axi_bid),
        .m_axi_bresp      (m_axi_bresp),
        .m_axi_buser      (m_axi_buser),
        .m_axi_bvalid     (m_axi_bvalid),
        .m_axi_bready     (m_axi_bready),

        .busy             ()
    );

    // ==================================================================
    // Protocol-agnostic core
    // ==================================================================
    monbus_group_core #(
        .FIFO_DEPTH_ERR       (FIFO_DEPTH_ERR),
        .FIFO_DEPTH_WRITE     (FIFO_DEPTH_WRITE),
        .ADDR_WIDTH           (ADDR_WIDTH),
        .AXI_ID_WIDTH_M       (AXI_ID_WIDTH),
        .AXI_ID_WIDTH_S       (1),
        .MAX_BURST_BEATS      (MAX_BURST_BEATS),
        .FLUSH_TIMEOUT_CYCLES (FLUSH_TIMEOUT_CYCLES),
        .NUM_PROTOCOLS        (NUM_PROTOCOLS),
        .USE_COMPRESSION      (USE_COMPRESSION)
    ) u_core (
        .axi_aclk    (axi_aclk),
        .axi_aresetn (axi_aresetn),

        .monbus_valid     (monbus_valid),
        .monbus_ready     (monbus_ready),
        .monbus_packet    (monbus_packet),
        .monbus_timestamp (monbus_timestamp),
        .mon_time_out     (mon_time_out),

        .irq_out          (irq_out),
        .err_fifo_full    (err_fifo_full),
        .write_fifo_full  (write_fifo_full),
        .err_fifo_count   (err_fifo_count),
        .write_fifo_count (write_fifo_count),

        .cfg_base_addr        (cfg_base_addr),
        .cfg_limit_addr       (cfg_limit_addr),
        .cfg_flush_watermark  (cfg_flush_watermark),

        .cfg_axi_pkt_mask     (cfg_axi_pkt_mask),
        .cfg_axi_err_select   (cfg_axi_err_select),
        .cfg_axi_error_mask   (cfg_axi_error_mask),
        .cfg_axi_timeout_mask (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask   (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask  (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask    (cfg_axi_perf_mask),
        .cfg_axi_addr_mask    (cfg_axi_addr_mask),
        .cfg_axi_debug_mask   (cfg_axi_debug_mask),

        .cfg_axis_pkt_mask     (cfg_axis_pkt_mask),
        .cfg_axis_err_select   (cfg_axis_err_select),
        .cfg_axis_error_mask   (cfg_axis_error_mask),
        .cfg_axis_timeout_mask (cfg_axis_timeout_mask),
        .cfg_axis_compl_mask   (cfg_axis_compl_mask),
        .cfg_axis_credit_mask  (cfg_axis_credit_mask),
        .cfg_axis_channel_mask (cfg_axis_channel_mask),
        .cfg_axis_stream_mask  (cfg_axis_stream_mask),

        .cfg_core_pkt_mask     (cfg_core_pkt_mask),
        .cfg_core_err_select   (cfg_core_err_select),
        .cfg_core_error_mask   (cfg_core_error_mask),
        .cfg_core_timeout_mask (cfg_core_timeout_mask),
        .cfg_core_compl_mask   (cfg_core_compl_mask),
        .cfg_core_thresh_mask  (cfg_core_thresh_mask),
        .cfg_core_perf_mask    (cfg_core_perf_mask),
        .cfg_core_debug_mask   (cfg_core_debug_mask),

        .mon_compressor_stat_tier1_a        (mon_compressor_stat_tier1_a),
        .mon_compressor_stat_tier1_b        (mon_compressor_stat_tier1_b),
        .mon_compressor_stat_tier1_c        (mon_compressor_stat_tier1_c),
        .mon_compressor_stat_tier0          (mon_compressor_stat_tier0),
        .mon_compressor_stat_cam_miss       (mon_compressor_stat_cam_miss),
        .mon_compressor_stat_delta_ts_ovf   (mon_compressor_stat_delta_ts_ovf),
        .mon_compressor_stat_event_data_ovf (mon_compressor_stat_event_data_ovf),
        .mon_compressor_stat_ed_delta_ovf   (mon_compressor_stat_ed_delta_ovf),

        // Master-write FUB to AXI4 leaf
        .fub_m_awid    (axi_wr_fub_awid),
        .fub_m_awaddr  (axi_wr_fub_awaddr),
        .fub_m_awlen   (axi_wr_fub_awlen),
        .fub_m_awsize  (axi_wr_fub_awsize),
        .fub_m_awburst (axi_wr_fub_awburst),
        .fub_m_awvalid (axi_wr_fub_awvalid),
        .fub_m_awready (axi_wr_fub_awready),

        .fub_m_wdata   (axi_wr_fub_wdata),
        .fub_m_wstrb   (axi_wr_fub_wstrb),
        .fub_m_wlast   (axi_wr_fub_wlast),
        .fub_m_wvalid  (axi_wr_fub_wvalid),
        .fub_m_wready  (axi_wr_fub_wready),

        .fub_m_bid     (axi_wr_fub_bid),
        .fub_m_bresp   (axi_wr_fub_bresp),
        .fub_m_bvalid  (axi_wr_fub_bvalid),
        .fub_m_bready  (axi_wr_fub_bready),

        // Slave-read FUB from AXIL leaf (bridge to AXI4-shaped FUB)
        .fub_s_arid    (1'b0),
        .fub_s_araddr  (axil_rd_fub_araddr),
        .fub_s_arlen   (8'd0),
        .fub_s_arsize  (3'd3),
        .fub_s_arburst (2'b01),
        .fub_s_arvalid (axil_rd_fub_arvalid),
        .fub_s_arready (axil_rd_fub_arready),

        .fub_s_rid     (core_s_rid_unused),
        .fub_s_rdata   (axil_rd_fub_rdata),
        .fub_s_rresp   (axil_rd_fub_rresp),
        .fub_s_rlast   (core_s_rlast_unused),
        .fub_s_rvalid  (axil_rd_fub_rvalid),
        .fub_s_rready  (axil_rd_fub_rready)
    );

endmodule : monbus_axil_axi4_group
