// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: monbus_axi4_axi4_group
// Purpose: AXI4-slave-read + AXI4-master-write wrapper for monbus_group_core.
//
//   Both leaves are AXI4 (axi4_slave_rd / axi4_master_wr). Their FUBs
//   pass through directly to the core's AXI4-shaped FUBs. The wrapper
//   supplies safe defaults for AXI4 fields the core does not produce
//   (awlock/awcache/awqos/awregion/awuser/wuser) at the master-write
//   leaf boundary.
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

module monbus_axi4_axi4_group
    import monitor_common_pkg::*;
#(
    parameter int FIFO_DEPTH_ERR       = 64,
    parameter int FIFO_DEPTH_WRITE     = 96,
    parameter int ADDR_WIDTH           = 32,
    parameter int AXI_ID_WIDTH_S       = 8,    // slave read id
    parameter int AXI_ID_WIDTH_M       = 8,    // master write id
    parameter int AXI_USER_WIDTH       = 1,
    parameter int MAX_BURST_BEATS      = 64,
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

    // ----- AXI4 slave read (burst err FIFO drain) -----
    input  logic [AXI_ID_WIDTH_S-1:0]     s_axi_arid,
    input  logic [ADDR_WIDTH-1:0]         s_axi_araddr,
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

    output logic [AXI_ID_WIDTH_S-1:0]     s_axi_rid,
    output logic [63:0]                   s_axi_rdata,
    output logic [1:0]                    s_axi_rresp,
    output logic                          s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_ruser,
    output logic                          s_axi_rvalid,
    input  logic                          s_axi_rready,

    // ----- AXI4 master write (burst bulk capture) -----
    output logic [AXI_ID_WIDTH_M-1:0]     m_axi_awid,
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

    input  logic [AXI_ID_WIDTH_M-1:0]     m_axi_bid,
    input  logic [1:0]                    m_axi_bresp,
    input  logic [AXI_USER_WIDTH-1:0]     m_axi_buser,
    input  logic                          m_axi_bvalid,
    output logic                          m_axi_bready,

    output logic                          irq_out,

    input  logic [ADDR_WIDTH-1:0]         cfg_base_addr,
    input  logic [ADDR_WIDTH-1:0]         cfg_limit_addr,
    input  logic [15:0]                   cfg_flush_watermark,

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

    // Slave-read FUB nets
    logic [AXI_ID_WIDTH_S-1:0]   axi_rd_fub_arid;
    logic [ADDR_WIDTH-1:0]       axi_rd_fub_araddr;
    logic [7:0]                  axi_rd_fub_arlen;
    logic [2:0]                  axi_rd_fub_arsize;
    logic [1:0]                  axi_rd_fub_arburst;
    /* verilator lint_off UNUSED */
    logic                        axi_rd_fub_arlock;
    logic [3:0]                  axi_rd_fub_arcache;
    logic [2:0]                  axi_rd_fub_arprot;
    logic [3:0]                  axi_rd_fub_arqos;
    logic [3:0]                  axi_rd_fub_arregion;
    logic [AXI_USER_WIDTH-1:0]   axi_rd_fub_aruser;
    /* verilator lint_on UNUSED */
    logic                        axi_rd_fub_arvalid;
    logic                        axi_rd_fub_arready;
    logic [AXI_ID_WIDTH_S-1:0]   axi_rd_fub_rid;
    logic [63:0]                 axi_rd_fub_rdata;
    logic [1:0]                  axi_rd_fub_rresp;
    logic                        axi_rd_fub_rlast;
    logic                        axi_rd_fub_rvalid;
    logic                        axi_rd_fub_rready;

    // Master-write FUB nets
    logic [AXI_ID_WIDTH_M-1:0]   axi_wr_fub_awid;
    logic [ADDR_WIDTH-1:0]       axi_wr_fub_awaddr;
    logic [7:0]                  axi_wr_fub_awlen;
    logic [2:0]                  axi_wr_fub_awsize;
    logic [1:0]                  axi_wr_fub_awburst;
    logic                        axi_wr_fub_awvalid;
    logic                        axi_wr_fub_awready;
    logic [63:0]                 axi_wr_fub_wdata;
    logic [7:0]                  axi_wr_fub_wstrb;
    logic                        axi_wr_fub_wlast;
    logic                        axi_wr_fub_wvalid;
    logic                        axi_wr_fub_wready;
    logic [AXI_ID_WIDTH_M-1:0]   axi_wr_fub_bid;
    logic [1:0]                  axi_wr_fub_bresp;
    logic                        axi_wr_fub_bvalid;
    logic                        axi_wr_fub_bready;

    /* verilator lint_off UNUSED */
    logic [AXI_USER_WIDTH-1:0]   _unused_buser = m_axi_buser;
    /* verilator lint_on UNUSED */

    assign s_axi_ruser = '0;

    // ==================================================================
    // AXI4 slave read leaf
    // ==================================================================
    axi4_slave_rd #(
        .AXI_ID_WIDTH    (AXI_ID_WIDTH_S),
        .AXI_ADDR_WIDTH  (ADDR_WIDTH),
        .AXI_DATA_WIDTH  (64),
        .AXI_USER_WIDTH  (AXI_USER_WIDTH),
        .SKID_DEPTH_AR   (SKID_DEPTH_AR),
        .SKID_DEPTH_R    (SKID_DEPTH_R)
    ) u_axi4_rd (
        .aclk             (axi_aclk),
        .aresetn          (axi_aresetn),

        .s_axi_arid       (s_axi_arid),
        .s_axi_araddr     (s_axi_araddr),
        .s_axi_arlen      (s_axi_arlen),
        .s_axi_arsize     (s_axi_arsize),
        .s_axi_arburst    (s_axi_arburst),
        .s_axi_arlock     (s_axi_arlock),
        .s_axi_arcache    (s_axi_arcache),
        .s_axi_arprot     (s_axi_arprot),
        .s_axi_arqos      (s_axi_arqos),
        .s_axi_arregion   (s_axi_arregion),
        .s_axi_aruser     (s_axi_aruser),
        .s_axi_arvalid    (s_axi_arvalid),
        .s_axi_arready    (s_axi_arready),

        .s_axi_rid        (s_axi_rid),
        .s_axi_rdata      (s_axi_rdata),
        .s_axi_rresp      (s_axi_rresp),
        .s_axi_rlast      (s_axi_rlast),
        .s_axi_ruser      (),
        .s_axi_rvalid     (s_axi_rvalid),
        .s_axi_rready     (s_axi_rready),

        .fub_axi_arid     (axi_rd_fub_arid),
        .fub_axi_araddr   (axi_rd_fub_araddr),
        .fub_axi_arlen    (axi_rd_fub_arlen),
        .fub_axi_arsize   (axi_rd_fub_arsize),
        .fub_axi_arburst  (axi_rd_fub_arburst),
        .fub_axi_arlock   (axi_rd_fub_arlock),
        .fub_axi_arcache  (axi_rd_fub_arcache),
        .fub_axi_arprot   (axi_rd_fub_arprot),
        .fub_axi_arqos    (axi_rd_fub_arqos),
        .fub_axi_arregion (axi_rd_fub_arregion),
        .fub_axi_aruser   (axi_rd_fub_aruser),
        .fub_axi_arvalid  (axi_rd_fub_arvalid),
        .fub_axi_arready  (axi_rd_fub_arready),

        .fub_axi_rid      (axi_rd_fub_rid),
        .fub_axi_rdata    (axi_rd_fub_rdata),
        .fub_axi_rresp    (axi_rd_fub_rresp),
        .fub_axi_rlast    (axi_rd_fub_rlast),
        .fub_axi_ruser    ({AXI_USER_WIDTH{1'b0}}),
        .fub_axi_rvalid   (axi_rd_fub_rvalid),
        .fub_axi_rready   (axi_rd_fub_rready),

        .busy             ()
    );

    // ==================================================================
    // AXI4 master write leaf
    // ==================================================================
    axi4_master_wr #(
        .AXI_ID_WIDTH    (AXI_ID_WIDTH_M),
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
        .fub_axi_awcache  (4'b0010),
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
        .AXI_ID_WIDTH_M       (AXI_ID_WIDTH_M),
        .AXI_ID_WIDTH_S       (AXI_ID_WIDTH_S),
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

        // Master-write FUB (full pass-through to AXI4 leaf)
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

        // Slave-read FUB (full pass-through to AXI4 leaf)
        .fub_s_arid    (axi_rd_fub_arid),
        .fub_s_araddr  (axi_rd_fub_araddr),
        .fub_s_arlen   (axi_rd_fub_arlen),
        .fub_s_arsize  (axi_rd_fub_arsize),
        .fub_s_arburst (axi_rd_fub_arburst),
        .fub_s_arvalid (axi_rd_fub_arvalid),
        .fub_s_arready (axi_rd_fub_arready),

        .fub_s_rid     (axi_rd_fub_rid),
        .fub_s_rdata   (axi_rd_fub_rdata),
        .fub_s_rresp   (axi_rd_fub_rresp),
        .fub_s_rlast   (axi_rd_fub_rlast),
        .fub_s_rvalid  (axi_rd_fub_rvalid),
        .fub_s_rready  (axi_rd_fub_rready)
    );

endmodule : monbus_axi4_axi4_group
