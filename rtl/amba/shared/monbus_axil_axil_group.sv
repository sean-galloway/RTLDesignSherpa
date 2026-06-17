// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: monbus_axil_axil_group
// Purpose: AXIL-slave-read + AXIL-master-write wrapper for monbus_group_core.
//
//   Slave-read leaf:  axil4_slave_rd  (single-beat). Wrapper bridges its
//                     AXIL FUB into monbus_group_core's AXI4-shaped read
//                     FUB by supplying arid=0 / arlen=0 / arsize=3 /
//                     arburst=INCR. The core's rlast and rid go nowhere
//                     (AXIL has no last/id fields).
//
//   Master-write leaf: axil4_master_wr (single-beat). Core's MAX_BURST_BEATS
//                     is forced to 1, so each AW/W pair the core issues
//                     is a single beat. The leaf consumes the W beat
//                     without referencing wlast.
//
//   This wrapper replaces the legacy monbus_axil_group.sv (which fused
//   the core + AXIL skids into a single module).
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

module monbus_axil_axil_group
    import monitor_common_pkg::*;
#(
    parameter int FIFO_DEPTH_ERR       = 64,
    parameter int FIFO_DEPTH_WRITE     = 96,   // beats
    parameter int ADDR_WIDTH           = 32,
    parameter int FLUSH_TIMEOUT_CYCLES = 1024,
    parameter int NUM_PROTOCOLS        = 3,
    parameter int USE_COMPRESSION      = 0,
    parameter int HALF_BEAT_EN         = 0,
    parameter int SKID_DEPTH_AR        = 2,
    parameter int SKID_DEPTH_R         = 4,
    parameter int SKID_DEPTH_AW        = 2,
    parameter int SKID_DEPTH_W         = 2,
    parameter int SKID_DEPTH_B         = 2
) (
    input  logic                          axi_aclk,
    input  logic                          axi_aresetn,
    input  logic                          cam_clear,   // sync clear: compressor CAM + stats

    // ----- Monitor-bus input + timestamp -----
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

    // ----- AXIL master write (bulk capture) -----
    output logic                          m_axil_awvalid,
    input  logic                          m_axil_awready,
    output logic [ADDR_WIDTH-1:0]         m_axil_awaddr,
    output logic [2:0]                    m_axil_awprot,

    output logic                          m_axil_wvalid,
    input  logic                          m_axil_wready,
    output logic [63:0]                   m_axil_wdata,
    output logic [7:0]                    m_axil_wstrb,

    input  logic                          m_axil_bvalid,
    output logic                          m_axil_bready,
    input  logic [1:0]                    m_axil_bresp,

    output logic                          irq_out,

    // ----- Config -----
    input  logic [ADDR_WIDTH-1:0]         cfg_base_addr,
    input  logic [ADDR_WIDTH-1:0]         cfg_limit_addr,
    input  logic [15:0]                   cfg_flush_watermark,
    input  logic                          cfg_compress_en,

    // AXI (protocol 0)
    input  logic [15:0]                   cfg_axi_pkt_mask,
    input  logic [15:0]                   cfg_axi_err_select,
    input  logic [15:0]                   cfg_axi_error_mask,
    input  logic [15:0]                   cfg_axi_timeout_mask,
    input  logic [15:0]                   cfg_axi_compl_mask,
    input  logic [15:0]                   cfg_axi_thresh_mask,
    input  logic [15:0]                   cfg_axi_perf_mask,
    input  logic [15:0]                   cfg_axi_addr_mask,
    input  logic [15:0]                   cfg_axi_debug_mask,
    // AXIS (protocol 1)
    input  logic [15:0]                   cfg_axis_pkt_mask,
    input  logic [15:0]                   cfg_axis_err_select,
    input  logic [15:0]                   cfg_axis_error_mask,
    input  logic [15:0]                   cfg_axis_timeout_mask,
    input  logic [15:0]                   cfg_axis_compl_mask,
    input  logic [15:0]                   cfg_axis_credit_mask,
    input  logic [15:0]                   cfg_axis_channel_mask,
    input  logic [15:0]                   cfg_axis_stream_mask,
    // CORE (protocol 4)
    input  logic [15:0]                   cfg_core_pkt_mask,
    input  logic [15:0]                   cfg_core_err_select,
    input  logic [15:0]                   cfg_core_error_mask,
    input  logic [15:0]                   cfg_core_timeout_mask,
    input  logic [15:0]                   cfg_core_compl_mask,
    input  logic [15:0]                   cfg_core_thresh_mask,
    input  logic [15:0]                   cfg_core_perf_mask,
    input  logic [15:0]                   cfg_core_debug_mask,

    // ----- Status / debug -----
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

    // ==================================================================
    // FUB nets between leaves and core
    // ==================================================================

    // Slave-read (AXIL leaf -> bridge -> core's AXI4-shaped FUB)
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

    // Master-write (core's AXI4-shaped FUB -> bridge -> AXIL leaf)
    logic [ADDR_WIDTH-1:0]   axil_wr_fub_awaddr;
    logic                    axil_wr_fub_awvalid;
    logic                    axil_wr_fub_awready;
    logic [63:0]             axil_wr_fub_wdata;
    logic [7:0]              axil_wr_fub_wstrb;
    logic                    axil_wr_fub_wvalid;
    logic                    axil_wr_fub_wready;
    logic [1:0]              axil_wr_fub_bresp;
    logic                    axil_wr_fub_bvalid;
    logic                    axil_wr_fub_bready;

    // Core-side AXI4-shaped read FUB (the burst signals are tied off in
    // AXIL builds and arlen is forced to 0)
    /* verilator lint_off UNUSED */
    logic                    core_s_arready_unused;
    logic                    core_s_rlast_unused;
    logic [0:0]              core_s_rid_unused;
    /* verilator lint_on UNUSED */

    // Core-side AXI4-shaped write FUB
    /* verilator lint_off UNUSED */
    logic [0:0]              core_m_awid_unused;
    logic [7:0]              core_m_awlen_unused;
    logic [2:0]              core_m_awsize_unused;
    logic [1:0]              core_m_awburst_unused;
    logic                    core_m_wlast_unused;
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
    // AXIL master write leaf
    // ==================================================================
    axil4_master_wr #(
        .AXIL_ADDR_WIDTH (ADDR_WIDTH),
        .AXIL_DATA_WIDTH (64),
        .SKID_DEPTH_AW   (SKID_DEPTH_AW),
        .SKID_DEPTH_W    (SKID_DEPTH_W),
        .SKID_DEPTH_B    (SKID_DEPTH_B)
    ) u_axil_wr (
        .aclk           (axi_aclk),
        .aresetn        (axi_aresetn),

        .fub_awaddr     (axil_wr_fub_awaddr),
        .fub_awprot     (3'b000),
        .fub_awvalid    (axil_wr_fub_awvalid),
        .fub_awready    (axil_wr_fub_awready),
        .fub_wdata      (axil_wr_fub_wdata),
        .fub_wstrb      (axil_wr_fub_wstrb),
        .fub_wvalid     (axil_wr_fub_wvalid),
        .fub_wready     (axil_wr_fub_wready),
        .fub_bresp      (axil_wr_fub_bresp),
        .fub_bvalid     (axil_wr_fub_bvalid),
        .fub_bready     (axil_wr_fub_bready),

        .m_axil_awaddr  (m_axil_awaddr),
        .m_axil_awprot  (m_axil_awprot),
        .m_axil_awvalid (m_axil_awvalid),
        .m_axil_awready (m_axil_awready),
        .m_axil_wdata   (m_axil_wdata),
        .m_axil_wstrb   (m_axil_wstrb),
        .m_axil_wvalid  (m_axil_wvalid),
        .m_axil_wready  (m_axil_wready),
        .m_axil_bresp   (m_axil_bresp),
        .m_axil_bvalid  (m_axil_bvalid),
        .m_axil_bready  (m_axil_bready),

        .busy           ()
    );

    // ==================================================================
    // Protocol-agnostic core
    // ==================================================================
    monbus_group_core #(
        .FIFO_DEPTH_ERR       (FIFO_DEPTH_ERR),
        .FIFO_DEPTH_WRITE     (FIFO_DEPTH_WRITE),
        .ADDR_WIDTH           (ADDR_WIDTH),
        .AXI_ID_WIDTH_M       (1),
        .AXI_ID_WIDTH_S       (1),
        .MAX_BURST_BEATS      (1),   // AXIL master: single-beat
        .FLUSH_TIMEOUT_CYCLES (FLUSH_TIMEOUT_CYCLES),
        .NUM_PROTOCOLS        (NUM_PROTOCOLS),
        .USE_COMPRESSION      (USE_COMPRESSION),
        .HALF_BEAT_EN         (HALF_BEAT_EN)
    ) u_core (
        .axi_aclk    (axi_aclk),
        .axi_aresetn (axi_aresetn),
        .cam_clear   (cam_clear),

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
        .cfg_compress_en      (cfg_compress_en),

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

        // Master-write FUB (core drives, wrapper feeds AXIL leaf)
        .fub_m_awid    (core_m_awid_unused),
        .fub_m_awaddr  (axil_wr_fub_awaddr),
        .fub_m_awlen   (core_m_awlen_unused),
        .fub_m_awsize  (core_m_awsize_unused),
        .fub_m_awburst (core_m_awburst_unused),
        .fub_m_awvalid (axil_wr_fub_awvalid),
        .fub_m_awready (axil_wr_fub_awready),

        .fub_m_wdata   (axil_wr_fub_wdata),
        .fub_m_wstrb   (axil_wr_fub_wstrb),
        .fub_m_wlast   (core_m_wlast_unused),
        .fub_m_wvalid  (axil_wr_fub_wvalid),
        .fub_m_wready  (axil_wr_fub_wready),

        .fub_m_bid     (1'b0),
        .fub_m_bresp   (axil_wr_fub_bresp),
        .fub_m_bvalid  (axil_wr_fub_bvalid),
        .fub_m_bready  (axil_wr_fub_bready),

        // Slave-read FUB (wrapper drives from AXIL leaf -> core)
        .fub_s_arid    (1'b0),
        .fub_s_araddr  (axil_rd_fub_araddr),
        .fub_s_arlen   (8'd0),       // single-beat
        .fub_s_arsize  (3'd3),       // 8 bytes
        .fub_s_arburst (2'b01),      // INCR
        .fub_s_arvalid (axil_rd_fub_arvalid),
        .fub_s_arready (axil_rd_fub_arready),

        .fub_s_rid     (core_s_rid_unused),
        .fub_s_rdata   (axil_rd_fub_rdata),
        .fub_s_rresp   (axil_rd_fub_rresp),
        .fub_s_rlast   (core_s_rlast_unused),
        .fub_s_rvalid  (axil_rd_fub_rvalid),
        .fub_s_rready  (axil_rd_fub_rready)
    );

endmodule : monbus_axil_axil_group
