// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monbus_wb4_axi4_group
// Purpose: Wishbone-read + AXI4-master-write wrapper for monbus_group_core.
//
// Documentation: docs/markdown/rtl-amba/monitor/monbus_wb4_groups.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-10
//
//==============================================================================
// Description:
//   monbus_axil4_axi4_group with its read-only CSR port presented as a Wishbone
//   B4 slave instead of an AXI4-Lite one, so a Wishbone host can own a
//   monitor group without an AXI bridge in front of it.
//
//   This is a THIN wrapper on purpose. The group's drain path, compressor,
//   FIFOs and statistics are the proven ones; only the host read port
//   changes, through monbus_wb4_rd_shim. A duplicate of the group body
//   would be a second copy to keep in step, and the one nobody edits is the
//   one that rots.
//
//   Writes are refused. The CSR port is read-only, so a Wishbone write
//   terminates ERR in the shim and never reaches the group.
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - monbus_axil4_axi4_group.sv (the group this wraps)
//   - monbus_wb4_rd_shim.sv (the Wishbone read port)
//==============================================================================

`timescale 1ns / 1ps

module monbus_wb4_axi4_group
    import monitor_common_pkg::*;
#(

    parameter int FIFO_DEPTH_ERR       = 64,
    parameter int FIFO_DEPTH_WRITE     = 96,
    parameter int ADDR_WIDTH           = 32,
    // Err-FIFO drain (AXIL slave-read) data width. 64 = one beat per record
    // slice; 32 = a 2:1 read serializer presents each 64-bit slice as a low
    // then high beat (6 beats/record) for a 32-bit host crossbar. See
    // monbus_axil4_axil4_group for the identical mechanism.
    parameter int S_AXIL_DATA_WIDTH    = 64,
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
    input  logic                          cam_clear,   // sync clear: compressor CAM + stats

    input  logic                          monbus_valid,
    output logic                          monbus_ready,
    input  monitor_packet_t               monbus_packet,
    input  monbus_timestamp_t             monbus_timestamp,

    output monbus_timestamp_t             mon_time_out,
    // Wishbone B4 slave: the host's read port for records and statistics
    input  logic                          s_wb_CYC,
    input  logic                          s_wb_STB,
    input  logic                          s_wb_WE,
    input  logic [ADDR_WIDTH-1:0]         s_wb_ADR,
    input  logic [S_AXIL_DATA_WIDTH-1:0]  s_wb_DAT_W,
    input  logic [S_AXIL_DATA_WIDTH/8-1:0] s_wb_SEL,
    input  logic [2:0]                    s_wb_CTI,
    input  logic [1:0]                    s_wb_BTE,
    output logic                          s_wb_STALL,
    output logic                          s_wb_ACK,
    output logic                          s_wb_ERR,
    output logic                          s_wb_RTY,
    output logic [S_AXIL_DATA_WIDTH-1:0]  s_wb_DAT_R,

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
    input  logic                          cfg_compress_en,

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

    // Wishbone host port -> the group's AXI4-Lite read slave port.
    logic                         w_s_axil_arvalid, w_s_axil_arready;
    logic [ADDR_WIDTH-1:0]        w_s_axil_araddr;
    logic [2:0]                   w_s_axil_arprot;
    logic                         w_s_axil_rvalid, w_s_axil_rready;
    logic [S_AXIL_DATA_WIDTH-1:0] w_s_axil_rdata;
    logic [1:0]                   w_s_axil_rresp;

    monbus_wb4_rd_shim #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (S_AXIL_DATA_WIDTH)
    ) u_wb_rd_shim (
        .clk            (axi_aclk),
        .aresetn        (axi_aresetn),
        .s_wb_CYC       (s_wb_CYC),
        .s_wb_STB       (s_wb_STB),
        .s_wb_WE        (s_wb_WE),
        .s_wb_ADR       (s_wb_ADR),
        .s_wb_DAT_W     (s_wb_DAT_W),
        .s_wb_SEL       (s_wb_SEL),
        .s_wb_CTI       (s_wb_CTI),
        .s_wb_BTE       (s_wb_BTE),
        .s_wb_STALL     (s_wb_STALL),
        .s_wb_ACK       (s_wb_ACK),
        .s_wb_ERR       (s_wb_ERR),
        .s_wb_RTY       (s_wb_RTY),
        .s_wb_DAT_R     (s_wb_DAT_R),
        .m_axil_arvalid (w_s_axil_arvalid),
        .m_axil_arready (w_s_axil_arready),
        .m_axil_araddr  (w_s_axil_araddr),
        .m_axil_arprot  (w_s_axil_arprot),
        .m_axil_rvalid  (w_s_axil_rvalid),
        .m_axil_rready  (w_s_axil_rready),
        .m_axil_rdata   (w_s_axil_rdata),
        .m_axil_rresp   (w_s_axil_rresp)
    );

    monbus_axil4_axi4_group #(
        .FIFO_DEPTH_ERR          (FIFO_DEPTH_ERR),
        .FIFO_DEPTH_WRITE        (FIFO_DEPTH_WRITE),
        .ADDR_WIDTH              (ADDR_WIDTH),
        .S_AXIL_DATA_WIDTH       (S_AXIL_DATA_WIDTH),
        .AXI_ID_WIDTH            (AXI_ID_WIDTH),
        .AXI_USER_WIDTH          (AXI_USER_WIDTH),
        .MAX_BURST_BEATS         (MAX_BURST_BEATS),
        .FLUSH_TIMEOUT_CYCLES    (FLUSH_TIMEOUT_CYCLES),
        .NUM_PROTOCOLS           (NUM_PROTOCOLS),
        .USE_COMPRESSION         (USE_COMPRESSION),
        .SKID_DEPTH_AR           (SKID_DEPTH_AR),
        .SKID_DEPTH_R            (SKID_DEPTH_R),
        .SKID_DEPTH_AW           (SKID_DEPTH_AW),
        .SKID_DEPTH_W            (SKID_DEPTH_W),
        .SKID_DEPTH_B            (SKID_DEPTH_B)
    ) u_group (
        .axi_aclk                    (axi_aclk),
        .axi_aresetn                 (axi_aresetn),
        .cam_clear                   (cam_clear),
        .monbus_valid                (monbus_valid),
        .monbus_ready                (monbus_ready),
        .monbus_packet               (monbus_packet),
        .monbus_timestamp            (monbus_timestamp),
        .mon_time_out                (mon_time_out),
        .m_axi_awid                  (m_axi_awid),
        .m_axi_awaddr                (m_axi_awaddr),
        .m_axi_awlen                 (m_axi_awlen),
        .m_axi_awsize                (m_axi_awsize),
        .m_axi_awburst               (m_axi_awburst),
        .m_axi_awlock                (m_axi_awlock),
        .m_axi_awcache               (m_axi_awcache),
        .m_axi_awprot                (m_axi_awprot),
        .m_axi_awqos                 (m_axi_awqos),
        .m_axi_awregion              (m_axi_awregion),
        .m_axi_awuser                (m_axi_awuser),
        .m_axi_awvalid               (m_axi_awvalid),
        .m_axi_awready               (m_axi_awready),
        .m_axi_wdata                 (m_axi_wdata),
        .m_axi_wstrb                 (m_axi_wstrb),
        .m_axi_wlast                 (m_axi_wlast),
        .m_axi_wuser                 (m_axi_wuser),
        .m_axi_wvalid                (m_axi_wvalid),
        .m_axi_wready                (m_axi_wready),
        .m_axi_bid                   (m_axi_bid),
        .m_axi_bresp                 (m_axi_bresp),
        .m_axi_buser                 (m_axi_buser),
        .m_axi_bvalid                (m_axi_bvalid),
        .m_axi_bready                (m_axi_bready),
        .irq_out                     (irq_out),
        .cfg_base_addr               (cfg_base_addr),
        .cfg_limit_addr              (cfg_limit_addr),
        .cfg_flush_watermark         (cfg_flush_watermark),
        .cfg_compress_en             (cfg_compress_en),
        .cfg_axi_pkt_mask            (cfg_axi_pkt_mask),
        .cfg_axi_err_select          (cfg_axi_err_select),
        .cfg_axi_error_mask          (cfg_axi_error_mask),
        .cfg_axi_timeout_mask        (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask          (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask         (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask           (cfg_axi_perf_mask),
        .cfg_axi_addr_mask           (cfg_axi_addr_mask),
        .cfg_axi_debug_mask          (cfg_axi_debug_mask),
        .cfg_axis_pkt_mask           (cfg_axis_pkt_mask),
        .cfg_axis_err_select         (cfg_axis_err_select),
        .cfg_axis_error_mask         (cfg_axis_error_mask),
        .cfg_axis_timeout_mask       (cfg_axis_timeout_mask),
        .cfg_axis_compl_mask         (cfg_axis_compl_mask),
        .cfg_axis_credit_mask        (cfg_axis_credit_mask),
        .cfg_axis_channel_mask       (cfg_axis_channel_mask),
        .cfg_axis_stream_mask        (cfg_axis_stream_mask),
        .cfg_core_pkt_mask           (cfg_core_pkt_mask),
        .cfg_core_err_select         (cfg_core_err_select),
        .cfg_core_error_mask         (cfg_core_error_mask),
        .cfg_core_timeout_mask       (cfg_core_timeout_mask),
        .cfg_core_compl_mask         (cfg_core_compl_mask),
        .cfg_core_thresh_mask        (cfg_core_thresh_mask),
        .cfg_core_perf_mask          (cfg_core_perf_mask),
        .cfg_core_debug_mask         (cfg_core_debug_mask),
        .err_fifo_full               (err_fifo_full),
        .write_fifo_full             (write_fifo_full),
        .err_fifo_count              (err_fifo_count),
        .write_fifo_count            (write_fifo_count),
        .mon_compressor_stat_tier1_a (mon_compressor_stat_tier1_a),
        .mon_compressor_stat_tier1_b (mon_compressor_stat_tier1_b),
        .mon_compressor_stat_tier1_c (mon_compressor_stat_tier1_c),
        .mon_compressor_stat_tier0   (mon_compressor_stat_tier0),
        .mon_compressor_stat_cam_miss(mon_compressor_stat_cam_miss),
        .mon_compressor_stat_delta_ts_ovf(mon_compressor_stat_delta_ts_ovf),
        .mon_compressor_stat_event_data_ovf(mon_compressor_stat_event_data_ovf),
        .mon_compressor_stat_ed_delta_ovf(mon_compressor_stat_ed_delta_ovf),
        .s_axil_arvalid              (w_s_axil_arvalid),
        .s_axil_arready              (w_s_axil_arready),
        .s_axil_araddr               (w_s_axil_araddr),
        .s_axil_arprot               (w_s_axil_arprot),
        .s_axil_rvalid               (w_s_axil_rvalid),
        .s_axil_rready               (w_s_axil_rready),
        .s_axil_rdata                (w_s_axil_rdata),
        .s_axil_rresp                (w_s_axil_rresp)
    );

endmodule : monbus_wb4_axi4_group
