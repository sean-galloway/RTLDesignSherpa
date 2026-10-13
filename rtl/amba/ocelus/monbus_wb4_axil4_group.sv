// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monbus_wb4_axil4_group
// Purpose: Wishbone-read + AXI4-Lite-master-write wrapper for monbus_group_core.
//
// Documentation: docs/markdown/rtl-amba/monitor/monbus_wb4_groups.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-10
//
//==============================================================================
// Description:
//   monbus_axil4_axil4_group with its read-only CSR port presented as a Wishbone
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
//   - monbus_axil4_axil4_group.sv (the group this wraps)
//   - monbus_wb4_rd_shim.sv (the Wishbone read port)
//==============================================================================

`timescale 1ns / 1ps

module monbus_wb4_axil4_group
    import monitor_common_pkg::*;
#(

    parameter int FIFO_DEPTH_ERR       = 64,
    parameter int FIFO_DEPTH_WRITE     = 96,   // beats
    parameter int ADDR_WIDTH           = 32,
    // Err-FIFO drain AXIL data width. The monbus record is three 64-bit
    // slices ({tag,ts}, packet[127:64], packet[63:0]). With a 64-bit drain
    // each slice is one beat (3 beats/record). With a 32-bit drain (for a
    // 32-bit host crossbar) a 2:1 read serializer splits each slice into a
    // low then high 32-bit beat (6 beats/record); the err-FIFO record is
    // popped when the slice-2 LEAF beat is consumed, which in 32-bit mode
    // happens on the LOW half of that slice (the high half is replayed from
    // a held register, not a second leaf read).
    parameter int S_AXIL_DATA_WIDTH    = 64,
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

    monbus_axil4_axil4_group #(
        .FIFO_DEPTH_ERR          (FIFO_DEPTH_ERR),
        .FIFO_DEPTH_WRITE        (FIFO_DEPTH_WRITE),
        .ADDR_WIDTH              (ADDR_WIDTH),
        .S_AXIL_DATA_WIDTH       (S_AXIL_DATA_WIDTH),
        .FLUSH_TIMEOUT_CYCLES    (FLUSH_TIMEOUT_CYCLES),
        .NUM_PROTOCOLS           (NUM_PROTOCOLS),
        .USE_COMPRESSION         (USE_COMPRESSION),
        .HALF_BEAT_EN            (HALF_BEAT_EN),
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
        .m_axil_awvalid              (m_axil_awvalid),
        .m_axil_awready              (m_axil_awready),
        .m_axil_awaddr               (m_axil_awaddr),
        .m_axil_awprot               (m_axil_awprot),
        .m_axil_wvalid               (m_axil_wvalid),
        .m_axil_wready               (m_axil_wready),
        .m_axil_wdata                (m_axil_wdata),
        .m_axil_wstrb                (m_axil_wstrb),
        .m_axil_bvalid               (m_axil_bvalid),
        .m_axil_bready               (m_axil_bready),
        .m_axil_bresp                (m_axil_bresp),
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

endmodule : monbus_wb4_axil4_group
