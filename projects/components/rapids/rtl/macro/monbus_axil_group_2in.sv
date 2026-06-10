// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Module: monbus_axil_group_2in
// Purpose: RAPIDS 2-input wrapper around the shared monbus_axil_axil_group
//          (member of the monbus_<p1>_<p2>_group family; this 2in
//          wrapper merges source + sink monbus streams via monbus_arbiter
//          before feeding the AXIL/AXIL shared group).
//
// Documentation: rtl/amba/PRD.md
// Subsystem: rapids_macro

`timescale 1ns / 1ps

/*
================================================================================
Monbus AXIL Group (2-input wrapper for RAPIDS source + sink streams)
================================================================================
RAPIDS has source + sink data paths and therefore two upstream monbus
producers. The previous design embedded a 2-input round-robin arbiter
directly inside a RAPIDS-specific copy of monbus_axil_group, which led to
800+ lines of duplicated capture/filtering/FIFO/AXIL logic shared with
the single-input STREAM variant.

This wrapper restores the same 2-input port surface but builds it on top
of the unified shared monbus_axil_group (rtl/amba/shared/) via an
external monbus_arbiter(CLIENTS=2). The arbitration is one tiny
instance, the capture pipeline is one shared module — and the rapids
TB that drove source_/sink_ packets keeps working unchanged.

Port surface is identical to the deleted RAPIDS monbus_axil_group.sv so
existing tests / TB classes / filelists need only retarget the dut_name
and add this file to their compile order.
================================================================================
*/

`include "reset_defs.svh"

module monbus_axil_group_2in
    import monitor_common_pkg::*;
#(
    parameter int FIFO_DEPTH_ERR       = 64,
    parameter int FIFO_DEPTH_WRITE     = 96,    // beats (beat-granular write FIFO)
    parameter int ADDR_WIDTH           = 32,
    parameter int FLUSH_TIMEOUT_CYCLES = 1024,
    parameter int NUM_PROTOCOLS        = 3,
    parameter int USE_COMPRESSION      = 0
) (
    // Clock and Reset
    input  logic                          axi_aclk,
    input  logic                          axi_aresetn,

    // Source Monitor Bus Input
    input  logic                          source_monbus_valid,
    output logic                          source_monbus_ready,
    input  monitor_packet_t               source_monbus_packet,
    input  monbus_timestamp_t             source_monbus_timestamp,

    // Sink Monitor Bus Input
    input  logic                          sink_monbus_valid,
    output logic                          sink_monbus_ready,
    input  monitor_packet_t               sink_monbus_packet,
    input  monbus_timestamp_t             sink_monbus_timestamp,

    // Free-running monitor-time output
    output monbus_timestamp_t             mon_time_out,

    // Error/Interrupt FIFO (Slave Read Interface)
    input  logic                          s_axil_arvalid,
    output logic                          s_axil_arready,
    input  logic [ADDR_WIDTH-1:0]         s_axil_araddr,
    input  logic [2:0]                    s_axil_arprot,
    output logic                          s_axil_rvalid,
    input  logic                          s_axil_rready,
    output logic [63:0]                   s_axil_rdata,
    output logic [1:0]                    s_axil_rresp,

    // Master Write Interface (64-bit captures)
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

    // IRQ
    output logic                          irq_out,

    // Configuration
    input  logic [ADDR_WIDTH-1:0]         cfg_base_addr,
    input  logic [ADDR_WIDTH-1:0]         cfg_limit_addr,
    input  logic [15:0]                   cfg_flush_watermark, // beats

    // Per-protocol filtering
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

    // Debug/Status
    output logic                          err_fifo_full,
    output logic                          write_fifo_full,
    output logic [15:0]                   err_fifo_count,    // records
    output logic [15:0]                   write_fifo_count   // beats
);

    // ----------------------------------------------------------------
    // Internal: arbiter output feeding the shared group
    // ----------------------------------------------------------------
    logic                arb_monbus_valid;
    logic                arb_monbus_ready;
    monitor_packet_t     arb_monbus_packet;
    monbus_timestamp_t   arb_monbus_source_ts;

    // Unpacked arrays for monbus_arbiter input (idx 0 = source, 1 = sink)
    logic                arb_in_valid     [2];
    logic                arb_in_ready     [2];
    monitor_packet_t     arb_in_packet    [2];
    monbus_timestamp_t   arb_in_timestamp [2];

    assign arb_in_valid    [0] = source_monbus_valid;
    assign arb_in_valid    [1] = sink_monbus_valid;
    assign source_monbus_ready = arb_in_ready[0];
    assign sink_monbus_ready   = arb_in_ready[1];
    assign arb_in_packet   [0] = source_monbus_packet;
    assign arb_in_packet   [1] = sink_monbus_packet;
    assign arb_in_timestamp[0] = source_monbus_timestamp;
    assign arb_in_timestamp[1] = sink_monbus_timestamp;

    monbus_arbiter #(
        .CLIENTS            (2),
        .INPUT_SKID_ENABLE  (1),
        .OUTPUT_SKID_ENABLE (1),
        .INPUT_SKID_DEPTH   (2),
        .OUTPUT_SKID_DEPTH  (2)
    ) u_arbiter (
        .axi_aclk           (axi_aclk),
        .axi_aresetn        (axi_aresetn),
        .block_arb          (1'b0),
        .monbus_valid_in    (arb_in_valid),
        .monbus_ready_in    (arb_in_ready),
        .monbus_packet_in   (arb_in_packet),
        .monbus_timestamp_in(arb_in_timestamp),
        .monbus_valid       (arb_monbus_valid),
        .monbus_ready       (arb_monbus_ready),
        .monbus_packet      (arb_monbus_packet),
        .monbus_timestamp   (arb_monbus_source_ts),
        /* verilator lint_off PINCONNECTEMPTY */
        .grant_valid        (),
        .grant              (),
        .grant_id           (),
        .last_grant         ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // ----------------------------------------------------------------
    // Shared single-input AXIL group consumes the arbitrated stream
    // ----------------------------------------------------------------
    monbus_axil_axil_group #(
        .FIFO_DEPTH_ERR       (FIFO_DEPTH_ERR),
        .FIFO_DEPTH_WRITE     (FIFO_DEPTH_WRITE),
        .ADDR_WIDTH           (ADDR_WIDTH),
        .FLUSH_TIMEOUT_CYCLES (FLUSH_TIMEOUT_CYCLES),
        .NUM_PROTOCOLS        (NUM_PROTOCOLS),
        .USE_COMPRESSION      (USE_COMPRESSION)
    ) u_group (
        .axi_aclk               (axi_aclk),
        .axi_aresetn            (axi_aresetn),

        .monbus_valid           (arb_monbus_valid),
        .monbus_ready           (arb_monbus_ready),
        .monbus_packet          (arb_monbus_packet),
        .monbus_timestamp       (arb_monbus_source_ts),

        .mon_time_out           (mon_time_out),

        .s_axil_arvalid         (s_axil_arvalid),
        .s_axil_arready         (s_axil_arready),
        .s_axil_araddr          (s_axil_araddr),
        .s_axil_arprot          (s_axil_arprot),
        .s_axil_rvalid          (s_axil_rvalid),
        .s_axil_rready          (s_axil_rready),
        .s_axil_rdata           (s_axil_rdata),
        .s_axil_rresp           (s_axil_rresp),

        .m_axil_awvalid         (m_axil_awvalid),
        .m_axil_awready         (m_axil_awready),
        .m_axil_awaddr          (m_axil_awaddr),
        .m_axil_awprot          (m_axil_awprot),
        .m_axil_wvalid          (m_axil_wvalid),
        .m_axil_wready          (m_axil_wready),
        .m_axil_wdata           (m_axil_wdata),
        .m_axil_wstrb           (m_axil_wstrb),
        .m_axil_bvalid          (m_axil_bvalid),
        .m_axil_bready          (m_axil_bready),
        .m_axil_bresp           (m_axil_bresp),

        .irq_out                (irq_out),

        .cfg_base_addr          (cfg_base_addr),
        .cfg_limit_addr         (cfg_limit_addr),
        .cfg_flush_watermark    (cfg_flush_watermark),

        .cfg_axi_pkt_mask       (cfg_axi_pkt_mask),
        .cfg_axi_err_select     (cfg_axi_err_select),
        .cfg_axi_error_mask     (cfg_axi_error_mask),
        .cfg_axi_timeout_mask   (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask     (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask    (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask      (cfg_axi_perf_mask),
        .cfg_axi_addr_mask      (cfg_axi_addr_mask),
        .cfg_axi_debug_mask     (cfg_axi_debug_mask),

        .cfg_axis_pkt_mask      (cfg_axis_pkt_mask),
        .cfg_axis_err_select    (cfg_axis_err_select),
        .cfg_axis_error_mask    (cfg_axis_error_mask),
        .cfg_axis_timeout_mask  (cfg_axis_timeout_mask),
        .cfg_axis_compl_mask    (cfg_axis_compl_mask),
        .cfg_axis_credit_mask   (cfg_axis_credit_mask),
        .cfg_axis_channel_mask  (cfg_axis_channel_mask),
        .cfg_axis_stream_mask   (cfg_axis_stream_mask),

        .cfg_core_pkt_mask      (cfg_core_pkt_mask),
        .cfg_core_err_select    (cfg_core_err_select),
        .cfg_core_error_mask    (cfg_core_error_mask),
        .cfg_core_timeout_mask  (cfg_core_timeout_mask),
        .cfg_core_compl_mask    (cfg_core_compl_mask),
        .cfg_core_thresh_mask   (cfg_core_thresh_mask),
        .cfg_core_perf_mask     (cfg_core_perf_mask),
        .cfg_core_debug_mask    (cfg_core_debug_mask),

        .err_fifo_full          (err_fifo_full),
        .write_fifo_full        (write_fifo_full),
        .err_fifo_count         (err_fifo_count),
        .write_fifo_count       (write_fifo_count),

        // Compressor stats -- this 2-input wrapper does not enable
        // compression (USE_COMPRESSION defaults to 0); leave dangling.
        /* verilator lint_off PINCONNECTEMPTY */
        .mon_compressor_stat_tier1_a        (),
        .mon_compressor_stat_tier1_b        (),
        .mon_compressor_stat_tier1_c        (),
        .mon_compressor_stat_tier0          (),
        .mon_compressor_stat_cam_miss       (),
        .mon_compressor_stat_delta_ts_ovf   (),
        .mon_compressor_stat_event_data_ovf (),
        .mon_compressor_stat_ed_delta_ovf   ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

endmodule : monbus_axil_group_2in
