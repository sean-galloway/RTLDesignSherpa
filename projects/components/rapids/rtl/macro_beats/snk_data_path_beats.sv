// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: sink_data_path
// Purpose: RAPIDS Beats Sink Data Path - Fill to AXI Write Pipeline
//
// Description:
//   Multi-channel sink data path combining:
//   - snk_sram_controller: Per-channel FIFO buffering with allocation control
//   - axi_write_engine: Multi-channel AXI4 write master with round-robin arbitration
//
//   Data flow: External Fill Interface -> SRAM Controller -> AXI Write Engine -> Memory
//
//   For Phase 1 "beats" architecture, the fill interface is exposed externally
//   (no network_slave module). Data is written to memory via AXI4 burst writes.
//
// Architecture:
//   1. Fill Allocation: External source reserves SRAM space before writing
//   2. Fill Data: External source writes data to per-channel FIFO
//   3. Scheduler Interface: Receives write commands from scheduler array
//   4. Drain: AXI Write Engine drains SRAM and writes to memory
//
// Documentation: projects/components/rapids/docs/rapids_spec/
// Subsystem: rapids_macro_beats
//
// Author: sean galloway
// Created: 2026-01-10

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module snk_data_path_beats #(
    // Primary parameters
    parameter int NUM_CHANNELS = 8,
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int AXI_ID_WIDTH = 8,
    parameter int SRAM_DEPTH = 512,
    parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,
    parameter int PIPELINE = 0,
    parameter int AW_MAX_OUTSTANDING = 8,
    parameter int W_PHASE_FIFO_DEPTH = 64,
    parameter int B_PHASE_FIFO_DEPTH = 16,

    // Short aliases
    parameter int NC = NUM_CHANNELS,
    parameter int AW = ADDR_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int IW = AXI_ID_WIDTH,
    parameter int SD = SRAM_DEPTH,
    parameter int SCW = SEG_COUNT_WIDTH,
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1
) (
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // Configuration Interface
    //=========================================================================
    input  logic [7:0]                  cfg_axi_wr_xfer_beats,

    //=========================================================================
    // Fill Allocation Interface (External -> SRAM Controller)
    // External source requests space before filling
    //=========================================================================
    input  logic                        fill_alloc_req,
    input  logic [7:0]                  fill_alloc_size,
    input  logic [CIW-1:0]              fill_alloc_id,
    output logic [NC-1:0][SCW-1:0]      fill_space_free,

    //=========================================================================
    // Fill Data Interface (External -> SRAM Controller)
    // External source writes data to per-channel FIFO
    //=========================================================================
    input  logic                        fill_valid,
    output logic                        fill_ready,
    input  logic [CIW-1:0]              fill_id,
    input  logic [DW-1:0]               fill_data,

    //=========================================================================
    // Scheduler Interface (Per-Channel Write Requests)
    // Scheduler issues write commands with address, beats remaining
    //=========================================================================
    input  logic [NC-1:0]               sched_wr_valid,
    output logic [NC-1:0]               sched_wr_ready,
    input  logic [NC-1:0][AW-1:0]       sched_wr_addr,
    input  logic [NC-1:0][31:0]         sched_wr_beats,
    input  logic [NC-1:0][7:0]          sched_wr_burst_len,

    //=========================================================================
    // Completion Interface (to Schedulers)
    //=========================================================================
    output logic [NC-1:0]               sched_wr_done_strobe,
    output logic [NC-1:0][31:0]         sched_wr_beats_done,

    //=========================================================================
    // AXI4 Write Master Interface
    //=========================================================================
    // AW Channel
    output logic [IW-1:0]               m_axi_awid,
    output logic [AW-1:0]               m_axi_awaddr,
    output logic [7:0]                  m_axi_awlen,
    output logic [2:0]                  m_axi_awsize,
    output logic [1:0]                  m_axi_awburst,
    output logic                        m_axi_awvalid,
    input  logic                        m_axi_awready,

    // W Channel
    output logic [DW-1:0]               m_axi_wdata,
    output logic [(DW/8)-1:0]           m_axi_wstrb,
    output logic                        m_axi_wlast,
    output logic                        m_axi_wvalid,
    input  logic                        m_axi_wready,

    // B Channel
    input  logic [IW-1:0]               m_axi_bid,
    input  logic [1:0]                  m_axi_bresp,
    input  logic                        m_axi_bvalid,
    output logic                        m_axi_bready,

    //=========================================================================
    // Debug Interface
    //=========================================================================
    output logic [NC-1:0]               dbg_sram_bridge_pending,
    output logic [NC-1:0]               dbg_sram_bridge_out_valid
);

    //=========================================================================
    // Internal Signals - SRAM Controller to AXI Write Engine
    //=========================================================================

    // Drain flow control (AXI Write Engine -> SRAM Controller)
    logic [NC-1:0][SCW-1:0]             drain_data_avail;
    logic [NC-1:0]                      drain_req;
    logic [NC-1:0][7:0]                 drain_size;

    // Drain data (SRAM Controller -> AXI Write Engine)
    logic [NC-1:0]                      drain_valid;
    logic                               drain_read;
    logic [CIW-1:0]                     drain_id;
    logic [DW-1:0]                      drain_data;

    //=========================================================================
    // SRAM Controller Instance
    //=========================================================================

    snk_sram_controller_beats #(
        .NUM_CHANNELS       (NC),
        .DATA_WIDTH         (DW),
        .SRAM_DEPTH         (SD),
        .SEG_COUNT_WIDTH    (SCW)
    ) u_snk_sram_controller (
        .clk                (clk),
        .rst_n              (rst_n),

        // Fill Allocation Interface
        .fill_alloc_req     (fill_alloc_req),
        .fill_alloc_size    (fill_alloc_size),
        .fill_alloc_id      (fill_alloc_id),
        .fill_space_free    (fill_space_free),

        // Fill Data Interface
        .fill_valid         (fill_valid),
        .fill_ready         (fill_ready),
        .fill_id            (fill_id),
        .fill_data          (fill_data),

        // Drain Flow Control Interface
        .drain_data_avail   (drain_data_avail),
        .drain_req          (drain_req),
        .drain_size         (drain_size),

        // Drain Data Interface
        .drain_valid        (drain_valid),
        .drain_read         (drain_read),
        .drain_id           (drain_id),
        .drain_data         (drain_data),

        // Debug
        .dbg_bridge_pending   (dbg_sram_bridge_pending),
        .dbg_bridge_out_valid (dbg_sram_bridge_out_valid)
    );

    //=========================================================================
    // AXI Write Engine Instance
    //=========================================================================

    axi_write_engine_beats #(
        .NUM_CHANNELS       (NC),
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .ID_WIDTH           (IW),
        .USER_WIDTH         (CIW),
        .SEG_COUNT_WIDTH    (SCW),
        .PIPELINE           (PIPELINE),
        .AW_MAX_OUTSTANDING (AW_MAX_OUTSTANDING),
        .W_PHASE_FIFO_DEPTH (W_PHASE_FIFO_DEPTH),
        .B_PHASE_FIFO_DEPTH (B_PHASE_FIFO_DEPTH)
    ) u_axi_write_engine (
        .clk                (clk),
        .rst_n              (rst_n),

        // Configuration
        .cfg_axi_wr_xfer_beats (cfg_axi_wr_xfer_beats),

        // Scheduler Interface
        .sched_wr_valid     (sched_wr_valid),
        .sched_wr_ready     (sched_wr_ready),
        .sched_wr_addr      (sched_wr_addr),
        .sched_wr_beats     (sched_wr_beats),
        .sched_wr_burst_len (sched_wr_burst_len),

        // Completion Interface
        .sched_wr_done_strobe (sched_wr_done_strobe),
        .sched_wr_beats_done  (sched_wr_beats_done),

        // SRAM Drain Interface
        .axi_wr_drain_req        (drain_req),
        .axi_wr_drain_size       (drain_size),
        .axi_wr_drain_data_avail (drain_data_avail),

        // SRAM Data Interface
        .axi_wr_sram_valid  (drain_valid),
        .axi_wr_sram_drain  (drain_read),
        .axi_wr_sram_id     (drain_id),
        .axi_wr_sram_data   (drain_data),

        // AXI Write Master Interface
        .m_axi_awid         (m_axi_awid),
        .m_axi_awaddr       (m_axi_awaddr),
        .m_axi_awlen        (m_axi_awlen),
        .m_axi_awsize       (m_axi_awsize),
        .m_axi_awburst      (m_axi_awburst),
        .m_axi_awvalid      (m_axi_awvalid),
        .m_axi_awready      (m_axi_awready),

        .m_axi_wdata        (m_axi_wdata),
        .m_axi_wstrb        (m_axi_wstrb),
        .m_axi_wlast        (m_axi_wlast),
        .m_axi_wuser        (),  // Not used at this level
        .m_axi_wvalid       (m_axi_wvalid),
        .m_axi_wready       (m_axi_wready),

        .m_axi_bid          (m_axi_bid),
        .m_axi_bresp        (m_axi_bresp),
        .m_axi_bvalid       (m_axi_bvalid),
        .m_axi_bready       (m_axi_bready),

        // Error and Debug (unconnected at this level)
        .sched_wr_error     (),
        .dbg_wr_all_complete(),
        .dbg_aw_transactions(),
        .dbg_w_beats        ()
    );

endmodule : snk_data_path_beats
