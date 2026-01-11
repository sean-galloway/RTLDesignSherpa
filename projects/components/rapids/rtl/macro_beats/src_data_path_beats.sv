// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: source_data_path
// Purpose: RAPIDS Beats Source Data Path - AXI Read to Drain Pipeline
//
// Description:
//   Multi-channel source data path combining:
//   - axi_read_engine: Multi-channel AXI4 read master with round-robin arbitration
//   - src_sram_controller: Per-channel FIFO buffering with allocation control
//
//   Data flow: Memory -> AXI Read Engine -> SRAM Controller -> External Drain Interface
//
//   For Phase 1 "beats" architecture, the drain interface is exposed externally
//   (no network_master module). Data is read from memory via AXI4 burst reads
//   and buffered in SRAM for external consumption.
//
// Architecture:
//   1. Scheduler Interface: Receives read commands from scheduler array
//   2. AXI Read: AXI Read Engine issues read commands to memory
//   3. SRAM Fill: Read data is allocated/written to per-channel FIFO
//   4. Drain: External consumer drains SRAM data
//
// Documentation: projects/components/rapids/docs/rapids_spec/
// Subsystem: rapids_macro_beats
//
// Author: sean galloway
// Created: 2026-01-10

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module src_data_path_beats #(
    // Primary parameters
    parameter int NUM_CHANNELS = 8,
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int AXI_ID_WIDTH = 8,
    parameter int SRAM_DEPTH = 512,
    parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,
    parameter int PIPELINE = 0,
    parameter int AR_MAX_OUTSTANDING = 8,

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
    input  logic [7:0]                  cfg_axi_rd_xfer_beats,

    //=========================================================================
    // Scheduler Interface (Per-Channel Read Requests)
    // Scheduler issues read commands with address, beats remaining
    //=========================================================================
    input  logic [NC-1:0]               sched_rd_valid,
    input  logic [NC-1:0][AW-1:0]       sched_rd_addr,
    input  logic [NC-1:0][31:0]         sched_rd_beats,

    //=========================================================================
    // Completion Interface (to Schedulers)
    //=========================================================================
    output logic [NC-1:0]               sched_rd_done_strobe,
    output logic [NC-1:0][31:0]         sched_rd_beats_done,
    output logic [NC-1:0]               sched_rd_error,

    //=========================================================================
    // Drain Flow Control Interface (External Consumer)
    // External consumer monitors available data per channel
    //=========================================================================
    output logic [NC-1:0][SCW-1:0]      drain_data_avail,
    input  logic [NC-1:0]               drain_req,
    input  logic [NC-1:0][7:0]          drain_size,

    //=========================================================================
    // Drain Data Interface (SRAM Controller -> External)
    // External consumer reads data from per-channel FIFO
    //=========================================================================
    output logic [NC-1:0]               drain_valid,
    input  logic                        drain_read,
    input  logic [CIW-1:0]              drain_id,
    output logic [DW-1:0]               drain_data,

    //=========================================================================
    // AXI4 Read Master Interface
    //=========================================================================
    // AR Channel
    output logic [IW-1:0]               m_axi_arid,
    output logic [AW-1:0]               m_axi_araddr,
    output logic [7:0]                  m_axi_arlen,
    output logic [2:0]                  m_axi_arsize,
    output logic [1:0]                  m_axi_arburst,
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,

    // R Channel
    input  logic [IW-1:0]               m_axi_rid,
    input  logic [DW-1:0]               m_axi_rdata,
    input  logic [1:0]                  m_axi_rresp,
    input  logic                        m_axi_rlast,
    input  logic                        m_axi_rvalid,
    output logic                        m_axi_rready,

    //=========================================================================
    // Debug Interface
    //=========================================================================
    output logic [NC-1:0]               dbg_rd_all_complete,
    output logic [31:0]                 dbg_r_beats_rcvd,
    output logic [31:0]                 dbg_sram_writes,
    output logic [NC-1:0]               dbg_arb_request,
    output logic [NC-1:0]               dbg_sram_bridge_pending,
    output logic [NC-1:0]               dbg_sram_bridge_out_valid
);

    //=========================================================================
    // Internal Signals - AXI Read Engine to SRAM Controller
    //=========================================================================

    // SRAM Allocation (AXI Read Engine -> SRAM Controller)
    logic                               alloc_req;
    logic [7:0]                         alloc_size;
    logic [IW-1:0]                      alloc_id;
    logic [NC-1:0][SCW-1:0]             alloc_space_free;

    // SRAM Write Data (AXI Read Engine -> SRAM Controller)
    logic                               sram_valid;
    logic                               sram_ready;
    logic [IW-1:0]                      sram_id;
    logic [DW-1:0]                      sram_data;

    //=========================================================================
    // AXI Read Engine Instance
    //=========================================================================

    axi_read_engine_beats #(
        .NUM_CHANNELS       (NC),
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .ID_WIDTH           (IW),
        .SEG_COUNT_WIDTH    (SCW),
        .PIPELINE           (PIPELINE),
        .AR_MAX_OUTSTANDING (AR_MAX_OUTSTANDING),
        .STROBE_EVERY_BEAT  (0)
    ) u_axi_read_engine (
        .clk                (clk),
        .rst_n              (rst_n),

        // Configuration
        .cfg_axi_rd_xfer_beats (cfg_axi_rd_xfer_beats),

        // Scheduler Interface
        .sched_rd_valid     (sched_rd_valid),
        .sched_rd_addr      (sched_rd_addr),
        .sched_rd_beats     (sched_rd_beats),

        // Completion Interface
        .sched_rd_done_strobe (sched_rd_done_strobe),
        .sched_rd_beats_done  (sched_rd_beats_done),

        // SRAM Allocation Interface
        .axi_rd_alloc_req        (alloc_req),
        .axi_rd_alloc_size       (alloc_size),
        .axi_rd_alloc_id         (alloc_id),
        .axi_rd_alloc_space_free (alloc_space_free),

        // SRAM Write Interface
        .axi_rd_sram_valid  (sram_valid),
        .axi_rd_sram_ready  (sram_ready),
        .axi_rd_sram_id     (sram_id),
        .axi_rd_sram_data   (sram_data),

        // AXI Read Master Interface
        .m_axi_arvalid      (m_axi_arvalid),
        .m_axi_arready      (m_axi_arready),
        .m_axi_arid         (m_axi_arid),
        .m_axi_araddr       (m_axi_araddr),
        .m_axi_arlen        (m_axi_arlen),
        .m_axi_arsize       (m_axi_arsize),
        .m_axi_arburst      (m_axi_arburst),

        .m_axi_rvalid       (m_axi_rvalid),
        .m_axi_rready       (m_axi_rready),
        .m_axi_rid          (m_axi_rid),
        .m_axi_rdata        (m_axi_rdata),
        .m_axi_rresp        (m_axi_rresp),
        .m_axi_rlast        (m_axi_rlast),

        // Error Interface
        .sched_rd_error     (sched_rd_error),

        // Debug Interface
        .dbg_rd_all_complete (dbg_rd_all_complete),
        .dbg_r_beats_rcvd    (dbg_r_beats_rcvd),
        .dbg_sram_writes     (dbg_sram_writes),
        .dbg_arb_request     (dbg_arb_request)
    );

    //=========================================================================
    // SRAM Controller Instance
    //=========================================================================

    src_sram_controller_beats #(
        .NUM_CHANNELS       (NC),
        .DATA_WIDTH         (DW),
        .SRAM_DEPTH         (SD),
        .SEG_COUNT_WIDTH    (SCW)
    ) u_src_sram_controller (
        .clk                (clk),
        .rst_n              (rst_n),

        // Fill Allocation Interface (from AXI Read Engine)
        .fill_alloc_req     (alloc_req),
        .fill_alloc_size    (alloc_size),
        .fill_alloc_id      (alloc_id[CIW-1:0]),
        .fill_space_free    (alloc_space_free),

        // Fill Data Interface (from AXI Read Engine)
        .fill_valid         (sram_valid),
        .fill_ready         (sram_ready),
        .fill_id            (sram_id[CIW-1:0]),
        .fill_data          (sram_data),

        // Drain Flow Control Interface (to External Consumer)
        .drain_data_avail   (drain_data_avail),
        .drain_req          (drain_req),
        .drain_size         (drain_size),

        // Drain Data Interface (to External Consumer)
        .drain_valid        (drain_valid),
        .drain_read         (drain_read),
        .drain_id           (drain_id),
        .drain_data         (drain_data),

        // Debug
        .dbg_bridge_pending   (dbg_sram_bridge_pending),
        .dbg_bridge_out_valid (dbg_sram_bridge_out_valid)
    );

endmodule : src_data_path_beats
