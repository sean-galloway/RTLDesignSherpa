// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: sink_data_path_axis
// Purpose: RAPIDS Beats Sink Data Path with AXIS Interface
//
// Description:
//   Wrapper that adds AXI-Stream slave interface to sink_data_path.
//   Converts AXIS protocol to fill interface for SRAM ingress.
//
//   Data flow: AXIS Slave -> Fill Logic -> sink_data_path -> AXI Write -> Memory
//
//   The AXIS to fill conversion:
//   - Tracks incoming AXIS beats per channel using tid/tdest
//   - Manages fill_alloc_req to reserve SRAM space before data
//   - Converts AXIS tvalid/tready to fill_valid/fill_ready
//
// Architecture:
//   1. AXIS Slave: Receives streaming data with tid for channel selection
//   2. Fill Allocator: Requests SRAM space based on packet tracking
//   3. Fill Data Path: Routes AXIS data to appropriate channel FIFO
//   4. sink_data_path: Buffers and writes to memory via AXI
//
// Documentation: projects/components/rapids/docs/rapids_spec/
// Subsystem: rapids_macro_beats
//
// Author: sean galloway
// Created: 2026-01-10

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module snk_data_path_axis_beats #(
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

    // AXIS parameters
    parameter int AXIS_ID_WIDTH = 8,
    parameter int AXIS_DEST_WIDTH = 4,
    parameter int AXIS_USER_WIDTH = 1,

    // Short aliases
    parameter int NC = NUM_CHANNELS,
    parameter int AW = ADDR_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int IW = AXI_ID_WIDTH,
    parameter int SD = SRAM_DEPTH,
    parameter int SCW = SEG_COUNT_WIDTH,
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1,
    parameter int SW = DW / 8
) (
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // Configuration Interface
    //=========================================================================
    input  logic [7:0]                  cfg_axi_wr_xfer_beats,
    input  logic [7:0]                  cfg_alloc_size,   // Default allocation size per request

    //=========================================================================
    // AXI-Stream Slave Interface (Network Input)
    //=========================================================================
    input  logic [DW-1:0]               s_axis_tdata,
    input  logic [SW-1:0]               s_axis_tstrb,
    input  logic                        s_axis_tlast,
    input  logic [AXIS_ID_WIDTH-1:0]    s_axis_tid,
    input  logic [AXIS_DEST_WIDTH-1:0]  s_axis_tdest,
    input  logic [AXIS_USER_WIDTH-1:0]  s_axis_tuser,
    input  logic                        s_axis_tvalid,
    output logic                        s_axis_tready,

    //=========================================================================
    // Scheduler Interface (Per-Channel Write Requests)
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
    output logic [NC-1:0]               dbg_sram_bridge_out_valid,
    output logic [31:0]                 dbg_axis_beats_received,
    output logic [31:0]                 dbg_axis_packets_received
);

    //=========================================================================
    // Internal Signals
    //=========================================================================

    // Fill interface to sink_data_path
    logic                        fill_alloc_req;
    logic [7:0]                  fill_alloc_size;
    logic [CIW-1:0]              fill_alloc_id;
    logic [NC-1:0][SCW-1:0]      fill_space_free;

    logic                        fill_valid;
    logic                        fill_ready;
    logic [CIW-1:0]              fill_id;
    logic [DW-1:0]               fill_data;

    // Channel extraction from AXIS
    logic [CIW-1:0]              axis_channel_id;

    // Allocation tracking per channel
    logic [NC-1:0][15:0]         r_pending_alloc;  // Beats allocated but not yet filled
    logic [NC-1:0]               r_need_alloc;     // Channel needs allocation

    // Statistics
    logic [31:0]                 r_axis_beats_received;
    logic [31:0]                 r_axis_packets_received;

    //=========================================================================
    // Channel ID Extraction
    //=========================================================================
    // Use lower bits of tid as channel ID
    assign axis_channel_id = s_axis_tid[CIW-1:0];

    //=========================================================================
    // AXIS to Fill Interface Conversion
    //=========================================================================

    // Fill data directly from AXIS
    assign fill_data = s_axis_tdata;
    assign fill_id = axis_channel_id;

    // Determine if we need allocation before accepting data
    wire w_channel_needs_alloc = (r_pending_alloc[axis_channel_id] == '0);
    wire w_channel_has_space = (fill_space_free[axis_channel_id] >= cfg_alloc_size);

    // Generate allocation request when needed and space available
    assign fill_alloc_req = s_axis_tvalid && w_channel_needs_alloc && w_channel_has_space;
    assign fill_alloc_size = cfg_alloc_size;
    assign fill_alloc_id = axis_channel_id;

    // Data valid when:
    // 1. AXIS has valid data AND
    // 2. Channel has pending allocation (space reserved) OR allocation is happening this cycle
    // NOTE: Must include allocation case to avoid losing first beat of each packet!
    assign fill_valid = s_axis_tvalid &&
                        ((r_pending_alloc[axis_channel_id] > 0) ||
                         (w_channel_needs_alloc && w_channel_has_space));

    // AXIS ready when:
    // 1. Fill interface is ready
    // 2. OR we're doing an allocation request (will accept data next cycle)
    assign s_axis_tready = (fill_ready && (r_pending_alloc[axis_channel_id] > 0)) ||
                           (fill_alloc_req);

    //=========================================================================
    // Allocation Tracking
    //=========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pending_alloc <= '{default:'0};
            r_axis_beats_received <= '0;
            r_axis_packets_received <= '0;
        end else begin
            for (int ch = 0; ch < NC; ch++) begin
                // Allocation adds to pending count
                if (fill_alloc_req && (fill_alloc_id == ch[CIW-1:0])) begin
                    if (fill_valid && fill_ready && (fill_id == ch[CIW-1:0])) begin
                        // Allocate and consume in same cycle
                        r_pending_alloc[ch] <= r_pending_alloc[ch] + fill_alloc_size - 1'b1;
                    end else begin
                        // Just allocate
                        r_pending_alloc[ch] <= r_pending_alloc[ch] + fill_alloc_size;
                    end
                end else if (fill_valid && fill_ready && (fill_id == ch[CIW-1:0])) begin
                    // Just consume
                    r_pending_alloc[ch] <= r_pending_alloc[ch] - 1'b1;
                end
            end

            // Statistics
            if (s_axis_tvalid && s_axis_tready) begin
                r_axis_beats_received <= r_axis_beats_received + 1'b1;
                if (s_axis_tlast) begin
                    r_axis_packets_received <= r_axis_packets_received + 1'b1;
                end
            end
        end
    )

    //=========================================================================
    // Debug Outputs
    //=========================================================================
    assign dbg_axis_beats_received = r_axis_beats_received;
    assign dbg_axis_packets_received = r_axis_packets_received;

    //=========================================================================
    // Sink Data Path Instance
    //=========================================================================

    snk_data_path_beats #(
        .NUM_CHANNELS       (NC),
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .AXI_ID_WIDTH       (IW),
        .SRAM_DEPTH         (SD),
        .SEG_COUNT_WIDTH    (SCW),
        .PIPELINE           (PIPELINE),
        .AW_MAX_OUTSTANDING (AW_MAX_OUTSTANDING),
        .W_PHASE_FIFO_DEPTH (W_PHASE_FIFO_DEPTH),
        .B_PHASE_FIFO_DEPTH (B_PHASE_FIFO_DEPTH)
    ) u_sink_data_path (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Configuration
        .cfg_axi_wr_xfer_beats  (cfg_axi_wr_xfer_beats),

        // Fill Allocation Interface
        .fill_alloc_req         (fill_alloc_req),
        .fill_alloc_size        (fill_alloc_size),
        .fill_alloc_id          (fill_alloc_id),
        .fill_space_free        (fill_space_free),

        // Fill Data Interface
        .fill_valid             (fill_valid),
        .fill_ready             (fill_ready),
        .fill_id                (fill_id),
        .fill_data              (fill_data),

        // Scheduler Interface
        .sched_wr_valid         (sched_wr_valid),
        .sched_wr_ready         (sched_wr_ready),
        .sched_wr_addr          (sched_wr_addr),
        .sched_wr_beats         (sched_wr_beats),
        .sched_wr_burst_len     (sched_wr_burst_len),

        // Completion Interface
        .sched_wr_done_strobe   (sched_wr_done_strobe),
        .sched_wr_beats_done    (sched_wr_beats_done),

        // AXI Write Master Interface
        .m_axi_awid             (m_axi_awid),
        .m_axi_awaddr           (m_axi_awaddr),
        .m_axi_awlen            (m_axi_awlen),
        .m_axi_awsize           (m_axi_awsize),
        .m_axi_awburst          (m_axi_awburst),
        .m_axi_awvalid          (m_axi_awvalid),
        .m_axi_awready          (m_axi_awready),

        .m_axi_wdata            (m_axi_wdata),
        .m_axi_wstrb            (m_axi_wstrb),
        .m_axi_wlast            (m_axi_wlast),
        .m_axi_wvalid           (m_axi_wvalid),
        .m_axi_wready           (m_axi_wready),

        .m_axi_bid              (m_axi_bid),
        .m_axi_bresp            (m_axi_bresp),
        .m_axi_bvalid           (m_axi_bvalid),
        .m_axi_bready           (m_axi_bready),

        // Debug Interface
        .dbg_sram_bridge_pending    (dbg_sram_bridge_pending),
        .dbg_sram_bridge_out_valid  (dbg_sram_bridge_out_valid)
    );

endmodule : snk_data_path_axis_beats
