// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: source_data_path_axis
// Purpose: RAPIDS Beats Source Data Path with AXIS Interface
//
// Description:
//   Wrapper that adds AXI-Stream master interface to source_data_path.
//   Converts drain interface to AXIS protocol for network egress.
//
//   Data flow: Memory -> AXI Read -> source_data_path -> Drain Logic -> AXIS Master
//
//   The drain to AXIS conversion:
//   - Monitors drain_data_avail for each channel
//   - Issues drain requests based on available data and AXIS backpressure
//   - Converts drain_data/drain_valid to AXIS tdata/tvalid
//   - Uses round-robin arbitration across channels for fair access
//
// Architecture:
//   1. source_data_path: Reads from memory and buffers in SRAM
//   2. Channel Arbiter: Round-robin selection of channels with data
//   3. Drain Controller: Manages drain_req/drain_size for selected channel
//   4. AXIS Master: Streams data out with tid for channel identification
//
// Documentation: projects/components/rapids/docs/rapids_spec/
// Subsystem: rapids_macro_beats
//
// Author: sean galloway
// Created: 2026-01-10

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module src_data_path_axis_beats #(
    // Primary parameters
    parameter int NUM_CHANNELS = 8,
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int AXI_ID_WIDTH = 8,
    parameter int SRAM_DEPTH = 512,
    parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,
    parameter int PIPELINE = 0,
    parameter int AR_MAX_OUTSTANDING = 8,

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
    input  logic [7:0]                  cfg_axi_rd_xfer_beats,
    input  logic [7:0]                  cfg_drain_size,   // Beats to drain per request

    //=========================================================================
    // Scheduler Interface (Per-Channel Read Requests)
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
    // AXI-Stream Master Interface (Network Output)
    //=========================================================================
    output logic [DW-1:0]               m_axis_tdata,
    output logic [SW-1:0]               m_axis_tstrb,
    output logic                        m_axis_tlast,
    output logic [AXIS_ID_WIDTH-1:0]    m_axis_tid,
    output logic [AXIS_DEST_WIDTH-1:0]  m_axis_tdest,
    output logic [AXIS_USER_WIDTH-1:0]  m_axis_tuser,
    output logic                        m_axis_tvalid,
    input  logic                        m_axis_tready,

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
    output logic [NC-1:0]               dbg_sram_bridge_out_valid,
    output logic [31:0]                 dbg_axis_beats_sent,
    output logic [31:0]                 dbg_axis_packets_sent
);

    //=========================================================================
    // Internal Signals
    //=========================================================================

    // Drain interface from source_data_path
    logic [NC-1:0][SCW-1:0]      drain_data_avail;
    logic [NC-1:0]               drain_req;
    logic [NC-1:0][7:0]          drain_size;

    logic [NC-1:0]               drain_valid;
    logic                        drain_read;
    logic [CIW-1:0]              drain_id;
    logic [DW-1:0]               drain_data;

    // Channel arbitration
    logic [NC-1:0]               r_arb_request;    // Channels requesting service
    logic [CIW-1:0]              r_arb_grant_id;   // Currently granted channel
    logic                        r_arb_active;     // Arbitration grant is active
    logic [7:0]                  r_drain_remaining; // Beats remaining in current drain

    // Packet tracking per channel
    logic [NC-1:0][15:0]         r_packet_beats;   // Beats sent in current packet
    logic [NC-1:0]               r_packet_active;  // Packet in progress

    // Statistics
    logic [31:0]                 r_axis_beats_sent;
    logic [31:0]                 r_axis_packets_sent;

    //=========================================================================
    // Channel Arbitration Logic
    //=========================================================================
    // Simple round-robin arbiter selects channels with available data

    // Request when channel has data available
    always_comb begin
        for (int ch = 0; ch < NC; ch++) begin
            r_arb_request[ch] = (drain_data_avail[ch] > 0);
        end
    end

    // Round-robin arbiter state machine
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_arb_grant_id <= '0;
            r_arb_active <= 1'b0;
            r_drain_remaining <= '0;
        end else begin
            if (!r_arb_active || (r_drain_remaining == 0 && m_axis_tvalid && m_axis_tready)) begin
                // No active grant or current drain complete - find next channel
                r_arb_active <= 1'b0;
                for (int ch = 0; ch < NC; ch++) begin
                    // Start search from channel after current grant (round-robin)
                    logic [CIW-1:0] check_ch;
                    check_ch = (r_arb_grant_id + 1 + ch) % NC;
                    if (drain_data_avail[check_ch] >= cfg_drain_size) begin
                        r_arb_grant_id <= check_ch;
                        r_arb_active <= 1'b1;
                        r_drain_remaining <= cfg_drain_size;
                        break;
                    end
                end
            end else if (drain_read && drain_valid[r_arb_grant_id]) begin
                // Decrement remaining on successful read
                if (r_drain_remaining > 0) begin
                    r_drain_remaining <= r_drain_remaining - 1'b1;
                end
            end
        end
    )

    //=========================================================================
    // Drain Request Generation
    //=========================================================================

    // Generate drain requests based on arbitration
    always_comb begin
        drain_req = '0;
        drain_size = '{default:'0};
        if (r_arb_active) begin
            drain_req[r_arb_grant_id] = 1'b1;
            drain_size[r_arb_grant_id] = cfg_drain_size;
        end
    end

    // Drain read when AXIS accepts data
    assign drain_id = r_arb_grant_id;
    assign drain_read = m_axis_tvalid && m_axis_tready && r_arb_active;

    //=========================================================================
    // Drain to AXIS Interface Conversion
    //=========================================================================

    // AXIS tdata directly from drain
    assign m_axis_tdata = drain_data;

    // All bytes valid
    assign m_axis_tstrb = {SW{1'b1}};

    // Channel ID in tid
    assign m_axis_tid = {{(AXIS_ID_WIDTH-CIW){1'b0}}, r_arb_grant_id};

    // Destination from configuration (can be channel-based)
    assign m_axis_tdest = {{(AXIS_DEST_WIDTH-CIW){1'b0}}, r_arb_grant_id};

    // User field unused
    assign m_axis_tuser = '0;

    // Valid when we have data and active grant
    assign m_axis_tvalid = r_arb_active && drain_valid[r_arb_grant_id];

    // Last when drain remaining reaches 0
    assign m_axis_tlast = (r_drain_remaining == 1);

    //=========================================================================
    // Statistics
    //=========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_axis_beats_sent <= '0;
            r_axis_packets_sent <= '0;
        end else begin
            if (m_axis_tvalid && m_axis_tready) begin
                r_axis_beats_sent <= r_axis_beats_sent + 1'b1;
                if (m_axis_tlast) begin
                    r_axis_packets_sent <= r_axis_packets_sent + 1'b1;
                end
            end
        end
    )

    //=========================================================================
    // Debug Outputs
    //=========================================================================
    assign dbg_axis_beats_sent = r_axis_beats_sent;
    assign dbg_axis_packets_sent = r_axis_packets_sent;

    //=========================================================================
    // Source Data Path Instance
    //=========================================================================

    src_data_path_beats #(
        .NUM_CHANNELS       (NC),
        .ADDR_WIDTH         (AW),
        .DATA_WIDTH         (DW),
        .AXI_ID_WIDTH       (IW),
        .SRAM_DEPTH         (SD),
        .SEG_COUNT_WIDTH    (SCW),
        .PIPELINE           (PIPELINE),
        .AR_MAX_OUTSTANDING (AR_MAX_OUTSTANDING)
    ) u_source_data_path (
        .clk                    (clk),
        .rst_n                  (rst_n),

        // Configuration
        .cfg_axi_rd_xfer_beats  (cfg_axi_rd_xfer_beats),

        // Scheduler Interface
        .sched_rd_valid         (sched_rd_valid),
        .sched_rd_addr          (sched_rd_addr),
        .sched_rd_beats         (sched_rd_beats),

        // Completion Interface
        .sched_rd_done_strobe   (sched_rd_done_strobe),
        .sched_rd_beats_done    (sched_rd_beats_done),
        .sched_rd_error         (sched_rd_error),

        // Drain Flow Control Interface
        .drain_data_avail       (drain_data_avail),
        .drain_req              (drain_req),
        .drain_size             (drain_size),

        // Drain Data Interface
        .drain_valid            (drain_valid),
        .drain_read             (drain_read),
        .drain_id               (drain_id),
        .drain_data             (drain_data),

        // AXI Read Master Interface
        .m_axi_arid             (m_axi_arid),
        .m_axi_araddr           (m_axi_araddr),
        .m_axi_arlen            (m_axi_arlen),
        .m_axi_arsize           (m_axi_arsize),
        .m_axi_arburst          (m_axi_arburst),
        .m_axi_arvalid          (m_axi_arvalid),
        .m_axi_arready          (m_axi_arready),

        .m_axi_rid              (m_axi_rid),
        .m_axi_rdata            (m_axi_rdata),
        .m_axi_rresp            (m_axi_rresp),
        .m_axi_rlast            (m_axi_rlast),
        .m_axi_rvalid           (m_axi_rvalid),
        .m_axi_rready           (m_axi_rready),

        // Debug Interface
        .dbg_rd_all_complete    (dbg_rd_all_complete),
        .dbg_r_beats_rcvd       (dbg_r_beats_rcvd),
        .dbg_sram_writes        (dbg_sram_writes),
        .dbg_arb_request        (dbg_arb_request),
        .dbg_sram_bridge_pending    (dbg_sram_bridge_pending),
        .dbg_sram_bridge_out_valid  (dbg_sram_bridge_out_valid)
    );

endmodule : src_data_path_axis_beats
