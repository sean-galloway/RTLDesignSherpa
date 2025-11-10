// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_write_engine
// Purpose: Multi-Channel AXI4 Write Engine with Space-Aware Arbitration
//
// Description:
//   High-performance multi-channel AXI4 write engine with:
//   - Round-robin arbitration across channels
//   - Space-aware request masking (only arbitrate channels with sufficient SRAM data)
//   - Pre-allocation handshake with SRAM controller
//   - Streaming data path from SRAM controller
//
// Architecture:
//   1. Scheduler Interface: Each channel can request write bursts
//   2. Space Checking: Mask channels without sufficient SRAM data
//   3. Arbitration: Round-robin arbiter selects next channel to service
//   4. AXI AW Issue: Issue write command to AXI, assert wr_alloc to SRAM controller
//   5. AXI W Stream: Stream write data from SRAM controller
//   6. AXI B Response: Handle write response, complete transaction
//
// Key Features:
//   - Arbiter only grants to channels with sufficient SRAM data
//   - wr_alloc asserted when AXI AW command issues
//   - Channel ID encoded in AXI transaction ID for response routing
//   - No internal buffering (streaming pipeline)
//
// Documentation: projects/components/stream/PRD.md
// Subsystem: stream_fub
//
// Author: sean galloway
// Created: 2025-10-30

`timescale 1ns / 1ps

// Import common STREAM and monitor packages
`include "stream_imports.svh"
`include "reset_defs.svh"


module axi_write_engine #(
    // Primary parameters (long names for external configuration)
    parameter int NUM_CHANNELS = 8,                 // Number of channels
    parameter int ADDR_WIDTH = 64,                  // AXI address width
    parameter int DATA_WIDTH = 512,                 // AXI data width
    parameter int ID_WIDTH = 8,                     // AXI ID width
    parameter int MAX_BURST_LEN = 16,               // Maximum AXI burst length
    parameter int COUNT_WIDTH = 8,                  // Width of space/count signals (typically $clog2(FIFO_DEPTH)+1)
    parameter int PIPELINE = 0,                     // 0: wait for all data before next request per channel
                                                    // 1: allow multiple outstanding requests per channel

    // Short aliases (for internal use)
    parameter int NC = NUM_CHANNELS,
    parameter int AW = ADDR_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int IW = ID_WIDTH,
    parameter int CW = (NC > 1) ? $clog2(NC) : 1  // Channel ID width
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // Configuration Interface
    //=========================================================================
    input  logic [7:0]                  cfg_axi_wr_xfer_beats,  // Transfer size in beats (applies to all channels)

    //=========================================================================
    // Scheduler Interface (Per-Channel Write Requests)
    //=========================================================================
    input  logic [NC-1:0]               sched_wr_valid,      // Channel requests write
    output logic [NC-1:0]               sched_wr_ready,      // Engine ready for channel
    input  logic [NC-1:0][AW-1:0]       sched_wr_addr,       // Destination addresses
    input  logic [NC-1:0][31:0]         sched_wr_beats,      // Beats remaining to write
    input  logic [NC-1:0][7:0]          sched_wr_burst_len,  // Requested burst length

    //=========================================================================
    // SRAM Allocation Interface (to SRAM Controller)
    //=========================================================================
    // Pre-allocation interface (before data read)
    output logic [NC-1:0]               wr_alloc_req,        // Channel requests to reserve space
    output logic [NC-1:0][7:0]          wr_alloc_size,       // Beats to reserve
    input  logic [NC-1:0][COUNT_WIDTH-1:0] wr_data_available, // Data count available (beats in FIFO)

    //=========================================================================
    // AXI4 AW Channel (Write Address)
    //=========================================================================
    output logic [IW-1:0]               m_axi_awid,
    output logic [AW-1:0]               m_axi_awaddr,
    output logic [7:0]                  m_axi_awlen,         // Burst length - 1
    output logic [2:0]                  m_axi_awsize,        // Burst size (log2(bytes))
    output logic [1:0]                  m_axi_awburst,       // Burst type (INCR)
    output logic                        m_axi_awvalid,
    input  logic                        m_axi_awready,

    //=========================================================================
    // AXI4 W Channel (Write Data)
    //=========================================================================
    output logic [DW-1:0]               m_axi_wdata,
    output logic [(DW/8)-1:0]           m_axi_wstrb,
    output logic                        m_axi_wlast,
    output logic                        m_axi_wvalid,
    input  logic                        m_axi_wready,

    //=========================================================================
    // AXI4 B Channel (Write Response)
    //=========================================================================
    input  logic [IW-1:0]               m_axi_bid,
    input  logic [1:0]                  m_axi_bresp,
    input  logic                        m_axi_bvalid,
    output logic                        m_axi_bready,

    //=========================================================================
    // SRAM Read Interface (from SRAM Controller)
    // ID-based interface matching sram_controller output
    //=========================================================================
    input  logic [NC-1:0]               axi_wr_sram_valid,   // Per-channel valid (data available)
    output logic                        axi_wr_sram_drain,   // Drain request (consumer ready)
    output logic [CW-1:0]               axi_wr_sram_id,      // Channel ID select for drain
    input  logic [DW-1:0]               axi_wr_sram_data,    // Data from selected channel (muxed)

    //=========================================================================
    // Completion Interface (to Schedulers)
    //=========================================================================
    // Notify schedulers when write burst completes
    output logic [NC-1:0]               sched_wr_done_strobe,  // Burst completed (pulsed for 1 cycle)
    output logic [NC-1:0][31:0]         sched_wr_beats_done,   // Number of beats completed in burst

    //=========================================================================
    // Debug Interface (for verification/debug only)
    //=========================================================================
    output logic [31:0]                 dbg_aw_transactions,   // Total AW transactions issued
    output logic [31:0]                 dbg_w_beats            // Total W beats written to AXI
);

    //=========================================================================
    // Local Parameters
    //=========================================================================

    localparam int BYTES_PER_BEAT = DW / 8;
    localparam int AXSIZE = $clog2(BYTES_PER_BEAT);

    //=========================================================================
    // Outstanding Transaction Tracking
    //=========================================================================
    // PIPELINE=0: Boolean flag per channel (0 or 1 transaction)
    // PIPELINE=1: Counter per channel (0 to MAX_OUTSTANDING)

    logic [NC-1:0] r_outstanding;             // Boolean: channel at/exceeds limit
    logic [NC-1:0][3:0] r_outstanding_count;  // PIPELINE=1: Counter (0-15)

    generate
        if (PIPELINE == 0) begin : gen_no_pipeline_tracking
            // Per-channel boolean flag (0 or 1 outstanding)
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_outstanding <= '0;
                end else begin
                    for (int i = 0; i < NC; i++) begin
                        // Set outstanding when AW issues for this channel
                        if (m_axi_awvalid && m_axi_awready && (r_aw_channel_id == i[CW-1:0])) begin
                            r_outstanding[i] <= 1'b1;
                        end
                        // Clear outstanding when B response arrives for this channel
                        // FIX: Changed from else-if to independent if to handle same-cycle AW/B
                        if (m_axi_bvalid && m_axi_bready &&
                                (m_axi_bid[CW-1:0] == i[CW-1:0])) begin
                            r_outstanding[i] <= 1'b0;
                        end
                    end
                end
            )
            // Counter not used in PIPELINE=0 mode
            assign r_outstanding_count = '0;

        end else begin : gen_pipeline_tracking
            // Per-channel counter (0 to MAX_OUTSTANDING)
            localparam int MAX_OUTSTANDING = 8;  // Limit per channel

            logic [NC-1:0] w_incr, w_decr;  // Increment/decrement signals

            // Determine which channels increment/decrement
            always_comb begin
                for (int i = 0; i < NC; i++) begin
                    w_incr[i] = m_axi_awvalid && m_axi_awready && (r_aw_channel_id == i[CW-1:0]);
                    w_decr[i] = m_axi_bvalid && m_axi_bready && (m_axi_bid[CW-1:0] == i[CW-1:0]);
                end
            end

            // Update counters
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_outstanding_count <= '0;
                end else begin
                    for (int i = 0; i < NC; i++) begin
                        case ({w_incr[i], w_decr[i]})
                            2'b10: r_outstanding_count[i] <= r_outstanding_count[i] + 4'd1;  // AW only
                            2'b01: r_outstanding_count[i] <= r_outstanding_count[i] - 4'd1;  // B only
                            default: r_outstanding_count[i] <= r_outstanding_count[i];       // Both or neither
                        endcase
                    end
                end
            )

            // Boolean flag = at or exceeds limit (prevents new AW when maxed)
            always_comb begin
                for (int i = 0; i < NC; i++) begin
                    r_outstanding[i] = (r_outstanding_count[i] >= 4'(MAX_OUTSTANDING));
                end
            end
        end
    endgenerate

    //=========================================================================
    // Beats Written Tracking (for address calculation)
    //=========================================================================
    // Track how many beats have been written (B responses received)
    // Track whether we've issued first AW for current descriptor (PIPELINE=1 only)

    logic [NC-1:0][31:0] r_beats_written;  // Beats written per channel (B responses)
    logic [NC-1:0][31:0] r_beats_issued;   // Beats issued per channel (AW transactions)
    logic [NC-1:0] r_aw_issued;  // Has first AW been issued for current descriptor (PIPELINE=1)

    // Track beats written: increment when B response arrives, reset when sched_wr_valid de-asserts
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_beats_written <= '{default:0};
            r_aw_issued <= '0;
        end else begin
            for (int i = 0; i < NC; i++) begin
                // Reset written counter when scheduler de-asserts valid (new descriptor or transfer complete)
                if (!sched_wr_valid[i]) begin
                    r_beats_written[i] <= 32'h0;
                    r_aw_issued[i] <= 1'b0;  // New descriptor coming, clear AW issued flag
                // Increment when B response arrives for this channel
                end else if (m_axi_bvalid && m_axi_bready && (m_axi_bid[CW-1:0] == i[CW-1:0])) begin
                    r_beats_written[i] <= r_beats_written[i] + {24'h0, cfg_axi_wr_xfer_beats};
                end

                // Track when first AW issues for descriptor (PIPELINE=1 only)
                if (m_axi_awvalid && m_axi_awready && (r_aw_channel_id == i[CW-1:0])) begin
                    r_aw_issued[i] <= 1'b1;
                end
            end
        end
    )

    // Track beats issued: increment when AW issues, reset when sched_wr_valid de-asserts
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_beats_issued <= '{default:0};
        end else begin
            for (int i = 0; i < NC; i++) begin
                // Reset issued counter when scheduler de-asserts valid (new descriptor or transfer complete)
                if (!sched_wr_valid[i]) begin
                    r_beats_issued[i] <= 32'h0;
                // Increment when AW transaction issues for this channel
                end else if (m_axi_awvalid && m_axi_awready && (w_arb_grant_id == i[CW-1:0])) begin
                    r_beats_issued[i] <= r_beats_issued[i] + {24'h0, cfg_axi_wr_xfer_beats};
                end
            end
        end
    )

    //=========================================================================
    // Data-Aware Request Masking
    //=========================================================================
    // Only allow arbitration for channels with sufficient SRAM data
    // and (if PIPELINE=0) no outstanding transactions
    // Write engine drains SRAM - fabric will backpressure if needed

    logic [NC-1:0] w_data_ok;            // Channel has enough data for burst
    logic [NC-1:0] w_no_outstanding;     // Channel has no outstanding transaction (or pipeline allowed)
    logic [NC-1:0] w_arb_request;        // Masked requests to arbiter

    always_comb begin
        for (int i = 0; i < NC; i++) begin
            // Check if channel has enough data for configured burst size
            // OR if this is the final burst (remaining data < burst size)
            logic has_data = (COUNT_WIDTH'(wr_data_available[i]) >= COUNT_WIDTH'(cfg_axi_wr_xfer_beats));
            logic is_final_burst = (COUNT_WIDTH'(wr_data_available[i]) > 0) &&
                                (COUNT_WIDTH'(wr_data_available[i]) < COUNT_WIDTH'(cfg_axi_wr_xfer_beats));
            w_data_ok[i] = has_data || is_final_burst;

            // Check no-pipeline constraint (only for PIPELINE=0 mode)
            if (PIPELINE == 0) begin
                w_no_outstanding[i] = !r_outstanding[i];
            end else begin
                w_no_outstanding[i] = 1'b1;  // PIPELINE=1: always allow (ignore outstanding)
            end

            // Only request arbitration if:
            // 1. Scheduler is requesting (sched_wr_valid)
            // 2. Sufficient SRAM data available (w_data_ok)
            // 3. No outstanding transaction (w_no_outstanding) if PIPELINE=0
            w_arb_request[i] = sched_wr_valid[i] && w_data_ok[i] && w_no_outstanding[i];
        end
    end

    //=========================================================================
    // Round-Robin Arbiter (or Direct Grant for Single Channel)
    //=========================================================================

    logic              w_arb_grant_valid;
    logic [NC-1:0]     w_arb_grant;
    logic [CW-1:0]     w_arb_grant_id;
    logic [NC-1:0]     w_arb_grant_ack;

    generate
        if (NC == 1) begin : gen_single_channel
            // Single channel - no arbitration needed, grant directly
            assign w_arb_grant_valid = w_arb_request[0];
            assign w_arb_grant = w_arb_request;  // Direct passthrough
            assign w_arb_grant_id = 1'b0;        // Always channel 0
            // ACK signal must still be driven for AW channel management
        end else begin : gen_multi_channel
            // Multiple channels - use round-robin arbiter
            arbiter_round_robin #(
                .CLIENTS      (NC),
                .WAIT_GNT_ACK (1)              // Use ACK mode (wait for command acceptance)
            ) u_arbiter (
                .clk          (clk),
                .rst_n        (rst_n),
                .block_arb    (1'b0),          // Never block arbitration
                .request      (w_arb_request),
                .grant_ack    (w_arb_grant_ack),
                .grant_valid  (w_arb_grant_valid),
                .grant        (w_arb_grant),
                .grant_id     (w_arb_grant_id),
                .last_grant   ()               // Not used
            );
        end
    endgenerate

    //=========================================================================
    // AW Channel Management
    //=========================================================================

    logic [7:0]    r_aw_len;
    logic [CW-1:0] r_aw_channel_id;
    logic          r_aw_valid;

    // Acknowledge arbiter grant when AXI accepts AW command
    assign w_arb_grant_ack = w_arb_grant & {NC{(m_axi_awvalid && m_axi_awready)}};

    // AW channel issue logic
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_aw_valid <= 1'b0;
            r_aw_len <= '0;
            r_aw_channel_id <= '0;
        end else begin
            // Accept new command from arbiter
            if (w_arb_grant_valid && !r_aw_valid) begin
                r_aw_valid <= 1'b1;
                r_aw_channel_id <= w_arb_grant_id;
                r_aw_len <= cfg_axi_wr_xfer_beats - 8'd1;  // AXI uses len-1 (configured burst size)
            end

            // Clear valid when AXI accepts AW
            if (m_axi_awvalid && m_axi_awready) begin
                r_aw_valid <= 1'b0;
            end
        end
    )

    // AXI AW outputs
    assign m_axi_awvalid = r_aw_valid;
    assign m_axi_awid = {{(IW-CW){1'b0}}, r_aw_channel_id};  // Channel ID in lower bits
    // Address = base + beats_issued (simple combinational, same as read engine)
    assign m_axi_awaddr = sched_wr_addr[w_arb_grant_id] + (AW'(r_beats_issued[w_arb_grant_id]) << AXSIZE);
    assign m_axi_awlen = r_aw_len;
    assign m_axi_awsize = 3'(AXSIZE);
    assign m_axi_awburst = 2'b01;  // INCR

    //=========================================================================
    // SRAM Pre-Allocation
    //=========================================================================
    // Assert wr_alloc when AXI AW command is issued
    // This reserves the SRAM read path, actual drain controlled by axi_wr_sram_ready

    logic [NC-1:0] r_alloc_req;
    logic [NC-1:0][7:0] r_alloc_size;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_alloc_req <= '0;
            r_alloc_size <= '0;
        end else begin
            // Default: clear allocation request after 1 cycle
            r_alloc_req <= '0;

            // Assert allocation when AXI AW command issues
            if (m_axi_awvalid && m_axi_awready) begin
                r_alloc_req[r_aw_channel_id] <= 1'b1;
                r_alloc_size[r_aw_channel_id] <= cfg_axi_wr_xfer_beats;  // Configured burst size
            end
        end
    )

    assign wr_alloc_req = r_alloc_req;
    assign wr_alloc_size = r_alloc_size;

    //=========================================================================
    // Scheduler Ready Signals
    //=========================================================================
    // Ready when descriptor transfer completes (final B response received)
    // NOT when AW handshakes (that would reset r_beats_written prematurely!)

    logic [NC-1:0] r_sched_ready;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_sched_ready <= '0;
        end else begin
            // Default: clear ready
            r_sched_ready <= '0;

            // Assert ready when B response completes descriptor transfer
            // Check if this B response finishes all beats for the descriptor
            if (m_axi_bvalid && m_axi_bready) begin
                logic [CW-1:0] ch_id;
                logic [31:0] new_beats_written;

                ch_id = m_axi_bid[CW-1:0];
                new_beats_written = r_beats_written[ch_id] + {24'h0, cfg_axi_wr_xfer_beats};

                // If all descriptor beats completed, assert ready
                if (new_beats_written >= sched_wr_beats[ch_id]) begin
                    r_sched_ready[ch_id] <= 1'b1;
                end
            end
        end
    )

    assign sched_wr_ready = r_sched_ready;

    // Debug: Track sched_wr_ready assertions
    `ifndef SYNTHESIS
    always @(posedge clk) begin
        if (m_axi_bvalid && m_axi_bready) begin
            automatic logic [CW-1:0] ch_id = m_axi_bid[CW-1:0];
            automatic logic [31:0] new_beats = r_beats_written[ch_id] + {24'h0, cfg_axi_wr_xfer_beats};
            $display("AXI_WR_ENG @%t: B response ch=%0d, r_beats_written=%0d, new=%0d, sched_wr_beats=%0d, ready_will_assert=%b",
                    $time, ch_id, r_beats_written[ch_id], new_beats, sched_wr_beats[ch_id],
                    (new_beats >= sched_wr_beats[ch_id]));
        end

        for (int i = 0; i < NC; i++) begin
            if (r_sched_ready[i]) begin
                $display("AXI_WR_ENG @%t: sched_wr_ready[%0d] ASSERTED (valid=%b, beats=%0d)",
                        $time, i, sched_wr_valid[i], sched_wr_beats[i]);
            end
        end
    end
    `endif

    //=========================================================================
    // W Channel Management
    //=========================================================================
    // Stream data from active channel's FIFO to AXI W channel
    //
    // PIPELINE=0: Direct connection from AW to W (one transaction at a time)
    // PIPELINE=1: AW commands queued in FIFO, W processes sequentially

    logic [7:0]    r_w_beats_remaining;
    logic [CW-1:0] r_w_channel_id;
    logic          r_w_active;

    // Signals for W channel start (either direct or from FIFO)
    logic          w_start_w_phase;
    logic [7:0]    w_start_w_len;
    logic [CW-1:0] w_start_w_channel_id;

    generate
        if (PIPELINE == 0) begin : gen_w_no_pipeline
            // PIPELINE=0: Direct connection from AW to W
            // W phase starts immediately when AW handshakes
            assign w_start_w_phase = m_axi_awvalid && m_axi_awready;
            assign w_start_w_len = m_axi_awlen + 8'd1;
            assign w_start_w_channel_id = r_aw_channel_id;

        end else begin : gen_w_pipeline
            // PIPELINE=1: Queue AW commands in FIFO for sequential W processing
            // This prevents W channel state from being overwritten by subsequent AW commands

            localparam int AW_FIFO_WIDTH = AW + 8 + CW;  // addr + len + channel_id
            localparam int AW_FIFO_DEPTH = 16;           // Max 16 outstanding AW commands

            // FIFO write interface (enqueue AW commands)
            logic                        aw_fifo_wr_valid;
            logic                        aw_fifo_wr_ready;
            logic [AW_FIFO_WIDTH-1:0]    aw_fifo_wr_data;

            // FIFO read interface (dequeue for W processing)
            logic                        aw_fifo_rd_valid;
            logic                        aw_fifo_rd_ready;
            logic [AW_FIFO_WIDTH-1:0]    aw_fifo_rd_data;

            // Pack AW command into FIFO on AW handshake
            assign aw_fifo_wr_valid = m_axi_awvalid && m_axi_awready;
            assign aw_fifo_wr_data = {m_axi_awaddr, m_axi_awlen, r_aw_channel_id};

            // W phase starts when FIFO has data and W is idle
            assign w_start_w_phase = aw_fifo_rd_valid && !r_w_active;
            // Extract len and channel_id from FIFO data (address not needed for W channel)
            assign w_start_w_len = aw_fifo_rd_data[CW+7:CW] + 8'd1;  // awlen + 1 = beat count
            assign w_start_w_channel_id = aw_fifo_rd_data[CW-1:0];

            // Dequeue FIFO entry when W phase starts
            assign aw_fifo_rd_ready = w_start_w_phase;

            // AW command FIFO
            gaxi_fifo_sync #(
                .MEM_STYLE    (FIFO_AUTO),
                .REGISTERED   (0),               // No extra latency
                .DATA_WIDTH   (AW_FIFO_WIDTH),
                .DEPTH        (AW_FIFO_DEPTH)
            ) u_aw_cmd_fifo (
                .axi_aclk     (clk),
                .axi_aresetn  (rst_n),
                .wr_valid     (aw_fifo_wr_valid),
                .wr_ready     (aw_fifo_wr_ready),
                .wr_data      (aw_fifo_wr_data),
                .rd_valid     (aw_fifo_rd_valid),
                .rd_ready     (aw_fifo_rd_ready),
                .rd_data      (aw_fifo_rd_data),
                .count        ()                 // Not used
            );

        end
    endgenerate

    // W channel state machine (common to both PIPELINE modes)
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_w_beats_remaining <= '0;
            r_w_channel_id <= '0;
            r_w_active <= 1'b0;
        end else begin
            // Start W phase (from direct connection or FIFO)
            if (w_start_w_phase) begin
                r_w_beats_remaining <= w_start_w_len;
                r_w_channel_id <= w_start_w_channel_id;
                r_w_active <= 1'b1;
            end

            // Decrement beats as data transfers
            if (r_w_active && m_axi_wvalid && m_axi_wready) begin
                r_w_beats_remaining <= r_w_beats_remaining - 8'd1;

                // End W phase on last beat
                if (m_axi_wlast) begin
                    r_w_active <= 1'b0;
                end
            end
        end
    )

    // SRAM drain control - ID-based interface
    // When active and AXI ready, drain from SRAM using channel ID
    assign axi_wr_sram_drain = r_w_active && m_axi_wready;
    assign axi_wr_sram_id = r_w_channel_id;

    // W channel outputs - use ID-based SRAM interface
    assign m_axi_wvalid = r_w_active && axi_wr_sram_valid[r_w_channel_id];
    assign m_axi_wdata = axi_wr_sram_data;  // Muxed data from SRAM controller
    assign m_axi_wstrb = {(DW/8){1'b1}};  // All bytes valid
    assign m_axi_wlast = (r_w_beats_remaining == 8'd1);

    //=========================================================================
    // Completion Strobe Generation
    //=========================================================================
    // Notify scheduler when write burst completes (B response received)
    // This tells scheduler that data has been drained from SRAM and written to AXI

    logic [NC-1:0] r_done_strobe;
    logic [NC-1:0][31:0] r_beats_done;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_done_strobe <= '{default:0};
            r_beats_done <= '{default:0};
        end else begin
            // Default: clear strobe (one-cycle pulse)
            r_done_strobe <= '{default:0};

            // Pulse when B response is received (bvalid && bready)
            // This tells scheduler that write has completed and data is drained
            if (m_axi_bvalid && m_axi_bready) begin
                r_done_strobe[m_axi_bid[CW-1:0]] <= 1'b1;
                r_beats_done[m_axi_bid[CW-1:0]] <= {24'd0, cfg_axi_wr_xfer_beats};
            end
        end
    )

    assign sched_wr_done_strobe = r_done_strobe;
    assign sched_wr_beats_done = r_beats_done;

    //=========================================================================
    // B Channel → Response Handling
    //=========================================================================
    // Accept all responses (error handling can be added later)

    assign m_axi_bready = 1'b1;  // Always ready for response

    //=========================================================================
    // Debug Counters - Track AW transactions and W beats for verification
    //=========================================================================

    logic [31:0] r_aw_transactions;
    logic [31:0] r_w_beats;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_aw_transactions <= '0;
            r_w_beats <= '0;
        end else begin
            // Count AW transactions (write address handshakes)
            if (m_axi_awvalid && m_axi_awready) begin
                r_aw_transactions <= r_aw_transactions + 1'b1;
            end

            // Count W beats (write data handshakes)
            if (m_axi_wvalid && m_axi_wready) begin
                r_w_beats <= r_w_beats + 1'b1;
            end
        end
    )

    assign dbg_aw_transactions = r_aw_transactions;
    assign dbg_w_beats = r_w_beats;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    // Only one arbiter grant at a time
    assert property (@(posedge clk) disable iff (!rst_n)
        $onehot0(w_arb_grant));

    // Granted channel must have valid request
    assert property (@(posedge clk) disable iff (!rst_n)
        w_arb_grant_valid |-> (w_arb_request & w_arb_grant) != '0);

    // Allocation only when AW command issues
    assert property (@(posedge clk) disable iff (!rst_n)
        (|wr_alloc_req) |-> $past(m_axi_awvalid && m_axi_awready));

    // Channel ID must be valid
    assert property (@(posedge clk) disable iff (!rst_n)
        m_axi_awvalid |-> (r_aw_channel_id < NC));

    // W active only after AW issued
    assert property (@(posedge clk) disable iff (!rst_n)
        r_w_active |-> $past(m_axi_awvalid && m_axi_awready, 1) || $past(r_w_active, 1));
    `endif

endmodule : axi_write_engine
