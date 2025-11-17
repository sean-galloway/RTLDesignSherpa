// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_read_engine
// Purpose: Multi-Channel AXI4 Read Engine with Space-Aware Arbitration
//
// Description:
//   High-performance multi-channel AXI4 read engine with:
//   - Round-robin arbitration across channels
//   - Space-aware request masking (only arbitrate channels with sufficient SRAM space)
//   - Pre-allocation handshake with SRAM controller
//   - Streaming data path to SRAM controller
//
// Architecture:
//   1. Scheduler Interface: Each channel can request read bursts
//   2. Space Checking: Mask channels without sufficient SRAM space
//   3. Arbitration: Round-robin arbiter selects next channel to service
//   4. AXI AR Issue: Issue read command to AXI, assert rd_alloc to SRAM controller
//   5. AXI R Response: Stream read data directly to SRAM controller
//
// Key Features:
//   - Arbiter only grants to channels with sufficient SRAM space
//   - rd_alloc asserted when AXI AR command issues
//   - Channel ID encoded in AXI transaction ID for data routing
//   - No internal buffering (streaming pipeline)
//
// Performance Characteristics:
//   When ALL channels complete their work (w_arb_request == 0), the engine becomes
//   idle until new requests arrive. This is NOT a bubble - it's legitimate system idle.
//
//   Why This Matters for Testing:
//   - With few active channels (e.g., 4) and short bursts (e.g., xb2), there are brief
//     periods when all channels are in their WRITE phase, so NO channels are requesting reads
//   - During these periods, m_axi_arvalid = 0 (no R channel activity)
//   - This is EXPECTED behavior, not a performance bug
//   - The dbg_arb_request signal exposes w_arb_request to help testbenches distinguish:
//       * TRUE BUBBLE:  arvalid=0 while arb_request!=0 (channels waiting, arbiter stalled)
//       * SYSTEM IDLE:  arvalid=0 while arb_request==0 (no channels need service)
//
//   With more channels or longer bursts, this idle period is hidden because there's
//   always at least one channel in READ phase. But with minimal configs, the idle
//   periods become visible and must be filtered from bubble detection.
//
// Documentation: projects/components/stream/PRD.md
// Subsystem: stream_fub
//
// Author: sean galloway
// Created: 2025-10-29

`timescale 1ns / 1ps

// Import common STREAM and monitor packages
`include "stream_imports.svh"
`include "reset_defs.svh"


module axi_read_engine #(
    // Primary parameters (long names for external configuration)
    parameter int NUM_CHANNELS = 8,                 // Number of channels
    parameter int ADDR_WIDTH = 64,                  // AXI address width
    parameter int DATA_WIDTH = 512,                 // AXI data width
    parameter int ID_WIDTH = 8,                     // AXI ID width
    parameter int SEG_COUNT_WIDTH = 8,              // Width of space/count signals (typically $clog2(SRAM_DEPTH)+1)
    parameter int PIPELINE = 0,                     // 1: allow multiple outstanding requests per channel (pipelined)
                                                    // 0: wait for all data before next request per channel (non-pipelined)
    parameter int AR_MAX_OUTSTANDING = 8,           // Maximum outstanding AR requests per channel (PIPELINE=1 only)
    parameter int STROBE_EVERY_BEAT = 0,            // 0: strobe only on last beat (default)
                                                    // 1: strobe on every beat written to SRAM

    // Short aliases (for internal use)
    parameter int NC = NUM_CHANNELS,
    parameter int AW = ADDR_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int IW = ID_WIDTH,
    parameter int SCW = SEG_COUNT_WIDTH,            // Segment count width (matches sram_controller naming)
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1   // Channel ID width (min 1 bit)
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // Configuration Interface
    //=========================================================================
    input  logic [7:0]                  cfg_axi_rd_xfer_beats,  // Transfer size in beats (applies to all channels)

    //=========================================================================
    // Scheduler Interface (Per-Channel Read Requests)
    //=========================================================================
    input  logic [NC-1:0]               sched_rd_valid,      // Channel requests read
    output logic [NC-1:0]               sched_rd_ready,      // Engine ready for channel
    input  logic [NC-1:0][AW-1:0]       sched_rd_addr,       // Source addresses
    input  logic [NC-1:0][31:0]         sched_rd_beats,      // Beats remaining to read

    //=========================================================================
    // AXI4 AR Channel (Read Address)
    //=========================================================================
    output logic [IW-1:0]               m_axi_arid,
    output logic [AW-1:0]               m_axi_araddr,
    output logic [7:0]                  m_axi_arlen,         // Burst length - 1
    output logic [2:0]                  m_axi_arsize,        // Burst size (log2(bytes))
    output logic [1:0]                  m_axi_arburst,       // Burst type (INCR)
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,

    //=========================================================================
    // AXI4 R Channel (Read Data)
    //=========================================================================
    input  logic [IW-1:0]               m_axi_rid,
    input  logic [DW-1:0]               m_axi_rdata,
    input  logic [1:0]                  m_axi_rresp,
    input  logic                        m_axi_rlast,
    input  logic                        m_axi_rvalid,
    output logic                        m_axi_rready,

    //=========================================================================
    // SRAM Allocation Interface (to SRAM Controller)
    //=========================================================================
    // Pre-allocation interface (before data arrives)
    output logic                        rd_alloc_req,        // Channel requests space
    output logic [7:0]                  rd_alloc_size,       // Beats to reserve
    output logic [IW-1:0]               rd_alloc_id,         // Transaction ID → channel
    input  logic [NC-1:0][SCW-1:0]      rd_space_free,       // Free space count (beats available)

    //=========================================================================
    // SRAM Write Interface (to SRAM Controller)
    //=========================================================================
    // Data arriving from AXI read transactions
    output logic                        axi_rd_sram_valid,   // Read data valid
    input  logic                        axi_rd_sram_ready,   // Ready to accept data
    output logic [IW-1:0]               axi_rd_sram_id,      // Transaction ID → channel
    output logic [DW-1:0]               axi_rd_sram_data,    // Read data payload

    //=========================================================================
    // Completion Interface (to Schedulers)
    //=========================================================================
    // Notify schedulers when read burst completes
    output logic [NC-1:0]               sched_rd_done_strobe,  // Burst completed (pulsed for 1 cycle)
    output logic [NC-1:0][31:0]         sched_rd_beats_done,   // Number of beats completed in burst
    output logic [NC-1:0]               axi_rd_all_complete,   // All reads complete (no outstanding txns)

    //=========================================================================
    // Debug Interface (for verification/debug only)
    //=========================================================================
    output logic [31:0]                 dbg_r_beats_rcvd,    // Total R beats received from AXI
    output logic [31:0]                 dbg_sram_writes,     // Total writes to SRAM controller
    output logic [NC-1:0]               dbg_arb_request      // Arbiter request vector (for bubble filtering)
);

    //=========================================================================
    // Local Parameters
    //=========================================================================

    localparam int CW = (NC > 1) ? $clog2(NC) : 1;  // Minimum 1 bit for single channel
    localparam int BYTES_PER_BEAT = DW / 8;
    localparam int AXSIZE = $clog2(BYTES_PER_BEAT);
    localparam int MOW = $clog2(AR_MAX_OUTSTANDING + 1);  // Max Outstanding Width (bits needed for 0..AR_MAX_OUTSTANDING)

    //=========================================================================
    // Outstanding Transaction Tracking
    //=========================================================================
    // Track outstanding read transactions per channel
    // PIPELINE=0: Binary flag (0 or 1 outstanding)
    // PIPELINE=1: Counter (0 to AR_MAX_OUTSTANDING)

    logic [NC-1:0] r_outstanding_limit;              // 1 = channel at or exceeds max outstanding
    logic [NC-1:0][MOW-1:0] r_outstanding_count;   // Outstanding AR count per channel (PIPELINE=1 only)

    //=========================================================================
    // Beats Issued Tracking
    //=========================================================================
    // Track how many beats have been issued (AR transactions) vs. requested
    // This prevents issuing more ARs than the scheduler needs

    logic [NC-1:0][31:0] r_beats_issued;  // Beats issued per channel (cumulative)

    generate
        if (PIPELINE == 0) begin : gen_no_pipeline_tracking
            // Per-channel outstanding transaction tracking (non-pipelined mode)
            // Binary: 0 = no outstanding, 1 = has outstanding
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_outstanding_limit <= '0;
                end else begin
                    for (int i = 0; i < NC; i++) begin
                        // Set outstanding when AR issues for this channel
                        if (m_axi_arvalid && m_axi_arready && (w_arb_grant_id == i[CW-1:0])) begin
                            r_outstanding_limit[i] <= 1'b1;
                        end
                        // Clear outstanding when R last arrives for this channel
                        // FIX: Changed from else-if to independent if to handle same-cycle AR/R
                        if (m_axi_rvalid && m_axi_rready && m_axi_rlast &&
                                    (m_axi_rid[CW-1:0] == i[CW-1:0])) begin
                            r_outstanding_limit[i] <= 1'b0;
                        end
                    end
                end
            )
            // Counter not used in PIPELINE=0 mode
            assign r_outstanding_count = '0;

        end else begin : gen_pipeline_tracking
            // Per-channel counter (0 to AR_MAX_OUTSTANDING)
            logic [NC-1:0] w_incr, w_decr;  // Increment/decrement signals

            // Determine which channels increment/decrement
            always_comb begin
                for (int i = 0; i < NC; i++) begin
                    w_incr[i] = m_axi_arvalid && m_axi_arready && (w_arb_grant_id == i[CW-1:0]);
                    w_decr[i] = m_axi_rvalid && m_axi_rready && m_axi_rlast && (m_axi_rid[CW-1:0] == i[CW-1:0]);
                end
            end

            // Update counters
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_outstanding_count <= '0;
                end else begin
                    for (int i = 0; i < NC; i++) begin
                        case ({w_incr[i], w_decr[i]})
                            2'b10: r_outstanding_count[i] <= r_outstanding_count[i] + 1'b1;  // AR only
                            2'b01: r_outstanding_count[i] <= r_outstanding_count[i] - 1'b1;  // R last only
                            default: r_outstanding_count[i] <= r_outstanding_count[i];       // Both or neither
                        endcase
                    end
                end
            )

            // Boolean flag = at or exceeds limit (prevents new AR when maxed)
            always_comb begin
                for (int i = 0; i < NC; i++) begin
                    r_outstanding_limit[i] = (r_outstanding_count[i] >= $bits(r_outstanding_count[i])'(AR_MAX_OUTSTANDING));
                end
            end
        end
    endgenerate

    // Completion signal: sticky - stays high until new transfer starts
    // This prevents false pulses when outstanding_count temporarily hits 0 between bursts
    logic [NC-1:0] r_all_complete;
    logic [NC-1:0] r_all_complete_prev;  // Previous cycle value for edge detection

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_all_complete <= '1;  // Start as complete
            r_all_complete_prev <= '1;
        end else begin
            r_all_complete_prev <= r_all_complete;

            for (int i = 0; i < NC; i++) begin
                // Set complete when outstanding transactions reach zero
                if (r_outstanding_count[i] == '0) begin
                    r_all_complete[i] <= 1'b1;
                // Clear complete when transitioning from complete to having outstanding txns
                // This happens when first AR of new descriptor issues (count goes from 0 to non-zero)
                end else if (r_all_complete_prev[i] && (r_outstanding_count[i] != '0)) begin
                    r_all_complete[i] <= 1'b0;
                end
            end
        end
    )

    assign axi_rd_all_complete = r_all_complete;

    // Track beats issued: increment when AR issues, reset when sched_rd_valid de-asserts
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_beats_issued <= '{default:0};
        end else begin
            for (int i = 0; i < NC; i++) begin
                // Reset issued counter when scheduler de-asserts valid (new descriptor or transfer complete)
                if (!sched_rd_valid[i]) begin
                    r_beats_issued[i] <= 32'h0;
                // Increment when AR transaction issues for this channel
                end else if (m_axi_arvalid && m_axi_arready && (w_arb_grant_id == i[CW-1:0])) begin
                    r_beats_issued[i] <= r_beats_issued[i] + {24'h0, cfg_axi_rd_xfer_beats};
                end
            end
        end
    )

    //=========================================================================
    // Space-Aware Request Masking
    //=========================================================================
    // Only allow arbitration for channels with sufficient SRAM space
    // and (if PIPELINE=0) no outstanding transactions
    // and haven't issued more beats than requested

    logic [NC-1:0] w_space_ok;                  // Channel has enough space for burst
    logic [NC-1:0] w_below_outstanding_limit;   // Channel below max outstanding limit (can issue new AR)
    logic [NC-1:0] w_beats_ok;                  // Haven't issued more than requested
    logic [NC-1:0] w_arb_request;               // Masked requests to arbiter

    always_comb begin
        for (int i = 0; i < NC; i++) begin
            // Check if channel has enough space for configured burst size
            // FIX: Use SCW for both operands (was hardcoded 8, truncated for depths > 128)
            // FIX: Require 2x burst size margin to account for in-flight allocation timing
            w_space_ok[i] = (SCW'(rd_space_free[i]) >= SCW'(cfg_axi_rd_xfer_beats << 1));

            // Check outstanding constraint
            // PIPELINE=0: !r_outstanding_limit means no outstanding transaction (can issue)
            // PIPELINE=1: !r_outstanding_limit means below max outstanding (can issue more)
            w_below_outstanding_limit[i] = !r_outstanding_limit[i];

            // Check if next burst fits in remaining beats
            // Note: sched_rd_beats is REMAINING beats (decrements as engine completes bursts)
            // We only need to check if the next burst fits, not cumulative issued
            w_beats_ok[i] = ({24'h0, cfg_axi_rd_xfer_beats}) <= sched_rd_beats[i];

            // Only request arbitration if:
            // 1. Scheduler is requesting (sched_rd_valid)
            // 2. Sufficient SRAM space available (w_space_ok)
            // 3. Below outstanding limit (w_below_outstanding_limit)
            // 4. Haven't issued enough beats yet (w_beats_ok)
            w_arb_request[i] = sched_rd_valid[i] && w_space_ok[i] && w_below_outstanding_limit[i] && w_beats_ok[i];
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
            // ACK signal must still be driven for AR channel management
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
    // AR Channel Management - COMBINATIONAL (no flops for immediate response)
    //=========================================================================
    // FIX: Drive AR outputs combinationally from arbiter to avoid 1-cycle delay
    // When rd_space_free goes to 0, arvalid must drop in the same cycle

    // AXI AR outputs - COMBINATIONAL
    assign m_axi_arvalid = w_arb_grant_valid;
    assign m_axi_arid = {{(IW-CW){1'b0}}, w_arb_grant_id};  // Channel ID in lower bits
    assign m_axi_araddr = sched_rd_addr[w_arb_grant_id] + (AW'(r_beats_issued[w_arb_grant_id]) << AXSIZE);
    assign m_axi_arlen = cfg_axi_rd_xfer_beats - 8'd1;  // AXI uses len-1 (configured burst size)
    assign m_axi_arsize = 3'(AXSIZE);
    assign m_axi_arburst = 2'b01;  // INCR

    // Acknowledge arbiter grant when AXI accepts AR command
    assign w_arb_grant_ack = w_arb_grant & {NC{(m_axi_arvalid && m_axi_arready)}};

    //=========================================================================
    // SRAM Pre-Allocation
    //=========================================================================
    // Assert rd_alloc when AXI AR command is issued

    logic          r_alloc_req;
    logic [7:0]    r_alloc_size;
    logic [IW-1:0] r_alloc_id;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_alloc_req <= 1'b0;
            r_alloc_size <= '0;
            r_alloc_id <= '0;
        end else begin
            // Default: clear allocation request after 1 cycle
            r_alloc_req <= 1'b0;

            // Assert allocation when AXI AR command issues
            if (m_axi_arvalid && m_axi_arready) begin
                r_alloc_req <= 1'b1;
                r_alloc_size <= cfg_axi_rd_xfer_beats;  // Configured burst size
                r_alloc_id <= {{(IW-CW){1'b0}}, w_arb_grant_id};  // Channel ID from arbiter
            end
        end
    )

    assign rd_alloc_req = r_alloc_req;
    assign rd_alloc_size = r_alloc_size;
    assign rd_alloc_id = r_alloc_id;

    //=========================================================================
    // Scheduler Ready Signals
    //=========================================================================
    // Ready when granted and AR command accepted

    logic [NC-1:0] r_sched_ready;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_sched_ready <= '0;
        end else begin
            // Default: clear ready
            r_sched_ready <= '0;

            // Assert ready when command accepted
            if (m_axi_arvalid && m_axi_arready) begin
                r_sched_ready[w_arb_grant_id] <= 1'b1;
            end
        end
    )

    assign sched_rd_ready = r_sched_ready;

    //=========================================================================
    // AXI R Channel → SRAM Controller
    //=========================================================================
    // Direct passthrough (no buffering)

    assign axi_rd_sram_valid = m_axi_rvalid;
    assign axi_rd_sram_id = m_axi_rid;
    assign axi_rd_sram_data = m_axi_rdata;
    assign m_axi_rready = axi_rd_sram_ready;

    //=========================================================================
    // Completion Strobe Generation
    //=========================================================================
    // Two modes controlled by STROBE_EVERY_BEAT parameter:
    //   Mode 0 (default): Strobe only on last beat, report full burst size
    //   Mode 1: Strobe every beat, report 1 beat each time

    // Per-channel tracking: beats in current outstanding burst
    logic [NC-1:0][7:0] r_burst_beats;  // Beats expected in current burst (arlen + 1)

    // Capture burst size when AR issues
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_burst_beats <= '{default:0};
        end else begin
            for (int i = 0; i < NC; i++) begin
                // Start of new burst: capture beat count
                if (m_axi_arvalid && m_axi_arready && (w_arb_grant_id == i[CW-1:0])) begin
                    r_burst_beats[i] <= cfg_axi_rd_xfer_beats;  // Configured burst size
                end
            end
        end
    )

    // Generate completion strobes - REGISTERED but based on AR handshake
    // FIX: Scheduler needs to know when AR transaction is accepted (not R completion)
    // Register to break combinational loop, but pulse immediately on AR handshake
    logic [NC-1:0] r_done_strobe;
    logic [NC-1:0][31:0] r_beats_done;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_done_strobe <= '{default:0};
            r_beats_done <= '{default:0};
        end else begin
            // Default: clear strobe (one-cycle pulse)
            r_done_strobe <= '{default:0};

            // Pulse when AR transaction is accepted (arvalid && arready)
            // This tells scheduler that request was issued to AXI bus
            if (m_axi_arvalid && m_axi_arready) begin
                r_done_strobe[w_arb_grant_id] <= 1'b1;
                r_beats_done[w_arb_grant_id] <= {24'd0, cfg_axi_rd_xfer_beats};
            end
        end
    )

    assign sched_rd_done_strobe = r_done_strobe;
    assign sched_rd_beats_done = r_beats_done;

    //=========================================================================
    // Debug Counters
    //=========================================================================
    // Track R beats received and SRAM writes for debug visibility

    logic [31:0] r_r_beats_rcvd;
    logic [31:0] r_sram_writes;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_r_beats_rcvd <= '0;
            r_sram_writes <= '0;
        end else begin
            // Count R beats received from AXI
            if (m_axi_rvalid && m_axi_rready) begin
                r_r_beats_rcvd <= r_r_beats_rcvd + 1'b1;
            end

            // Count successful SRAM writes
            if (axi_rd_sram_valid && axi_rd_sram_ready) begin
                r_sram_writes <= r_sram_writes + 1'b1;
            end
        end
    )

    assign dbg_r_beats_rcvd = r_r_beats_rcvd;
    assign dbg_sram_writes = r_sram_writes;

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

    // Allocation only when AR command issues
    assert property (@(posedge clk) disable iff (!rst_n)
        rd_alloc_req |-> $past(m_axi_arvalid && m_axi_arready));

    // Channel ID must be valid
    assert property (@(posedge clk) disable iff (!rst_n)
        m_axi_arvalid |-> (w_arb_grant_id < NC));
    `endif

    //=========================================================================
    // Debug Signal Assignments
    //=========================================================================
    // Expose arbiter request vector for testbench bubble filtering
    // When w_arb_request == 0, all channels are idle (not a bubble!)
    assign dbg_arb_request = w_arb_request;

endmodule : axi_read_engine
