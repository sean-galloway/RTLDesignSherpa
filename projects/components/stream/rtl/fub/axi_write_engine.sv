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
//   2. Data Checking: Mask channels without sufficient SRAM data available
//   3. Arbitration: Round-robin arbiter selects next channel to service
//   4. AXI AW Issue: Issue write command to AXI, assert wr_drain to reserve data
//   5. AXI W Stream: Stream write data from SRAM controller
//   6. AXI B Response: Handle write response, complete transaction
//
// Key Features:
//   - Arbiter only grants to channels with sufficient SRAM data
//   - wr_drain_req asserted when AXI AW command issues (reserves data)
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
    parameter int USER_WIDTH = 8,                   // AXI USER width (for channel tracking)
    parameter int SEG_COUNT_WIDTH = 8,              // Width of space/count signals (typically $clog2(SRAM_DEPTH)+1)
    parameter int PIPELINE = 0,                     // 0: wait for all data before next request per channel
                                                    // 1: allow multiple outstanding requests per channel
    parameter int AW_MAX_OUTSTANDING = 8,           // Maximum outstanding AW requests per channel (PIPELINE=1 only)
    parameter int W_PHASE_FIFO_DEPTH = 64,          // W-phase transaction FIFO depth (in-order with AW)
    parameter int B_PHASE_FIFO_DEPTH = 16,          // B-phase transaction FIFO depth (out-of-order responses)

    // Short aliases (for internal use)
    parameter int NC = NUM_CHANNELS,
    parameter int AW = ADDR_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int IW = ID_WIDTH,
    parameter int UW = USER_WIDTH,
    parameter int SCW = SEG_COUNT_WIDTH,            // Segment count width (matches sram_controller naming)
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1   // Channel ID width (min 1 bit)
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
    // Completion Interface (to Schedulers)
    //=========================================================================
    // Notify schedulers when write burst completes
    output logic [NC-1:0]               sched_wr_done_strobe,  // Burst completed (pulsed for 1 cycle)
    output logic [NC-1:0][31:0]         sched_wr_beats_done,   // Number of beats completed in burst

    //=========================================================================
    // SRAM Drain Interface (to SRAM Controller)
    //=========================================================================
    // Drain interface (reserves data before AW command)
    output logic [NC-1:0]               axi_wr_drain_req,        // Channel requests to reserve data
    output logic [NC-1:0][7:0]          axi_wr_drain_size,       // Beats to reserve
    input  logic [NC-1:0][SCW-1:0]      axi_wr_drain_data_avail, // Data available after reservations

    //=========================================================================
    // SRAM Read Interface (from SRAM Controller)
    // ID-based interface matching sram_controller output
    //=========================================================================
    input  logic [NC-1:0]               axi_wr_sram_valid,      // Per-channel valid (registered, for arbitration)
    input  logic [NC-1:0]               axi_wr_sram_valid_comb, // Per-channel valid (combinational, for m_axi_wvalid gate)
    output logic                        axi_wr_sram_drain,   // Drain request (consumer ready)
    output logic [CIW-1:0]              axi_wr_sram_id,      // Channel ID select for drain
    input  logic [DW-1:0]               axi_wr_sram_data,    // Data from selected channel (muxed)

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
    output logic [UW-1:0]               m_axi_wuser,     // Channel ID for transaction tracking
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
    // Error Signals (to Scheduler)
    //=========================================================================
    output logic [NC-1:0]               sched_wr_error,        // Sticky error flag per channel (bad B response)

    //=========================================================================
    // Debug Interface (for verification/debug only)
    //=========================================================================
    output logic [NC-1:0]               dbg_wr_all_complete,   // All writes complete (no outstanding txns)
    output logic [31:0]                 dbg_aw_transactions,   // Total AW transactions issued
    output logic [31:0]                 dbg_w_beats,           // Total W beats written to AXI

    // Sideband for per-channel bus instrumentation (axi_bus_meter).
    // o_active_channel_id holds the channel index whose burst is currently
    // driving (or about to drive) the W bus. o_active_channel_valid is
    // high during a W burst (between the W-phase FSM accepting a txn and
    // completing it). When low, W bus activity is not attributable to any
    // channel and per-channel counters should not be incremented.
    output logic [CIW-1:0]              o_active_channel_id,
    output logic                        o_active_channel_valid
);

    //=========================================================================
    // Local Parameters
    //=========================================================================

    localparam int BYTES_PER_BEAT = DW / 8;
    localparam int AXSIZE = $clog2(BYTES_PER_BEAT);
    localparam int MOW = $clog2(AW_MAX_OUTSTANDING + 1);  // Max Outstanding Width (bits needed for 0..AW_MAX_OUTSTANDING)

    //=========================================================================
    // Forward Declarations (signals/typedefs used in always blocks below
    // before their natural definition site - hoisted to satisfy declaration-
    // before-use checks)
    //=========================================================================

    // AW channel registers (driven by AW Channel Management block below)
    logic [7:0]      r_aw_len;
    logic [CIW-1:0]  r_aw_channel_id;
    logic            r_aw_valid;

    // Beats-written counter per channel (driven by always_ff after this block)
    logic [NC-1:0][31:0] r_beats_written;

    // W-phase transaction FIFO (in-order with AW, single shared FIFO)
    typedef struct packed {
        logic [7:0]     beats;       // Number of beats for this W transaction
        logic [CIW-1:0] channel_id;  // Channel ID for this transaction
    } w_phase_txn_t;

    logic            w_phase_txn_fifo_wr;
    logic            w_phase_txn_fifo_rd;
    w_phase_txn_t    w_phase_txn_fifo_din;
    w_phase_txn_t    w_phase_txn_fifo_dout;
    logic            w_phase_txn_fifo_empty;
    logic            w_phase_txn_fifo_full;
    logic            w_phase_txn_fifo_wr_ready;
    logic            w_phase_txn_fifo_rd_valid;

    // B-phase transaction FIFOs (per-channel, out-of-order responses)
    typedef struct packed {
        logic [7:0]  beats;     // Number of beats in this transaction
        logic        last;      // Is this the last transfer for descriptor?
    } b_phase_txn_t;

    logic [NC-1:0]           b_phase_txn_fifo_wr;
    logic [NC-1:0]           b_phase_txn_fifo_rd;
    b_phase_txn_t [NC-1:0]   b_phase_txn_fifo_din;
    b_phase_txn_t [NC-1:0]   b_phase_txn_fifo_dout;
    logic [NC-1:0]           b_phase_txn_fifo_empty;
    logic [NC-1:0]           b_phase_txn_fifo_full;

    //=========================================================================
    // Outstanding Transaction Tracking
    //=========================================================================
    // PIPELINE=0: Boolean flag per channel (0 or 1 transaction)
    // PIPELINE=1: Counter per channel (0 to MAX_OUTSTANDING)

    logic [NC-1:0] r_outstanding_limit;             // Boolean: channel at/exceeds limit
    logic [NC-1:0][MOW-1:0] r_outstanding_count;  // PIPELINE=1: Counter (0 to AW_MAX_OUTSTANDING)

    generate
        if (PIPELINE == 0) begin : gen_no_pipeline_tracking
            // Per-channel boolean flag (0 or 1 outstanding)
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_outstanding_limit <= '0;
                end else begin
                    for (int i = 0; i < NC; i++) begin
                        // Set outstanding when AW issues for this channel
                        if (m_axi_awvalid && m_axi_awready && (r_aw_channel_id == i[CIW-1:0])) begin
                            r_outstanding_limit[i] <= 1'b1;
                        end
                        // Clear outstanding when B response arrives for this channel
                        // FIX: Changed from else-if to independent if to handle same-cycle AW/B
                        if (m_axi_bvalid && m_axi_bready &&
                                (m_axi_bid[CIW-1:0] == i[CIW-1:0])) begin
                            r_outstanding_limit[i] <= 1'b0;
                        end
                    end
                end
            )
            // Counter not used in PIPELINE=0 mode
            assign r_outstanding_count = '0;

        end else begin : gen_pipeline_tracking
            // Per-channel counter (0 to AW_MAX_OUTSTANDING)
            logic [NC-1:0] w_incr, w_decr;  // Increment/decrement signals

            // Determine which channels increment/decrement
            always_comb begin
                for (int i = 0; i < NC; i++) begin
                    w_incr[i] = m_axi_awvalid && m_axi_awready && (r_aw_channel_id == i[CIW-1:0]);
                    w_decr[i] = m_axi_bvalid && m_axi_bready && (m_axi_bid[CIW-1:0] == i[CIW-1:0]);
                end
            end

            // Update counters
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_outstanding_count <= '0;
                end else begin
                    for (int i = 0; i < NC; i++) begin
                        case ({w_incr[i], w_decr[i]})
                            2'b10: r_outstanding_count[i] <= r_outstanding_count[i] + 1'b1;  // AW only
                            2'b01: r_outstanding_count[i] <= r_outstanding_count[i] - 1'b1;  // B only
                            default: r_outstanding_count[i] <= r_outstanding_count[i];       // Both or neither
                        endcase
                    end
                end
            )

            // Boolean flag = at or exceeds limit (prevents new AW when maxed)
            always_comb begin
                for (int i = 0; i < NC; i++) begin
                    r_outstanding_limit[i] = (r_outstanding_count[i] >= $bits(r_outstanding_count[i])'(AW_MAX_OUTSTANDING));
                end
            end
        end
    endgenerate

    // Completion signal: sticky - stays high until new transfer starts
    // This prevents false pulses when outstanding_count temporarily hits 0 between bursts
    logic [NC-1:0] r_all_complete;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_all_complete <= '1;  // Start as complete
        end else begin
            for (int i = 0; i < NC; i++) begin
                // Set complete when outstanding transactions reach zero
                if (r_outstanding_count[i] == '0) begin
                    r_all_complete[i] <= 1'b1;
                end
                // Clear complete when new transfer starts
                if (sched_wr_valid[i] && r_beats_written[i] == '0) begin
                    r_all_complete[i] <= 1'b0;
                end
            end
        end
    )

    assign dbg_wr_all_complete = r_all_complete;

    //=========================================================================
    // Beats Written Tracking (for completion detection)
    //=========================================================================
    // Track how many beats have been written (B responses received)
    // Note: Address tracking moved to scheduler, r_beats_issued removed
    // (r_beats_written declared in forward-declarations block above)

    // Track beats written: increment when B response arrives, reset when sched_wr_valid de-asserts
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_beats_written <= '{default:0};
        end else begin
            for (int i = 0; i < NC; i++) begin
                // Reset written counter when scheduler de-asserts valid (new descriptor or transfer complete)
                if (!sched_wr_valid[i]) begin
                    r_beats_written[i] <= 32'h0;
                // Increment when B response arrives for this channel (use actual transfer size from FIFO)
                end else if (m_axi_bvalid && m_axi_bready && (m_axi_bid[CIW-1:0] == i[CIW-1:0])) begin
                    r_beats_written[i] <= r_beats_written[i] + {24'h0, b_phase_txn_fifo_dout[i].beats};
                end
            end
        end
    )

    //=========================================================================
    // Data-Aware Request Masking
    //=========================================================================
    // Only allow arbitration for channels with sufficient SRAM data
    // and (if PIPELINE=0) no outstanding transactions
    //
    // For PERFORMANCE: Always burst the full configured amount (cfg_axi_wr_xfer_beats)
    // Only allow partial bursts on the final burst of a descriptor
    //
    // TODO: Decouple drain activity from sched_wr_valid.
    //   Today, when sched_wr_valid drops (e.g. scheduler enters CH_ERROR after
    //   a timeout, or any upstream abort), every gating signal collapses to 0
    //   in the else-branch below and the engine quits — even if the SRAM,
    //   bridge, and W-side FIFOs still hold beats that were already accounted
    //   for as "to do". Those beats become permanently stranded.
    //
    //   Desired behavior: if sched_wr_valid drops while there are still beats
    //   left in this channel's drain path (SRAM occupancy + bridge_occupancy +
    //   any in-flight AW/W FIFO entries), the engine should:
    //     1. Continue draining residual data via partial-burst issuance until
    //        the drain path is empty,
    //     2. Wait for all outstanding B responses to come back,
    //     3. Then return to a clean idle state with all per-channel state
    //        reset (sched_wr_beats, r_outstanding_limit, b_phase FIFO, etc.).
    //   This makes the engine resilient to upstream errors and keeps SRAM
    //   from holding stale beats across descriptors.

    logic [NC-1:0]      w_has_data;           // Channel has enough data for burst
    logic [NC-1:0]      w_data_ok;            // Channel has enough data for burst
    logic [NC-1:0]      w_no_outstanding;     // Channel has no outstanding transaction (or pipeline allowed)
    logic [NC-1:0]      w_arb_request;        // Masked requests to arbiter
    logic [NC-1:0][7:0] w_transfer_size;      // Masked requests to arbiter
    logic [NC-1:0]      w_final_burst;        // Final burst

    //=========================================================================
    // In-flight drain-request pipeline (closes the stale-data_avail race)
    //=========================================================================
    // axi_wr_drain_data_avail is registered twice on the way out of
    // sram_controller (once inside sram_controller_unit, once at the
    // wrapper boundary) for 100 MHz timing closure. That means the wr
    // engine sees a 2-cycle-stale view: drain_reqs fired at cycles
    // T-1 and T are NOT yet reflected in axi_wr_drain_data_avail(T).
    //
    // If the engine relied on the raw stale view, it could fire an AW
    // (and a drain_req) for a channel whose actual drain_ctrl count is
    // already exhausted by an in-flight prior drain_req for the same
    // channel. drain_ctrl silently drops the second drain_req's rd_ptr
    // advance (rd_empty=1 → advance gated off in stream_drain_ctrl).
    // The wr engine then commits a phantom burst -- pre-fix it leaked
    // bogus W beats onto the AXI bus; post-fix it just stalls forever.
    //
    // Fix: track per-channel drain_req sizes for the last 2 cycles
    // (the exact width of the staleness window). Subtract those from
    // the registered view so the arbitration check sees the "true"
    // count that drain_ctrl will reach by the time our drain_req lands.
    logic [NC-1:0][SCW-1:0] w_drain_t;          // drain_req size firing THIS cycle
    logic [NC-1:0][SCW-1:0] r_drain_tminus1;    // drain_req size that fired LAST cycle
    logic [NC-1:0][SCW-1:0] w_pending_drain;    // sum of in-flight (not yet in registered view)
    logic [NC-1:0][SCW-1:0] w_effective_avail;  // registered avail minus in-flight

    always_comb begin
        w_drain_t = '{default:0};
        if (m_axi_awvalid && m_axi_awready) begin
            w_drain_t[r_aw_channel_id] = SCW'(m_axi_awlen) + SCW'(1);
        end
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_drain_tminus1 <= '{default:0};
        end else begin
            r_drain_tminus1 <= w_drain_t;
        end
    )

    always_comb begin
        for (int i = 0; i < NC; i++) begin
            w_pending_drain[i] = r_drain_tminus1[i] + w_drain_t[i];
            w_effective_avail[i] = (axi_wr_drain_data_avail[i] >= w_pending_drain[i])
                                    ? (axi_wr_drain_data_avail[i] - w_pending_drain[i])
                                    : '0;
        end
    end

    always_comb begin
        for (int i = 0; i < NC; i++) begin

            // Only check data availability if scheduler is requesting
            // This prevents issues with uninitialized/inactive channels
            if (sched_wr_valid[i]) begin
                // Find the amount to transfer now (cast to 8-bit for AXI burst length)
                // sched_wr_beats uses 0==0 encoding, cfg_axi_wr_xfer_beats stores ARLEN (0==1 beat)
                w_transfer_size[i] = 8'((sched_wr_beats[i] <= (32'(cfg_axi_wr_xfer_beats) + 32'd1)) ?
                            (sched_wr_beats[i] - 32'd1) : 32'(cfg_axi_wr_xfer_beats));
                // Check if channel has enough data for configured burst size.
                // Use w_effective_avail (= registered avail minus drain_reqs
                // still in flight) so the stale-view race against drain_ctrl
                // can't trigger a phantom burst.
                w_has_data[i] = (SCW'(w_effective_avail[i]) >= SCW'(w_transfer_size[i] + 8'd1));

                // OR if this is the final burst (remaining beats < burst size AND all data available)
                w_final_burst[i] = (sched_wr_beats[i] > 0) &&
                                    (sched_wr_beats[i] <= (32'(cfg_axi_wr_xfer_beats) + 32'd1)) &&
                                    (SCW'(w_effective_avail[i]) >= SCW'(sched_wr_beats[i]));

                w_data_ok[i] = w_has_data[i] || w_final_burst[i];
            end else begin
                // Channel not requesting - don't check data availability
                w_has_data[i] = 1'b0;
                w_transfer_size[i] = 'b0;
                w_final_burst[i] = 1'b0;
                w_data_ok[i] = 1'b0;
            end

            // Check outstanding constraint
            // PIPELINE=0: Block if any outstanding transaction
            // PIPELINE=1: Block if at or exceeds AW_MAX_OUTSTANDING
            w_no_outstanding[i] = !r_outstanding_limit[i];

            // Only request arbitration if:
            // 1. Scheduler is requesting (sched_wr_valid)
            // 2. Sufficient SRAM data available (w_data_ok) - accounting for bridge latency
            // 3. Outstanding count below limit (w_no_outstanding)
            w_arb_request[i] = sched_wr_valid[i] && w_data_ok[i] && w_no_outstanding[i];
        end
    end

    //=========================================================================
    // Arbiter Request Pipeline
    //=========================================================================
    // Register w_arb_request -> r_arb_request to break the long timing cone
    // from r_write_beats_remaining (scheduler) and axi_wr_drain_data_avail
    // (sram_controller) through the 32-bit comparators in w_data_ok into the
    // arbiter priority encoder and out to grant_reg. Closes 100 MHz timing on
    // the Nexys A7-100T (-1 part) at 8 channels; the unpipelined cone was
    // ~16 levels of logic.
    //
    // Steady-state cost: 0. While sched_wr_valid stays high (the descriptor
    // is actively transferring), r_arb_request tracks w_arb_request 1 cycle
    // later -- the engine still pipelines AWs at the same rate and the
    // arbiter still grants every cycle. Only the descriptor START sees an
    // extra 1-cycle latency for the first AW.
    //
    // End-of-descriptor safety: when live sched_wr_valid drops, r_arb_request
    // stays high for 1 stale cycle. Two complementary guards prevent that
    // stale grant from being acted on:
    //   1. AW-issue block below ANDs with live sched_wr_valid[w_arb_grant_id]
    //      so no AW is captured for a channel that's no longer requesting.
    //   2. w_arb_grant_ack auto-releases the arbiter when the grant is stale
    //      (live valid = 0) so arbitration advances without waiting for an
    //      AW handshake that will never come.
    logic [NC-1:0] r_arb_request;
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_arb_request <= '0;
        end else begin
            r_arb_request <= w_arb_request;
        end
    )

    //=========================================================================
    // Round-Robin Arbiter (or Direct Grant for Single Channel)
    //=========================================================================

    logic              w_arb_grant_valid;
    logic [NC-1:0]     w_arb_grant;
    logic [CIW-1:0]    w_arb_grant_id;
    logic [NC-1:0]     w_arb_grant_ack;

    generate
        if (NC == 1) begin : gen_single_channel
            // Single channel: no round-robin needed, but the datapath relies on
            // the arbiter's registered, ack-held grant timing for correct burst
            // sequencing. Use the single-client equivalent (req/grant + hold for
            // ack) -- a plain combinational passthrough injects a bubble beat at
            // every burst boundary (see arbiter_single_client header).
            arbiter_single_client #(
                .WAIT_GNT_ACK (1)
            ) u_arbiter_single (
                .clk          (clk),
                .rst_n        (rst_n),
                .block_arb    (1'b0),
                .request      (r_arb_request[0]),
                .grant_ack    (w_arb_grant_ack[0]),
                .grant_valid  (w_arb_grant_valid),
                .grant        (w_arb_grant[0]),
                .grant_id     (w_arb_grant_id[0])
            );
        end else begin : gen_multi_channel
            // Multiple channels - use round-robin arbiter
            arbiter_round_robin #(
                .CLIENTS      (NC),
                .WAIT_GNT_ACK (1)              // Use ACK mode (wait for command acceptance)
            ) u_arbiter (
                .clk          (clk),
                .rst_n        (rst_n),
                .block_arb    (1'b0),          // Never block arbitration
                .request      (r_arb_request),
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
    // (r_aw_len, r_aw_channel_id, r_aw_valid declared in forward-declarations
    // block at the top of the module)

    // Acknowledge arbiter grant when AXI accepts AW command, OR when the
    // grant is stale (live sched_wr_valid dropped after the registered
    // r_arb_request was captured). Stale-release prevents the arbiter from
    // stalling on a channel that will never see its AW issued, since the
    // AW-issue block below is gated by live sched_wr_valid[w_arb_grant_id].
    logic [NC-1:0] w_stale_grant;
    assign w_stale_grant = w_arb_grant & ~sched_wr_valid;
    assign w_arb_grant_ack = (w_arb_grant & {NC{(m_axi_awvalid && m_axi_awready)}})
                           | w_stale_grant;

    // AW channel issue logic
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_aw_valid <= 1'b0;
            r_aw_len <= '0;
            r_aw_channel_id <= '0;
        end else begin
            // Accept new command from arbiter; gate by live sched_wr_valid so
            // a stale grant (from the 1-cycle r_arb_request pipeline) cannot
            // capture an AW for a channel the scheduler is no longer driving.
            if (w_arb_grant_valid && !r_aw_valid && sched_wr_valid[w_arb_grant_id]) begin
                r_aw_valid <= 1'b1;
                r_aw_channel_id <= w_arb_grant_id;
                r_aw_len <= w_transfer_size[w_arb_grant_id];  // cfg_axi_wr_xfer_beats stores AWLEN value directly
            end

            // Clear valid when AXI accepts AW
            if (m_axi_awvalid && m_axi_awready) begin
                r_aw_valid <= 1'b0;
            end
        end
    )

    // AXI AW outputs
    assign m_axi_awvalid = r_aw_valid;
    assign m_axi_awid = {{(IW-CIW){1'b0}}, r_aw_channel_id};  // Channel ID in lower bits
    // Address comes directly from scheduler (scheduler increments after each AW)
    assign m_axi_awaddr = sched_wr_addr[r_aw_channel_id];
    assign m_axi_awlen = r_aw_len;
    assign m_axi_awsize = 3'(AXSIZE);
    assign m_axi_awburst = 2'b01;  // INCR

    //=========================================================================
    // SRAM Drain Request
    //=========================================================================
    // Generate drain request when AXI AW command issues
    // This reserves data in the SRAM before W channel starts draining

    logic [NC-1:0] w_drain_req;
    logic [NC-1:0][7:0] w_drain_size;

    always_comb begin
        w_drain_req = '0;
        w_drain_size = '{default:8'h0};

        // Generate drain request when AW handshakes
        if (m_axi_awvalid && m_axi_awready) begin
            w_drain_req[r_aw_channel_id] = 1'b1;
            w_drain_size[r_aw_channel_id] = m_axi_awlen + 8'd1;  // AXI len is 0-based
        end
    end

    assign axi_wr_drain_req = w_drain_req;
    assign axi_wr_drain_size = w_drain_size;

    //=========================================================================
    // Scheduler Ready Signals
    //=========================================================================
    // Ready when final B response completes (B channel handshake with 'last' flag)
    // The 'last' flag in txn_fifo indicates this was the final AW for the descriptor

    logic [NC-1:0] r_sched_ready;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_sched_ready <= '0;
        end else begin
            // Default: clear ready
            r_sched_ready <= '0;

            // Assert ready when B response completes for the LAST transaction of a descriptor
            // The 'last' flag was set when the AW was issued (see txn_fifo_din logic)
            if (m_axi_bvalid && m_axi_bready) begin
                logic [CIW-1:0] ch_id;
                ch_id = m_axi_bid[CIW-1:0];

                // Check if this B response corresponds to the last AW for this descriptor
                if (b_phase_txn_fifo_dout[ch_id].last) begin
                    r_sched_ready[ch_id] <= 1'b1;
                end
            end
        end
    )

    assign sched_wr_ready = r_sched_ready;

    // Debug: Track sched_wr_ready assertions

    //=========================================================================
    // W Channel Management - FIFO-Based Tracking (No FSM!)
    //=========================================================================
    // Use single W-phase transaction FIFO to track active W transfers
    // FIFO is shared across all channels (in-order with AW issue)
    //
    // Key Concept: When AW issues for ANY channel, push transaction to the
    // shared W-phase FIFO. W-phase logic pops from FIFO to get next channel
    // and beats. This preserves AW command order which is critical for W-phase.

    logic [7:0]     r_w_beats_remaining;
    logic [CIW-1:0] r_w_channel_id;
    logic           r_w_active;

    // W-phase control logic - FIFO-based, no FSM state machine!
    // Read from single shared W-phase FIFO to get next channel and beats
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_w_beats_remaining <= '0;
            r_w_channel_id <= '0;
            r_w_active <= 1'b0;
        end else begin
            // Case 1: No active W transfer, check for pending W transaction in FIFO
            if (!r_w_active) begin
                if (!w_phase_txn_fifo_empty) begin
                    // Start W transfer using info from FIFO head
                    r_w_active <= 1'b1;
                    r_w_channel_id <= w_phase_txn_fifo_dout.channel_id;
                    r_w_beats_remaining <= w_phase_txn_fifo_dout.beats;
                end
            end

            // Case 2: Active W transfer, decrement beats on W handshake
            else if (m_axi_wvalid && m_axi_wready) begin
                r_w_beats_remaining <= r_w_beats_remaining - 8'd1;

                // Last beat of current transfer
                if (m_axi_wlast) begin
                    // Check if more pending transactions in FIFO
                    if (!w_phase_txn_fifo_empty) begin
                        // Continue with next transaction from FIFO (NO BUBBLE!)
                        r_w_channel_id <= w_phase_txn_fifo_dout.channel_id;
                        r_w_beats_remaining <= w_phase_txn_fifo_dout.beats;
                        // r_w_active stays 1 → Continuous wvalid!
                    end else begin
                        // No more transactions in FIFO, go idle
                        r_w_active <= 1'b0;
                    end
                end
            end
        end
    )

    // SRAM drain control - ID-based interface
    // When active and AXI ready, drain from SRAM using channel ID
    assign axi_wr_sram_drain = r_w_active && m_axi_wready;
    assign axi_wr_sram_id = r_w_channel_id;

    // W channel outputs - use ID-based SRAM interface
    //
    // Gate m_axi_wvalid with BOTH the registered and the combinational
    // per-channel valid. The registered valid is fine for arbitration
    // decisions (it's the long-cone signal that needed pipelining), but
    // it lags by 1 cycle relative to the actual data appearing on
    // axi_wr_sram_data. If we used registered valid alone, the cycle
    // after a ch's latency-bridge skid empties (drained on T-1, no new
    // data pushed in T) the registered valid is still 1 in T but the
    // muxed data wire shows stale skid contents. A spurious m_axi_wvalid
    // pulse with stale data then leaks onto the AXI bus -- exactly the
    // dma_2ch CRC-mismatch shape caught by sram_chan_tracker.
    // ANDing in the combinational valid filters that 1-cycle dry window.
    assign m_axi_wvalid = r_w_active
                       && axi_wr_sram_valid[r_w_channel_id]
                       && axi_wr_sram_valid_comb[r_w_channel_id];
    assign m_axi_wdata = axi_wr_sram_data;  // Muxed data from SRAM controller
    assign m_axi_wstrb = {(DW/8){1'b1}};  // All bytes valid
    assign m_axi_wlast = (r_w_beats_remaining == 8'd1);
    assign m_axi_wuser = UW'(r_w_channel_id);  // Channel ID for debug/tracking

    //=========================================================================
    // W-Phase Transaction Tracking FIFO (In-Order with AW - SINGLE FIFO)
    //=========================================================================
    // Track beats and channel ID for W-phase (in-order with AW issue)
    // Push on AW handshake, pop on W last beat
    //
    // CRITICAL: Since W-phase is in-order with AW, we use ONE shared FIFO
    // (not per-channel). This preserves the order that AW commands were issued.

    // (w_phase_txn_t typedef and w_phase_txn_fifo_* signals declared in
    // forward-declarations block at the top of the module)

    gaxi_fifo_sync #(
        .DATA_WIDTH($bits(w_phase_txn_t)),
        .DEPTH(W_PHASE_FIFO_DEPTH)
    ) u_w_phase_txn_fifo (
        .axi_aclk   (clk),
        .axi_aresetn(rst_n),
        .wr_data    (w_phase_txn_fifo_din),
        .wr_valid   (w_phase_txn_fifo_wr),
        .wr_ready   (w_phase_txn_fifo_wr_ready),
        .rd_data    (w_phase_txn_fifo_dout),
        .rd_valid   (w_phase_txn_fifo_rd_valid),
        .rd_ready   (w_phase_txn_fifo_rd),
        .count      ()  // Not used
    );

    // Convert wr_ready/rd_valid to full/empty flags
    assign w_phase_txn_fifo_full = !w_phase_txn_fifo_wr_ready;
    assign w_phase_txn_fifo_empty = !w_phase_txn_fifo_rd_valid;

    // Push to W-phase FIFO on AW handshake (in-order)
    // This preserves the order that AW commands were issued
    always_comb begin
        w_phase_txn_fifo_wr = 1'b0;
        w_phase_txn_fifo_din = '0;

        if (m_axi_awvalid && m_axi_awready) begin
            w_phase_txn_fifo_wr = 1'b1;
            w_phase_txn_fifo_din.beats = m_axi_awlen + 8'd1;
            w_phase_txn_fifo_din.channel_id = r_aw_channel_id;
        end
    end

    // Pop from W-phase FIFO when loading new W transfer
    // Two cases: (1) starting idle, (2) completing current and loading next
    logic w_phase_fifo_pop;

    always_comb begin
        w_phase_fifo_pop = 1'b0;

        // Pop when starting new W transfer from idle
        if (!r_w_active && !w_phase_txn_fifo_empty) begin
            w_phase_fifo_pop = 1'b1;
        end
        // Pop when completing current transfer and loading next
        else if (m_axi_wvalid && m_axi_wready && m_axi_wlast && !w_phase_txn_fifo_empty) begin
            w_phase_fifo_pop = 1'b1;
        end
    end

    assign w_phase_txn_fifo_rd = w_phase_fifo_pop;

    //=========================================================================
    // B-Phase Transaction Tracking FIFOs (Out-of-Order Responses)
    //=========================================================================
    // Track beats and last-flag for each outstanding transaction per channel
    // Push on AW handshake, pop on B response

    // (b_phase_txn_t typedef and b_phase_txn_fifo_* signals declared in
    // forward-declarations block at the top of the module)

    genvar g;
    generate
        for (g = 0; g < NC; g++) begin : gen_b_phase_txn_fifos
            logic b_phase_txn_fifo_wr_ready;
            logic b_phase_txn_fifo_rd_valid;

            gaxi_fifo_sync #(
                .DATA_WIDTH($bits(b_phase_txn_t)),
                .DEPTH(B_PHASE_FIFO_DEPTH)
            ) u_b_phase_txn_fifo (
                .axi_aclk   (clk),
                .axi_aresetn(rst_n),
                .wr_data    (b_phase_txn_fifo_din[g]),
                .wr_valid   (b_phase_txn_fifo_wr[g]),
                .wr_ready   (b_phase_txn_fifo_wr_ready),
                .rd_data    (b_phase_txn_fifo_dout[g]),
                .rd_valid   (b_phase_txn_fifo_rd_valid),
                .rd_ready   (b_phase_txn_fifo_rd[g]),
                .count      ()  // Not used
            );

            // Convert wr_ready/rd_valid to full/empty flags
            assign b_phase_txn_fifo_full[g] = !b_phase_txn_fifo_wr_ready;
            assign b_phase_txn_fifo_empty[g] = !b_phase_txn_fifo_rd_valid;
        end
    endgenerate

    // Push to B-phase FIFO on AW handshake
    always_comb begin
        b_phase_txn_fifo_wr = '0;
        b_phase_txn_fifo_din = '{default: '0};

        if (m_axi_awvalid && m_axi_awready) begin
            b_phase_txn_fifo_wr[r_aw_channel_id] = 1'b1;
            b_phase_txn_fifo_din[r_aw_channel_id].beats = m_axi_awlen + 8'd1;
            // Determine if this is last transfer: check if remaining beats after this <= cfg_axi_wr_xfer_beats
            b_phase_txn_fifo_din[r_aw_channel_id].last =
                (sched_wr_beats[r_aw_channel_id] <= {24'd0, m_axi_awlen} + 32'd1);
        end
    end

    // Pop from B-phase FIFO on B response
    always_comb begin
        b_phase_txn_fifo_rd = '0;

        if (m_axi_bvalid && m_axi_bready) begin
            b_phase_txn_fifo_rd[m_axi_bid[CIW-1:0]] = !b_phase_txn_fifo_empty[m_axi_bid[CIW-1:0]];
        end
    end

    //=========================================================================
    // Completion Strobe Generation
    //=========================================================================

    //=========================================================================
    // Completion Strobe Generation - Fire on AW handshake (not B response)
    //=========================================================================
    // Notify scheduler immediately when AW issues so it can proceed

    logic [NC-1:0] r_done_strobe;
    logic [NC-1:0][31:0] r_beats_done;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_done_strobe <= '{default:0};
            r_beats_done <= '{default:0};
        end else begin
            // Default: clear strobe (one-cycle pulse)
            r_done_strobe <= '{default:0};

            // Pulse when AW handshakes (transaction issued to AXI)
            // This tells scheduler that SRAM data is committed and it can proceed
            if (m_axi_awvalid && m_axi_awready) begin
                r_done_strobe[r_aw_channel_id] <= 1'b1;
                r_beats_done[r_aw_channel_id] <= {24'd0, m_axi_awlen} + 32'd1;
            end
        end
    )

    assign sched_wr_done_strobe = r_done_strobe;
    assign sched_wr_beats_done = r_beats_done;

    // synopsys translate_off
    // Hang diagnostic: when sched_wr_valid is high but w_arb_request is low for
    // 1024+ cycles, dump the blocking conditions. Helps debug "stuck near end"
    // hangs where SRAM has data but the engine refuses to issue the final
    // partial burst.
    logic [15:0] r_stuck_counter [NC];
    initial begin
        for (int i = 0; i < NC; i++) r_stuck_counter[i] = 0;
    end
    always_ff @(posedge clk) begin
        for (int i = 0; i < NC; i++) begin
            if (sched_wr_valid[i] && !w_arb_request[i] && !(m_axi_bvalid && m_axi_bready)) begin
                r_stuck_counter[i] <= r_stuck_counter[i] + 1;
                if (r_stuck_counter[i] == 1024) begin
                    $display("[%0t] WR ENGINE STUCK ch%0d: sched_wr_beats=%0d transfer_size=%0d has_data=%b final=%b data_ok=%b no_out=%b arb_req=%b drain_avail=%0d",
                        $time, i,
                        sched_wr_beats[i], w_transfer_size[i], w_has_data[i], w_final_burst[i],
                        w_data_ok[i], w_no_outstanding[i], w_arb_request[i],
                        axi_wr_drain_data_avail[i]);
                end
            end else begin
                r_stuck_counter[i] <= '0;
            end
        end
    end
    // synopsys translate_on

    //=========================================================================
    // B Channel → Response Handling
    //=========================================================================
    // Accept all responses and flag errors per channel

    assign m_axi_bready = 1'b1;  // Always ready for response

    // Error tracking: sticky error flags per channel
    logic [NC-1:0] r_wr_error;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_wr_error <= '0;
        end else begin
            // Check for bad B response on each valid B beat
            if (m_axi_bvalid && m_axi_bready && (m_axi_bresp != 2'b00)) begin
                // Extract channel ID from BID and set corresponding error flag
                logic [CIW-1:0] ch_id;
                ch_id = m_axi_bid[CIW-1:0];
                r_wr_error[ch_id] <= 1'b1;

                // Debug display for error detection
            end
            // Note: Error flags are NOT auto-cleared - must be cleared by external logic
            // Scheduler can clear on channel reset or descriptor completion
        end
    )

    assign sched_wr_error = r_wr_error;

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

    // Sideband to axi_bus_meter -- mirrors the W-phase FSM state.
    assign o_active_channel_id    = r_w_channel_id;
    assign o_active_channel_valid = r_w_active;

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

`ifdef ENHANCED_DEBUG
    // synopsys translate_off
    // Sim-only end-of-simulation state dump for the "drain-ctrl stale
    // view" debug. Snapshots W-phase + AW + B-phase state per channel
    // so the log shows what was in flight when the test ended.
    //
    // Gate: `define ENHANCED_DEBUG (or +define+ENHANCED_DEBUG on the
    // simulator command line) to enable. Off by default.
    int unsigned dbg_aw_per_ch [NC];
    int unsigned dbg_b_per_ch  [NC];
    int unsigned dbg_w_fifo_push_per_ch [NC];
    initial for (int i = 0; i < NC; i++) begin
        dbg_aw_per_ch[i] = 0;
        dbg_b_per_ch[i]  = 0;
        dbg_w_fifo_push_per_ch[i] = 0;
    end
    always_ff @(posedge clk) begin
        if (m_axi_awvalid && m_axi_awready) begin
            dbg_aw_per_ch[r_aw_channel_id] += 1;
        end
        if (m_axi_bvalid && m_axi_bready) begin
            dbg_b_per_ch[m_axi_bid[CIW-1:0]] += 1;
        end
        if (w_phase_txn_fifo_wr && w_phase_txn_fifo_wr_ready) begin
            dbg_w_fifo_push_per_ch[w_phase_txn_fifo_din.channel_id] += 1;
        end
    end

    final begin
        $display("[%0t] [WR_ENG] FINAL state:", $time);
        $display("[%0t] [WR_ENG]   r_w_active=%b r_w_channel_id=%0d r_w_beats_remaining=%0d",
                 $time, r_w_active, r_w_channel_id, r_w_beats_remaining);
        $display("[%0t] [WR_ENG]   w_phase_txn_fifo empty=%b full=%b head_ch=%0d head_beats=%0d",
                 $time, w_phase_txn_fifo_empty, w_phase_txn_fifo_full,
                 w_phase_txn_fifo_dout.channel_id, w_phase_txn_fifo_dout.beats);
        $display("[%0t] [WR_ENG]   GLOBAL: r_aw_transactions=%0d r_w_beats=%0d",
                 $time, r_aw_transactions, r_w_beats);
        for (int i = 0; i < NC; i++) begin
            $display("[%0t] [WR_ENG]   ch%0d: aw=%0d b=%0d w_fifo_pushed=%0d sched_wr_valid=%b sched_wr_beats=%0d r_aw_valid=%b outstanding=%0d outstanding_limit=%b drain_data_avail=%0d has_data=%b final_burst=%b arb_request=%b r_beats_written=%0d",
                     $time, i,
                     dbg_aw_per_ch[i], dbg_b_per_ch[i], dbg_w_fifo_push_per_ch[i],
                     sched_wr_valid[i], sched_wr_beats[i], (r_aw_valid && r_aw_channel_id == CIW'(i)),
                     r_outstanding_count[i], r_outstanding_limit[i],
                     axi_wr_drain_data_avail[i],
                     w_has_data[i], w_final_burst[i], w_arb_request[i],
                     r_beats_written[i]);
        end
    end
    // synopsys translate_on
`endif // ENHANCED_DEBUG

    `ifdef FORMAL
    // Only one arbiter grant at a time
    assert property (@(posedge clk) disable iff (!rst_n)
        $onehot0(w_arb_grant));

    // Granted channel must have valid request (registered version: arbiter
    // sees r_arb_request, not the live w_arb_request, after the request
    // pipeline added for 8-channel 100 MHz timing closure).
    assert property (@(posedge clk) disable iff (!rst_n)
        w_arb_grant_valid |-> (r_arb_request & w_arb_grant) != '0);

    // Drain request only when AW command issues
    assert property (@(posedge clk) disable iff (!rst_n)
        (|axi_wr_drain_req) |-> $past(m_axi_awvalid && m_axi_awready));

    // Channel ID must be valid
    assert property (@(posedge clk) disable iff (!rst_n)
        m_axi_awvalid |-> (r_aw_channel_id < NC));

    // W active only after AW issued
    assert property (@(posedge clk) disable iff (!rst_n)
        r_w_active |-> $past(m_axi_awvalid && m_axi_awready, 1) || $past(r_w_active, 1));
    `endif

endmodule : axi_write_engine
