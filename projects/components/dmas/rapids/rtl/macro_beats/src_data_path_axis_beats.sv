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
// Documentation: projects/components/dmas/rapids/docs/rapids_spec/
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
    logic [NC-1:0]               drain_valid_comb;
    logic                        drain_read;
    logic [CIW-1:0]              drain_id;
    logic [DW-1:0]               drain_data;

    // Channel arbitration
    logic [NC-1:0]               r_arb_request;    // Channels requesting service
    logic [NC-1:0]               w_ch_grantable;   // Threshold or final-partial
    logic [NC-1:0]               w_no_more_fill;   // No further fill coming
    logic [7:0]                  w_grant_size [NC];// min(cfg_drain_size, avail)
    // In-flight drain-request pipeline -- closes the stale-avail race.
    // drain_data_avail is flopped once at the SRAM macro boundary
    // (stream sram_controller.sv: unit output is combinational at :307, macro
    // flops it at :264), so a reservation fired this cycle is NOT yet reflected
    // in the view we arbitrate on. Sizing a reservation from the raw view
    // over-reserves; drain_ctrl_beats then SILENTLY drops the excess rd_ptr
    // advance (gated by !r_rd_empty at drain_ctrl_beats.sv:101) -- no $error --
    // and the surplus beats are orphaned at the latency-bridge output where
    // drain_data_avail can no longer see them. Track two cycles (stream tracks
    // two; one is sufficient here, two is conservative and free).
    logic [NC-1:0][SCW-1:0]      w_drain_t;        // reservation firing THIS cycle
    logic [NC-1:0][SCW-1:0]      r_drain_tminus1;  // reservation that fired LAST cycle
    logic [NC-1:0][SCW-1:0]      w_pending_drain;  // in-flight, not yet in the view
    logic [NC-1:0][SCW-1:0]      w_effective_avail;// view minus in-flight
    logic [CIW-1:0]              r_arb_grant_id;   // Currently granted channel
    logic                        r_arb_active;     // Arbitration grant is active
    logic [7:0]                  r_drain_remaining; // Beats remaining in current drain
    logic                        r_grant_pulse;     // 1-cycle drain reservation

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

    always_comb begin
        w_drain_t = '{default:'0};
        if (r_grant_pulse) begin
            w_drain_t[r_arb_grant_id] = SCW'(r_drain_remaining);
        end
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_drain_tminus1 <= '{default:'0};
        end else begin
            r_drain_tminus1 <= w_drain_t;
        end
    )

    always_comb begin
        for (int ch = 0; ch < NC; ch++) begin
            w_pending_drain[ch]   = r_drain_tminus1[ch] + w_drain_t[ch];
            w_effective_avail[ch] = (drain_data_avail[ch] >= w_pending_drain[ch])
                                  ? (drain_data_avail[ch] - w_pending_drain[ch]) : '0;
        end
    end

    // Grant qualification. cfg_drain_size is a THRESHOLD: start draining once
    // this many beats are available, OR drain a short final batch when nothing
    // more is coming for that channel.
    always_comb begin
        for (int ch = 0; ch < NC; ch++) begin
            // Nothing further will arrive: scheduler has no beats left to fetch
            // AND no AXI reads are still outstanding for the channel.
            w_no_more_fill[ch] = (sched_rd_beats[ch] == 32'd0) && dbg_rd_all_complete[ch];
            w_ch_grantable[ch] = (w_effective_avail[ch] >= SCW'(cfg_drain_size))
                              || ((w_effective_avail[ch] != '0) && w_no_more_fill[ch]);
            // Reserve ONLY what is really present. drain_ctrl advances rd_ptr by
            // the full rd_size in one cycle, so reserving more than is there makes
            // rd_ptr overshoot wr_ptr and corrupts the occupancy permanently.
            w_grant_size[ch] = (w_effective_avail[ch] >= SCW'(cfg_drain_size))
                              ? cfg_drain_size : 8'(w_effective_avail[ch]);
            r_arb_request[ch] = w_ch_grantable[ch];
        end
    end

    // Round-robin arbiter state machine
    // Arbiter advances when:
    // 1. No active grant (!r_arb_active)
    // 2. Current drain complete (r_drain_remaining == 0 && m_axis_tvalid && m_axis_tready)
    // 3. Current channel has no more data (r_arb_active && drain_data_avail[r_arb_grant_id] == 0)
    //    This prevents arbiter from getting stuck waiting for handshake on empty channel
    // STREAM's consumer model (axi_write_engine.sv:655-690): take a grant ONCE,
    // drain exactly the reserved number of beats, retire on the last one, and
    // NEVER re-consult availability mid-drain.
    //
    // This matters because the SRAM now REGISTERS drain_data_avail for timing
    // closure (stream/rtl/fub/sram_controller.sv output register block), so the
    // arbiter's view is one cycle stale. The previous FSM abandoned a live grant
    // on `drain_data_avail[grant] == 0` and re-armed on the same stale vector; at
    // cfg_drain_size==1 that fired on the very first accepted beat, so it dropped
    // and re-arbitrated every beat and stranded data. Arbitration must not know
    // about the flops -- it just arbitrates the signals it gets.
    logic w_beat_accepted;
    assign w_beat_accepted = m_axis_tvalid && m_axis_tready;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_arb_grant_id    <= '0;
            r_arb_active      <= 1'b0;
            r_drain_remaining <= '0;
            r_grant_pulse     <= 1'b0;
        end else begin
            r_grant_pulse <= 1'b0;
            if (!r_arb_active) begin
                for (int ch = 0; ch < NC; ch++) begin
                    logic [CIW-1:0] check_ch;
                    check_ch = (r_arb_grant_id + 1 + ch) % NC;
                    if (w_ch_grantable[check_ch]) begin
                        r_arb_grant_id    <= check_ch;
                        r_arb_active      <= 1'b1;
                        r_drain_remaining <= w_grant_size[check_ch];
                        r_grant_pulse     <= 1'b1;
                        break;
                    end
                end
            end else if (w_beat_accepted) begin
                // Decrement is NOT in an else-branch of an advance term any more,
                // so a completing beat is always counted against the block.
                if (r_drain_remaining <= 8'd1) begin
                    r_arb_active      <= 1'b0;
                    r_drain_remaining <= '0;
                end else begin
                    r_drain_remaining <= r_drain_remaining - 8'd1;
                end
            end
        end
    )

    //=========================================================================
    // Drain Request Generation
    //=========================================================================

    // Generate drain requests based on arbitration
    // ONE-CYCLE reservation. drain_ctrl_beats has no edge detect -- it advances
    // rd_ptr whenever (rd_valid && !rd_empty), so a HELD request re-advances the
    // pointer every cycle. Pulse it exactly once, carrying the reserved size.
    always_comb begin
        drain_req = '0;
        drain_size = '{default:'0};
        if (r_grant_pulse) begin
            drain_req[r_arb_grant_id] = 1'b1;
            drain_size[r_arb_grant_id] = r_drain_remaining;
        end
    end

    // Drain read when AXIS accepts data
    assign drain_id = r_arb_grant_id;
    assign drain_read = w_beat_accepted;

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
    // Gate on BOTH the registered and the combinational per-channel valid.
    // The registered valid is the right input to ARBITRATION (it is the long
    // cone that needed the flop), but it lags the data by a cycle. Gating on it
    // alone lets the SRAM unit pop a beat while tvalid is suppressed -- the beat
    // is consumed and never transmitted. STREAM's write engine documents this
    // exact failure at axi_write_engine.sv:694-702. src had neither the flop nor
    // the tap before the SRAM became stream's, so it was self-consistent; adding
    // the flop without this tap is what lost beats at cfg_drain_size==1.
    assign m_axis_tvalid = r_arb_active
                        && drain_valid[r_arb_grant_id]
                        && drain_valid_comb[r_arb_grant_id];

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
        .drain_valid_comb       (drain_valid_comb),
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
