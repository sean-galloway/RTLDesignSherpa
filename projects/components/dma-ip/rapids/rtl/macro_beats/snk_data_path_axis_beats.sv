// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: snk_data_path_axis_beats
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
// Documentation: projects/components/dma-ip/rapids/docs/rapids_spec/
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
    parameter int PIPELINE = 1,
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
    output logic [NC-1:0]               sched_wr_commit_strobe,
    output logic [NC-1:0][31:0]         sched_wr_commit_beats,

    // Sticky per-channel write error, passed up from snk_data_path_beats.
    output logic [NC-1:0]               sched_wr_error,

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
    output logic [31:0]                 dbg_axis_packets_received,

    // Active-channel sideband for per-channel bus instrumentation
    // (axi_bus_meter). The W bus carries no wid, so the write engine's
    // channel index must travel out of band to reach the meter at the top.
    output logic [CIW-1:0]              o_active_channel_id,
    output logic                        o_active_channel_valid
);

    //=========================================================================
    // Internal Signals
    //=========================================================================

    // Fill interface to sink_data_path
`ifdef RAPIDS_CHAR_ILA
    (* mark_debug = "true" *)
`endif
    logic                        fill_alloc_req;
    logic [7:0]                  fill_alloc_size;
    logic [CIW-1:0]              fill_alloc_id;
`ifdef RAPIDS_CHAR_ILA
    (* mark_debug = "true" *)
`endif
    logic [NC-1:0][SCW-1:0]      fill_space_free;

`ifdef RAPIDS_CHAR_ILA
    (* mark_debug = "true" *)
`endif
    logic                        fill_valid;
`ifdef RAPIDS_CHAR_ILA
    (* mark_debug = "true" *)
`endif
    logic                        fill_ready;
    logic [CIW-1:0]              fill_id;
    logic [DW-1:0]               fill_data;

    // Channel extraction from AXIS
    logic [CIW-1:0]              axis_channel_id;

    // Allocation tracking per channel
`ifdef RAPIDS_CHAR_ILA
    (* mark_debug = "true" *)
`endif
    logic [NC-1:0][15:0]         r_pending_alloc;  // Beats allocated but not yet filled
    // cfg_alloc_size is software-writable. At 0 the space test (space_free >= 0)
    // is vacuously true and fill_alloc_size is 0, so the same-cycle
    // allocate-and-consume branch below computes 0 + 0 - 1 and underflows
    // r_pending_alloc to 16'hFFFF. Ingress then streams 65535 beats while
    // alloc_ctrl advanced its write pointer by 0. The underflow itself is
    // OBSERVED (r_pending_alloc reaches 16'hFFFF in simulation); the downstream
    // consequence of filling past the reservation is NOT demonstrated here, so
    // this guard is defensive on that point. Clamp to the minimum reservation.
    logic [7:0]                  w_eff_alloc_size; // cfg_alloc_size, 0 -> 1
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
    // An allocation reaches fill_space_free three cycles after its handshake
    // (alloc_ctrl's count, then sram_controller's boundary flop, then the
    // registered view). A whole-segment allocation keeps r_pending_alloc
    // above zero for that long, so the stale view was never consulted; a
    // partial allocation of one or two beats (below) is consumed before the
    // view moves, and a second allocation against the stale count
    // over-allocated the buffer: on the Genesys 2 alloc_ctrl's count ran
    // past the depth, space_free wrapped to 246, the ingress kept
    // allocating, and 30 beats vanished (fifo 94 + bridge 4 for 128
    // accepted). Hold a channel's next allocation until its view is current.
    logic [NC-1:0][1:0] r_alloc_settle;   // cycles until fill_space_free reflects the last allocation
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_alloc_settle <= '{default:'0};
        end else begin
            for (int ch = 0; ch < NC; ch++) begin
                if (fill_alloc_req && (fill_alloc_id == ch[CIW-1:0]))
                    r_alloc_settle[ch] <= 2'd3;
                else if (r_alloc_settle[ch] != 2'd0)
                    r_alloc_settle[ch] <= r_alloc_settle[ch] - 2'd1;
            end
        end
    )

    wire w_channel_needs_alloc = (r_pending_alloc[axis_channel_id] == '0) &&
                                 (r_alloc_settle[axis_channel_id] == 2'd0);
    assign w_eff_alloc_size = (cfg_alloc_size == 8'd0) ? 8'd1 : cfg_alloc_size;

    // rapids BUG-009, second mechanism (Genesys 2 ILA, 2026-09-29): allocate
    // what is left when less than a segment is free. Allocation is
    // segment-granular (cfg_alloc_size, 16 by default) and a packet that ends
    // mid-segment leaves the phase shifted: after a 4-beat packet 12 beats of
    // its segment stay allocated, the next packet consumes them, and from then
    // on the last 4 slots of a 128-deep buffer could never be allocated again
    // until something drained -- while the write engine, configured for a
    // 128-beat burst, waited for exactly those slots. The channel accepted 124
    // beats and never issued an AW. With a partial allocation the buffer can
    // always be filled to the top, so a burst up to the depth is always
    // satisfiable. r_pending_alloc adds fill_alloc_size, so nothing else
    // changes; alloc_ctrl takes any size.
    logic [SCW-1:0] w_space_now;      // free beats of the channel presenting data
    logic [7:0]     w_alloc_now;      // this cycle's allocation: a segment, or the remainder
    assign w_space_now = fill_space_free[axis_channel_id];
    assign w_alloc_now = (w_space_now >= SCW'(w_eff_alloc_size)) ? w_eff_alloc_size : 8'(w_space_now);
    wire w_channel_has_space = (w_space_now != '0);

    // Generate allocation request when needed and space available
    assign fill_alloc_req = s_axis_tvalid && w_channel_needs_alloc && w_channel_has_space;
    assign fill_alloc_size = w_alloc_now;
    assign fill_alloc_id = axis_channel_id;

    // Data valid when:
    // 1. AXIS has valid data AND
    // 2. Channel has pending allocation (space reserved) OR allocation is happening this cycle
    // NOTE: Must include allocation case to avoid losing first beat of each packet!
    assign fill_valid = s_axis_tvalid &&
                        ((r_pending_alloc[axis_channel_id] > 0) ||
                         (w_channel_needs_alloc && w_channel_has_space));

    // AXIS ready when the fill interface can take the beat AND the channel
    // either holds an allocation or is allocating this cycle. The allocation
    // cycle used to be accepted regardless of fill_ready: the beat was taken
    // from AXIS while fill_valid && !fill_ready dropped it on the floor. That
    // only bites when the FIFO is full at an allocation, which the wrapped
    // space count above made routine (Genesys 2, `trace_E`: eight beats lost
    // per 1024 cycles, every one on an allocation cycle with fill_ready low).
    // The allocation itself still goes through without the beat; the beat is
    // taken the cycle fill_ready returns.
    assign s_axis_tready = fill_ready &&
                           ((r_pending_alloc[axis_channel_id] > 0) || fill_alloc_req);

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
        .sched_wr_commit_strobe (sched_wr_commit_strobe),
        .sched_wr_commit_beats  (sched_wr_commit_beats),
        .sched_wr_error         (sched_wr_error),

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
        .dbg_sram_bridge_out_valid  (dbg_sram_bridge_out_valid),

        // Active-channel sideband (RAPIDS TASK-001)
        .o_active_channel_id        (o_active_channel_id),
        .o_active_channel_valid     (o_active_channel_valid)
    );

endmodule : snk_data_path_axis_beats
