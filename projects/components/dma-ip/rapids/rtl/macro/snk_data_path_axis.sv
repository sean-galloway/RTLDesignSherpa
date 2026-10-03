// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: snk_data_path_axis
// Purpose: RAPIDS byte-granular Sink Data Path with AXIS Interface (TASK-019)
//
// Description:
//   Wrapper that adds the AXI-Stream slave interface to snk_data_path and
//   converts the packed byte stream into beat-aligned memory beats with byte
//   enables. Beat-granular predecessor: macro_beats/snk_data_path_axis_beats.sv.
//
//   Byte placement: a packet's bytes arrive packed from lane 0 (tstrb may be
//   partial only on the tlast beat). The scheduler's packet record gives the
//   destination byte offset within the first memory beat, so stream lane l
//   lands in memory lane (offset + l): a barrel shift by the offset, with the
//   bytes that spill over the beat boundary held for the next memory beat.
//   After tlast a non-empty spill becomes one more (partial) memory beat.
//   Byte enables shift with the data and are stored beside it in the SRAM,
//   so the write engine drives WSTRB straight from the buffer.
//
//   Packet contract (first cut): the bytes of a tlast-delimited packet equal
//   the descriptor's byte length. A mismatch sets the channel's sticky
//   sched_wr_error bit; nothing is padded or dropped silently.
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
// Subsystem: rapids_macro
//
// Author: sean galloway
// Created: 2026-01-10

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module snk_data_path_axis #(
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
    parameter int SW = DW / 8,
    parameter int OFF_W = (SW > 1) ? $clog2(SW) : 1
) (
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // Configuration Interface
    //=========================================================================
    input  logic [7:0]                  cfg_axi_wr_xfer_beats,
    input  logic [7:0]                  cfg_alloc_size,   // Default allocation size per request
    // Per-channel reset (level or pulse). Clears that channel's ingress state
    // and its SRAM and write-engine state without touching other channels.
    input  logic [NC-1:0]               cfg_channel_reset,

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
    // Packet records from the schedulers (TASK-019): byte length and the
    // destination byte offset of each DATA descriptor, one pulse per record.
    input  logic [NC-1:0]               sched_wr_pkt_valid,
    output logic [NC-1:0]               sched_wr_pkt_ready,
    input  logic [NC-1:0][31:0]         sched_wr_pkt_bytes,
    input  logic [NC-1:0][OFF_W-1:0]    sched_wr_pkt_offset,

    //=========================================================================
    // Completion Interface (to Schedulers)
    //=========================================================================
    output logic [NC-1:0]               sched_wr_done_strobe,
    output logic [NC-1:0][31:0]         sched_wr_beats_done,
    output logic [NC-1:0]               sched_wr_commit_strobe,
    output logic [NC-1:0][31:0]         sched_wr_commit_beats,

    // Sticky per-channel write error, passed up from snk_data_path.
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
    // Fill interface to snk_data_path: {byte enables, data} per beat
    logic                        fill_alloc_req;
    logic [7:0]                  fill_alloc_size;
    logic [CIW-1:0]              fill_alloc_id;
    logic [NC-1:0][SCW-1:0]      fill_space_free;
    logic                        fill_valid;
    logic                        fill_ready;
    logic [CIW-1:0]              fill_id;
    logic [DW+SW-1:0]            fill_data;
    logic [NC-1:0]               w_engine_wr_error;   // from the write engine (B responses)

    //=========================================================================
    // Channel reset: held for the reset cycle and the one after it, so a packet
    // record the scheduler emits while it is still leaving its own state is
    // dropped too.
    //=========================================================================
    logic [NC-1:0] r_rst_d1;
    logic [NC-1:0] w_rst;
    logic [NC-1:0] r_discard;   // stream packet cut by a reset: accept and drop to tlast
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) r_rst_d1 <= '0;
        else                      r_rst_d1 <= cfg_channel_reset;
    )
    assign w_rst = cfg_channel_reset | r_rst_d1;

    //=========================================================================
    // Packet records: a small queue per channel of {offset, bytes}
    //=========================================================================
    localparam int PQ_DEPTH = 4;
    localparam int PQ_PW    = $clog2(PQ_DEPTH);
    logic [NC-1:0][PQ_DEPTH-1:0][OFF_W-1:0] r_pq_off;
    logic [NC-1:0][PQ_DEPTH-1:0][31:0]      r_pq_bytes;
    logic [NC-1:0][PQ_PW:0]                 r_pq_wp, r_pq_rp;
    logic [NC-1:0][PQ_PW:0]                 w_pq_count;
    logic [NC-1:0]                          w_pq_empty, w_pq_full, w_pq_push, w_pq_pop;
    logic [NC-1:0][OFF_W-1:0]               w_head_off;
    logic [NC-1:0][31:0]                    w_head_bytes;

    always_comb begin
        for (int ch = 0; ch < NC; ch++) begin
            w_pq_count[ch]   = r_pq_wp[ch] - r_pq_rp[ch];
            w_pq_empty[ch]   = (w_pq_count[ch] == '0);
            w_pq_full[ch]    = (w_pq_count[ch] == (PQ_PW+1)'(PQ_DEPTH));
            w_pq_push[ch]    = sched_wr_pkt_valid[ch] && !w_pq_full[ch] && !w_rst[ch];
            w_head_off[ch]   = r_pq_off[ch][r_pq_rp[ch][PQ_PW-1:0]];
            w_head_bytes[ch] = r_pq_bytes[ch][r_pq_rp[ch][PQ_PW-1:0]];
        end
    end
    assign sched_wr_pkt_ready = ~w_pq_full;

    //=========================================================================
    // Ingress shifter: packed stream beats -> beat-aligned memory beats
    //=========================================================================
    // Per-channel state (packets of different tids may interleave by beat)
    logic [NC-1:0][DW-1:0]       r_hold_data;      // spill bytes, already in their memory lanes 0..off-1
    logic [NC-1:0][SW-1:0]       r_hold_strb;
    logic [NC-1:0][31:0]         r_pkt_rx_bytes;   // bytes received for the head packet so far
    logic [NC-1:0]               r_pkt_len_error;  // sticky: packet bytes != descriptor bytes
    // After tlast a non-empty spill is emitted as one more memory beat
    logic                        r_flush_valid;
    logic [CIW-1:0]              r_flush_ch;
    // Output register: one memory beat for the fill logic below
    logic                        r_out_valid;
    logic [CIW-1:0]              r_out_id;
    logic [DW-1:0]               r_out_data;
    logic [SW-1:0]               r_out_strb;
    logic                        w_out_take;       // fill logic accepts r_out this cycle
    logic                        w_out_free;       // r_out may be (re)loaded this cycle

    // The incoming beat, placed
    logic [CIW-1:0]              w_in_ch;
    logic [OFF_W-1:0]            w_in_off;
    logic [DW-1:0]               w_in_data_m;      // tdata with non-strobed bytes zeroed
    logic [2*DW-1:0]             w_in_wide;        // [DW-1:0] this memory beat, [2DW-1:DW] the spill
    logic [2*SW-1:0]             w_in_wide_strb;
    logic                        w_in_accept;      // a beat is placed into the shifter
    logic                        w_in_drop;        // a beat of a reset-cut packet is discarded
    logic [7:0]                  w_in_bytes;       // bytes carried by this stream beat (popcount of tstrb)
    logic [31:0]                 w_rx_total;       // bytes of the packet including this beat

    assign w_in_ch  = s_axis_tid[CIW-1:0];
    assign w_in_off = w_head_off[w_in_ch];

    // Non-strobed bytes of a partial last beat are stream junk; unmasked they would
    // shift into the spill hold and be ORed into the channel's next packet.
    always_comb begin
        for (int b = 0; b < SW; b++)
            w_in_data_m[b*8 +: 8] = s_axis_tstrb[b] ? s_axis_tdata[b*8 +: 8] : 8'h00;
    end
    assign w_in_wide      = ({{DW{1'b0}}, w_in_data_m} << (w_in_off * 8)) | {{DW{1'b0}}, r_hold_data[w_in_ch]};
    assign w_in_wide_strb = ({{SW{1'b0}}, s_axis_tstrb} << w_in_off)      | {{SW{1'b0}}, r_hold_strb[w_in_ch]};

    always_comb begin
        w_in_bytes = '0;
        for (int b = 0; b < SW; b++) w_in_bytes = w_in_bytes + 8'(s_axis_tstrb[b]);
    end
    assign w_rx_total = r_pkt_rx_bytes[w_in_ch] + 32'(w_in_bytes);

    // A stream beat is taken when the output register can take a memory beat,
    // no spill is waiting to be flushed, and the channel's packet record is
    // known (the scheduler has started the descriptor).
    // A channel in reset takes nothing. A packet that a reset cut mid-stream
    // is drained: its remaining beats are accepted and dropped up to tlast.
    assign w_out_free    = !r_out_valid || w_out_take;
    assign s_axis_tready = !w_rst[w_in_ch] &&
                           (r_discard[w_in_ch] ||
                            (w_out_free && !r_flush_valid && !w_pq_empty[w_in_ch]));
    assign w_in_accept   = s_axis_tvalid && s_axis_tready && !r_discard[w_in_ch];
    assign w_in_drop     = s_axis_tvalid && s_axis_tready &&  r_discard[w_in_ch];

    // The packet completes on tlast with no spill, or on the flush beat.
    logic w_pkt_done_now;      // tlast beat, spill empty
    logic w_pkt_done_flush;    // flush beat emitted
    assign w_pkt_done_now   = w_in_accept && s_axis_tlast && (w_in_wide_strb[2*SW-1:SW] == '0);
    assign w_pkt_done_flush = r_flush_valid && w_out_free;

    // The out-reg load landing this cycle (flush drain or accepted beat) and
    // the channel it belongs to. The per-channel reset block below runs last
    // and must not kill a load that belongs to a channel NOT in reset
    // (rapids BUG-014: the stale r_out_id/r_flush_ch compares used to clobber
    // a healthy channel's just-loaded beat and flush registration).
    logic                        w_load_any;
    logic [CIW-1:0]              w_load_id;
    logic                        w_flush_set;
    assign w_load_any  = w_pkt_done_flush || w_in_accept;
    assign w_load_id   = w_pkt_done_flush ? r_flush_ch : w_in_ch;
    assign w_flush_set = w_in_accept && s_axis_tlast && (w_in_wide_strb[2*SW-1:SW] != '0);

    always_comb begin
        w_pq_pop = '0;
        if (w_pkt_done_now)   w_pq_pop[w_in_ch]    = 1'b1;
        if (w_pkt_done_flush) w_pq_pop[r_flush_ch] = 1'b1;
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pq_off        <= '{default:'0};
            r_pq_bytes      <= '{default:'0};
            r_pq_wp         <= '{default:'0};
            r_pq_rp         <= '{default:'0};
            r_hold_data     <= '{default:'0};
            r_hold_strb     <= '{default:'0};
            r_pkt_rx_bytes  <= '{default:'0};
            r_pkt_len_error <= '0;
            r_flush_valid   <= 1'b0;
            r_flush_ch      <= '0;
            r_out_valid     <= 1'b0;
            r_out_id        <= '0;
            r_out_data      <= '0;
            r_out_strb      <= '0;
            r_discard       <= '0;
        end else begin
            // packet record queues
            for (int ch = 0; ch < NC; ch++) begin
                if (w_pq_push[ch]) begin
                    r_pq_off[ch][r_pq_wp[ch][PQ_PW-1:0]]   <= sched_wr_pkt_offset[ch];
                    r_pq_bytes[ch][r_pq_wp[ch][PQ_PW-1:0]] <= sched_wr_pkt_bytes[ch];
                    r_pq_wp[ch] <= r_pq_wp[ch] + 1'b1;
                end
                if (w_pq_pop[ch]) r_pq_rp[ch] <= r_pq_rp[ch] + 1'b1;
            end
            // output register hand-off
            if (w_out_take) r_out_valid <= 1'b0;
            if (r_flush_valid && w_out_free) begin
                // the spill of the finished packet becomes its last memory beat
                r_out_valid <= 1'b1;
                r_out_id    <= r_flush_ch;
                r_out_data  <= r_hold_data[r_flush_ch];
                r_out_strb  <= r_hold_strb[r_flush_ch];
                r_hold_data[r_flush_ch] <= '0;
                r_hold_strb[r_flush_ch] <= '0;
                r_flush_valid <= 1'b0;
                r_pkt_rx_bytes[r_flush_ch] <= '0;
            end else if (w_in_accept) begin
                r_out_valid <= 1'b1;
                r_out_id    <= w_in_ch;
                r_out_data  <= w_in_wide[DW-1:0];
                r_out_strb  <= w_in_wide_strb[SW-1:0];
                r_hold_data[w_in_ch] <= w_in_wide[2*DW-1:DW];
                r_hold_strb[w_in_ch] <= w_in_wide_strb[2*SW-1:SW];
                r_pkt_rx_bytes[w_in_ch] <= w_rx_total;
                if (s_axis_tlast) begin
                    // packet contract: bytes received must equal the record
                    if (w_rx_total != w_head_bytes[w_in_ch]) r_pkt_len_error[w_in_ch] <= 1'b1;
                    if (w_in_wide_strb[2*SW-1:SW] != '0) begin
                        r_flush_valid <= 1'b1;        // spill -> one more memory beat
                        r_flush_ch    <= w_in_ch;
                    end else begin
                        r_pkt_rx_bytes[w_in_ch] <= '0;
                    end
                end
            end
            if (w_in_drop && s_axis_tlast) r_discard[w_in_ch] <= 1'b0;
            // channel reset: last, so it wins over every update above
            for (int ch = 0; ch < NC; ch++) begin
                if (w_rst[ch]) begin
                    if ((r_pkt_rx_bytes[ch] != '0) && !(r_flush_valid && (r_flush_ch == ch[CIW-1:0])))
                        r_discard[ch] <= 1'b1;
                    r_pq_wp[ch]        <= '0;
                    r_pq_rp[ch]        <= '0;
                    r_hold_data[ch]    <= '0;
                    r_hold_strb[ch]    <= '0;
                    r_pkt_rx_bytes[ch] <= '0;
                    r_pkt_len_error[ch] <= 1'b0;
                    // Drop this channel's held beat -- unless a load for a
                    // healthy channel lands this same edge (BUG-014).
                    if ((r_out_id == ch[CIW-1:0]) &&
                        !(w_load_any && (w_load_id != ch[CIW-1:0])))
                        r_out_valid <= 1'b0;
                    if ((r_flush_ch == ch[CIW-1:0]) && !w_flush_set)
                        r_flush_valid <= 1'b0;
                end
            end
        end
    )

    // Sticky write error: the engine's B-response errors or a packet-length
    // mismatch on ingress.
    assign sched_wr_error = w_engine_wr_error | r_pkt_len_error;

    //=========================================================================
    // Memory beat -> fill interface (allocation logic as in the beats design)
    //=========================================================================
    // Allocation tracking per channel
    logic [NC-1:0][15:0]         r_pending_alloc;  // Beats allocated but not yet filled
    // cfg_alloc_size is software-writable. At 0 the space test (space_free >= 0)
    // is vacuously true and fill_alloc_size is 0, so the same-cycle
    // allocate-and-consume branch below would underflow r_pending_alloc.
    // Clamp to the minimum reservation.
    logic [7:0]                  w_eff_alloc_size; // cfg_alloc_size, 0 -> 1
    // Statistics
    logic [31:0]                 r_axis_beats_received;
    logic [31:0]                 r_axis_packets_received;

    // Fill data is the placed memory beat with its byte enables
    assign fill_data = {r_out_strb, r_out_data};
    assign fill_id   = r_out_id;

    // An allocation reaches fill_space_free three cycles after its handshake
    // (alloc_ctrl's count, then sram_controller's boundary flop, then the
    // registered view). Hold a channel's next allocation until its view is
    // current (rapids BUG-009, third mechanism).
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
                if (w_rst[ch]) r_alloc_settle[ch] <= 2'd0;
            end
        end
    )
    wire w_out_rst = w_rst[r_out_id];   // the held beat belongs to a channel in reset
    wire w_channel_needs_alloc = (r_pending_alloc[r_out_id] == '0) &&
                                 (r_alloc_settle[r_out_id] == 2'd0);
    assign w_eff_alloc_size = (cfg_alloc_size == 8'd0) ? 8'd1 : cfg_alloc_size;

    // Allocate a segment, or what is left when less than a segment is free
    // (rapids BUG-009, second mechanism), so the buffer can always fill to
    // the top and a burst up to the depth is always satisfiable.
    logic [SCW-1:0] w_space_now;      // free beats of the channel presenting data
    logic [7:0]     w_alloc_now;      // this cycle's allocation: a segment, or the remainder
    assign w_space_now = fill_space_free[r_out_id];
    assign w_alloc_now = (w_space_now >= SCW'(w_eff_alloc_size)) ? w_eff_alloc_size : 8'(w_space_now);
    wire w_channel_has_space = (w_space_now != '0);

    assign fill_alloc_req  = r_out_valid && !w_out_rst && w_channel_needs_alloc && w_channel_has_space;
    assign fill_alloc_size = w_alloc_now;
    assign fill_alloc_id   = r_out_id;

    // Data valid when the channel holds an allocation or allocates this cycle
    assign fill_valid = r_out_valid && !w_out_rst &&
                        ((r_pending_alloc[r_out_id] > 0) ||
                         (w_channel_needs_alloc && w_channel_has_space));
    // The memory beat leaves the output register only when the fill interface
    // takes it (fill_ready), never on an allocation cycle with fill_ready low.
    assign w_out_take = fill_ready && !w_out_rst &&
                        ((r_pending_alloc[r_out_id] > 0) || fill_alloc_req);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pending_alloc <= '{default:'0};
            r_axis_beats_received <= '0;
            r_axis_packets_received <= '0;
        end else begin
            for (int ch = 0; ch < NC; ch++) begin
                if (fill_alloc_req && (fill_alloc_id == ch[CIW-1:0])) begin
                    if (fill_valid && fill_ready && (fill_id == ch[CIW-1:0])) begin
                        r_pending_alloc[ch] <= r_pending_alloc[ch] + fill_alloc_size - 1'b1;
                    end else begin
                        r_pending_alloc[ch] <= r_pending_alloc[ch] + fill_alloc_size;
                    end
                end else if (fill_valid && fill_ready && (fill_id == ch[CIW-1:0])) begin
                    r_pending_alloc[ch] <= r_pending_alloc[ch] - 1'b1;
                end
                if (w_rst[ch]) r_pending_alloc[ch] <= '0;
            end
            // Statistics: stream beats and packets accepted
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

    snk_data_path #(
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
        .cfg_channel_reset      (cfg_channel_reset),

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
        .sched_wr_error         (w_engine_wr_error),

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

endmodule : snk_data_path_axis
