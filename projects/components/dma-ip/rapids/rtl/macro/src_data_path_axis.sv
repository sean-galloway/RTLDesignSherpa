// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: src_data_path_axis
// Purpose: RAPIDS byte-granular Source Data Path with AXIS Interface (TASK-019)
//
//   Byte granularity: the scheduler's packet record gives each DATA
//   descriptor's byte length and the source byte offset within the first
//   memory beat. Memory beats are popped from the SRAM and re-packed from
//   lane 0 (a barrel shift by the offset, holding the bytes above the offset
//   for the next stream beat); the last stream beat of a packet carries a
//   contiguous tstrb for the remaining bytes and tlast. Packets therefore
//   follow descriptors, not drain reservations. Beat-granular predecessor:
//   macro_beats/src_data_path_axis_beats.sv.
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
// Documentation: projects/components/dma-ip/rapids/docs/rapids_spec/
// Subsystem: rapids_macro
//
// Author: sean galloway
// Created: 2026-01-10

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module src_data_path_axis #(
    // Primary parameters
    parameter int NUM_CHANNELS = 8,
    parameter int ADDR_WIDTH = 64,
    parameter int DATA_WIDTH = 512,
    parameter int AXI_ID_WIDTH = 8,
    parameter int SRAM_DEPTH = 512,
    parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,
    parameter int PIPELINE = 1,
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
    parameter int SW = DW / 8,
    parameter int OFF_W = (SW > 1) ? $clog2(SW) : 1
) (
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // Configuration Interface
    //=========================================================================
    input  logic [7:0]                  cfg_axi_rd_xfer_beats,
    input  logic [7:0]                  cfg_drain_size,   // Beats to drain per request
    // Per-channel reset (level or pulse). Clears that channel's egress state
    // and its SRAM and read-engine state without touching other channels.
    input  logic [NC-1:0]               cfg_channel_reset,

    //=========================================================================
    // Scheduler Interface (Per-Channel Read Requests)
    //=========================================================================
    input  logic [NC-1:0]               sched_rd_valid,
    input  logic [NC-1:0][AW-1:0]       sched_rd_addr,
    input  logic [NC-1:0][31:0]         sched_rd_beats,
    // Packet records from the schedulers (TASK-019): byte length and the
    // source byte offset of each DATA descriptor, one pulse per record.
    input  logic [NC-1:0]               sched_rd_pkt_valid,
    output logic [NC-1:0]               sched_rd_pkt_ready,
    input  logic [NC-1:0][31:0]         sched_rd_pkt_bytes,
    input  logic [NC-1:0][OFF_W-1:0]    sched_rd_pkt_offset,

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
    // cfg_drain_size is software-writable. At 0 the threshold test
    // (avail >= 0) is vacuously true, so a channel with avail==0 is granted a
    // block of 0 beats; the FSM then waits for a beat that can never arrive
    // (m_axis_tvalid needs real SRAM data) and r_arb_active latches high,
    // starving every channel. Clamp to the minimum useful quantum.
    logic [7:0]                  w_eff_drain_size; // cfg_drain_size, 0 -> 1
    // In-flight drain-request pipeline -- closes the stale-avail race.
    // drain_data_avail is flopped once at the SRAM macro boundary
    // (stream sram_controller.sv: unit output is combinational at :307, macro
    // flops it at :264), so a reservation fired this cycle is NOT yet reflected
    // in the view we arbitrate on. Sizing a reservation from the raw view
    // over-reserves; drain_ctrl then SILENTLY drops the excess rd_ptr
    // advance (gated by !r_rd_empty at drain_ctrl.sv:101) -- no $error --
    // and the surplus beats are orphaned at the latency-bridge output where
    // drain_data_avail can no longer see them. Track two cycles (stream tracks
    // two; one is sufficient here, two is conservative and free).
    logic [NC-1:0][SCW-1:0]      w_drain_t;        // reservation firing THIS cycle
    logic [NC-1:0][SCW-1:0]      r_drain_tminus1;  // reservation that fired LAST cycle
    logic [NC-1:0][SCW-1:0]      w_pending_drain;  // in-flight, not yet in the view
    logic [NC-1:0][SCW-1:0]      w_effective_avail;// view minus in-flight
    // Two stages, as in STREAM's write engine (axi_write_engine.sv: AW issue
    // = reservation, W phase = drain, joined by a small in-order queue):
    //   RESERVATION: one round-robin decision per cycle while the queue has
    //   room; each decision is a ONE-CYCLE drain_req pulse of grant_size beats.
    //   DRAIN: pops the queue in order, sends exactly the reserved beats, and
    //   loads the next entry ON the last beat -- no bubble between grants.
    // A single grant-drain-retire FSM (the previous shape) reserves the next
    // block only after the current one has fully drained, which at
    // cfg_drain_size == 1 is one beat every other cycle: measured 50% on the
    // Genesys 2 AXI4-rd and AXIS-out, against 96-100% before the SRAM swap.
    logic [CIW-1:0]              r_rr_last;         // round-robin base (last reserved)
    logic                        r_res_valid;       // reservation pulse (= drain_req)
    logic [CIW-1:0]              r_res_ch;
    logic [7:0]                  r_res_size;
    localparam int RQ_DEPTH = 4;                    // reservations in flight
    localparam int RQ_PW    = $clog2(RQ_DEPTH);
    logic [RQ_DEPTH-1:0][CIW-1:0] r_rq_ch;
    logic [RQ_DEPTH-1:0][7:0]     r_rq_size;
    logic [RQ_PW:0]              r_rq_wp, r_rq_rp;
    logic [RQ_PW:0]              w_rq_count;
    logic                        w_rq_empty, w_rq_room;
    logic [CIW-1:0]              r_d_ch;            // channel being drained
    logic                        r_d_active;
    logic [7:0]                  r_d_remaining;     // beats left in the current block
    logic                        w_beat_accepted;
    logic                        w_d_load;          // drain stage takes the queue head

    //=========================================================================
    // Channel reset: held for the reset cycle and the one after it, so a packet
    // record the scheduler emits while it is still leaving its own state is
    // dropped too.
    //=========================================================================
    logic [NC-1:0] r_rst_d1;
    logic [NC-1:0] w_rst;
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
            w_pq_push[ch]    = sched_rd_pkt_valid[ch] && !w_pq_full[ch] && !w_rst[ch];
            w_head_off[ch]   = r_pq_off[ch][r_pq_rp[ch][PQ_PW-1:0]];
            w_head_bytes[ch] = r_pq_bytes[ch][r_pq_rp[ch][PQ_PW-1:0]];
        end
    end
    assign sched_rd_pkt_ready = ~w_pq_full;

    //=========================================================================
    // Egress shifter: beat-aligned memory beats -> packed stream beats
    //=========================================================================
    // Per-channel state for the head packet
    logic [NC-1:0][DW-1:0]       r_hold_data;      // bytes above the offset of the last popped beat, at lane 0
    logic [NC-1:0]               r_hold_valid;
    logic [NC-1:0]               r_eg_started;     // head packet has popped at least one memory beat
    logic [NC-1:0][31:0]         r_eg_bytes_left;  // stream bytes still to send
    logic [NC-1:0][31:0]         r_eg_mem_left;    // memory beats still to pop
    // Output register: one stream beat
    logic                        r_out_valid;
    logic [DW-1:0]               r_out_data;
    logic [SW-1:0]               r_out_strb;
    logic                        r_out_last;
    logic [CIW-1:0]              r_out_ch;
    logic                        w_out_free;

    // The channel being drained
    logic [CIW-1:0]              w_c;
    logic [OFF_W-1:0]            w_off;
    logic [31:0]                 w_bytes_left;     // before this cycle's output
    logic [32:0]                 w_mem_span;
    logic [31:0]                 w_mem_total;      // memory beats of the head packet
    logic [31:0]                 w_mem_left;       // before this cycle's pop
    logic                        w_pop;            // pop a memory beat this cycle
    logic                        w_emit_on_pop;    // the pop produces a stream beat
    logic [NC-1:0]               w_need_flush;     // last memory beat popped, bytes still held
    logic                        w_flush_any;
    logic [CIW-1:0]              w_flush_ch;
    logic [DW-1:0]               w_pop_out;        // stream beat formed from hold + popped beat
    logic [DW-1:0]               w_pop_hold_next;  // bytes of the popped beat above the offset
    logic [DW-1:0]               w_out_data_n;
    logic [7:0]                  w_out_bytes_n;    // 1..SW (8 bits: up to 1024-bit beats)
    logic [31:0]                 w_bytes_left_sel; // bytes_left of the channel that emits
    logic [SW-1:0]               w_out_strb_n;

    assign w_c          = r_d_ch;
    assign w_off        = w_head_off[w_c];
    assign w_bytes_left = r_eg_started[w_c] ? r_eg_bytes_left[w_c] : w_head_bytes[w_c];
    assign w_mem_span   = 33'(w_off) + 33'(w_head_bytes[w_c]) + 33'(SW - 1);
    assign w_mem_total  = 32'(w_mem_span >> OFF_W);
    assign w_mem_left   = r_eg_started[w_c] ? r_eg_mem_left[w_c] : w_mem_total;

    always_comb begin
        for (int ch = 0; ch < NC; ch++) begin
            w_need_flush[ch] = r_eg_started[ch] && (r_eg_mem_left[ch] == 32'd0) && (r_eg_bytes_left[ch] != 32'd0)
                            && !w_rst[ch];
        end
        w_flush_any = 1'b0;
        w_flush_ch  = '0;
        for (int ch = 0; ch < NC; ch++) begin
            if (w_need_flush[ch] && !w_flush_any) begin
                w_flush_any = 1'b1;
                w_flush_ch  = CIW'(ch);
            end
        end
    end

    // A memory beat is popped when the drain stage has one, the output
    // register is free, no flush is pending and the packet record is known.
    assign w_out_free = !r_out_valid || m_axis_tready;
    assign w_pop = r_d_active && drain_valid[w_c] && drain_valid_comb[w_c]
                && w_out_free && !w_flush_any && !w_pq_empty[w_c] && !w_rst[w_c];
    // offset 0: every pop is a stream beat. offset > 0: the first pop only
    // primes the hold, unless the packet fits in that one memory beat.
    assign w_emit_on_pop = (w_off == '0) || r_hold_valid[w_c] || (w_mem_left == 32'd1);
    // hold (lanes 0..SW-1-off) completed by the popped beat's low lanes
    assign w_pop_out       = r_hold_valid[w_c] ? (r_hold_data[w_c] | (drain_data << ((SW - 32'(w_off)) * 8)))
                                               : (drain_data >> (w_off * 8));
    assign w_pop_hold_next = drain_data >> (w_off * 8);

    // Next output beat: from a flush (held bytes only) or from a pop
    assign w_out_data_n     = w_flush_any ? r_hold_data[w_flush_ch] : w_pop_out;
    assign w_bytes_left_sel = w_flush_any ? r_eg_bytes_left[w_flush_ch] : w_bytes_left;
    assign w_out_bytes_n    = (w_bytes_left_sel >= 32'(SW)) ? 8'(SW) : 8'(w_bytes_left_sel);
    assign w_out_strb_n     = (w_out_bytes_n >= 8'(SW)) ? {SW{1'b1}} : ~({SW{1'b1}} << w_out_bytes_n);

    logic w_emit;            // an output beat is loaded this cycle
    logic [CIW-1:0] w_emit_ch;
    assign w_emit    = (w_flush_any && w_out_free) || (w_pop && w_emit_on_pop);
    assign w_emit_ch = w_flush_any ? w_flush_ch : w_c;

    always_comb begin
        w_pq_pop = '0;
        if (w_emit && (w_bytes_left_sel == 32'(w_out_bytes_n))) w_pq_pop[w_emit_ch] = 1'b1;
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pq_off        <= '{default:'0};
            r_pq_bytes      <= '{default:'0};
            r_pq_wp         <= '{default:'0};
            r_pq_rp         <= '{default:'0};
            r_hold_data     <= '{default:'0};
            r_hold_valid    <= '0;
            r_eg_started    <= '0;
            r_eg_bytes_left <= '{default:'0};
            r_eg_mem_left   <= '{default:'0};
            r_out_valid     <= 1'b0;
            r_out_data      <= '0;
            r_out_strb      <= '0;
            r_out_last      <= 1'b0;
            r_out_ch        <= '0;
        end else begin
            for (int ch = 0; ch < NC; ch++) begin
                if (w_pq_push[ch]) begin
                    r_pq_off[ch][r_pq_wp[ch][PQ_PW-1:0]]   <= sched_rd_pkt_offset[ch];
                    r_pq_bytes[ch][r_pq_wp[ch][PQ_PW-1:0]] <= sched_rd_pkt_bytes[ch];
                    r_pq_wp[ch] <= r_pq_wp[ch] + 1'b1;
                end
            end
            if (m_axis_tvalid && m_axis_tready) r_out_valid <= 1'b0;
            if (w_emit) begin
                r_out_valid <= 1'b1;
                r_out_data  <= w_out_data_n;
                r_out_strb  <= w_out_strb_n;
                r_out_last  <= (w_bytes_left_sel == 32'(w_out_bytes_n));
                r_out_ch    <= w_emit_ch;
            end
            if (w_pop) begin
                r_eg_started[w_c]  <= 1'b1;
                r_eg_mem_left[w_c] <= w_mem_left - 32'd1;
                if (w_off != '0) begin
                    r_hold_data[w_c]  <= w_pop_hold_next;
                    r_hold_valid[w_c] <= 1'b1;
                end
                r_eg_bytes_left[w_c] <= w_emit_on_pop ? (w_bytes_left - 32'(w_out_bytes_n)) : w_bytes_left;
            end else if (w_flush_any && w_out_free) begin
                r_eg_bytes_left[w_flush_ch] <= r_eg_bytes_left[w_flush_ch] - 32'(w_out_bytes_n);
            end
            // Packet done: retire the record and clear the channel's shifter
            // state. Last on purpose: the pop that emits a packet's final beat
            // also runs the pop bookkeeping above, and this must win.
            for (int ch = 0; ch < NC; ch++) begin
                if (w_pq_pop[ch]) begin
                    r_pq_rp[ch]         <= r_pq_rp[ch] + 1'b1;
                    r_eg_started[ch]    <= 1'b0;
                    r_hold_valid[ch]    <= 1'b0;
                    r_hold_data[ch]     <= '0;
                    r_eg_bytes_left[ch] <= '0;
                    r_eg_mem_left[ch]   <= '0;
                end
            end
            // Channel reset: last, so it wins over every update above. A beat
            // already in the output register still completes (AXIS stability).
            for (int ch = 0; ch < NC; ch++) begin
                if (w_rst[ch]) begin
                    r_pq_wp[ch]         <= '0;
                    r_pq_rp[ch]         <= '0;
                    r_eg_started[ch]    <= 1'b0;
                    r_hold_valid[ch]    <= 1'b0;
                    r_hold_data[ch]     <= '0;
                    r_eg_bytes_left[ch] <= '0;
                    r_eg_mem_left[ch]   <= '0;
                end
            end
        end
    )

    //=========================================================================
    // Drain stage: memory beats in reservation order (unchanged from beats)
    //=========================================================================
    always_comb begin
        w_drain_t = '{default:'0};
        if (r_res_valid) begin
            w_drain_t[r_res_ch] = SCW'(r_res_size);
        end
    end
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_drain_tminus1 <= '{default:'0};
        end else begin
            r_drain_tminus1 <= w_drain_t;
            for (int ch = 0; ch < NC; ch++) begin
                if (w_rst[ch]) r_drain_tminus1[ch] <= '0;
            end
        end
    )
    always_comb begin
        for (int ch = 0; ch < NC; ch++) begin
            w_pending_drain[ch]   = r_drain_tminus1[ch] + w_drain_t[ch];
            w_effective_avail[ch] = (drain_data_avail[ch] >= w_pending_drain[ch])
                                  ? (drain_data_avail[ch] - w_pending_drain[ch]) : '0;
        end
    end
    assign w_eff_drain_size = (cfg_drain_size == 8'd0) ? 8'd1 : cfg_drain_size;
    always_comb begin
        for (int ch = 0; ch < NC; ch++) begin
            w_no_more_fill[ch] = (sched_rd_beats[ch] == 32'd0) && dbg_rd_all_complete[ch];
            w_ch_grantable[ch] = !w_rst[ch] &&
                                 ((w_effective_avail[ch] >= SCW'(w_eff_drain_size))
                                  || ((w_effective_avail[ch] != '0) && w_no_more_fill[ch]));
            w_grant_size[ch] = (w_effective_avail[ch] >= SCW'(w_eff_drain_size))
                              ? w_eff_drain_size : 8'(w_effective_avail[ch]);
            r_arb_request[ch] = w_ch_grantable[ch];
        end
    end
    assign w_rq_count = r_rq_wp - r_rq_rp;
    assign w_rq_empty = (w_rq_count == '0);
    assign w_rq_room  = ((w_rq_count + (RQ_PW+1)'(r_res_valid)) < (RQ_PW+1)'(RQ_DEPTH));
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rr_last   <= '0;
            r_res_valid <= 1'b0;
            r_res_ch    <= '0;
            r_res_size  <= '0;
        end else begin
            r_res_valid <= 1'b0;
            if (w_rq_room) begin
                for (int ch = 0; ch < NC; ch++) begin
                    logic [CIW-1:0] check_ch;
                    check_ch = CIW'((int'(r_rr_last) + 1 + ch) % NC);
                    if (w_ch_grantable[check_ch]) begin
                        r_res_valid <= 1'b1;
                        r_res_ch    <= check_ch;
                        r_res_size  <= w_grant_size[check_ch];
                        r_rr_last   <= check_ch;
                        break;
                    end
                end
            end
        end
    )
    always_comb begin
        drain_req  = '0;
        drain_size = '{default:'0};
        if (r_res_valid) begin
            drain_req[r_res_ch]  = 1'b1;
            drain_size[r_res_ch] = r_res_size;
        end
    end
    // The drain stage advances on memory-beat pops, not on stream handshakes
    assign w_beat_accepted = w_pop;
    assign w_d_load = !w_rq_empty
                   && (!r_d_active || (w_beat_accepted && (r_d_remaining <= 8'd1)));
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rq_wp       <= '0;
            r_rq_rp       <= '0;
            r_rq_ch       <= '0;
            r_rq_size     <= '0;
            r_d_ch        <= '0;
            r_d_active    <= 1'b0;
            r_d_remaining <= '0;
        end else begin
            if (r_res_valid && !w_rst[r_res_ch]) begin
                r_rq_ch[r_rq_wp[RQ_PW-1:0]]   <= r_res_ch;
                r_rq_size[r_rq_wp[RQ_PW-1:0]] <= r_res_size;
                r_rq_wp                       <= r_rq_wp + 1'b1;
            end
            if (w_d_load) begin
                r_d_active    <= (r_rq_size[r_rq_rp[RQ_PW-1:0]] != 8'd0);  // a killed entry loads idle
                r_d_ch        <= r_rq_ch[r_rq_rp[RQ_PW-1:0]];
                r_d_remaining <= r_rq_size[r_rq_rp[RQ_PW-1:0]];
                r_rq_rp       <= r_rq_rp + 1'b1;
            end else if (r_d_active && w_beat_accepted) begin
                if (r_d_remaining <= 8'd1) begin
                    r_d_active    <= 1'b0;
                    r_d_remaining <= '0;
                end else begin
                    r_d_remaining <= r_d_remaining - 8'd1;
                end
            end
            // Channel reset, last: void queued reservations of the channel and
            // stop draining it. r_d_active gates the clear so a block of another
            // channel loaded this cycle survives a stale r_d_ch.
            for (int k = 0; k < RQ_DEPTH; k++) begin
                if (w_rst[r_rq_ch[k]] &&
                    !(r_res_valid && !w_rst[r_res_ch] && (k == int'(r_rq_wp[RQ_PW-1:0]))))
                    r_rq_size[k] <= '0;
            end
            for (int ch = 0; ch < NC; ch++) begin
                if (w_rst[ch] && r_d_active && (r_d_ch == ch[CIW-1:0])) begin
                    r_d_active    <= 1'b0;
                    r_d_remaining <= '0;
                end
            end
        end
    )
    assign drain_id   = r_d_ch;
    assign drain_read = w_pop;

    //=========================================================================
    // AXIS master outputs
    //=========================================================================
    logic [31:0]                 r_axis_beats_sent;
    logic [31:0]                 r_axis_packets_sent;
    assign m_axis_tdata  = r_out_data;
    assign m_axis_tstrb  = r_out_strb;
    assign m_axis_tid    = {{(AXIS_ID_WIDTH-CIW){1'b0}}, r_out_ch};
    assign m_axis_tdest  = {{(AXIS_DEST_WIDTH-CIW){1'b0}}, r_out_ch};
    assign m_axis_tuser  = '0;
    assign m_axis_tvalid = r_out_valid;
    assign m_axis_tlast  = r_out_last;
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
    assign dbg_axis_beats_sent = r_axis_beats_sent;
    assign dbg_axis_packets_sent = r_axis_packets_sent;

    src_data_path #(
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
        .cfg_channel_reset      (cfg_channel_reset),

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

endmodule : src_data_path_axis
