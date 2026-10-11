// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_to_axi3_wr
// Purpose: AXI4 Full to AXI3 Protocol Converter (WRITE-ONLY)
//
// Description:
//   Converts AXI4 full protocol to AXI3 for WRITE path only by:
//   - Burst chopping: AXI4 bursts longer than 16 beats are split into
//     multiple AXI3 bursts of up to 16 beats each.
//   - Truncating AXI4 AWLEN (8 bits) to AXI3 AWLEN (4 bits) per chunk
//   - Dropping AXI4-specific signals (QOS, REGION)
//   - Mapping AXI4 1-bit AWLOCK to AXI3 2-bit AWLOCK
//     (normal -> 2'b00, exclusive -> 2'b10)
//   - Stamping each W beat with the owning AWID on m_axi3_wid
//   - Forwarding WDATA, WSTRB, WUSER unchanged and forcing WLAST at each
//     chunk boundary
//   - Buffering early W beats that arrive before the matching AW handshake
//     (one full AXI3 burst of storage)
//   - Merging per-chunk B responses using worst-rank order and returning
//     exactly one s_axi B response per AXI4 AW after the last chunk's B
//
//   Standalone write-only implementation. For read conversion, use
//   axi4_to_axi3_rd.sv.
//
//   Key Features:
//   - Write-only: AW, W, B channels only
//   - Per-burst WID stamping so an AXI3 slave can demux by WID
//   - Early-W buffering for AXI4 masters that send W before AW
//   - W segmentation via a chunk-descriptor FIFO pushed at AW acceptance;
//     the descriptor FIFO provides context for beats already buffered in
//     the early-W buffer
//
// Parameters:
//   AXI_ID_WIDTH: Transaction ID width on AXI4/AXI3 side (1-16)
//   AXI_ADDR_WIDTH: Address bus width (12-64)
//   AXI_DATA_WIDTH: Data bus width - must match (32, 64, 128, 256)
//   AXI_USER_WIDTH: User signal width on AXI4/AXI3 side (0-1024)
//
// Limitations:
//   - Data widths must match (no data width conversion)
//   - AXI4 WRAP bursts longer than 16 beats are not supported
//   - Early-W buffer holds at most 16 beats ahead of the matching AW;
//     additional early W is backpressured on s_axi_wready (legal AXI4)
//   - Same-ID AXI4 AWs are serialized (one outstanding per ID); concurrent
//     AWs with different IDs are supported
//   - Write-only: No read path support
//
// Author: RTL Design Sherpa
// Created: 2026-10-10

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_to_axi3_wr #(
    // Width Configuration
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,

    // Calculated Parameters
    localparam int STRB_WIDTH = AXI_DATA_WIDTH / 8
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI4 Write Interface (Input - Full Protocol)
    //==========================================================================

    // Write Address Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_awaddr,
    input  logic [7:0]                  s_axi_awlen,
    input  logic [2:0]                  s_axi_awsize,
    input  logic [1:0]                  s_axi_awburst,
    input  logic                        s_axi_awlock,
    input  logic [3:0]                  s_axi_awcache,
    input  logic [2:0]                  s_axi_awprot,
    input  logic [3:0]                  s_axi_awqos,
    input  logic [3:0]                  s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_awuser,
    input  logic                        s_axi_awvalid,
    output logic                        s_axi_awready,

    // Write Data Channel
    input  logic [AXI_DATA_WIDTH-1:0]   s_axi_wdata,
    input  logic [STRB_WIDTH-1:0]       s_axi_wstrb,
    input  logic                        s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_wuser,
    input  logic                        s_axi_wvalid,
    output logic                        s_axi_wready,

    // Write Response Channel
    output logic [AXI_ID_WIDTH-1:0]     s_axi_bid,
    output logic [1:0]                  s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_buser,
    output logic                        s_axi_bvalid,
    input  logic                        s_axi_bready,

    //==========================================================================
    // Master AXI3 Write Interface (Output - AXI3 Protocol)
    //==========================================================================

    // Write Address Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi3_awid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axi3_awaddr,
    output logic [3:0]                  m_axi3_awlen,
    output logic [2:0]                  m_axi3_awsize,
    output logic [1:0]                  m_axi3_awburst,
    output logic [1:0]                  m_axi3_awlock,
    output logic [3:0]                  m_axi3_awcache,
    output logic [2:0]                  m_axi3_awprot,
    output logic [AXI_USER_WIDTH-1:0]   m_axi3_awuser,
    output logic                        m_axi3_awvalid,
    input  logic                        m_axi3_awready,

    // Write Data Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi3_wid,
    output logic [AXI_DATA_WIDTH-1:0]   m_axi3_wdata,
    output logic [STRB_WIDTH-1:0]       m_axi3_wstrb,
    output logic                        m_axi3_wlast,
    output logic [AXI_USER_WIDTH-1:0]   m_axi3_wuser,
    output logic                        m_axi3_wvalid,
    input  logic                        m_axi3_wready,

    // Write Response Channel
    input  logic [AXI_ID_WIDTH-1:0]     m_axi3_bid,
    input  logic [1:0]                  m_axi3_bresp,
    input  logic [AXI_USER_WIDTH-1:0]   m_axi3_buser,
    input  logic                        m_axi3_bvalid,
    output logic                        m_axi3_bready
);

    //==========================================================================
    // Local Parameters and Typedefs
    //==========================================================================

    localparam int Axi3MaxBeats   = 16;
    localparam int AwQueueDepth   = 4;
    localparam int WBufferDepth   = Axi3MaxBeats;
    localparam int MaxAxi4Beats   = 256;
    localparam int MaxChunksPerAw = (MaxAxi4Beats + Axi3MaxBeats - 1) / Axi3MaxBeats;
    localparam int ChunkFifoDepth = AwQueueDepth * MaxChunksPerAw;
    localparam int NumIds         = 1 << AXI_ID_WIDTH;

    typedef struct packed {
        logic [AXI_ID_WIDTH-1:0]   id;
        logic [AXI_ADDR_WIDTH-1:0] addr;
        logic [7:0]                len;
        logic [2:0]                size;
        logic [1:0]                burst;
        logic                      lock;
        logic [3:0]                cache;
        logic [2:0]                prot;
        logic [AXI_USER_WIDTH-1:0] user;
    } aw_req_t;

    typedef struct packed {
        logic [AXI_DATA_WIDTH-1:0] data;
        logic [STRB_WIDTH-1:0]     strb;
        logic                      last;
        logic [AXI_USER_WIDTH-1:0] user;
    } w_beat_t;

    typedef struct packed {
        logic [AXI_ID_WIDTH-1:0] id;
        logic [4:0]              beats;
    } chunk_desc_t;

    //==========================================================================
    // Internal Signals
    //==========================================================================

    // AW queue and active burst state
    aw_req_t aw_queue[$:AwQueueDepth-1];
    aw_req_t active_aw;
    logic    active_valid;
    // Max AXI4 burst is 256 beats (awlen=255), so remaining beats needs 9 bits.
    logic [8:0]                active_remaining;
    logic [AXI_ADDR_WIDTH-1:0] active_addr;

    // Chunk-descriptor FIFO pushed at AW acceptance; consumed by the W segmenter
    chunk_desc_t desc_fifo[$:ChunkFifoDepth-1];
    chunk_desc_t cur_desc;
    logic        cur_desc_valid;
    logic [4:0]  cur_desc_beats_remaining;

    // Early-W buffering
    w_beat_t w_buffer[$:WBufferDepth-1];

    // Per-ID B merge state
    logic       pending_id_busy [NumIds];
    logic       b_merge_busy    [NumIds];
    logic [7:0] b_merge_chunks_left [NumIds];
    logic [1:0] b_merge_worst   [NumIds];

    // Forwarded B response register
    logic                    b_pending_valid;
    logic [AXI_ID_WIDTH-1:0] b_pending_id;
    logic [1:0]              b_pending_resp;
    logic [AXI_USER_WIDTH-1:0] b_pending_user;

    // Current chunk size (1..16 beats)
    logic [4:0] chunk_beats;

    // Convenience aliases
    logic w_handshake;
    logic m_w_handshake;
    logic [AXI_ID_WIDTH-1:0] b_id;

    //==========================================================================
    // Burst Length Assertion
    //==========================================================================

    // AXI3 supports up to 16 beats. INCR/FIXED bursts are chopped; WRAP bursts
    // longer than 16 beats are unsupported (non-goal 6.3 of the spec).
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            // No check during reset
        end else begin
            if (s_axi_awvalid && s_axi_awready &&
                (s_axi_awburst == 2'b10) && (s_axi_awlen > 8'd15))
                $error("ASSERT_A3_WR_WRAP_LEN16: AXI4 WRAP burst length %0d exceeds AXI3 maximum of 16 beats", s_axi_awlen);
        end
    )

    //==========================================================================
    // Slave AW Channel Accept Logic
    //==========================================================================

    assign s_axi_awready = (aw_queue.size() < AwQueueDepth) &&
                           !pending_id_busy[s_axi_awid] &&
                           ((desc_fifo.size() + MaxChunksPerAw) <= ChunkFifoDepth);

    //==========================================================================
    // Master AW Channel Chunk Issuance
    //==========================================================================

    assign chunk_beats = (active_remaining > 9'(Axi3MaxBeats)) ?
                         5'(Axi3MaxBeats) : 5'(active_remaining);

    assign m_axi3_awid    = active_valid ? active_aw.id    : '0;
    assign m_axi3_awaddr  = active_valid ? active_addr     : '0;
    assign m_axi3_awlen   = active_valid ? (4'(chunk_beats - 5'd1)) : '0;
    assign m_axi3_awsize  = active_valid ? active_aw.size  : '0;
    assign m_axi3_awburst = active_valid ? active_aw.burst : '0;
    assign m_axi3_awlock  = active_valid ? (active_aw.lock ? 2'b10 : 2'b00) : '0;
    assign m_axi3_awcache = active_valid ? active_aw.cache : '0;
    assign m_axi3_awprot  = active_valid ? active_aw.prot  : '0;
    assign m_axi3_awuser  = active_valid ? active_aw.user  : '0;
    assign m_axi3_awvalid = active_valid;

    //==========================================================================
    // Write Data Channel: Segmentation + WID Stamping
    //==========================================================================

    assign w_handshake   = s_axi_wvalid && s_axi_wready;
    assign m_w_handshake = m_axi3_wvalid && m_axi3_wready;

    // Accept W beats as long as the early-W buffer has space. When the buffer
    // is full s_axi_wready is deasserted, which is the legal AXI4 mechanism
    // for throttling early W data.
    assign s_axi_wready = (w_buffer.size() < WBufferDepth);

    // Forward buffered W beats only when a chunk descriptor is available (so
    // WID and beat count are known). WLAST is forced at descriptor expiry,
    // producing a legal AXI3 WLAST for every chopped burst.
    assign m_axi3_wid   = cur_desc_valid ? cur_desc.id : '0;
    assign m_axi3_wdata = w_buffer[0].data;
    assign m_axi3_wstrb = w_buffer[0].strb;
    assign m_axi3_wlast = cur_desc_valid && (cur_desc_beats_remaining == 5'd1);
    assign m_axi3_wuser = w_buffer[0].user;
    assign m_axi3_wvalid = cur_desc_valid && (w_buffer.size() > 0);

    //==========================================================================
    // AXI3 to AXI4 Write Response Channel Merge
    //==========================================================================

    assign b_id = m_axi3_bid;

    assign s_axi_bvalid = b_pending_valid;
    assign s_axi_bid    = b_pending_valid ? b_pending_id   : '0;
    assign s_axi_bresp  = b_pending_valid ? b_pending_resp : '0;
    assign s_axi_buser  = b_pending_valid ? b_pending_user : '0;

    always_comb begin
        m_axi3_bready = 1'b0;
        for (int i = 0; i < NumIds; i++) begin
            if (b_merge_busy[i] && (b_merge_chunks_left[i] > 0)) begin
                if ((b_merge_chunks_left[i] > 1) || !b_pending_valid) begin
                    m_axi3_bready = 1'b1;
                end
            end
        end
    end

    //==========================================================================
    // Sequential State: AW Queue, Chunk Scheduler, W Segmenter, B Merge
    //==========================================================================

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            aw_queue.delete();
            desc_fifo.delete();
            w_buffer.delete();
            active_valid           <= 1'b0;
            active_aw              <= '0;
            active_remaining       <= '0;
            active_addr            <= '0;
            cur_desc_valid         <= 1'b0;
            cur_desc               <= '0;
            cur_desc_beats_remaining <= '0;
            b_pending_valid        <= 1'b0;
            b_pending_id           <= '0;
            b_pending_resp         <= '0;
            b_pending_user         <= '0;
            for (int i = 0; i < NumIds; i++) begin
                pending_id_busy[i]     <= 1'b0;
                b_merge_busy[i]        <= 1'b0;
                b_merge_chunks_left[i] <= '0;
                b_merge_worst[i]       <= 2'b00;
            end
        end else begin
            // Accept a new slave AW into the queue and push its chunk
            // descriptors. The descriptors are consumed by the W segmenter and
            // may be used immediately if W beats have already been buffered.
            if (s_axi_awvalid && s_axi_awready) begin
                aw_req_t push;
                push.id    = s_axi_awid;
                push.addr  = s_axi_awaddr;
                push.len   = s_axi_awlen;
                push.size  = s_axi_awsize;
                push.burst = s_axi_awburst;
                push.lock  = s_axi_awlock;
                push.cache = s_axi_awcache;
                push.prot  = s_axi_awprot;
                push.user  = s_axi_awuser;
                aw_queue.push_back(push);

                pending_id_busy[s_axi_awid] <= 1'b1;
                b_merge_busy[s_axi_awid]    <= 1'b1;
                b_merge_worst[s_axi_awid]   <= 2'b00;

                begin
                    logic [8:0] total_beats;
                    logic [7:0] total_chunks;
                    int         chunk_idx;
                    total_beats = 9'(s_axi_awlen) + 9'd1;
                    total_chunks = 8'(((total_beats + 9'(Axi3MaxBeats) - 9'd1) >> 4));
                    b_merge_chunks_left[s_axi_awid] <= total_chunks;

                    for (chunk_idx = 0; chunk_idx < total_chunks; chunk_idx++) begin
                        chunk_desc_t desc;
                        desc.id = s_axi_awid;
                        if ((total_beats - (9'(chunk_idx) << 4)) > 9'(Axi3MaxBeats))
                            desc.beats = 5'(Axi3MaxBeats);
                        else
                            desc.beats = 5'(total_beats - (9'(chunk_idx) << 4));
                        desc_fifo.push_back(desc);
                    end
                end
            end

            // Start chunking the next queued request.
            if (!active_valid && (aw_queue.size() > 0)) begin
                aw_req_t popped;
                popped = aw_queue.pop_front();
                active_aw        <= popped;
                active_remaining <= 9'(popped.len) + 9'd1;
                active_addr      <= popped.addr;
                active_valid     <= 1'b1;
            end

            // Issue a chunk when the master AW handshake occurs.
            if (active_valid && m_axi3_awvalid && m_axi3_awready) begin
                active_remaining <= active_remaining - 9'(chunk_beats);
                if (active_aw.burst == 2'b01) begin // INCR
                    active_addr <= active_addr +
                                   (AXI_ADDR_WIDTH'(chunk_beats) << active_aw.size);
                end
                if (active_remaining <= 9'(Axi3MaxBeats)) begin
                    active_valid <= 1'b0;
                end
            end

            // Buffer an incoming W beat.
            if (w_handshake) begin
                w_beat_t beat;
                beat.data = s_axi_wdata;
                beat.strb = s_axi_wstrb;
                beat.last = s_axi_wlast;
                beat.user = s_axi_wuser;
                w_buffer.push_back(beat);
            end

            // Load the next chunk descriptor when the current one expires.
            if (!cur_desc_valid && (desc_fifo.size() > 0)) begin
                chunk_desc_t d;
                d = desc_fifo.pop_front();
                cur_desc_valid         <= 1'b1;
                cur_desc               <= d;
                cur_desc_beats_remaining <= d.beats;
            end

            // Forward a buffered W beat to the AXI3 master.
            if (m_w_handshake) begin
                w_buffer.pop_front();
                if (cur_desc_valid) begin
                    if (cur_desc_beats_remaining == 5'd1) begin
                        cur_desc_valid <= 1'b0;
                    end else begin
                        cur_desc_beats_remaining <= cur_desc_beats_remaining - 5'd1;
                    end
                end
            end

            // Update merge state on each chunk's B response.
            if (m_axi3_bvalid && m_axi3_bready) begin
                if (b_merge_busy[b_id] && (b_merge_chunks_left[b_id] > 0)) begin
                    logic [1:0] new_worst;
                    new_worst = (m_axi3_bresp > b_merge_worst[b_id]) ?
                                m_axi3_bresp : b_merge_worst[b_id];
                    b_merge_worst[b_id] <= new_worst;

                    if (b_merge_chunks_left[b_id] == 8'd1) begin
                        b_merge_chunks_left[b_id] <= '0;
                        b_pending_valid <= 1'b1;
                        b_pending_id    <= b_id;
                        b_pending_resp  <= new_worst;
                        b_pending_user  <= m_axi3_buser;
                    end else begin
                        b_merge_chunks_left[b_id] <= b_merge_chunks_left[b_id] - 8'd1;
                    end
                end
            end

            // Forward the merged B response to the AXI4 slave.
            if (s_axi_bvalid && s_axi_bready) begin
                b_pending_valid             <= 1'b0;
                b_merge_busy[b_pending_id]  <= 1'b0;
                b_merge_worst[b_pending_id] <= 2'b00;
                pending_id_busy[b_pending_id] <= 1'b0;
            end
        end
    )

endmodule : axi4_to_axi3_wr
