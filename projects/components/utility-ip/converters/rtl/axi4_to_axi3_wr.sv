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
//     (normal -> 2'b00, exclusive -> 2'b01)
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
//   - W segmentation via a descriptor FIFO pushed at AW acceptance (one
//     entry per AXI4 AW: its ID and total beats); the segmenter cuts it into
//     AXI3 bursts of up to 16 and gives context to beats already buffered in
//     the early-W buffer
//   - All storage is gaxi_fifo_sync (rtl/amba/gaxi): AW queue, descriptor
//     FIFO, early-W buffer
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
    localparam int DescFifoDepth  = AwQueueDepth;
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
        logic [AXI_USER_WIDTH-1:0] user;
    } w_beat_t;   // WLAST is not stored: it is regenerated per AXI3 burst

    // One per AXI4 AW: the W segmenter cuts `beats` into AXI3 bursts.
    typedef struct packed {
        logic [AXI_ID_WIDTH-1:0] id;
        logic [8:0]              beats;
    } chunk_desc_t;

    //==========================================================================
    // Internal Signals
    //==========================================================================

    // AW queue and active burst state
    logic    awq_wr_ready, awq_rd_valid, awq_rd_ready;
    aw_req_t awq_wr_data, awq_rd_data;
    aw_req_t active_aw;
    logic    active_valid;
    // Max AXI4 burst is 256 beats (awlen=255), so remaining beats needs 9 bits.
    logic [8:0]                active_remaining;
    logic [AXI_ADDR_WIDTH-1:0] active_addr;

    // Descriptor FIFO pushed at AW acceptance; consumed by the W segmenter
    logic        descq_wr_ready, descq_rd_valid, descq_rd_ready;
    chunk_desc_t descq_wr_data, descq_rd_data;
    logic [AXI_ID_WIDTH-1:0] cur_desc_id;
    logic        cur_desc_valid;
    logic [8:0]  cur_desc_beats_remaining;    // in the whole AXI4 burst
    logic [4:0]  cur_chunk_beats_remaining;   // in the current AXI3 burst

    // Early-W buffering
    logic        wbuf_rd_valid, wbuf_rd_ready;
    w_beat_t     wbuf_wr_data, wbuf_rd_data;

    logic        aw_handshake;
    // Idle with the FIFO empty: the new AW (descriptor) loads at once
    logic        aw_bypass, aw_load, desc_bypass, desc_load;
    aw_req_t     aw_load_data;
    chunk_desc_t desc_load_data;

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

    assign s_axi_awready = awq_wr_ready && descq_wr_ready &&
                           !pending_id_busy[s_axi_awid];
    assign aw_handshake  = s_axi_awvalid && s_axi_awready;

    assign awq_wr_data.id    = s_axi_awid;
    assign awq_wr_data.addr  = s_axi_awaddr;
    assign awq_wr_data.len   = s_axi_awlen;
    assign awq_wr_data.size  = s_axi_awsize;
    assign awq_wr_data.burst = s_axi_awburst;
    assign awq_wr_data.lock  = s_axi_awlock;
    assign awq_wr_data.cache = s_axi_awcache;
    assign awq_wr_data.prot  = s_axi_awprot;
    assign awq_wr_data.user  = s_axi_awuser;

    assign descq_wr_data.id    = s_axi_awid;
    assign descq_wr_data.beats = 9'(s_axi_awlen) + 9'd1;

    gaxi_fifo_sync #(
        .DATA_WIDTH ($bits(aw_req_t)),
        .DEPTH      (AwQueueDepth)
    ) u_aw_queue (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (aw_handshake && !aw_bypass),
        .wr_ready    (awq_wr_ready),
        .wr_data     (awq_wr_data),
        .rd_ready    (awq_rd_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (awq_rd_valid),
        .rd_data     (awq_rd_data)
    );

    gaxi_fifo_sync #(
        .DATA_WIDTH ($bits(chunk_desc_t)),
        .DEPTH      (DescFifoDepth)
    ) u_desc_fifo (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (aw_handshake && !desc_bypass),
        .wr_ready    (descq_wr_ready),
        .wr_data     (descq_wr_data),
        .rd_ready    (descq_rd_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (descq_rd_valid),
        .rd_data     (descq_rd_data)
    );

    // Start chunking the next queued request once the active one is done;
    // load the next descriptor once the current one is done. An AW arriving
    // while a stage is idle with its FIFO empty bypasses that FIFO, so it
    // takes effect the edge it is accepted, as it did before the queues were
    // FIFOs (a same-ID write waits on the previous one's B, so every cycle
    // here is a cycle per write). Order holds: a bypass needs an empty FIFO.
    assign awq_rd_ready   = !active_valid;
    assign aw_bypass      = aw_handshake && !active_valid && !awq_rd_valid;
    assign aw_load        = (awq_rd_valid && awq_rd_ready) || aw_bypass;
    assign aw_load_data   = awq_rd_valid ? awq_rd_data : awq_wr_data;

    assign descq_rd_ready = !cur_desc_valid;
    assign desc_bypass    = aw_handshake && !cur_desc_valid && !descq_rd_valid;
    assign desc_load      = (descq_rd_valid && descq_rd_ready) || desc_bypass;
    assign desc_load_data = descq_rd_valid ? descq_rd_data : descq_wr_data;

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
    assign m_axi3_awlock  = active_valid ? (active_aw.lock ? 2'b01 : 2'b00) : '0;
    assign m_axi3_awcache = active_valid ? active_aw.cache : '0;
    assign m_axi3_awprot  = active_valid ? active_aw.prot  : '0;
    assign m_axi3_awuser  = active_valid ? active_aw.user  : '0;
    assign m_axi3_awvalid = active_valid;

    //==========================================================================
    // Write Data Channel: Segmentation + WID Stamping
    //==========================================================================

    assign m_w_handshake = m_axi3_wvalid && m_axi3_wready;

    // Accept W beats as long as the early-W buffer has space. When the buffer
    // is full s_axi_wready is deasserted, which is the legal AXI4 mechanism
    // for throttling early W data.
    // s_axi_wlast is not stored: the descriptor's beat count places WLAST on
    // every AXI3 burst, the AXI4 one included.
    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_wlast;
    assign unused_wlast = s_axi_wlast;
    /* verilator lint_on UNUSEDSIGNAL */

    assign wbuf_wr_data.data = s_axi_wdata;
    assign wbuf_wr_data.strb = s_axi_wstrb;
    assign wbuf_wr_data.user = s_axi_wuser;

    gaxi_fifo_sync #(
        .DATA_WIDTH ($bits(w_beat_t)),
        .DEPTH      (WBufferDepth)
    ) u_w_buffer (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (s_axi_wvalid),
        .wr_ready    (s_axi_wready),
        .wr_data     (wbuf_wr_data),
        .rd_ready    (wbuf_rd_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (wbuf_rd_valid),
        .rd_data     (wbuf_rd_data)
    );
    assign wbuf_rd_ready = cur_desc_valid && m_axi3_wready;

    // Forward buffered W beats only when a chunk descriptor is available (so
    // WID and beat count are known). WLAST is forced at descriptor expiry,
    // producing a legal AXI3 WLAST for every chopped burst.
    assign m_axi3_wid   = cur_desc_valid ? cur_desc_id : '0;
    assign m_axi3_wdata = wbuf_rd_data.data;
    assign m_axi3_wstrb = wbuf_rd_data.strb;
    assign m_axi3_wlast = cur_desc_valid && (cur_chunk_beats_remaining == 5'd1);
    assign m_axi3_wuser = wbuf_rd_data.user;
    assign m_axi3_wvalid = cur_desc_valid && wbuf_rd_valid;

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
            active_valid           <= 1'b0;
            active_aw              <= '0;
            active_remaining       <= '0;
            active_addr            <= '0;
            cur_desc_valid         <= 1'b0;
            cur_desc_id            <= '0;
            cur_desc_beats_remaining <= '0;
            cur_chunk_beats_remaining <= '0;
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
            // Accept a new slave AW: the AW queue and the descriptor FIFO
            // take it (above); here, its per-ID B merge state. The descriptor
            // may be used at once if W beats have already been buffered.
            if (aw_handshake) begin
                pending_id_busy[s_axi_awid] <= 1'b1;
                b_merge_busy[s_axi_awid]    <= 1'b1;
                b_merge_worst[s_axi_awid]   <= 2'b00;

                // AXI3 bursts this AW is cut into: ceil((awlen+1) / 16)
                b_merge_chunks_left[s_axi_awid] <=
                    8'((9'(s_axi_awlen) + 9'd1 + 9'(Axi3MaxBeats) - 9'd1) >> 4);
            end

            // Start chunking the next queued request.
            if (aw_load) begin
                active_aw        <= aw_load_data;
                active_remaining <= 9'(aw_load_data.len) + 9'd1;
                active_addr      <= aw_load_data.addr;
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

            // Load the next descriptor when the current one expires.
            if (desc_load) begin
                cur_desc_valid            <= 1'b1;
                cur_desc_id               <= desc_load_data.id;
                cur_desc_beats_remaining  <= desc_load_data.beats;
                cur_chunk_beats_remaining <= (desc_load_data.beats > 9'(Axi3MaxBeats)) ?
                                             5'(Axi3MaxBeats) : 5'(desc_load_data.beats);
            end

            // Forward a buffered W beat to the AXI3 master. WLAST closes each
            // AXI3 burst; the next one of the same AW starts on the next beat.
            if (m_w_handshake) begin
                cur_desc_beats_remaining <= cur_desc_beats_remaining - 9'd1;
                if (cur_desc_beats_remaining == 9'd1) begin
                    cur_desc_valid <= 1'b0;
                end else if (cur_chunk_beats_remaining == 5'd1) begin
                    cur_chunk_beats_remaining <=
                        ((cur_desc_beats_remaining - 9'd1) > 9'(Axi3MaxBeats)) ?
                        5'(Axi3MaxBeats) : 5'(cur_desc_beats_remaining - 9'd1);
                end else begin
                    cur_chunk_beats_remaining <= cur_chunk_beats_remaining - 5'd1;
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
