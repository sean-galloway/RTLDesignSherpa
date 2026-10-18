// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi4_to_axi3_rd
// Purpose: AXI4 Full to AXI3 Protocol Converter (READ-ONLY)
//
// Description:
//   Converts AXI4 full protocol to AXI3 for READ path only by:
//   - Burst chopping: AXI4 bursts longer than 16 beats are split into
//     multiple AXI3 bursts of up to 16 beats each.
//   - Truncating AXI4 ARLEN (8 bits) to AXI3 ARLEN (4 bits) per chunk
//   - Dropping AXI4-specific signals (QOS, REGION)
//   - Mapping AXI4 1-bit ARLOCK to AXI3 2-bit ARLOCK
//     (normal -> 2'b00, exclusive -> 2'b01)
//   - Preserving ID, data, and user information
//   - Merging per-chunk RRESP using worst-rank order and suppressing
//     intermediate RLAST beats so the AXI4 master sees a single burst.
//
//   Standalone read-only implementation. For write conversion, use
//   axi4_to_axi3_wr.sv.
//
//   Key Features:
//   - Read-only: AR, R channels only
//   - Per-ID merge state so concurrent chopped bursts never cross
//   - Pipelined chunk issuance: chunk n+1 AR can handshake while chunk n
//     R beats are still streaming
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
//   - Read-only: No write path support
//
// Author: RTL Design Sherpa
// Created: 2026-10-10

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_to_axi3_rd #(
    // Width Configuration
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1
) (
    // Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,

    //==========================================================================
    // Slave AXI4 Read Interface (Input - Full Protocol)
    //==========================================================================

    // Read Address Channel
    input  logic [AXI_ID_WIDTH-1:0]     s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]   s_axi_araddr,
    input  logic [7:0]                  s_axi_arlen,
    input  logic [2:0]                  s_axi_arsize,
    input  logic [1:0]                  s_axi_arburst,
    input  logic                        s_axi_arlock,
    input  logic [3:0]                  s_axi_arcache,
    input  logic [2:0]                  s_axi_arprot,
    input  logic [3:0]                  s_axi_arqos,
    input  logic [3:0]                  s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]   s_axi_aruser,
    input  logic                        s_axi_arvalid,
    output logic                        s_axi_arready,

    // Read Data Channel
    output logic [AXI_ID_WIDTH-1:0]     s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]   s_axi_rdata,
    output logic [1:0]                  s_axi_rresp,
    output logic                        s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]   s_axi_ruser,
    output logic                        s_axi_rvalid,
    input  logic                        s_axi_rready,

    //==========================================================================
    // Master AXI3 Read Interface (Output - AXI3 Protocol)
    //==========================================================================

    // Read Address Channel
    output logic [AXI_ID_WIDTH-1:0]     m_axi3_arid,
    output logic [AXI_ADDR_WIDTH-1:0]   m_axi3_araddr,
    output logic [3:0]                  m_axi3_arlen,
    output logic [2:0]                  m_axi3_arsize,
    output logic [1:0]                  m_axi3_arburst,
    output logic [1:0]                  m_axi3_arlock,
    output logic [3:0]                  m_axi3_arcache,
    output logic [2:0]                  m_axi3_arprot,
    output logic [AXI_USER_WIDTH-1:0]   m_axi3_aruser,
    output logic                        m_axi3_arvalid,
    input  logic                        m_axi3_arready,

    // Read Data Channel
    input  logic [AXI_ID_WIDTH-1:0]     m_axi3_rid,
    input  logic [AXI_DATA_WIDTH-1:0]   m_axi3_rdata,
    input  logic [1:0]                  m_axi3_rresp,
    input  logic                        m_axi3_rlast,
    input  logic [AXI_USER_WIDTH-1:0]   m_axi3_ruser,
    input  logic                        m_axi3_rvalid,
    output logic                        m_axi3_rready
);

    //==========================================================================
    // Local Parameters and Typedefs
    //==========================================================================

    localparam int Axi3MaxBeats = 16;
    localparam int ArQueueDepth = 4;
    localparam int NumIds       = 1 << AXI_ID_WIDTH;

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
    } ar_req_t;

    //==========================================================================
    // Internal Signals
    //==========================================================================

    // Slave AR queue (gaxi_fifo_sync) and per-ID outstanding tracking
    logic    arq_wr_ready, arq_rd_valid, arq_rd_ready;
    ar_req_t arq_wr_data, arq_rd_data;
    logic    ar_handshake;
    logic    ar_bypass;       // idle and the queue empty: start the new AR at once
    logic    ar_load;
    ar_req_t ar_load_data;
    logic    pending_id_busy [NumIds];

    // Active request being chunked out to the AXI3 master
    ar_req_t active_req;
    logic    active_valid;
    // Max AXI4 burst is 256 beats (arlen=255), so remaining beats needs 9 bits.
    logic [8:0]                active_remaining;
    logic [AXI_ADDR_WIDTH-1:0] active_addr;
    logic [7:0]                active_chunks_total;
    logic [7:0]                active_chunks_issued;

    // Per-ID merge state for response merging
    logic       merge_busy [NumIds];
    logic [7:0] merge_chunks_left [NumIds];
    logic [1:0] merge_worst [NumIds];

    // Current chunk size (1..16 beats)
    logic [4:0] chunk_beats;

    // Convenience aliases for the current R beat
    logic [AXI_ID_WIDTH-1:0] r_id;
    logic [1:0]              merged_final_resp;

    //==========================================================================
    // Burst Length Assertion
    //==========================================================================

    // AXI3 supports up to 16 beats. INCR/FIXED bursts are chopped; WRAP bursts
    // longer than 16 beats are unsupported (non-goal 6.3 of the spec).
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            // No check during reset
        end else begin
            if (s_axi_arvalid && s_axi_arready &&
                (s_axi_arburst == 2'b10) && (s_axi_arlen > 8'd15))
                $error("ASSERT_A3_RD_WRAP_LEN16: AXI4 WRAP burst length %0d exceeds AXI3 maximum of 16 beats", s_axi_arlen);
        end
    )

    //==========================================================================
    // Slave AR Channel Accept Logic
    //==========================================================================

    assign s_axi_arready = arq_wr_ready && !pending_id_busy[s_axi_arid];
    assign ar_handshake  = s_axi_arvalid && s_axi_arready;

    assign arq_wr_data.id    = s_axi_arid;
    assign arq_wr_data.addr  = s_axi_araddr;
    assign arq_wr_data.len   = s_axi_arlen;
    assign arq_wr_data.size  = s_axi_arsize;
    assign arq_wr_data.burst = s_axi_arburst;
    assign arq_wr_data.lock  = s_axi_arlock;
    assign arq_wr_data.cache = s_axi_arcache;
    assign arq_wr_data.prot  = s_axi_arprot;
    assign arq_wr_data.user  = s_axi_aruser;

    gaxi_fifo_sync #(
        .DATA_WIDTH ($bits(ar_req_t)),
        .DEPTH      (ArQueueDepth)
    ) u_ar_queue (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (ar_handshake && !ar_bypass),
        .wr_ready    (arq_wr_ready),
        .wr_data     (arq_wr_data),
        .rd_ready    (arq_rd_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (arq_rd_valid),
        .rd_data     (arq_rd_data)
    );

    // Start chunking the next queued request once the active one is done.
    // An AR arriving while idle with the queue empty bypasses it, so it
    // starts the edge it is accepted, as it did before the queue was a FIFO
    // (a same-ID read waits on the previous one's last R, so every cycle
    // here is a cycle per read). Order holds: the bypass needs an empty queue.
    assign arq_rd_ready = !active_valid;
    assign ar_bypass    = ar_handshake && !active_valid && !arq_rd_valid;
    assign ar_load      = (arq_rd_valid && arq_rd_ready) || ar_bypass;
    assign ar_load_data = arq_rd_valid ? arq_rd_data : arq_wr_data;

    //==========================================================================
    // Master AR Channel Chunk Issuance
    //==========================================================================

    assign chunk_beats = (active_remaining > 9'(Axi3MaxBeats)) ?
                         5'(Axi3MaxBeats) : 5'(active_remaining);

    assign m_axi3_arid    = active_valid ? active_req.id    : '0;
    assign m_axi3_araddr  = active_valid ? active_addr      : '0;
    assign m_axi3_arlen   = active_valid ? (4'(chunk_beats - 5'd1)) : '0;
    assign m_axi3_arsize  = active_valid ? active_req.size  : '0;
    assign m_axi3_arburst = active_valid ? active_req.burst : '0;
    assign m_axi3_arlock  = active_valid ? (active_req.lock ? 2'b01 : 2'b00) : '0;
    assign m_axi3_arcache = active_valid ? active_req.cache : '0;
    assign m_axi3_arprot  = active_valid ? active_req.prot  : '0;
    assign m_axi3_aruser  = active_valid ? active_req.user  : '0;
    assign m_axi3_arvalid = active_valid;

    //==========================================================================
    // AXI3 to AXI4 Read Data Channel Merge
    //==========================================================================

    assign s_axi_rid    = m_axi3_rid;
    assign s_axi_rdata  = m_axi3_rdata;
    assign s_axi_ruser  = m_axi3_ruser;
    assign s_axi_rvalid = m_axi3_rvalid;
    assign m_axi3_rready = s_axi_rready;

    assign r_id = m_axi3_rid;
    assign merged_final_resp = (m_axi3_rresp > merge_worst[r_id]) ?
                               m_axi3_rresp : merge_worst[r_id];

    always_comb begin
        s_axi_rresp = m_axi3_rresp;
        s_axi_rlast = 1'b0;
        if (m_axi3_rvalid && m_axi3_rlast &&
            merge_busy[r_id] && (merge_chunks_left[r_id] == 8'd1)) begin
            s_axi_rresp = merged_final_resp;
            s_axi_rlast = 1'b1;
        end
    end

    //==========================================================================
    // Sequential State: AR Queue, Chunk Scheduler, and Per-ID Merge State
    //==========================================================================

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            active_valid      <= 1'b0;
            active_req        <= '0;
            active_remaining  <= '0;
            active_addr       <= '0;
            active_chunks_total <= '0;
            active_chunks_issued <= '0;
            for (int i = 0; i < NumIds; i++) begin
                pending_id_busy[i]  <= 1'b0;
                merge_busy[i]       <= 1'b0;
                merge_chunks_left[i] <= '0;
                merge_worst[i]      <= 2'b00;
            end
        end else begin
            // Accept a new slave AR into the queue (above).
            if (ar_handshake) begin
                pending_id_busy[s_axi_arid] <= 1'b1;
            end

            // Start chunking the next queued request.
            if (ar_load) begin
                active_req          <= ar_load_data;
                active_remaining    <= 9'(ar_load_data.len) + 9'd1;
                active_addr         <= ar_load_data.addr;
                active_chunks_total <= 8'(((( {1'b0, ar_load_data.len} + 9'd1) + 9'd15) >> 4));
                active_chunks_issued <= '0;
                active_valid        <= 1'b1;
            end

            // Issue a chunk when the master AR handshake occurs.
            if (active_valid && m_axi3_arvalid && m_axi3_arready) begin
                if (active_chunks_issued == '0) begin
                    merge_busy[active_req.id]        <= 1'b1;
                    merge_chunks_left[active_req.id] <= active_chunks_total;
                    merge_worst[active_req.id]       <= 2'b00;
                end

                active_remaining <= active_remaining - 9'(chunk_beats);
                if (active_req.burst == 2'b01) begin // INCR
                    active_addr <= active_addr +
                                   (AXI_ADDR_WIDTH'(chunk_beats) << active_req.size);
                end
                active_chunks_issued <= active_chunks_issued + 8'd1;

                if (active_remaining <= 9'(Axi3MaxBeats)) begin
                    active_valid <= 1'b0;
                end
            end

            // Update merge state on each chunk's last R beat.
            if (m_axi3_rvalid && m_axi3_rready && m_axi3_rlast) begin
                merge_worst[r_id] <= merged_final_resp;
                if (merge_busy[r_id] && (merge_chunks_left[r_id] == 8'd1)) begin
                    merge_busy[r_id]       <= 1'b0;
                    merge_chunks_left[r_id] <= '0;
                    pending_id_busy[r_id]  <= 1'b0;
                end else if (merge_busy[r_id]) begin
                    merge_chunks_left[r_id] <= merge_chunks_left[r_id] - 8'd1;
                end
            end
        end
    )

endmodule : axi4_to_axi3_rd
