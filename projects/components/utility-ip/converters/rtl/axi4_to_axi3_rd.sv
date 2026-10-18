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
//   - One AR per cycle, and no AR storage for unchopped reads: they pass
//     straight to the AXI3 port, so no granted request queues behind the
//     crossbar's arbiter; only a chopped read is registered while it issues
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
//   - Up to MAX_OUTSTANDING reads in flight; a chopped read (ARLEN > 15)
//     waits for its ID to drain, since its chunks' RLASTs are merged into one
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
    parameter int AXI_USER_WIDTH    = 1,
    // Reads in flight, all IDs together
    parameter int MAX_OUTSTANDING   = 32
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
    localparam int NumIds       = 1 << AXI_ID_WIDTH;
    localparam int CntW         = $clog2(MAX_OUTSTANDING + 1);

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

    // Outstanding state. Unchopped reads (ARLEN <= 15) need no per-ID check:
    // the AXI3 slave returns same-ID reads in order, each with its own RLAST,
    // and one queued behind a chopped read of its ID comes back after the
    // chopped read's last chunk. A chopped read waits for its ID to drain
    // (an unchopped read ahead of it would otherwise be counted as one of its
    // chunks). So only the chopped path -- registered -- looks an ID up;
    // the pass-through path checks one total count.
    logic [CntW-1:0] id_count [NumIds];
    logic            id_chop  [NumIds];
    logic [CntW-1:0] total_count;
    logic            total_full;

    // Active request being chunked out to the AXI3 master: a chopped read
    // only. An unchopped AR passes straight through to the AXI3 port (the
    // converter holds no granted request behind the crossbar's arbiter, so
    // round-robin at the slave is not skewed by a queue here).
    ar_req_t active_req;
    logic    active_valid;
    // Max AXI4 burst is 256 beats (arlen=255), so remaining beats needs 9 bits.
    logic [8:0]                active_remaining;
    logic [AXI_ADDR_WIDTH-1:0] active_addr;

    // Per-ID merge state of a chopped read
    logic [7:0] merge_chunks_left [NumIds];
    logic [1:0] merge_worst [NumIds];

    // Current chunk size (1..16 beats)
    logic [4:0] chunk_beats;
    logic       ar_chop;          // the incoming AR is longer than 16 beats
    logic       ar_id_ok;         // its ID can take it
    logic       ar_last_issue;    // the active request issues its last chunk
    logic       ar_handshake;
    logic       ar_direct;        // an unchopped AR offered straight to the port

    // Convenience aliases for the current R beat
    logic [AXI_ID_WIDTH-1:0] r_id;
    logic                    r_last_hs;
    logic                    r_txn_done;   // this RLAST ends an AXI4 read
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

    assign chunk_beats = (active_remaining > 9'(Axi3MaxBeats)) ?
                         5'(Axi3MaxBeats) : 5'(active_remaining);

    assign ar_last_issue = active_valid && m_axi3_arready &&
                           (active_remaining <= 9'(Axi3MaxBeats));
    assign ar_chop       = (s_axi_arlen > 8'd15);
    assign total_full    = (total_count == CntW'(MAX_OUTSTANDING));
    assign ar_id_ok      = !total_full &&
                           (!ar_chop || (!id_chop[s_axi_arid] && (id_count[s_axi_arid] == '0)));
    // Idle: an unchopped AR goes straight to the port and is accepted with
    // it; a chopped one is taken into the active register. While a chopped
    // read issues its chunks, new ARs wait (one cycle after a 17+ beat read).
    assign ar_direct     = !active_valid && s_axi_arvalid && !ar_chop && !total_full;
    assign s_axi_arready = !active_valid && ar_id_ok && (ar_chop || m_axi3_arready);
    assign ar_handshake  = s_axi_arvalid && s_axi_arready;

    //==========================================================================
    // Master AR Channel Chunk Issuance
    //==========================================================================

    assign m_axi3_arid    = active_valid ? active_req.id    : s_axi_arid;
    assign m_axi3_araddr  = active_valid ? active_addr      : s_axi_araddr;
    assign m_axi3_arlen   = active_valid ? (4'(chunk_beats - 5'd1)) : s_axi_arlen[3:0];
    assign m_axi3_arsize  = active_valid ? active_req.size  : s_axi_arsize;
    assign m_axi3_arburst = active_valid ? active_req.burst : s_axi_arburst;
    assign m_axi3_arlock  = (active_valid ? active_req.lock : s_axi_arlock) ? 2'b01 : 2'b00;
    assign m_axi3_arcache = active_valid ? active_req.cache : s_axi_arcache;
    assign m_axi3_arprot  = active_valid ? active_req.prot  : s_axi_arprot;
    assign m_axi3_aruser  = active_valid ? active_req.user  : s_axi_aruser;
    assign m_axi3_arvalid = active_valid || ar_direct;

    //==========================================================================
    // AXI3 to AXI4 Read Data Channel Merge
    //==========================================================================

    assign s_axi_rid    = m_axi3_rid;
    assign s_axi_rdata  = m_axi3_rdata;
    assign s_axi_ruser  = m_axi3_ruser;
    assign s_axi_rvalid = m_axi3_rvalid;
    assign m_axi3_rready = s_axi_rready;

    assign r_id       = m_axi3_rid;
    assign r_last_hs  = m_axi3_rvalid && m_axi3_rready && m_axi3_rlast;
    assign r_txn_done = !id_chop[r_id] || (merge_chunks_left[r_id] == 8'd1);
    assign merged_final_resp = (m_axi3_rresp > merge_worst[r_id]) ?
                               m_axi3_rresp : merge_worst[r_id];

    always_comb begin
        s_axi_rresp = m_axi3_rresp;
        s_axi_rlast = m_axi3_rlast;
        if (id_chop[r_id]) begin
            // A chopped read: one RLAST, on its last chunk, with the worst
            // RRESP of every chunk.
            s_axi_rlast = m_axi3_rlast && (merge_chunks_left[r_id] == 8'd1);
            if (s_axi_rlast)
                s_axi_rresp = merged_final_resp;
        end
    end

    //==========================================================================
    // Sequential State: Active Request, Chunk Scheduler, Per-ID State
    //==========================================================================

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            active_valid      <= 1'b0;
            active_req        <= '0;
            active_remaining  <= '0;
            active_addr       <= '0;
            total_count       <= '0;
            for (int i = 0; i < NumIds; i++) begin
                id_count[i]          <= '0;
                id_chop[i]           <= 1'b0;
                merge_chunks_left[i] <= '0;
                merge_worst[i]       <= 2'b00;
            end
        end else begin
            // Issue a chunk when the master AR handshake occurs.
            if (active_valid && m_axi3_arready) begin
                active_remaining <= active_remaining - 9'(chunk_beats);
                if (active_req.burst == 2'b01) begin // INCR
                    active_addr <= active_addr +
                                   (AXI_ADDR_WIDTH'(chunk_beats) << active_req.size);
                end
                if (ar_last_issue)
                    active_valid <= 1'b0;
            end

            // Accept a chopped AR into the active register; an unchopped one
            // has already gone to the port. Per-ID state is claimed at
            // acceptance either way (below).
            if (ar_handshake && ar_chop) begin
                active_req.id    <= s_axi_arid;
                active_req.addr  <= s_axi_araddr;
                active_req.len   <= s_axi_arlen;
                active_req.size  <= s_axi_arsize;
                active_req.burst <= s_axi_arburst;
                active_req.lock  <= s_axi_arlock;
                active_req.cache <= s_axi_arcache;
                active_req.prot  <= s_axi_arprot;
                active_req.user  <= s_axi_aruser;
                active_remaining <= 9'(s_axi_arlen) + 9'd1;
                active_addr      <= s_axi_araddr;
                active_valid     <= 1'b1;
                id_chop[s_axi_arid]           <= 1'b1;
                merge_chunks_left[s_axi_arid] <= 8'((9'(s_axi_arlen) + 9'd1 + 9'd15) >> 4);
                merge_worst[s_axi_arid]       <= 2'b00;
            end

            // Counts: +1 on acceptance, -1 on the RLAST that ends an AXI4
            // read. Both in one cycle leaves a count unchanged.
            if (ar_handshake && !(r_last_hs && r_txn_done))
                total_count <= total_count + CntW'(1);
            else if (!ar_handshake && (r_last_hs && r_txn_done))
                total_count <= total_count - CntW'(1);
            for (int i = 0; i < NumIds; i++) begin
                if ((ar_handshake && (s_axi_arid == AXI_ID_WIDTH'(i))) &&
                    !(r_last_hs && r_txn_done && (r_id == AXI_ID_WIDTH'(i))))
                    id_count[i] <= id_count[i] + CntW'(1);
                else if (!(ar_handshake && (s_axi_arid == AXI_ID_WIDTH'(i))) &&
                         (r_last_hs && r_txn_done && (r_id == AXI_ID_WIDTH'(i))))
                    id_count[i] <= id_count[i] - CntW'(1);
            end

            // Chopped-read merge state on each chunk's last R beat.
            if (r_last_hs && id_chop[r_id]) begin
                merge_worst[r_id] <= merged_final_resp;
                if (merge_chunks_left[r_id] == 8'd1) begin
                    id_chop[r_id]           <= 1'b0;
                    merge_chunks_left[r_id] <= '0;
                end else begin
                    merge_chunks_left[r_id] <= merge_chunks_left[r_id] - 8'd1;
                end
            end
        end
    )

endmodule : axi4_to_axi3_rd
