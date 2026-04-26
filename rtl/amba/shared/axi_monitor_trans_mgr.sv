// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_trans_mgr
// Purpose: Axi Monitor Trans Mgr module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18
// Refactored: 2026-04-23 (reduce synth logic levels on the AMBA monitors)

`timescale 1ns / 1ps

/**
 * AXI Monitor Bus Transaction Manager - Generic Monitor Package
 *
 * Tracks AXI transactions through their lifecycle, handling out-of-order
 * phase arrivals. Functionally identical to the previous revision — only
 * the RTL structure was rewritten to cut synth logic-level depth on the
 * trans_table update path.
 *
 * ---------------------------------------------------------------------------
 * STRUCTURE (was: one giant always_ff with dynamic-index writes)
 * ---------------------------------------------------------------------------
 * The original implementation used sequential priority-encoder loops
 * (w_X_trans_idx = -1; for (idx) if (w_X_trans_idx == -1 && ...) ...)
 * feeding a single always_ff that wrote `r_trans_table[w_X_trans_idx].field
 * <= ...`. Vivado fused the update logic across all 16 table entries and
 * the priority-encoder cone into one wide shared function, producing
 * ~12 LUT levels on the CE of each trans_table field (WNS -2.85 ns at
 * 100 MHz Artix-7).
 *
 * The rewritten implementation:
 *   (A) Computes parallel one-hot match vectors for addr/data/resp
 *       (`*_match_oh`) — each bit is a single AND of entry.valid and
 *       entry.id == cmd_id. 1 LUT per bit, fully independent across entries.
 *   (B) Computes one-hot "allocate-into-this-slot" vectors
 *       (`*_alloc_oh`), priority-encoded over the free slots once, with
 *       mutual exclusion between phases so a single free slot can't be
 *       double-claimed by addr + data-orphan in the same cycle.
 *   (C) Uses a per-entry `generate`-loop `always_ff` so each
 *       r_trans_table[i] update depends only on local one-hot bits and
 *       the shared input signals — NOT on other entries' state. Vivado
 *       therefore synthesises 16 parallel small update cones instead of
 *       one giant shared one.
 *
 * r_active_count, r_state_change, and the packet-reported feedback
 * semantics are preserved exactly.
 */

`include "reset_defs.svh"
module axi_monitor_trans_mgr
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
    import monitor_pkg::*;
#(
    parameter int MAX_TRANSACTIONS    = 16,   // Maximum outstanding transactions
    parameter int ADDR_WIDTH          = 32,   // Width of address bus
    parameter int ID_WIDTH            = 8,    // Width of ID bus
    parameter bit IS_READ             = 1'b1,   // 1 for read, 0 for write
    parameter bit IS_AXI              = 1'b1,   // 1 for AXI, 0 for AXI-Lite
    parameter bit ENABLE_PERF_PACKETS = 1'b0,   // Enable performance metrics tracking

    // Short params
    parameter int AW                  = ADDR_WIDTH,
    parameter int IW                  = ID_WIDTH
)
(
    // Global Clock and Reset
    input  logic                     aclk,
    input  logic                     aresetn,

    // Address channel
    input  logic                     cmd_valid,
    input  logic                     cmd_ready,
    input  logic [IW-1:0]            cmd_id,
    input  logic [AW-1:0]            cmd_addr,
    input  logic [7:0]               cmd_len,
    input  logic [2:0]               cmd_size,
    input  logic [1:0]               cmd_burst,

    // Data channel
    input  logic                     data_valid,
    input  logic                     data_ready,
    input  logic [IW-1:0]            data_id,
    input  logic                     data_last,
    input  logic [1:0]               data_resp,

    // Response channel (write only)
    input  logic                     resp_valid,
    input  logic                     resp_ready,
    input  logic [IW-1:0]            resp_id,
    input  logic [1:0]               resp_code,

    // Timestamp input
    input  logic [31:0]              timestamp,

    // Event reported feedback from reporter (FIX-001)
    input  logic [MAX_TRANSACTIONS-1:0] i_event_reported_flags,

    // Transaction table output - Fixed: Use unpacked array
    output bus_transaction_t         trans_table[MAX_TRANSACTIONS],
    output logic [7:0]               active_count,

    // State change detection (for debug module)
    output logic [MAX_TRANSACTIONS-1:0] state_change
);

    localparam int N = MAX_TRANSACTIONS;

    // =========================================================================
    // Registered state
    // =========================================================================
    bus_transaction_t r_trans_table[N];
    bus_transaction_t r_trans_table_prev[N];     // for state-change detection
    logic [7:0]       r_active_count;
    logic [N-1:0]     r_state_change;

    assign trans_table = r_trans_table;
    assign active_count = r_active_count;
    assign state_change = r_state_change;

    // =========================================================================
    // (A) Parallel one-hot match/occupancy vectors  — 1 LUT per bit
    //
    // These are intentionally marked (* keep = "true" *) so Vivado treats
    // them as anchors and does NOT fuse them into downstream update cones.
    // That's the core move that collapses the per-entry logic-level depth.
    // =========================================================================
    (* keep = "true" *) logic [N-1:0] addr_match_oh;
    (* keep = "true" *) logic [N-1:0] data_match_oh;   // read: id match; write: state match
    (* keep = "true" *) logic [N-1:0] resp_match_oh;
    (* keep = "true" *) logic [N-1:0] free_oh;         // slots currently empty

    always_comb begin
        for (int i = 0; i < N; i++) begin
            addr_match_oh[i] = r_trans_table[i].valid &&
                               (r_trans_table[i].id[IW-1:0] == cmd_id);
            resp_match_oh[i] = r_trans_table[i].valid &&
                               (r_trans_table[i].id[IW-1:0] == resp_id);
            free_oh[i]       = !r_trans_table[i].valid;
            if (IS_READ) begin
                data_match_oh[i] = r_trans_table[i].valid &&
                                   (r_trans_table[i].id[IW-1:0] == data_id);
            end else begin
                // Writes have no WID to match on; use first entry in
                // ADDR/DATA phase with cmd_received && !data_completed.
                data_match_oh[i] = r_trans_table[i].valid &&
                                   ((r_trans_table[i].state == TRANS_ADDR_PHASE) ||
                                    (r_trans_table[i].state == TRANS_DATA_PHASE)) &&
                                    r_trans_table[i].cmd_received &&
                                   !r_trans_table[i].data_completed;
            end
        end
    end

    // For the AXI-write data match we take the lowest-index matching entry
    // to preserve the legacy "first hit wins" semantic. Also computes the
    // "any-match" signal each phase needs to decide whether to allocate.
    logic [N-1:0] data_match_first_oh;
    logic         addr_hit_any, data_hit_any, resp_hit_any;

    always_comb begin
        addr_hit_any = |addr_match_oh;
        resp_hit_any = |resp_match_oh;
        data_hit_any = |data_match_oh;
        data_match_first_oh = '0;
        for (int i = 0; i < N; i++) begin
            if (data_match_oh[i] && (data_match_first_oh == '0)) begin
                data_match_first_oh[i] = 1'b1;
            end
        end
    end

    // For reads (ID-unique), addr_match_oh IS first-hit already. For writes
    // the data path uses data_match_first_oh. Addr/resp keep their "true"
    // one-hot because AXI IDs are unique across outstanding transactions.
    logic [N-1:0] addr_update_oh;
    logic [N-1:0] data_update_oh;
    logic [N-1:0] resp_update_oh;

    assign addr_update_oh = addr_match_oh;
    assign data_update_oh = IS_READ ? data_match_oh : data_match_first_oh;
    assign resp_update_oh = resp_match_oh;

    // =========================================================================
    // (B) One-hot allocation vectors — priority-encoded over free_oh, with
    //     mutex between phases so a slot can't be claimed twice in one cycle.
    // =========================================================================
    logic [N-1:0] addr_alloc_oh;   // addr phase allocates here (new txn)
    logic [N-1:0] data_alloc_oh;   // data phase allocates here (orphan)
    logic [N-1:0] resp_alloc_oh;   // resp phase allocates here (orphan, write only)

    logic addr_wants_alloc;
    logic data_wants_alloc;
    logic resp_wants_alloc;

    assign addr_wants_alloc = cmd_valid && !addr_hit_any;
    always_comb begin
        if (IS_READ) begin
            data_wants_alloc = data_valid && data_ready && !data_hit_any;
        end else begin
            data_wants_alloc = data_valid && data_ready && !IS_AXI && !data_hit_any;
        end
        resp_wants_alloc = (!IS_READ) && resp_valid && resp_ready && !resp_hit_any;
    end

    // Classic priority encoder: pick the lowest-index free slot, then the
    // next-lowest (excluding the first), then the one after that.
    always_comb begin
        logic [N-1:0] remaining;
        logic         taken;

        addr_alloc_oh = '0;
        data_alloc_oh = '0;
        resp_alloc_oh = '0;
        taken         = 1'b0;   // default — re-initialised per phase below
        remaining     = free_oh;

        // Addr phase (first priority)
        if (addr_wants_alloc) begin
            taken = 1'b0;
            for (int i = 0; i < N; i++) begin
                if (!taken && remaining[i]) begin
                    addr_alloc_oh[i] = 1'b1;
                    remaining[i]     = 1'b0;
                    taken            = 1'b1;
                end
            end
        end

        // Data orphan phase (second priority)
        if (data_wants_alloc) begin
            taken = 1'b0;
            for (int i = 0; i < N; i++) begin
                if (!taken && remaining[i]) begin
                    data_alloc_oh[i] = 1'b1;
                    remaining[i]     = 1'b0;
                    taken            = 1'b1;
                end
            end
        end

        // Resp orphan phase (third priority, write only)
        if (resp_wants_alloc) begin
            taken = 1'b0;
            for (int i = 0; i < N; i++) begin
                if (!taken && remaining[i]) begin
                    resp_alloc_oh[i] = 1'b1;
                    remaining[i]     = 1'b0;
                    taken            = 1'b1;
                end
            end
        end
    end

    // =========================================================================
    // Cleanup / completion eligibility (same policy as the original)
    // =========================================================================
    logic [N-1:0] w_can_cleanup;
    always_comb begin
        for (int i = 0; i < N; i++) begin
            if (r_trans_table[i].valid) begin
                unique case (r_trans_table[i].state)
                    TRANS_COMPLETE,
                    TRANS_ERROR,
                    TRANS_ORPHANED: w_can_cleanup[i] = r_trans_table[i].event_reported;
                    default:        w_can_cleanup[i] = 1'b0;
                endcase
            end else begin
                w_can_cleanup[i] = 1'b0;
            end
        end
    end

    // Channel index from ID (used only by addr allocation — kept for
    // source-compatibility with the old implementation).
    logic [5:0] w_addr_chan_idx;
    always_comb begin
        /* verilator lint_off WIDTHTRUNC */
        w_addr_chan_idx = IS_AXI ? (({24'h0, cmd_id} % 64)) : 0;
        /* verilator lint_on WIDTHTRUNC */
    end

    // =========================================================================
    // (C) Per-entry update — generate one small always_ff per trans_table[i].
    //
    // Each block depends only on r_trans_table[i] and the global one-hot
    // bits for index i, so Vivado cannot fuse them across entries.
    // =========================================================================
    generate
        for (genvar gi = 0; gi < N; gi++) begin : g_entry
            logic cmd_handshake;
            assign cmd_handshake = cmd_valid && cmd_ready;

            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    r_trans_table[gi] <= '0;
                end else begin
                    // ----------------------------------------------------
                    // ADDR PHASE — two independent updates per entry:
                    //   (a) allocate:  addr_alloc_oh[gi]
                    //   (b) update existing: addr_update_oh[gi] && cmd_handshake
                    // ----------------------------------------------------
                    if (addr_alloc_oh[gi]) begin
                        r_trans_table[gi].valid            <= 1'b1;
                        r_trans_table[gi].state            <= TRANS_ADDR_PHASE;
                        r_trans_table[gi].id               <= '0;
                        r_trans_table[gi].id[IW-1:0]       <= cmd_id;
                        r_trans_table[gi].addr             <= 32'(cmd_addr);
                        r_trans_table[gi].len              <= cmd_len;
                        r_trans_table[gi].size             <= cmd_size;
                        r_trans_table[gi].burst            <= cmd_burst;
                        r_trans_table[gi].cmd_received     <= cmd_ready;
                        r_trans_table[gi].addr_timer       <= '0;
                        r_trans_table[gi].data_started     <= 1'b0;
                        r_trans_table[gi].data_completed   <= 1'b0;
                        r_trans_table[gi].resp_received    <= 1'b0;
                        r_trans_table[gi].event_code.raw_code <= 4'h0;
                        r_trans_table[gi].event_reported   <= 1'b0;
                        r_trans_table[gi].data_timer       <= '0;
                        r_trans_table[gi].resp_timer       <= '0;
                        r_trans_table[gi].addr_timestamp   <= timestamp;
                        r_trans_table[gi].expected_beats   <= IS_AXI ? (cmd_len + 8'h1) : 8'h1;
                        r_trans_table[gi].data_beat_count  <= '0;
                        r_trans_table[gi].channel          <= w_addr_chan_idx;
                        r_trans_table[gi].eos_seen         <= 1'b0;
                    end
                    if (addr_update_oh[gi] && cmd_handshake) begin
                        r_trans_table[gi].cmd_received   <= 1'b1;
                        r_trans_table[gi].addr_timer     <= '0;
                        r_trans_table[gi].addr_timestamp <= timestamp;
                    end

                    // ----------------------------------------------------
                    // DATA PHASE
                    // ----------------------------------------------------
                    if (data_valid && data_ready) begin
                        if (data_update_oh[gi]) begin
                            r_trans_table[gi].data_started    <= 1'b1;
                            r_trans_table[gi].data_beat_count <=
                                r_trans_table[gi].data_beat_count + 1'b1;
                            r_trans_table[gi].data_timer      <= '0;
                            if (r_trans_table[gi].state != TRANS_ERROR) begin
                                r_trans_table[gi].state <= TRANS_DATA_PHASE;
                            end

                            if (IS_READ) begin
                                // READ: data_last marks end-of-burst.
                                if (data_last) begin
                                    r_trans_table[gi].data_completed <= 1'b1;
                                    r_trans_table[gi].data_timestamp <= timestamp;
                                end
                                if (data_resp[1]) begin
                                    r_trans_table[gi].state <= TRANS_ERROR;
                                    r_trans_table[gi].event_code.axi_error <=
                                        (data_resp[0]) ? EVT_RESP_DECERR : EVT_RESP_SLVERR;
                                end else if (data_last) begin
                                    r_trans_table[gi].state <= TRANS_COMPLETE;
                                end
                            end else begin
                                // WRITE: complete on data_last OR expected-beats.
                                if (data_last ||
                                    (r_trans_table[gi].data_beat_count + 1 ==
                                     r_trans_table[gi].expected_beats)) begin
                                    r_trans_table[gi].data_completed <= 1'b1;
                                    r_trans_table[gi].data_timestamp <= timestamp;
                                end
                            end
                        end else if (data_alloc_oh[gi]) begin
                            r_trans_table[gi].valid            <= 1'b1;
                            r_trans_table[gi].state            <= TRANS_ORPHANED;
                            r_trans_table[gi].id               <= '0;
                            if (IS_AXI) begin
                                r_trans_table[gi].id[IW-1:0]   <= data_id;
                                /* verilator lint_off WIDTHTRUNC */
                                r_trans_table[gi].channel      <= ({24'h0, data_id} % 64);
                                /* verilator lint_on WIDTHTRUNC */
                                r_trans_table[gi].expected_beats <= IS_READ ?
                                    8'h0 : 8'h1;
                            end else begin
                                r_trans_table[gi].expected_beats <= 8'h1;
                                r_trans_table[gi].channel        <= 6'h0;
                            end
                            r_trans_table[gi].data_started     <= 1'b1;
                            r_trans_table[gi].data_completed   <= data_last;
                            r_trans_table[gi].data_beat_count  <= 8'h1;
                            r_trans_table[gi].data_timestamp   <= timestamp;
                            r_trans_table[gi].event_code.axi_error <= EVT_DATA_ORPHAN;
                        end
                    end

                    // ----------------------------------------------------
                    // RESP PHASE (write only)
                    // ----------------------------------------------------
                    if (!IS_READ && resp_valid && resp_ready) begin
                        if (resp_update_oh[gi]) begin
                            r_trans_table[gi].resp_received  <= 1'b1;
                            r_trans_table[gi].resp_timestamp <= timestamp;
                            r_trans_table[gi].resp_timer     <= '0;
                            if (resp_code[1]) begin
                                r_trans_table[gi].state <= TRANS_ERROR;
                                r_trans_table[gi].event_code.axi_error <=
                                    (resp_code[0]) ? EVT_RESP_DECERR : EVT_RESP_SLVERR;
                            end else if (r_trans_table[gi].data_completed) begin
                                if (r_trans_table[gi].state != TRANS_ERROR) begin
                                    r_trans_table[gi].state <= TRANS_COMPLETE;
                                end
                            end else begin
                                // Resp before data completion = protocol violation
                                r_trans_table[gi].state <= TRANS_ERROR;
                                r_trans_table[gi].event_code.axi_error <= EVT_PROTOCOL;
                            end
                        end else if (resp_alloc_oh[gi]) begin
                            r_trans_table[gi].valid          <= 1'b1;
                            r_trans_table[gi].state          <= TRANS_ORPHANED;
                            r_trans_table[gi].id             <= '0;
                            if (IS_AXI) begin
                                r_trans_table[gi].id[IW-1:0] <= resp_id;
                                /* verilator lint_off WIDTHTRUNC */
                                r_trans_table[gi].channel    <= (resp_id % 64);
                                /* verilator lint_on WIDTHTRUNC */
                            end else begin
                                r_trans_table[gi].channel    <= 6'h0;
                            end
                            r_trans_table[gi].resp_received  <= 1'b1;
                            r_trans_table[gi].resp_timestamp <= timestamp;
                            r_trans_table[gi].event_code.axi_error <= EVT_RESP_ORPHAN;
                        end
                    end

                    // ----------------------------------------------------
                    // CLEANUP — applied last so it overrides same-cycle
                    // updates on the same entry (matches legacy behaviour).
                    // ----------------------------------------------------
                    if (r_trans_table[gi].valid && w_can_cleanup[gi]) begin
                        r_trans_table[gi].valid <= 1'b0;
                    end

                    // ----------------------------------------------------
                    // EVENT-REPORTED FEEDBACK (FIX-001) — also last; a
                    // cleaned-up entry must not re-set event_reported.
                    // ----------------------------------------------------
                    if (i_event_reported_flags[gi] && !r_trans_table[gi].event_reported) begin
                        r_trans_table[gi].event_reported <= 1'b1;
                    end
                end
            )
        end
    endgenerate

    // =========================================================================
    // Active-transaction counter and state-change detection
    //
    // Kept in their own always_ff blocks (single driver for r_active_count
    // and r_state_change) so they don't re-fuse into the per-entry cones.
    // =========================================================================
    logic [$clog2(N+1)-1:0] w_alloc_cnt;
    logic [$clog2(N+1)-1:0] w_cleanup_cnt;
    always_comb begin
        w_alloc_cnt = '0;
        for (int i = 0; i < N; i++) begin
            w_alloc_cnt = w_alloc_cnt +
                          {{($clog2(N+1)-1){1'b0}}, addr_alloc_oh[i]} +
                          {{($clog2(N+1)-1){1'b0}}, data_alloc_oh[i]} +
                          {{($clog2(N+1)-1){1'b0}}, resp_alloc_oh[i]};
        end
        w_cleanup_cnt = '0;
        for (int i = 0; i < N; i++) begin
            w_cleanup_cnt = w_cleanup_cnt +
                            {{($clog2(N+1)-1){1'b0}},
                             (r_trans_table[i].valid && w_can_cleanup[i])};
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_active_count <= '0;
        end else begin
            r_active_count <= r_active_count +
                              {{(8-$clog2(N+1)){1'b0}}, w_alloc_cnt} -
                              {{(8-$clog2(N+1)){1'b0}}, w_cleanup_cnt};
        end
    )

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int i = 0; i < N; i++) r_trans_table_prev[i] <= '0;
            r_state_change <= '0;
        end else begin
            r_trans_table_prev <= r_trans_table;
            for (int i = 0; i < N; i++) begin
                r_state_change[i] <= r_trans_table[i].valid &&
                                     r_trans_table_prev[i].valid &&
                                     (r_trans_table[i].state !=
                                      r_trans_table_prev[i].state);
            end
        end
    )

endmodule : axi_monitor_trans_mgr
