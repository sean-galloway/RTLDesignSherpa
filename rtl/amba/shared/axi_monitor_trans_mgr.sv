// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_trans_mgr
// Purpose: AXI Monitor Transaction Manager (CAM-backed).
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18 (original) / 2026-06-08 (CAM-backed rewrite)
//
// ============================================================================
// Tracks AXI transactions through their lifecycle, handling out-of-order
// phase arrivals. Per-transaction (valid, id, payload) storage and the
// addr/data/resp ID-lookup + free-slot + priority-encoded alloc logic
// live in the shared monitor_trans_cam module; this module owns the
// trans-mgr-specific FSM (per-slot next-payload computation, cleanup
// eligibility, event_reported feedback, active_count, state_change).
//
// This version delegates to monitor_trans_cam:
//
//   * 3 ID lookup ports (addr/data/resp) -> monitor_trans_cam
//   * free-slot vector + 3 priority-encoded alloc one-hots -> monitor_trans_cam
//   * per-slot registered storage of (valid, id, payload) -> monitor_trans_cam
//
// The trans_mgr still owns:
//
//   * The WID-less write-data match (state predicate over the payload,
//     not an id match -- the CAM can't see state, only id).
//   * The per-slot combinational next-payload computation (the
//     "what does the new bus_transaction_t look like after this cycle's
//     handshakes" logic, copied from the production always_ff with
//     non-blocking writes turned into blocking assignments to a `next`
//     temporary).
//   * The wants_alloc derivation (= input_handshake && !hit_any).
//   * Cleanup, event_reported, active_count, state_change -- the
//     trans-mgr-specific status outputs.
//
// CAM payload contains the full bus_transaction_t (including its `id`
// field) for clean unpack to the trans_table output port. The CAM's
// `entry_id` port is the actual lookup key; trans_mgr writes both
// atomically so they always agree.
//
// Synthesis intent: each slot's next-state lives in its own always_comb
// inside a generate loop, so synth still sees N independent small
// update cones rather than one fused cone. The CAM's per-slot
// registered storage preserves the production module's "16 parallel
// small update cones" shape.
// ============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_monitor_trans_mgr
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter int MAX_TRANSACTIONS    = 16,   // Maximum outstanding transactions
    parameter int ADDR_WIDTH          = 32,   // Width of address bus
    parameter int ID_WIDTH            = 8,    // Width of ID bus
    parameter bit IS_READ             = 1'b1, // 1 for read, 0 for write
    parameter bit IS_AXI              = 1'b1, // 1 for AXI, 0 for AXI-Lite
    parameter bit ENABLE_PERF_PACKETS = 1'b0, // Enable performance metrics tracking

    // Short params (kept for API compatibility with the production module)
    parameter int AW                  = ADDR_WIDTH,
    parameter int IW                  = ID_WIDTH
)
(
    // Global Clock and Reset
    input  logic                        aclk,
    input  logic                        aresetn,
    // Synchronous clear: empty the transaction CAM and zero the active-count
    // pipeline on the next edge (no full rst_n). Pulse only when idle.
    input  logic                        clear,

    // Address channel
    input  logic                        cmd_valid,
    input  logic                        cmd_ready,
    input  logic [IW-1:0]               cmd_id,
    input  logic [AW-1:0]               cmd_addr,
    input  logic [7:0]                  cmd_len,
    input  logic [2:0]                  cmd_size,
    input  logic [1:0]                  cmd_burst,

    // Data channel
    input  logic                        data_valid,
    input  logic                        data_ready,
    input  logic [IW-1:0]               data_id,
    input  logic                        data_last,
    input  logic [1:0]                  data_resp,

    // Response channel (write only)
    input  logic                        resp_valid,
    input  logic                        resp_ready,
    input  logic [IW-1:0]               resp_id,
    input  logic [1:0]                  resp_code,

    // Timestamp input
    input  logic [31:0]                 timestamp,

    // Event reported feedback from reporter (FIX-001)
    input  logic [MAX_TRANSACTIONS-1:0] i_event_reported_flags,

    // Transaction table output
    output bus_transaction_t            trans_table[MAX_TRANSACTIONS],
    output logic [7:0]                  active_count,

    // State change detection (for debug module)
    output logic [MAX_TRANSACTIONS-1:0] state_change
);

    localparam int N         = MAX_TRANSACTIONS;
    localparam int PAYLOAD_W = $bits(bus_transaction_t);

    // ------------------------------------------------------------------------
    // CAM signal nets
    // ------------------------------------------------------------------------
    logic [N-1:0]                 addr_match_oh;
    logic [N-1:0]                 data_match_oh;        // valid only for reads
    logic [N-1:0]                 resp_match_oh;
    logic [N-1:0]                 cam_data_match_first_oh; // unused (kept for clarity)
    logic [N-1:0]                 free_oh;

    logic [N-1:0]                 addr_alloc_oh;
    logic [N-1:0]                 data_alloc_oh;
    logic [N-1:0]                 resp_alloc_oh;

    logic [N-1:0]                 cam_entry_valid;
    bus_transaction_t             cam_entry_payload [N];

    logic [N-1:0]                 cam_entry_we;
    logic [N-1:0]                 cam_entry_valid_next;
    logic [IW-1:0]                cam_entry_id_next      [N];
    bus_transaction_t             cam_entry_payload_next [N];

    logic                         addr_wants_alloc;
    logic                         data_wants_alloc;
    logic                         resp_wants_alloc;

    // ------------------------------------------------------------------------
    // monitor_trans_cam -- keys + payload storage live here.
    // ------------------------------------------------------------------------
    /* verilator lint_off PINCONNECTEMPTY */
    monitor_trans_cam #(
        .DEPTH         (N),
        .ID_WIDTH      (IW),
        .PAYLOAD_WIDTH (PAYLOAD_W)
    ) u_cam (
        .clk                  (aclk),
        .rst_n                (aresetn),
        .clear                (clear),

        .lookup_addr_id       (cmd_id),
        .lookup_data_id       (data_id),
        .lookup_resp_id       (resp_id),

        .addr_match_oh        (addr_match_oh),
        .data_match_oh        (data_match_oh),
        .resp_match_oh        (resp_match_oh),
        .data_match_first_oh  (cam_data_match_first_oh),

        .free_oh              (free_oh),

        .addr_wants_alloc     (addr_wants_alloc),
        .data_wants_alloc     (data_wants_alloc),
        .resp_wants_alloc     (resp_wants_alloc),
        .addr_alloc_oh        (addr_alloc_oh),
        .data_alloc_oh        (data_alloc_oh),
        .resp_alloc_oh        (resp_alloc_oh),

        .entry_we             (cam_entry_we),
        .entry_valid_next     (cam_entry_valid_next),
        .entry_id_next        (cam_entry_id_next),
        .entry_payload_next   (cam_entry_payload_next),

        .entry_valid          (cam_entry_valid),
        // entry_id port is informational only; the trans_mgr trusts the
        // payload's `id` field as the source of truth (the CAM and the
        // payload are written atomically so they always agree).
        .entry_id             (),
        .entry_payload        (cam_entry_payload)
    );
    /* verilator lint_on PINCONNECTEMPTY */

    // ------------------------------------------------------------------------
    // WID-less write data-channel match.
    //
    // For AXI4 reads the data channel has a WID that matches the AR
    // channel's id, so cam_data_match_oh is what we want. For AXI4
    // writes the data channel has no WID; the upstream convention is
    // "first valid entry in ADDR_PHASE or DATA_PHASE that has
    // cmd_received && !data_completed wins". The CAM can't see state
    // (it stores payload as opaque bits) so this predicate is computed
    // locally over the CAM's payload outputs.
    // ------------------------------------------------------------------------
    (* keep = "true" *) logic [N-1:0] w_data_state_pred_oh;
    logic [N-1:0]                     w_data_state_first_oh;

    always_comb begin
        w_data_state_first_oh = '0;
        for (int i = 0; i < N; i++) begin
            w_data_state_pred_oh[i] = cam_entry_valid[i] &&
                                       ((cam_entry_payload[i].state == TRANS_ADDR_PHASE) ||
                                        (cam_entry_payload[i].state == TRANS_DATA_PHASE)) &&
                                       cam_entry_payload[i].cmd_received &&
                                       !cam_entry_payload[i].data_completed;
        end
        // Lowest-index first-match for the WID-less write path.
        for (int i = 0; i < N; i++) begin
            if (w_data_state_pred_oh[i] && (w_data_state_first_oh == '0)) begin
                w_data_state_first_oh[i] = 1'b1;
            end
        end
    end

    // ------------------------------------------------------------------------
    // Hit indicators + wants_alloc.
    // ------------------------------------------------------------------------
    logic addr_hit_any, data_hit_any, resp_hit_any;

    assign addr_hit_any = |addr_match_oh;
    assign resp_hit_any = |resp_match_oh;
    assign data_hit_any = IS_READ ? (|data_match_oh) : (|w_data_state_pred_oh);

    assign addr_wants_alloc = cmd_valid && !addr_hit_any;
    always_comb begin
        if (IS_READ) begin
            data_wants_alloc = data_valid && data_ready && !data_hit_any;
        end else begin
            data_wants_alloc = data_valid && data_ready && !IS_AXI && !data_hit_any;
        end
        resp_wants_alloc = (!IS_READ) && resp_valid && resp_ready && !resp_hit_any;
    end

    // ------------------------------------------------------------------------
    // Effective update one-hot (same role as the production module).
    // Reads use the CAM's id-based data match; writes use the local
    // first-match state-predicate vector.
    // ------------------------------------------------------------------------
    logic [N-1:0] addr_update_oh;
    logic [N-1:0] data_update_oh;
    logic [N-1:0] resp_update_oh;

    assign addr_update_oh = addr_match_oh;
    assign data_update_oh = IS_READ ? data_match_oh : w_data_state_first_oh;
    assign resp_update_oh = resp_match_oh;

    // ------------------------------------------------------------------------
    // Cleanup eligibility (same policy as the production module).
    // ------------------------------------------------------------------------
    logic [N-1:0] w_can_cleanup;
    always_comb begin
        for (int i = 0; i < N; i++) begin
            if (cam_entry_valid[i]) begin
                unique case (cam_entry_payload[i].state)
                    TRANS_COMPLETE,
                    TRANS_ERROR,
                    TRANS_ORPHANED: w_can_cleanup[i] = cam_entry_payload[i].event_reported;
                    default:        w_can_cleanup[i] = 1'b0;
                endcase
            end else begin
                w_can_cleanup[i] = 1'b0;
            end
        end
    end

    // Channel index from ID (used only by addr allocation -- kept for
    // source-compatibility with the production module).
    logic [5:0] w_addr_chan_idx;
    always_comb begin
        /* verilator lint_off WIDTHTRUNC */
        w_addr_chan_idx = IS_AXI ? (({24'h0, cmd_id} % 64)) : 0;
        /* verilator lint_on WIDTHTRUNC */
    end

    logic cmd_handshake;
    assign cmd_handshake = cmd_valid && cmd_ready;

    // ------------------------------------------------------------------------
    // Per-slot next-state computation.
    //
    // One always_comb per slot, mirroring the production module's
    // per-entry generate-loop always_ff. The body is a direct copy of
    // the production update logic with the non-blocking assignments
    // turned into blocking writes to a `next` temporary, so the
    // CAM's entry_payload_next port can take the whole struct at once.
    //
    // Mutex notes (preserved from production):
    //   * addr_alloc_oh[i] and addr_update_oh[i] can't both fire on the
    //     same slot (alloc is gated to free slots, update to valid).
    //   * Same for data_alloc/data_update and resp_alloc/resp_update.
    //   * Cleanup is applied last (overrides same-cycle valid set).
    //   * event_reported feedback is last (a cleaned-up entry must not
    //     get its event_reported re-set).
    // ------------------------------------------------------------------------
    generate
        for (genvar gi = 0; gi < N; gi++) begin : g_entry_next
            bus_transaction_t next;
            logic             next_we;
            logic [IW-1:0]    next_id;

            always_comb begin
                // Default: hold current state.
                next     = cam_entry_payload[gi];
                next_we  = 1'b0;
                next_id  = cam_entry_payload[gi].id[IW-1:0];

                // --- ADDR PHASE ---
                //
                // Field-by-field write to mirror the production module
                // exactly: fields that production touches via NBA are
                // assigned here; fields that production leaves alone
                // (data_timestamp, resp_timestamp on addr_alloc) MUST
                // be preserved across the alloc, so we do NOT pre-zero
                // `next`. Same rule applies to data_alloc and resp_alloc
                // below -- the equivalence test (this file's reason for
                // existing) catches any clobbered field.
                if (addr_alloc_oh[gi]) begin
                    next.valid                 = 1'b1;
                    next.state                 = TRANS_ADDR_PHASE;
                    next.id                    = '0;
                    next.id[IW-1:0]            = cmd_id;
                    next.addr                  = 32'(cmd_addr);
                    next.len                   = cmd_len;
                    next.size                  = cmd_size;
                    next.burst                 = cmd_burst;
                    next.cmd_received          = cmd_ready;
                    next.addr_timer            = '0;
                    next.data_started          = 1'b0;
                    next.data_completed        = 1'b0;
                    next.resp_received         = 1'b0;
                    next.event_code.raw_code   = 8'h0;
                    next.event_reported        = 1'b0;
                    next.data_timer            = '0;
                    next.resp_timer            = '0;
                    next.addr_timestamp        = timestamp;
                    next.expected_beats        = IS_AXI ? (cmd_len + 8'h1) : 8'h1;
                    next.data_beat_count       = '0;
                    next.channel               = w_addr_chan_idx;
                    next.eos_seen              = 1'b0;
                    next_we                    = 1'b1;
                    next_id                    = cmd_id;
                end
                if (addr_update_oh[gi] && cmd_handshake) begin
                    next.cmd_received   = 1'b1;
                    next.addr_timer     = '0;
                    next.addr_timestamp = timestamp;
                    next_we             = 1'b1;
                end

                // --- DATA PHASE ---
                if (data_valid && data_ready) begin
                    if (data_update_oh[gi]) begin
                        // Capture beats-after-increment for the
                        // "is this the last expected beat" test.
                        next.data_started    = 1'b1;
                        next.data_beat_count = cam_entry_payload[gi].data_beat_count + 1'b1;
                        next.data_timer      = '0;
                        if (next.state != TRANS_ERROR) begin
                            next.state = TRANS_DATA_PHASE;
                        end

                        if (IS_READ) begin
                            if (data_last) begin
                                next.data_completed = 1'b1;
                                next.data_timestamp = timestamp;
                            end
                            if (data_resp[1]) begin
                                next.state = TRANS_ERROR;
                                next.event_code.axi_error =
                                    (data_resp[0]) ? EVT_RESP_DECERR : EVT_RESP_SLVERR;
                            end else if (data_last) begin
                                next.state = TRANS_COMPLETE;
                            end
                        end else begin
                            // WRITE: complete on data_last OR
                            // post-increment beat count == expected.
                            if (data_last ||
                                (next.data_beat_count ==
                                 cam_entry_payload[gi].expected_beats)) begin
                                next.data_completed = 1'b1;
                                next.data_timestamp = timestamp;
                            end
                        end
                        next_we = 1'b1;
                    end else if (data_alloc_oh[gi]) begin
                        // Production touches: valid, state, id, channel,
                        // expected_beats, data_started, data_completed,
                        // data_beat_count, data_timestamp,
                        // event_code.axi_error. All other fields are
                        // preserved across the alloc (notably
                        // event_reported, addr/len/size/burst, timers).
                        next.valid                 = 1'b1;
                        next.state                 = TRANS_ORPHANED;
                        next.id                    = '0;
                        if (IS_AXI) begin
                            next.id[IW-1:0]        = data_id;
                            /* verilator lint_off WIDTHTRUNC */
                            next.channel           = ({24'h0, data_id} % 64);
                            /* verilator lint_on WIDTHTRUNC */
                            next.expected_beats    = IS_READ ? 8'h0 : 8'h1;
                        end else begin
                            next.expected_beats    = 8'h1;
                            next.channel           = 6'h0;
                        end
                        next.data_started          = 1'b1;
                        next.data_completed        = data_last;
                        next.data_beat_count       = 8'h1;
                        next.data_timestamp        = timestamp;
                        next.event_code.axi_error  = EVT_DATA_ORPHAN;
                        next_we                    = 1'b1;
                        next_id                    = IS_AXI ? data_id : '0;
                    end
                end

                // --- RESP PHASE (write only) ---
                //
                // For AXI4 writes the same slot can take BOTH a data
                // beat and the B response in the same cycle. Production
                // uses NBA, so the resp-update condition tests below
                // see the OLD (pre-cycle) value of data_completed and
                // state. With blocking writes we must explicitly read
                // from cam_entry_payload (the registered/old value),
                // not from `next` (which may already reflect the data
                // phase's update). The equivalence test catches this.
                if (!IS_READ && resp_valid && resp_ready) begin
                    if (resp_update_oh[gi]) begin
                        next.resp_received  = 1'b1;
                        next.resp_timestamp = timestamp;
                        next.resp_timer     = '0;
                        if (resp_code[1]) begin
                            next.state = TRANS_ERROR;
                            next.event_code.axi_error =
                                (resp_code[0]) ? EVT_RESP_DECERR : EVT_RESP_SLVERR;
                        end else if (cam_entry_payload[gi].data_completed) begin
                            if (cam_entry_payload[gi].state != TRANS_ERROR) begin
                                next.state = TRANS_COMPLETE;
                            end
                        end else begin
                            // Resp before data completion = protocol
                            // violation.
                            next.state = TRANS_ERROR;
                            next.event_code.axi_error = EVT_PROTOCOL;
                        end
                        next_we = 1'b1;
                    end else if (resp_alloc_oh[gi]) begin
                        // Production touches: valid, state, id, channel,
                        // resp_received, resp_timestamp,
                        // event_code.axi_error. All other fields are
                        // preserved (notably event_reported).
                        next.valid                 = 1'b1;
                        next.state                 = TRANS_ORPHANED;
                        next.id                    = '0;
                        if (IS_AXI) begin
                            next.id[IW-1:0]        = resp_id;
                            /* verilator lint_off WIDTHTRUNC */
                            next.channel           = (resp_id % 64);
                            /* verilator lint_on WIDTHTRUNC */
                        end else begin
                            next.channel           = 6'h0;
                        end
                        next.resp_received         = 1'b1;
                        next.resp_timestamp        = timestamp;
                        next.event_code.axi_error  = EVT_RESP_ORPHAN;
                        next_we                    = 1'b1;
                        next_id                    = IS_AXI ? resp_id : '0;
                    end
                end

                // --- CLEANUP (last; overrides same-cycle valid set) ---
                if (cam_entry_valid[gi] && w_can_cleanup[gi]) begin
                    next.valid = 1'b0;
                    next_we    = 1'b1;
                end

                // --- EVENT-REPORTED FEEDBACK (last; cleaned-up entry
                // must not get event_reported re-set) ---
                if (i_event_reported_flags[gi] &&
                        !cam_entry_payload[gi].event_reported) begin
                    next.event_reported = 1'b1;
                    next_we             = 1'b1;
                end
            end

            // Drive the CAM's per-slot write port.
            assign cam_entry_we[gi]             = next_we;
            assign cam_entry_valid_next[gi]     = next.valid;
            assign cam_entry_id_next[gi]        = next_id;
            assign cam_entry_payload_next[gi]   = next;
        end
    endgenerate

    // ------------------------------------------------------------------------
    // Outputs from the CAM's payload storage.
    // ------------------------------------------------------------------------
    assign trans_table = cam_entry_payload;

    // ========================================================================
    // Active-transaction counter and state-change detection
    //
    // Identical to the production module -- the alloc and cleanup
    // adder trees are pipelined one stage to close the long
    // combinational path at 100 MHz on the Artix-7 -1 part.
    // ========================================================================
    logic [$clog2(N+1)-1:0] w_alloc_cnt;
    logic [$clog2(N+1)-1:0] w_cleanup_cnt;
    logic [$clog2(N+1)-1:0] r_alloc_cnt;
    logic [$clog2(N+1)-1:0] r_cleanup_cnt;
    logic [7:0]             r_active_count;

    // Alloc/cleanup one-hot vectors feeding the popcount adder trees. These are
    // ALWAYS registered (q) so the popcount no longer sits on the route-bound
    // match -> alloc critical path. alloc and cleanup are registered by the
    // SAME amount so the active_count accounting (alloc - cleanup) stays
    // consistent -- it just lags one extra cycle overall.
    logic [N-1:0] w_cleanup_vec;
    logic [N-1:0] q_addr_alloc_oh, q_data_alloc_oh, q_resp_alloc_oh, q_cleanup_vec;
    always_comb begin
        for (int i = 0; i < N; i++)
            w_cleanup_vec[i] = cam_entry_valid[i] && w_can_cleanup[i];
    end
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            q_addr_alloc_oh <= '0; q_data_alloc_oh <= '0;
            q_resp_alloc_oh <= '0; q_cleanup_vec   <= '0;
        end else if (clear) begin
            q_addr_alloc_oh <= '0; q_data_alloc_oh <= '0;
            q_resp_alloc_oh <= '0; q_cleanup_vec   <= '0;
        end else begin
            q_addr_alloc_oh <= addr_alloc_oh;
            q_data_alloc_oh <= data_alloc_oh;
            q_resp_alloc_oh <= resp_alloc_oh;
            q_cleanup_vec   <= w_cleanup_vec;
        end
    )

    always_comb begin
        w_alloc_cnt = '0;
        for (int i = 0; i < N; i++) begin
            w_alloc_cnt = w_alloc_cnt +
                          {{($clog2(N+1)-1){1'b0}}, q_addr_alloc_oh[i]} +
                          {{($clog2(N+1)-1){1'b0}}, q_data_alloc_oh[i]} +
                          {{($clog2(N+1)-1){1'b0}}, q_resp_alloc_oh[i]};
        end
        w_cleanup_cnt = '0;
        for (int i = 0; i < N; i++) begin
            w_cleanup_cnt = w_cleanup_cnt +
                            {{($clog2(N+1)-1){1'b0}}, q_cleanup_vec[i]};
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_alloc_cnt   <= '0;
            r_cleanup_cnt <= '0;
        end else if (clear) begin
            r_alloc_cnt   <= '0;
            r_cleanup_cnt <= '0;
        end else begin
            r_alloc_cnt   <= w_alloc_cnt;
            r_cleanup_cnt <= w_cleanup_cnt;
        end
    )

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_active_count <= '0;
        end else if (clear) begin
            r_active_count <= '0;
        end else begin
            r_active_count <= r_active_count +
                              {{(8-$clog2(N+1)){1'b0}}, r_alloc_cnt} -
                              {{(8-$clog2(N+1)){1'b0}}, r_cleanup_cnt};
        end
    )

    assign active_count = r_active_count;

    // ------------------------------------------------------------------------
    // State-change detection.
    // ------------------------------------------------------------------------
    bus_transaction_t r_trans_table_prev [N];
    logic [N-1:0]     r_state_change;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int i = 0; i < N; i++) r_trans_table_prev[i] <= '0;
            r_state_change <= '0;
        end else begin
            r_trans_table_prev <= cam_entry_payload;
            for (int i = 0; i < N; i++) begin
                r_state_change[i] <= cam_entry_payload[i].valid &&
                                     r_trans_table_prev[i].valid &&
                                     (cam_entry_payload[i].state !=
                                      r_trans_table_prev[i].state);
            end
        end
    )

    assign state_change = r_state_change;

endmodule : axi_monitor_trans_mgr
