// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monbus_cam
// Purpose: True-LRU caching CAM for the monbus bulk-trace compressor.
//
// Documentation: docs/markdown/RTLAmba/shared/monbus_cam.md  (TBD)
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-06-06
// Revised: 2026-06-07 — FIFO eviction replaced by true LRU with
//          position-indexed storage. Bit-exact mirror of the Python
//          `Cam` class in bin/TBClasses/monbus/monbus_compressor.py
//          so the RTL compressor can produce a byte-identical slot
//          stream against the Python `Encoder` golden.
//
// ============================================================================
// Module: monbus_cam
// ============================================================================
//
// Storage model
// -------------
// Entries are indexed by **LRU position rank**, not by physical slot:
//
//   r_entry[0]            most-recently-used (MRU)
//   r_entry[1..count-1]   in LRU order, newer first
//   r_entry[count..DEPTH-1]  invalid (empty slots)
//
// This matches the Python golden's `entries` list exactly:
//   - `lookup(key)` returns the current position rank
//   - on TOUCH/INSTALL the matched (or new) entry moves to position 0
//   - older entries shift down by 1 position
//   - the LRU victim (when full) is whoever was at position DEPTH-1
//
// The `access_idx` returned to the caller IS the position rank that
// gets encoded into the compressed slot's `tmpl_idx` field — both
// encoder and decoder agree on it because both maintain the same
// position-indexed state through identical (action, key, data)
// sequences.
//
// Interface model
// ---------------
// One access port per cycle. Caller drives `access_key`, sees the
// combinational hit/idx/old_data, and in the same cycle commits one of:
//   - NONE     (action = ACTION_NONE)        pure lookup, no state change
//   - TOUCH    (action = ACTION_TOUCH)       hit; refresh payload + move-to-front
//   - INSTALL  (action = ACTION_INSTALL)     miss; install at MRU (evict LRU if full)
//
// Commit takes effect on the next rising edge of `clk`.
//
// Eviction
// --------
// On INSTALL when cam_full: the entry at position DEPTH-1 is evicted
// and the `evicted` output pulses high for that cycle. All other
// entries shift down one position; the new entry lands at position 0.
//
// Status outputs
// --------------
// cam_full   — count == DEPTH (combinational)
// cam_count  — current occupancy 0..DEPTH (combinational)
// evicted    — pulses high on a full-CAM INSTALL cycle (combinational)
//
// Reset
// -----
// All entries marked invalid. cam_count = 0.
//
// Caller protocol assertions (SIMULATION only)
// --------------------------------------------
// - ACTION_TOUCH must coincide with a hit (otherwise $error).
// - ACTION_INSTALL must coincide with a miss (otherwise $error -- the
//   match would create a duplicate-key entry, which violates the
//   one-hot-match invariant). The encoder dispatches TOUCH on hit and
//   INSTALL on miss, so this is the natural caller pattern.
// - Match vector must be at most one-hot.
//
// Testing
// -------
// Companion cocotb test: val/amba/test_monbus_cam.py
// Python golden model: bin/TBClasses/monbus/monbus_compressor.py (Cam class)
// ============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_cam #(
    parameter int KEY_WIDTH  = 49,      // template-key width
    parameter int DATA_WIDTH = 64,      // payload width (last_event_data)
    parameter int TS_WIDTH   = 24,      // per-entry last_ts width (per-template delta_ts)
    parameter int DEPTH      = 32,      // number of CAM entries (locked spec: 32)
    // localparams
    parameter int IDX_WIDTH  = (DEPTH > 1) ? $clog2(DEPTH) : 1,
    parameter int CNT_WIDTH  = $clog2(DEPTH + 1)
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // === Access port (single port, lookup + commit in one cycle) ===
    input  logic [KEY_WIDTH-1:0]    access_key,
    output logic                    access_hit,
    output logic [IDX_WIDTH-1:0]    access_idx,      // LRU position rank, valid only when access_hit
    output logic [DATA_WIDTH-1:0]   access_old_data, // last_event_data at access_idx, valid only when access_hit
    output logic [TS_WIDTH-1:0]     access_old_ts,   // last_ts at access_idx, valid only when access_hit

    // Commit (sampled on rising edge; takes effect cycle N+1):
    // 2'b00 ACTION_NONE     -- no state change
    // 2'b01 ACTION_TOUCH    -- caller saw a hit; move matched entry to MRU, update its data
    // 2'b10 ACTION_INSTALL  -- caller saw a miss; insert new entry at MRU (evict LRU if full)
    // 2'b11 reserved
    input  logic [1:0]              access_action,
    input  logic [DATA_WIDTH-1:0]   access_new_data,
    input  logic [TS_WIDTH-1:0]     access_new_ts,

    // === Status (combinational) ===
    output logic                    cam_full,
    output logic [CNT_WIDTH-1:0]    cam_count,

    // === Eviction pulse (combinational; high on full-CAM INSTALL) ===
    output logic                    evicted
);

    // ------------------------------------------------------------------------
    // Action encoding (must match access_action above and the Python golden).
    // ------------------------------------------------------------------------
    localparam logic [1:0] ACTION_NONE    = 2'b00;
    localparam logic [1:0] ACTION_TOUCH   = 2'b01;
    localparam logic [1:0] ACTION_INSTALL = 2'b10;

    // ------------------------------------------------------------------------
    // Position-indexed entry storage. r_entry[0] = MRU at any time.
    // r_valid[i] tracks whether slot i is occupied; for i < cam_count
    // this is always 1, for i >= cam_count always 0. r_valid is kept
    // explicit (rather than derived from cam_count) for symmetry with
    // the per-slot update logic below.
    // ------------------------------------------------------------------------
    logic                    r_valid [DEPTH];
    logic [KEY_WIDTH-1:0]    r_key   [DEPTH];
    logic [DATA_WIDTH-1:0]   r_data  [DEPTH];
    logic [TS_WIDTH-1:0]     r_ts    [DEPTH];
    logic [CNT_WIDTH-1:0]    r_count;

    // ------------------------------------------------------------------------
    // Combinational match vector + index encoder.
    // Returns the position rank of the matching entry (priority: lowest-
    // index wins, which equals "most recently touched" since lower
    // indices are more recent in the position-indexed storage).
    // ------------------------------------------------------------------------
    logic [DEPTH-1:0] w_match_oh;
    always_comb begin
        for (int i = 0; i < DEPTH; i++) begin
            w_match_oh[i] = r_valid[i] && (r_key[i] == access_key);
        end
    end

    always_comb begin
        access_hit      = 1'b0;
        access_idx      = '0;
        access_old_data = '0;
        access_old_ts   = '0;
        for (int i = DEPTH-1; i >= 0; i--) begin
            if (w_match_oh[i]) begin
                access_hit      = 1'b1;
                access_idx      = IDX_WIDTH'(i);
                access_old_data = r_data[i];
                access_old_ts   = r_ts[i];
            end
        end
    end

    // ------------------------------------------------------------------------
    // Status outputs.
    // ------------------------------------------------------------------------
    assign cam_count = r_count;
    assign cam_full  = (r_count == CNT_WIDTH'(DEPTH));
    assign evicted   = (access_action == ACTION_INSTALL) && cam_full;

    // ------------------------------------------------------------------------
    // Per-slot next-state shift logic.
    //
    // TOUCH at position P (the matched position, equal to access_idx):
    //   slot 0:       new entry  = (access_key, access_new_data, valid=1)
    //   slot 1..P:    new entry  = old entry [slot-1]
    //   slot P+1..N:  new entry  = old entry [slot] (unchanged)
    //
    // INSTALL when !cam_full at insertion_pos = cam_count:
    //   slot 0:       new entry  = (access_key, access_new_data, valid=1)
    //   slot 1..cam_count:    new entry = old entry [slot-1]   (shift down)
    //   slot cam_count+1..N:  new entry = old entry [slot]     (still invalid)
    //   r_count++
    //
    // INSTALL when cam_full (insertion_pos = DEPTH-1, evicting LRU):
    //   slot 0:       new entry  = (access_key, access_new_data, valid=1)
    //   slot 1..DEPTH-1:  new entry = old entry [slot-1]   (shift down, evicting [DEPTH-1])
    //   r_count stays at DEPTH
    //
    // NONE (or reserved): all slots hold.
    //
    // The TOUCH and INSTALL cases share the same shift-down structure;
    // they differ only in the "insertion position" (where the shift
    // stops). Below, `shift_to` is the highest slot that gets a new
    // value via shift-down (slots above `shift_to` are unchanged).
    // ------------------------------------------------------------------------
    logic [CNT_WIDTH-1:0]   shift_to;
    logic                   do_shift;
    logic [KEY_WIDTH-1:0]   new_key;
    logic [DATA_WIDTH-1:0]  new_data;
    logic [TS_WIDTH-1:0]    new_ts;

    always_comb begin
        do_shift = 1'b0;
        shift_to = '0;
        new_key  = access_key;
        new_data = access_new_data;
        new_ts   = access_new_ts;

        unique case (access_action)
            ACTION_TOUCH: begin
                if (access_hit) begin
                    do_shift = 1'b1;
                    shift_to = CNT_WIDTH'(access_idx);
                end
            end
            ACTION_INSTALL: begin
                do_shift = 1'b1;
                shift_to = cam_full ? CNT_WIDTH'(DEPTH-1) : r_count;
            end
            default: ; // NONE / reserved -- no shift
        endcase
    end

    // ------------------------------------------------------------------------
    // Registered state update.
    // ------------------------------------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < DEPTH; i++) begin
                r_valid[i] <= 1'b0;
                r_key[i]   <= '0;
                r_data[i]  <= '0;
                r_ts[i]    <= '0;
            end
            r_count <= '0;
        end else if (do_shift) begin
            // Slot 0 always becomes the touched/installed entry.
            r_valid[0] <= 1'b1;
            r_key[0]   <= new_key;
            r_data[0]  <= new_data;
            r_ts[0]    <= new_ts;

            // Slots 1..shift_to: shift down from i-1.
            for (int i = 1; i < DEPTH; i++) begin
                if (CNT_WIDTH'(i) <= shift_to) begin
                    r_valid[i] <= r_valid[i-1];
                    r_key[i]   <= r_key[i-1];
                    r_data[i]  <= r_data[i-1];
                    r_ts[i]    <= r_ts[i-1];
                end
                // Slots above shift_to are unchanged (no else branch).
            end

            // Count update.
            //   TOUCH: count unchanged (entry was already valid)
            //   INSTALL !full: count++
            //   INSTALL full: count stays at DEPTH
            if (access_action == ACTION_INSTALL && !cam_full) begin
                r_count <= r_count + 1'b1;
            end
        end
        // ACTION_NONE / TOUCH-without-hit / reserved: hold all state.
    )

    // ========================================================================
    // Caller-protocol assertions (simulation only)
    // ========================================================================

`ifdef SIMULATION
    // TOUCH without hit is a caller bug.
    always @(posedge clk) begin
        if (rst_n && (access_action == ACTION_TOUCH) && !access_hit) begin
            $error("monbus_cam: ACTION_TOUCH asserted but lookup missed (key=0x%h)",
                   access_key);
        end
    end

    // INSTALL when key is already present would create a duplicate.
    // (Encoder dispatches TOUCH-on-hit and INSTALL-on-miss, so this is
    // the natural caller pattern; the assertion catches caller bugs.)
    always @(posedge clk) begin
        if (rst_n && (access_action == ACTION_INSTALL) && access_hit) begin
            $error("monbus_cam: ACTION_INSTALL asserted but key already in CAM (key=0x%h)",
                   access_key);
        end
    end

    // Match vector must be at most one-hot.
    always @(posedge clk) begin
        if (rst_n) begin
            int match_count;
            match_count = 0;
            for (int i = 0; i < DEPTH; i++) begin
                if (w_match_oh[i]) match_count = match_count + 1;
            end
            if (match_count > 1) begin
                $error("monbus_cam: %0d slots matched lookup key (expected 0 or 1)",
                       match_count);
            end
        end
    end
`endif

endmodule : monbus_cam
