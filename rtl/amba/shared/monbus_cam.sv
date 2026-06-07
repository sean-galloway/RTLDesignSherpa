// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monbus_cam
// Purpose: Caching CAM for the monbus bulk-trace compressor.
//
// Documentation: docs/markdown/RTLAmba/shared/monbus_cam.md  (TBD)
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-06-06
//
// ============================================================================
// Module: monbus_cam
// ============================================================================
//
// What this is
// ------------
// A parameterizable Content-Addressable Memory designed for the monbus
// bulk-trace compressor that sits inside monbus_axil_group. Stores
// template entries keyed by a wide tuple (typical use:
//   {packet_type[4], protocol[4], event_code[8], channel_id[9],
//    agent_id[16], unit_id[8]}  =  49 bits)
// alongside a payload (typical: last_event_data[64]) used for the
// compressor's delta-encoding formats.
//
// Why not q32_axi_id_cam or cam_tag
// ---------------------------------
// The existing CAMs in the tree (rtl/common/cam_tag.sv,
// projects/.../q32_axi_id_cam.sv) are allocate/free designs: the
// upstream module explicitly issues a deallocate when an entry is
// done. The compressor has no such signal -- monbus templates are
// "cached" by access patterns, not owned. When the CAM fills, a new
// template MUST be installed by evicting an existing entry, never
// refused. This module handles that case internally.
//
// Eviction policy (current cut: FIFO)
// -----------------------------------
// On install-when-full, the entry installed earliest is evicted.
// Implemented with a single insertion-order ring pointer rather than
// per-entry LRU age counters -- N-1 entries don't have to be touched
// every cycle, and the eviction-victim lookup is a single index, not a
// max-over-N. Trade-off: worse hit rate than true LRU when traffic is
// bursty for one template then quiet for a while. The Python encoder
// model in bin/TBClasses/monbus/monbus_compressor.py supports both
// policies; if real traces show FIFO is insufficient, an LRU variant
// (or a parameterized policy selector) can land in a follow-up.
//
// Interface model
// ---------------
// One access port per cycle. The caller drives a lookup key, sees the
// combinational hit/miss result, and in the same cycle commits one of:
//   - NO-OP        (action = ACTION_NONE)         -- pure lookup
//   - TOUCH-update (action = ACTION_TOUCH)        -- hit, refresh payload
//   - INSTALL      (action = ACTION_INSTALL)      -- miss, install (may evict)
//
// Combinational lookup result available the SAME cycle the key is
// driven; the registered state update happens on the next rising edge.
// This matches a pipelined caller doing:
//   stage 0: produce key from input record
//   stage 1: look up + decide format + assert action
//   stage 2: see CAM state update reflected
//
// Status outputs
// --------------
// cam_full     -- all DEPTH slots in use
// cam_count    -- current occupancy (for stats / CSR readback)
// evicted     -- pulses 1 on a cycle an install caused eviction (for
//                  the compressor's escape-reason counter)
//
// Reset behavior
// --------------
// All entries marked invalid. r_install_ptr = 0. cam_count = 0.
//
// Testing
// -------
// Companion cocotb test: val/amba/test_monbus_cam.py  (TBD)
// Python golden model: bin/TBClasses/monbus/monbus_compressor.py (Cam class)
// ============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_cam #(
    parameter int KEY_WIDTH  = 49,      // template-key width
    parameter int DATA_WIDTH = 64,      // payload width (e.g. last_event_data)
    parameter int DEPTH      = 16,      // number of CAM entries
    // localparams
    parameter int IDX_WIDTH  = (DEPTH > 1) ? $clog2(DEPTH) : 1,
    parameter int CNT_WIDTH  = $clog2(DEPTH + 1)
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // === Access port (single port, lookup + commit in one cycle) ===
    // Lookup (combinational on this cycle's inputs):
    input  logic [KEY_WIDTH-1:0]    access_key,
    output logic                    access_hit,
    output logic [IDX_WIDTH-1:0]    access_idx,      // valid only when access_hit
    output logic [DATA_WIDTH-1:0]   access_old_data, // current payload at access_idx (valid only when access_hit)

    // Commit (sampled on rising edge; takes effect cycle N+1):
    // 2'b00 ACTION_NONE     -- no state change (pure lookup)
    // 2'b01 ACTION_TOUCH    -- entry at access_idx gets access_new_data written; no key change
    // 2'b10 ACTION_INSTALL  -- access_key + access_new_data installed; if full, oldest entry evicted
    // 2'b11 reserved
    input  logic [1:0]              access_action,
    input  logic [DATA_WIDTH-1:0]   access_new_data,

    // === Status (combinational) ===
    output logic                    cam_full,
    output logic [CNT_WIDTH-1:0]    cam_count,

    // === Eviction notification (combinational pulse on commit cycle) ===
    output logic                    evicted          // 1 when this cycle's INSTALL evicts an existing entry
);

    // ------------------------------------------------------------------------
    // Action encoding (must match the access_action input above).
    // ------------------------------------------------------------------------
    localparam logic [1:0] ACTION_NONE    = 2'b00;
    localparam logic [1:0] ACTION_TOUCH   = 2'b01;
    localparam logic [1:0] ACTION_INSTALL = 2'b10;
    // 2'b11 reserved

    // ------------------------------------------------------------------------
    // Entry storage: valid bit, key, payload, plus an insertion-order ring.
    // r_install_ptr names the slot where the NEXT install will land. On a
    // miss-with-full, that slot's existing contents are the FIFO victim.
    // On miss-with-not-full, that slot is necessarily invalid (the install
    // pointer wraps after DEPTH installs, never sooner than the CAM fills).
    // ------------------------------------------------------------------------
    logic                    r_valid     [DEPTH];
    logic [KEY_WIDTH-1:0]    r_key       [DEPTH];
    logic [DATA_WIDTH-1:0]   r_data      [DEPTH];
    logic [IDX_WIDTH-1:0]    r_install_ptr;
    logic [CNT_WIDTH-1:0]    r_count;

    // ------------------------------------------------------------------------
    // Combinational match vector + priority encoder for lookup hit.
    // Lowest index wins on duplicate matches (shouldn't happen by design --
    // each template tuple is unique by construction in the compressor -- but
    // the encoder is well-defined either way).
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
        for (int i = DEPTH-1; i >= 0; i--) begin
            if (w_match_oh[i]) begin
                access_hit      = 1'b1;
                access_idx      = IDX_WIDTH'(i);
                access_old_data = r_data[i];
            end
        end
    end

    // ------------------------------------------------------------------------
    // Status outputs.
    // ------------------------------------------------------------------------
    assign cam_count = r_count;
    assign cam_full  = (r_count == CNT_WIDTH'(DEPTH));

    // Eviction notification: pulses high on the cycle of a full-CAM install.
    assign evicted = (access_action == ACTION_INSTALL) && cam_full;

    // ------------------------------------------------------------------------
    // Registered state update.
    //
    // Touch:    overwrite r_data[access_idx]; valid stays 1; key stays the
    //           same. No effect on r_install_ptr / r_count.
    //
    // Install (CAM not full): land at r_install_ptr (guaranteed invalid),
    //           advance the pointer (mod DEPTH), bump r_count.
    //
    // Install (CAM full): land at r_install_ptr (the FIFO victim), advance
    //           the pointer, r_count stays at DEPTH. The victim's old data
    //           is silently overwritten -- the compressor caller has already
    //           consumed it via access_old_data on the lookup match (if any)
    //           or doesn't need it (miss path emits a raw escape that doesn't
    //           reference templates).
    //
    // Action collision (caller asserts both TOUCH and INSTALL simultaneously)
    // is undefined by the access_action enum; the case statement below
    // covers the two valid update actions and ignores the rest.
    // ------------------------------------------------------------------------

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < DEPTH; i++) begin
                r_valid[i] <= 1'b0;
                r_key[i]   <= '0;
                r_data[i]  <= '0;
            end
            r_install_ptr <= '0;
            r_count       <= '0;
        end else begin
            unique case (access_action)
                ACTION_TOUCH: begin
                    // Touch only takes effect when the lookup actually hit.
                    // If the caller asserts touch without a hit, this is a
                    // no-op (the protocol is "touch the entry you just hit").
                    if (access_hit) begin
                        r_data[access_idx] <= access_new_data;
                    end
                end

                ACTION_INSTALL: begin
                    r_valid[r_install_ptr] <= 1'b1;
                    r_key[r_install_ptr]   <= access_key;
                    r_data[r_install_ptr]  <= access_new_data;
                    // Advance install pointer (wraps via mod-DEPTH).
                    if (r_install_ptr == IDX_WIDTH'(DEPTH-1)) begin
                        r_install_ptr <= '0;
                    end else begin
                        r_install_ptr <= r_install_ptr + 1'b1;
                    end
                    // Only bump count when filling a previously-invalid slot.
                    if (!cam_full) begin
                        r_count <= r_count + 1'b1;
                    end
                end

                default: begin
                    // ACTION_NONE or reserved -- no state change.
                end
            endcase
        end
    )

    // ========================================================================
    // Assertions (simulation only)
    // ========================================================================

`ifdef SIMULATION
    // Touch without hit is a protocol violation by the caller -- flag it.
    always @(posedge clk) begin
        if (rst_n && (access_action == ACTION_TOUCH) && !access_hit) begin
            $error("monbus_cam: ACTION_TOUCH asserted but lookup missed (key=0x%h)",
                   access_key);
        end
    end

    // Match vector should be at most one-hot (templates are unique by
    // construction; if two slots match, something has gone wrong).
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
