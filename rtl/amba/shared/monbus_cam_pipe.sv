// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: monbus_cam_pipe
// Purpose: 2-cycle pipelined variant of monbus_cam. The single-cycle CAM's
//          compare -> priority-encode -> move-to-front shift ran as one
//          combinational chain across all 32 entries and was the 100 MHz
//          route-bound critical path. This splits it:
//            cycle T   : 32-way key compare (broadcast + 49b equality)
//            cycle T+1 : priority-encode + commit (shift) + result register
//          so each cycle does ONE half, not the series of both.
//
//          Result has 1-cycle latency vs monbus_cam (the caller registers it
//          one stage later). Throughput is unchanged (1 access/cycle) -- a
//          depth-1 FORWARDING path corrects the next lookup for the in-flight
//          commit, so the (hit, idx, old_data, old_ts) SEQUENCE is bit-exact
//          to monbus_cam. Validated by val/amba/test_monbus_cam_pipe.py.
//
// Subsystem: amba
// ============================================================================
//
// Forwarding (depth-1): when access A is compared at cycle T+1, the previous
// access P is committing this same cycle, so A's combinational match sees the
// PRE-P array. P's commit is a move-to-front from position P.shift_to:
//   - A.key == P.key            : A's entry is now at slot 0 with P's written
//                                  data/ts  -> hit, idx=0, old=P.new_*
//   - A matched the evicted LRU  : (P full-install, A.raw_idx==DEPTH-1) -> miss
//   - A.raw_idx < P.shift_to     : entry shifted down one          -> idx+1
//   - else                       : unchanged                       -> idx
// P.shift_to and the commit shift both read the SAME pre-P r_* this cycle, so
// they agree. Bubbles (access_en low) still let P commit and clear the pending
// slot, so a later access sees a fully-committed array (no forward needed).
// ============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_cam_pipe #(
    parameter int KEY_WIDTH  = 49,
    parameter int DATA_WIDTH = 64,
    parameter int TS_WIDTH   = 24,
    parameter int DEPTH      = 32,
    parameter int IDX_WIDTH  = (DEPTH > 1) ? $clog2(DEPTH) : 1,
    parameter int CNT_WIDTH  = $clog2(DEPTH + 1)
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // Access presented this cycle (accepted when access_en=1; one per cycle).
    // The access is always a lookup + touch-or-install: the CAM self-derives
    // TOUCH (on hit) vs INSTALL (on miss) from its own forwarded hit, because
    // a pipelined caller cannot know the hit at present-cycle time (exposing a
    // combinational hit would defeat the pipeline). This matches the
    // compressor, which always TOUCHes on hit / INSTALLs on miss.
    input  logic                    access_en,
    input  logic [KEY_WIDTH-1:0]    access_key,
    input  logic [DATA_WIDTH-1:0]   access_new_data,
    input  logic [TS_WIDTH-1:0]     access_new_ts,

    // Result of the access presented LAST cycle (1-cycle latency).
    output logic                    result_valid,
    output logic                    result_hit,
    output logic [IDX_WIDTH-1:0]    result_idx,
    output logic [DATA_WIDTH-1:0]   result_old_data,
    output logic [TS_WIDTH-1:0]     result_old_ts,

    output logic                    cam_full,
    output logic [CNT_WIDTH-1:0]    cam_count
);

    localparam logic [1:0] ACTION_NONE    = 2'b00;
    localparam logic [1:0] ACTION_TOUCH   = 2'b01;
    localparam logic [1:0] ACTION_INSTALL = 2'b10;

    logic                    r_valid [DEPTH];
    logic [KEY_WIDTH-1:0]    r_key   [DEPTH];
    logic [DATA_WIDTH-1:0]   r_data  [DEPTH];
    logic [TS_WIDTH-1:0]     r_ts    [DEPTH];
    logic [CNT_WIDTH-1:0]    r_count;

    assign cam_count = r_count;
    assign cam_full  = (r_count == CNT_WIDTH'(DEPTH));

    // ----- this cycle's combinational match (vs PRE-commit r_*) -----
    logic [DEPTH-1:0]        w_match_oh;
    always_comb begin
        for (int i = 0; i < DEPTH; i++)
            w_match_oh[i] = r_valid[i] && (r_key[i] == access_key);
    end
    logic                    raw_hit;
    logic [IDX_WIDTH-1:0]    raw_idx;
    logic [DATA_WIDTH-1:0]   raw_old_data;
    logic [TS_WIDTH-1:0]     raw_old_ts;
    always_comb begin
        raw_hit = 1'b0; raw_idx = '0; raw_old_data = '0; raw_old_ts = '0;
        for (int i = DEPTH-1; i >= 0; i--) begin
            if (w_match_oh[i]) begin
                raw_hit = 1'b1; raw_idx = IDX_WIDTH'(i);
                raw_old_data = r_data[i]; raw_old_ts = r_ts[i];
            end
        end
    end

    // ----- pending commit (access presented last cycle, commits now) -----
    logic                    s1_valid;
    logic [1:0]              s1_action;
    logic [KEY_WIDTH-1:0]    s1_key;
    logic [DATA_WIDTH-1:0]   s1_new_data;
    logic [TS_WIDTH-1:0]     s1_new_ts;
    logic [IDX_WIDTH-1:0]    s1_eff_idx;
    logic                    s1_eff_hit;

    // Commit geometry, combinational from s1_* + the SAME pre-commit r_*.
    logic [CNT_WIDTH-1:0]    s1_shift_to;
    logic                    s1_do_shift;
    logic                    s1_evict;
    always_comb begin
        s1_do_shift = 1'b0; s1_shift_to = '0; s1_evict = 1'b0;
        if (s1_valid) begin
            if (s1_action == ACTION_TOUCH) begin
                if (s1_eff_hit) begin
                    s1_do_shift = 1'b1;
                    s1_shift_to = CNT_WIDTH'(s1_eff_idx);
                end
            end else if (s1_action == ACTION_INSTALL) begin
                s1_do_shift = 1'b1;
                s1_shift_to = cam_full ? CNT_WIDTH'(DEPTH-1) : r_count;
                s1_evict    = cam_full;
            end
        end
    end

    // ----- forward-adjust raw match -> effective (post-s1) result -----
    logic                    eff_hit;
    logic [IDX_WIDTH-1:0]    eff_idx;
    logic [DATA_WIDTH-1:0]   eff_old_data;
    logic [TS_WIDTH-1:0]     eff_old_ts;
    always_comb begin
        eff_hit = raw_hit; eff_idx = raw_idx;
        eff_old_data = raw_old_data; eff_old_ts = raw_old_ts;
        if (s1_do_shift) begin
            if (access_key == s1_key) begin
                // same template P just moved to slot 0 with its written values
                eff_hit = 1'b1; eff_idx = '0;
                eff_old_data = s1_new_data; eff_old_ts = s1_new_ts;
            end else if (raw_hit) begin
                if (s1_evict && (raw_idx == IDX_WIDTH'(DEPTH-1))) begin
                    eff_hit = 1'b0;                 // matched the evicted LRU
                end else if (CNT_WIDTH'(raw_idx) < s1_shift_to) begin
                    eff_idx = raw_idx + IDX_WIDTH'(1);
                end
            end
        end
        // On a miss, idx/old_* are don't-care; zero them to match monbus_cam.
        if (!eff_hit) begin
            eff_idx = '0; eff_old_data = '0; eff_old_ts = '0;
        end
    end

    // ----- registered state: commit s1, capture this access -----
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < DEPTH; i++) begin
                r_valid[i] <= 1'b0; r_key[i] <= '0; r_data[i] <= '0; r_ts[i] <= '0;
            end
            r_count      <= '0;
            s1_valid     <= 1'b0;
            s1_action    <= ACTION_NONE;
            s1_key       <= '0;
            s1_new_data  <= '0;
            s1_new_ts    <= '0;
            s1_eff_idx   <= '0;
            s1_eff_hit   <= 1'b0;
            result_valid <= 1'b0;
            result_hit   <= 1'b0;
            result_idx   <= '0;
            result_old_data <= '0;
            result_old_ts   <= '0;
        end else begin
            // (1) Commit the pending access P (move-to-front shift).
            if (s1_do_shift) begin
                r_valid[0] <= 1'b1;
                r_key[0]   <= s1_key;
                r_data[0]  <= s1_new_data;
                r_ts[0]    <= s1_new_ts;
                for (int i = 1; i < DEPTH; i++) begin
                    if (CNT_WIDTH'(i) <= s1_shift_to) begin
                        r_valid[i] <= r_valid[i-1];
                        r_key[i]   <= r_key[i-1];
                        r_data[i]  <= r_data[i-1];
                        r_ts[i]    <= r_ts[i-1];
                    end
                end
                if (s1_action == ACTION_INSTALL && !cam_full)
                    r_count <= r_count + 1'b1;
            end

            // (2) Capture this cycle's access as the next pending commit, and
            //     register its (forwarded) result for output next cycle.
            if (access_en) begin
                s1_valid    <= 1'b1;
                // self-derived: TOUCH on (forwarded) hit, else INSTALL.
                s1_action   <= eff_hit ? ACTION_TOUCH : ACTION_INSTALL;
                s1_key      <= access_key;
                s1_new_data <= access_new_data;
                s1_new_ts   <= access_new_ts;
                s1_eff_idx  <= eff_idx;
                s1_eff_hit  <= eff_hit;
                result_valid    <= 1'b1;
                result_hit      <= eff_hit;
                result_idx      <= eff_idx;
                result_old_data <= eff_old_data;
                result_old_ts   <= eff_old_ts;
            end else begin
                s1_valid     <= 1'b0;
                result_valid <= 1'b0;
            end
        end
    )

endmodule : monbus_cam_pipe
