// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: error_injector
// Purpose:
//   Shared test stimulus: corrupts a coded valid/ready stream between an
//   encoder and a decoder under host control -- an exact number of errors per
//   block, a burst, an error rate, or random burst clusters.
//
// Documentation: projects/components/utility-ip/misc/README.md
// Subsystem: utility-ip/misc
//
// Author: sean galloway
// Created: 2026-10-04 (unified from bch_error_injector and rs_error_injector)

`timescale 1ns/1ps
`include "reset_defs.svh"

//==============================================================================
// Module: error_injector
//==============================================================================
// Description:
//   A three-stage valid/ready pipeline on the stream (data XORed with the
//   error pattern, keep/last untouched), so it sits anywhere on a coded
//   stream. Errors must be injected AFTER the encoder -- an error in the
//   generator's data is encoded faithfully and the code cannot see it --
//   which is why this is its own block and not a mode of the pattern
//   generator.
//
//   Granularity: SYMBOL_WIDTH = 1 makes it a bit injector (every hit XORs a
//   1, as binary BCH wants). SYMBOL_WIDTH = m makes it a symbol injector:
//   every hit XORs a random nonzero m-bit value into the symbol (a zero
//   would be no error), as Reed-Solomon wants. One module, both codecs.
//
//   Modes (cfg_mode):
//     0 NONE      pass through
//     1 COUNT     exactly cfg_count errors per block at uniformly random
//                 distinct positions, by selection sampling (Knuth's
//                 Algorithm S): symbol j of n is hit with probability
//                 e_left / (n - j), evaluated as r16 * (n - j) < e_left << 16
//                 with a 16-bit random r16; the last positions are hit with
//                 certainty when e_left catches up, so the count is exact
//                 whenever cfg_count <= n
//     2 BURST     cfg_count consecutive symbols from a random start
//     3 RATE      each symbol independently with probability cfg_rate / 65536
//     4 CLUSTERS  per block, draw N uniformly from [cfg_cnt_min, cfg_cnt_max],
//                 then per cluster draw a length uniformly from
//                 [cfg_len_min, cfg_len_max] and a uniform start in
//                 [0, N_SYMBOLS - length]; every symbol in a cluster range is
//                 hit. Overlapping clusters merge. Two dedicated xorshift
//                 streams draw the count/lengths and the starts, so cluster
//                 geometry is independent of the per-lane hit randoms.
//                 Presets model real media: small count and length ranges
//                 give DRAM multi-bit-upset patterns, larger ranges give
//                 flash disturbed pages.
//     5 LOCALIZED hits at cfg_rate density confined to one sub-window per
//                 block: the window width is drawn uniformly from
//                 [cfg_len_min, cfg_len_max] and its start uniformly from
//                 [0, N_SYMBOLS - width]. Models a damaged page region, a
//                 failed symbol column, or a half-plane failure -- real
//                 errors are often far more localized than uniform.
//     6 BADBLOCK  per block, with probability cfg_len_min / 65536 the block
//                 runs at the elevated rate cfg_len_max, otherwise at
//                 cfg_rate; models NAND retention tails and worn blocks --
//                 most of the stream is clean with a hard minority that is
//                 very bad, which uniform RATE cannot express.
//     7 DEBUG     deterministic walking errors: block b hits the symbols at
//                 ((b * step + j) mod N_SYMBOLS) for j < cfg_count, step =
//                 cfg_rate. No randoms on the hit path -- a counter and a
//                 subtract-compare -- so it is the hand-checkable bring-up
//                 mode whose timing closes by inspection. Every position is
//                 exercised over a campaign, at a configurable pace.
//
//   COUNT timing: exact selection sampling needs the running hit count --
//   each lane's threshold depends on how many lower lanes hit -- a prefix
//   recurrence that is ~111 logic levels when all lanes of a wide beat decide
//   in one cycle and cannot close at 100 MHz. Stage C therefore decides
//   GRP lanes per cycle (group-local 4-bit prefix, the group-start count
//   folded into per-lane thresholds in parallel), walking a wide beat over
//   N_GRP cycles while it waits in the B skid; the hit mask and count
//   accumulate in registers and release on the final group. GRP is 2 so the
//   conditional-increment ripple stays carry-chain shallow post-route; COUNT
//   mode on a 32-bit beat takes 16 cycles (~6 Mbit/s), far above any UART-fed
//   loop rate. BURST, RATE and CLUSTERS are per-lane independent and stay
//   single-cycle, full rate.
//
//   Pipeline (each stage a register with valid/ready):
//     A  accept the beat, snapshot the lane generators (r16 draw + error
//        value), the block position, and -- on a block's first beat -- draw
//        the cluster table from the two stream generators
//     B  the per-lane products r16 * (n - pos - u) and the burst start, in
//        DSPs, from A's registers -- the multiply is the long path
//     C  the decisions and the error mask; the statistics update one cycle
//        later from the registered hit count; the configuration is
//        re-registered locally, so the CSR block is off every path.
//
//   Statistics for the host: total symbols injected (bits when
//   SYMBOL_WIDTH = 1), blocks with at least one injected symbol, blocks with
//   more than T_SYMBOLS injected (the ones a decoder must flag), and the
//   count injected into the most recent block. cfg_clear zeroes them;
//   cfg_seed_load reseeds every generator.
//
//   Erasure marking: with cfg_mark_erasure set, out_erasure carries the
//   beat's hit mask -- lane u flagged exactly where a symbol was corrupted.
//   Wired to a decoder's erasure sideband it turns any placement mode into an
//   erasure run: the positions the decoder is TOLD about are precisely the
//   ones that were hit, which is the information a RAID stripe map or an
//   MC's known-bad column has. With the bit clear out_erasure is all zero.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH:     1 = bit injector, m = symbol injector (GF(2^m) symbols
//   SYMBOLS_PER_BEAT: lanes per beat
//   N_SYMBOLS:        block length in symbols (<= 65535)
//   T_SYMBOLS:        correctable count, for the over-t statistic only
//   DATA_WIDTH:       SYMBOL_WIDTH * SYMBOLS_PER_BEAT
//
//==============================================================================

module error_injector #(
    parameter int SYMBOL_WIDTH     = 1,
    parameter int SYMBOLS_PER_BEAT = 8,
    parameter int N_SYMBOLS        = 8191,
    parameter int T_SYMBOLS        = 8,
    parameter int DATA_WIDTH       = SYMBOL_WIDTH * SYMBOLS_PER_BEAT
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    input  logic                        in_valid,
    output logic                        in_ready,
    input  logic [DATA_WIDTH-1:0]       in_data,
    input  logic [SYMBOLS_PER_BEAT-1:0] in_keep,
    input  logic                        in_last,

    output logic                        out_valid,
    input  logic                        out_ready,
    output logic [DATA_WIDTH-1:0]       out_data,
    output logic [SYMBOLS_PER_BEAT-1:0] out_keep,
    output logic                        out_last,
    // the beat's hit mask when cfg_mark_erasure is set, else all zero
    output logic [SYMBOLS_PER_BEAT-1:0] out_erasure,

    input  logic [2:0]                  cfg_mode,
    input  logic [7:0]                  cfg_count,
    input  logic [15:0]                 cfg_rate,
    input  logic [31:0]                 cfg_seed,
    input  logic                        cfg_seed_load,
    input  logic                        cfg_clear,
    input  logic                        cfg_mark_erasure,
    input  logic [7:0]                  cfg_cnt_min,
    input  logic [7:0]                  cfg_cnt_max,
    input  logic [15:0]                 cfg_len_min,
    input  logic [15:0]                 cfg_len_max,

    output logic [31:0]                 o_inj_symbols,
    output logic [31:0]                 o_inj_blocks,
    output logic [31:0]                 o_inj_over_t,
    output logic [7:0]                  o_last_block_errors
);

    localparam int M     = SYMBOL_WIDTH;
    localparam int S     = SYMBOLS_PER_BEAT;
    localparam int N     = N_SYMBOLS;
    localparam int POS_W = 16;
    localparam int LW    = 32;
    localparam int MAXB  = 8;   // clusters per block in mode 4

    // -------------------------------------------------------------------------
    // Configuration, re-registered locally: the values are static during a run
    // and the CSR block sits far away; the copy is one cycle late, which no
    // caller can observe.
    // -------------------------------------------------------------------------
    logic [2:0]  r_mode;
    logic [7:0]  r_count;
    logic [15:0] r_rate;
    logic        r_mark_erasure;
    logic [7:0]  r_cnt_min, r_cnt_max;
    logic [15:0] r_len_min, r_len_max;
    // range spans + 1, registered once per config change. Registering keeps
    // the quasi-static config out of the per-block draw multiplies: left
    // combinational, Vivado builds a PCIN cascade across the 17 draw DSPs and
    // the config ripples through the whole chain (12.7 ns path on Genesys 2)
    logic [31:0] r_span_cnt, r_span_len;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_mode <= '0; r_count <= '0; r_rate <= '0; r_mark_erasure <= 1'b0;
            r_cnt_min <= '0; r_cnt_max <= '0; r_len_min <= '0; r_len_max <= '0;
            r_span_cnt <= '0; r_span_len <= '0;
        end else begin
            r_mode <= cfg_mode; r_count <= cfg_count; r_rate <= cfg_rate;
            r_mark_erasure <= cfg_mark_erasure;
            r_cnt_min <= cfg_cnt_min; r_cnt_max <= cfg_cnt_max;
            r_len_min <= cfg_len_min; r_len_max <= cfg_len_max;
            r_span_cnt <= 32'(cfg_cnt_max) - 32'(cfg_cnt_min) + 32'd1;
            r_span_len <= 32'(cfg_len_max) - 32'(cfg_len_min) + 32'd1;
        end
    )

    // -------------------------------------------------------------------------
    // Stage C control declarations (before first use: the stage A handshakes
    // below gate on them, and lint-decl-order requires declare-before-use)
    // -------------------------------------------------------------------------
    localparam int GRP   = (S < 2) ? S : 2;     // lanes decided per cycle
    localparam int N_GRP = (S + GRP - 1) / GRP; // cycles per COUNT beat
    localparam int CYC_W = (N_GRP > 1) ? $clog2(N_GRP) : 1;

    logic             w_count_mode;
    logic [CYC_W-1:0] r_cyc;      // group being decided
    logic             r_dec_busy; // a multi-cycle COUNT decision owns stage C
    logic [7:0]       r_k_mid;    // within-beat count entering the current group
    logic [7:0]       r_hit_acc;  // hits accumulated across the groups of this beat
    logic [S-1:0]     r_mask_acc;

    logic [7:0]       w_start_k, w_k_next, w_grp_hits;
    logic [GRP-1:0]   w_ghit;
    logic [GRP-1:0]   w_gkeep;
    logic [7:0]       w_kp [GRP];         // group-local capacity; 0 = cannot hit
    logic             w_dec_step, w_dec_fire;
    logic             w_app_mode, w_draw_hold, w_draw_wait;
    logic             r_b_first;          // the beat in A/B opens a block
    logic             r_draw_busy, r_draw_done;

    // -------------------------------------------------------------------------
    // Stage A: accept a beat; one 32-bit xorshift generator per lane advances
    // with it, plus two stream generators for mode-4 cluster geometry.
    // -------------------------------------------------------------------------
    logic w_a_fire, w_b_fire, w_c_fire;
    logic r_a_v, r_b_v, r_c_v;
    logic w_a_ready, w_b_ready, w_c_ready;

    assign w_c_ready = (!r_c_v || out_ready) && !r_dec_busy && !w_draw_wait;
    // COUNT holds the beat in B for N_GRP decision cycles; in that mode B only
    // refills once empty. BURST / RATE / CLUSTERS keep the single-cycle
    // overlap; the app modes also pause the input for the draw walk and hold
    // the block-start beat until the table is complete.
    assign w_b_ready = !r_b_v || (w_c_ready && !w_count_mode);
    assign w_a_ready = !r_a_v || (w_b_ready && !w_draw_hold);
    assign in_ready  = w_a_ready;
    assign w_a_fire  = in_valid && w_a_ready;
    assign w_b_fire  = r_a_v && w_b_ready;
    assign w_c_fire  = r_b_v && w_c_ready;
    assign w_draw_hold = w_app_mode && r_draw_busy;
    assign w_draw_wait = w_app_mode && r_b_v && r_b_first && !r_draw_done;

    function automatic logic [LW-1:0] xorshift32(input logic [LW-1:0] x);
        logic [LW-1:0] y;
        y = x ^ (x << 13);
        y = y ^ (y >> 17);
        y = y ^ (y << 5);
        return y;
    endfunction

    // One xorshift32 generator per lane (x ^= x << 13; x ^= x >> 17; x ^= x << 5):
    // every bit of the state changes on every step, so consecutive beats draw
    // decorrelated numbers. A one-bit-per-step LFSR was tried first and its
    // 16-bit windows, each the previous one shifted by a bit, clustered the
    // RATE mode's hits (261 in a 204 +- 54 window at S = 1).
    logic [LW-1:0] r_rnd [S];
    logic [LW-1:0] w_rnd [S];
    always_comb begin
        for (int u = 0; u < S; u++) w_rnd[u] = xorshift32(r_rnd[u]);
    end

    // The two cluster-geometry streams (mode 4): stream A draws the cluster
    // count and the lengths, stream B draws the starts. Distinct seed mixes
    // keep them independent of each other and of the lane generators.
    logic [LW-1:0] r_rnd_a, r_rnd_b;
    logic [LW-1:0] w_rnd_a, w_rnd_b;
    assign w_rnd_a = xorshift32(r_rnd_a);
    assign w_rnd_b = xorshift32(r_rnd_b);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int u = 0; u < S; u++) r_rnd[u] <= 32'h9E37_79B9 * 32'(u + 1);
            r_rnd_a <= (32'h9E37_79B9 * 32'd3);
            r_rnd_b <= (32'h9E37_79B9 * 32'd7);
        end else if (cfg_seed_load) begin
            // a zero state would stick at zero; the mix keeps every stream nonzero
            for (int u = 0; u < S; u++) r_rnd[u] <= (cfg_seed ^ (32'h9E37_79B9 * 32'(u + 1))) | 32'h1;
            r_rnd_a <= (cfg_seed ^ (32'h9E37_79B9 * 32'd3)) | 32'h1;
            r_rnd_b <= (cfg_seed ^ (32'h9E37_79B9 * 32'd7)) | 32'h1;
        end else if (w_a_fire) begin
            for (int u = 0; u < S; u++) r_rnd[u] <= w_rnd[u];
            r_rnd_a <= w_rnd_a;
            r_rnd_b <= w_rnd_b;
        end
    )

    // block position of lane 0 for the beat being accepted
    logic [POS_W-1:0] r_pos;
    logic             r_first;

    // A registers
    logic [DATA_WIDTH-1:0] r_a_data;
    logic [S-1:0]          r_a_keep;
    logic                  r_a_last, r_a_first;
    logic [POS_W-1:0]      r_a_pos;
    logic [15:0]           r_a_r16 [S];
    logic [M-1:0]          r_a_val [S];
    logic [15:0]           r_a_rem [S];    // n - pos - u, the selection-sampling denominator
    logic [S-1:0]          r_a_inrange;    // pos + u < n

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_pos   <= '0;
            r_first <= 1'b1;
            r_a_v   <= 1'b0;
            r_a_data <= '0; r_a_keep <= '0; r_a_last <= 1'b0; r_a_first <= 1'b0; r_a_pos <= '0;
            r_a_inrange <= '0;
            for (int u = 0; u < S; u++) begin
                r_a_r16[u] <= '0;
                r_a_val[u] <= '0;
                r_a_rem[u] <= '0;
            end
        end else begin
            if (w_a_fire) begin
                r_a_v     <= 1'b1;
                r_a_data  <= in_data;
                r_a_keep  <= in_keep;
                r_a_last  <= in_last;
                r_a_first <= r_first;
                r_a_pos   <= r_pos;
                for (int u = 0; u < S; u++) begin
                    r_a_r16[u]     <= w_rnd[u][15:0];
                    // the error value: raw register slice with zero remapped to
                    // one so every hit changes the symbol (M = 1 collapses to 1)
                    r_a_val[u]     <= (w_rnd[u][16 +: M] == '0) ? M'(1) : w_rnd[u][16 +: M];
                    r_a_rem[u]     <= POS_W'(N) - r_pos - POS_W'(u);
                    r_a_inrange[u] <= (r_pos + POS_W'(u)) < POS_W'(N);
                end
                r_pos   <= in_last ? '0 : r_pos + POS_W'(S);
                r_first <= in_last;
            end else if (w_b_fire) begin
                r_a_v <= 1'b0;
            end
        end
    )

    // -------------------------------------------------------------------------
    // Mode 4/5/6 block-start draw, SERIALIZED. The cluster/geometry values are
    // identical to the parallel form; only the timing differs. The streams are
    // walked one xorshift per cycle from a snapshot taken on the block's first
    // accepted beat, at most one multiply per cycle, because the parallel
    // unrolled draw -- 9 xorshifts plus 17 multiplies in one cycle -- mapped
    // into a PCIN-cascaded DSP blob and was the design's worst path twice
    // (~13 ns on Genesys 2). Validation hardware takes the backpressure: the
    // input pauses for the ~2*MAXB+2 cycle walk, and the block-start beat is
    // held at stage B until the table is complete.
    // -------------------------------------------------------------------------
    logic [POS_W-1:0] r_tab_start [MAXB];
    logic [15:0]      r_tab_len   [MAXB];
    logic [3:0]       r_n_burst;

    // per-block state for the application modes, filled by the draw walk
    // below; declared before first use (lint-decl-order), consumed in stage C
    logic [POS_W-1:0] r_loc_start, r_loc_wid;  // 5 LOCALIZED window
    logic             r_bad;                   // 6 BADBLOCK severity draw
    logic [15:0]      r_rate_eff;              // 6 BADBLOCK selected rate
    logic [POS_W-1:0] r_dbg_base;              // 7 DEBUG walk position

    logic [LW-1:0]    r_dxa, r_dxb;          // walking stream states
    logic [LW-1:0]    r_xa_hold, r_xb_hold;  // snapshot awaiting the walk
    logic             r_snap_pending;
    logic [4:0]       r_draw_cnt;
    logic [7:0]       w_fsm_n;
    logic [15:0]      w_fsm_l;
    logic [15:0]      w_fsm_li;
    logic [POS_W-1:0] w_fsm_s;
    logic [POS_W-1:0] w_fsm_s_loc;

    assign w_app_mode = (r_mode == 3'd4) || (r_mode == 3'd5) || (r_mode == 3'd6);

    // per-cycle draw step: at most one scale multiply on the registered
    // walking state, so no cascade and no long combinational chain. S_i uses
    // the L_i REGISTERED by the preceding odd count, not the live walking
    // state (which has already advanced past it).
    always_comb begin
        w_fsm_n = 8'(MAXB);
        if (r_cnt_max > r_cnt_min)
            w_fsm_n = r_cnt_min + 8'((32'(r_dxa[15:0]) * r_span_cnt) >> 16);
        else
            w_fsm_n = r_cnt_min;
        if (w_fsm_n > 8'(MAXB)) w_fsm_n = 8'(MAXB);
        if (r_len_max > r_len_min)
            w_fsm_l = r_len_min + 16'((32'(r_dxa[15:0]) * r_span_len) >> 16);
        else
            w_fsm_l = r_len_min;
        if (w_fsm_l > 16'(N)) w_fsm_l = 16'(N);
        w_fsm_li = r_tab_len[(int'(r_draw_cnt) >= 2) ? (int'(r_draw_cnt) - 2) / 2 : 0];
        w_fsm_s  = POS_W'((32'(r_dxb[15:0]) * (32'(N) - 32'(w_fsm_li) + 32'd1)) >> 16);
        // mode 5's window start must use the UNGATED width: r_loc_wid is
        // written without the (i < n_burst) cluster gate (mode 5 has no
        // cluster count), while r_tab_len is gated for mode 4 -- with a
        // zero/leftover cnt range the gated entry is 0 and would shift the
        // window start by drawing S against (N + 1) instead of (N - wid + 1)
        w_fsm_s_loc = POS_W'((32'(r_dxb[15:0]) * (32'(N) - 32'(r_loc_wid) + 32'd1)) >> 16);
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_n_burst <= '0;
            for (int i = 0; i < MAXB; i++) begin
                r_tab_start[i] <= '0;
                r_tab_len[i]   <= '0;
            end
            r_loc_start <= '0;
            r_loc_wid   <= '0;
            r_bad       <= 1'b0;
            r_rate_eff  <= '0;
            r_dbg_base  <= '0;
            r_dxa <= '0; r_dxb <= '0;
            r_xa_hold <= '0; r_xb_hold <= '0;
            r_snap_pending <= 1'b0; r_draw_busy <= 1'b0; r_draw_done <= 1'b0;
            r_draw_cnt <= '0;
        end else begin
            // snapshot the stream states on the block's first accepted beat;
            // 7 DEBUG advances its deterministic walk here too
            if (w_a_fire && r_first) begin
                r_xa_hold <= w_rnd_a;
                r_xb_hold <= w_rnd_b;
                r_snap_pending <= 1'b1;
                r_draw_done <= 1'b0;
                r_dbg_base <= (r_dbg_base + POS_W'(r_rate) >= POS_W'(N))
                              ? (r_dbg_base + POS_W'(r_rate) - POS_W'(N))
                              : (r_dbg_base + POS_W'(r_rate));
            end
            // start the walk once the previous one has finished; the table is
            // invalidated HERE (not at snapshot) so a previous walk's
            // end-of-walk done flag can never survive into the new block --
            // a block accepted mid-walk (non-app phases do not pause the
            // input) snapshots new state while the old walk is still running,
            // and only this ordering keeps done honest
            if (r_snap_pending && !r_draw_busy) begin
                r_snap_pending <= 1'b0;
                r_draw_busy    <= 1'b1;
                r_draw_done    <= 1'b0;
                r_draw_cnt     <= '0;
                r_dxa          <= r_xa_hold;
                r_dxb          <= r_xb_hold;
            end else if (r_draw_busy) begin
                r_draw_cnt <= r_draw_cnt + 1'b1;
                if (r_draw_cnt == 5'd0) begin
                    // N (and the 6 BADBLOCK severity draw) from the first value
                    r_n_burst  <= 4'(w_fsm_n);
                    r_bad      <= (r_dxa[15:0] < r_len_min);
                    r_rate_eff <= (r_dxa[15:0] < r_len_min) ? r_len_max : r_rate;
                    r_dxa      <= xorshift32(r_dxa);
                end else if (r_draw_cnt[0]) begin
                    // odd counts: L_i from the next stream-A value
                    automatic int li = (int'(r_draw_cnt) - 1) / 2;
                    if (li < MAXB) begin
                        r_tab_len[li] <= (li < int'(r_n_burst)) ? w_fsm_l : 16'd0;
                        if (li == 0) r_loc_wid <= w_fsm_l;   // 5 LOCALIZED window width
                    end
                    r_dxa <= xorshift32(r_dxa);
                end else begin
                    // even counts: S_i, using the L_i registered last cycle
                    automatic int si = (int'(r_draw_cnt) - 2) / 2;
                    r_tab_start[si] <= w_fsm_s;
                    if (si == 0) r_loc_start <= w_fsm_s_loc; // 5 LOCALIZED window start
                    r_dxb <= xorshift32(r_dxb);
                end
                if (r_draw_cnt == 5'(2 * MAXB + 1)) begin
                    r_draw_busy <= 1'b0;
                    r_draw_done <= 1'b1;
                end
            end
        end
    )

    // -------------------------------------------------------------------------
    // Stage B: the products, from A's registers -- a bare 16 x 16 multiply per
    // lane (one DSP). Only the high half matters: r16 * rem < e_left << 16 is
    // (r16 * rem) >> 16 < e_left, so the compare in C is 16 bits against 8.
    // -------------------------------------------------------------------------
    logic [31:0] w_lhs [S];       // r16 * (n - pos - u)
    logic [31:0] w_bprod;         // r16_0 * (n - e + 1), for the burst start
    logic [15:0] w_bspan;         // n - e + 1, the burst start's range
    always_comb begin
        for (int u = 0; u < S; u++) w_lhs[u] = 32'(r_a_r16[u]) * 32'(r_a_rem[u]);
        w_bspan = 16'(N) - 16'(r_count) + 16'd1;
        w_bprod = 32'(r_a_r16[0]) * 32'(w_bspan);
    end
    logic unused_frac;
    always_comb begin
        unused_frac = ^w_bprod[15:0];
        for (int u = 0; u < S; u++) unused_frac = unused_frac ^ (^w_lhs[u][15:0]);
    end

    logic [DATA_WIDTH-1:0] r_b_data;
    logic [S-1:0]          r_b_keep;
    logic                  r_b_last;
    logic [POS_W-1:0]      r_b_pos;
    logic [S-1:0]          r_b_inrange;
    logic [15:0]           r_b_lhs_hi [S];
    logic [15:0]           r_b_r16 [S];
    logic [M-1:0]          r_b_val [S];
    logic [POS_W-1:0]      r_b_bstart;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_b_v <= 1'b0;
            r_b_data <= '0; r_b_keep <= '0; r_b_last <= 1'b0; r_b_first <= 1'b0; r_b_pos <= '0;
            r_b_bstart <= '0; r_b_inrange <= '0;
            for (int u = 0; u < S; u++) begin
                r_b_lhs_hi[u] <= '0; r_b_r16[u] <= '0; r_b_val[u] <= '0;
            end
        end else begin
            if (w_b_fire) begin
                r_b_v      <= 1'b1;
                r_b_data   <= r_a_data;
                r_b_keep   <= r_a_keep;
                r_b_last   <= r_a_last;
                r_b_first  <= r_a_first;
                r_b_pos    <= r_a_pos;
                r_b_inrange <= r_a_inrange;
                r_b_bstart <= w_bprod[31:16];
                for (int u = 0; u < S; u++) begin
                    r_b_lhs_hi[u] <= w_lhs[u][31:16];
                    r_b_r16[u] <= r_a_r16[u];
                    r_b_val[u] <= r_a_val[u];
                end
            end else if (w_dec_fire) begin
                r_b_v <= 1'b0;
            end
        end
    )

    // -------------------------------------------------------------------------
    // Stage C: decisions. Per-block state lives here.
    //
    // COUNT decides GRP lanes per cycle: the prefix recurrence (each lane's
    // threshold depends on how many lower lanes hit) is ~111 logic levels
    // across a wide single-cycle beat and cannot close at 100 MHz. The beat
    // waits in the B skid while a group counter walks the lanes; the hit mask
    // and count accumulate in registers and release on the final group. The
    // group-local prefix counter is 4 bits (0..GRP): the group-start count is
    // folded into per-lane capacity thresholds in parallel
    // (Kp' = clamp(Kp - k_start)), which halves the ripple a raw 8-bit
    // counter would pay. BURST / RATE / CLUSTERS are per-lane independent and
    // stay single-cycle.
    // -------------------------------------------------------------------------
    logic [7:0]       r_e_left;       // COUNT: errors still to place after the previous beat
    logic [7:0]       r_blk_errors;   // injected so far in this block
    logic [POS_W-1:0] r_burst_start;

    logic [S-1:0]          w_hit;
    logic [DATA_WIDTH-1:0] w_mask;
    logic [7:0]            w_hits;
    logic [7:0]            w_e_after;

    assign w_count_mode = (r_mode == 3'd1);
    assign w_dec_step   = r_b_v && (w_c_fire || r_dec_busy);
    assign w_dec_fire   = w_dec_step && (!w_count_mode || (r_cyc == CYC_W'(N_GRP-1)));

    always_comb begin
        logic [7:0]       e_left;
        logic [POS_W-1:0] pos;
        logic [POS_W-1:0] bstart;
        logic [7:0]       k;
        logic [16:0]      dpos;
        int               base;
        int               u;
        // defaults for every variable the mode branches assign conditionally;
        // the strict harness sim build treats inferred latches as errors
        e_left     = '0;
        pos        = '0;
        bstart     = '0;
        k          = '0;
        dpos       = '0;
        base       = 0;
        u          = 0;
        w_start_k  = '0;
        w_k_next   = '0;
        w_grp_hits = '0;
        w_hits     = '0;
        w_e_after  = '0;
        w_mask     = '0;
        for (int i = 0; i < GRP; i++) begin
            w_ghit[i]  = 1'b0;
            w_gkeep[i] = 1'b0;
            w_kp[i]    = '0;
        end
        e_left = r_b_first ? r_count : r_e_left;
        bstart = r_b_first ? r_b_bstart : r_burst_start;
        // BURST / RATE / CLUSTERS / LOCALIZED / BADBLOCK / DEBUG:
        // per-lane independent, single cycle
        w_hits = '0;
        for (int u = 0; u < S; u++) begin
            pos = r_b_pos + POS_W'(u);
            w_hit[u] = 1'b0;
            if (r_b_keep[u]) begin
                case (r_mode)
                    3'd2:    w_hit[u] = (pos >= bstart) && (pos < bstart + POS_W'(r_count));
                    3'd3:    w_hit[u] = (r_b_r16[u] < r_rate);
                    3'd4: begin
                        for (int i = 0; i < MAXB; i++) begin
                            if ((i < r_n_burst) && (pos >= r_tab_start[i])
                                && ({1'b0, pos} < (17'(r_tab_start[i]) + 17'(r_tab_len[i]))))
                                w_hit[u] = 1'b1;
                        end
                    end
                    3'd5:    w_hit[u] = (pos >= r_loc_start)
                                         && ({1'b0, pos} < (17'(r_loc_start) + 17'(r_loc_wid)))
                                         && (r_b_r16[u] < r_rate);
                    3'd6:    w_hit[u] = (r_b_r16[u] < r_rate_eff);
                    3'd7: begin
                        dpos = (pos >= r_dbg_base) ? (17'(pos) - 17'(r_dbg_base))
                                                   : (17'(pos) + 17'(N) - 17'(r_dbg_base));
                        w_hit[u] = (dpos < 17'(r_count));
                    end
                    default: w_hit[u] = 1'b0;
                endcase
            end
            w_mask[u*M +: M] = w_hit[u] ? r_b_val[u] : '0;
            w_hits    = w_hits + 8'(w_hit[u]);
        end
        w_e_after = e_left - w_hits;
        // COUNT: decide the r_cyc group, accumulate; release on the last group
        if (w_count_mode) begin
            base      = int'(r_cyc) * GRP;
            w_start_k = (r_cyc == '0) ? 8'd0 : r_k_mid;
            k         = '0;               // group-local prefix, 0..GRP
            for (int i = 0; i < GRP; i++) begin
                u = base + i;
                w_gkeep[i] = 1'b0;
                w_kp[i]    = '0;          // clamped group-local capacity
                if (u < S) begin
                    w_gkeep[i] = r_b_keep[u];
                    if (r_b_inrange[u] && (r_b_lhs_hi[u] < 16'(e_left))) begin
                        automatic logic [8:0] kp_full;
                        kp_full = 9'(e_left) - 9'(r_b_lhs_hi[u]);
                        if (kp_full > 9'(w_start_k)) begin
                            automatic logic [8:0] kp_loc;
                            kp_loc  = kp_full - 9'(w_start_k);
                            w_kp[i] = (kp_loc > 9'(GRP)) ? 8'(GRP + 1) : 8'(kp_loc);
                        end
                    end
                end
                w_ghit[i] = w_gkeep[i] && (k < w_kp[i]);
                k         = k + 8'(w_ghit[i]);
            end
            w_k_next   = w_start_k + k;
            w_grp_hits = k;
            w_hits     = r_hit_acc + w_grp_hits;
            w_e_after  = e_left - w_hits;
            for (int u = 0; u < S; u++) begin
                if ((u / GRP) == int'(r_cyc)) w_hit[u] = w_ghit[u % GRP];
                else                          w_hit[u] = r_mask_acc[u];
                w_mask[u*M +: M] = w_hit[u] ? r_b_val[u] : '0;
            end
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_cyc      <= '0;
            r_dec_busy <= 1'b0;
            r_k_mid    <= '0;
            r_hit_acc  <= '0;
            r_mask_acc <= '0;
        end else begin
            if (w_dec_fire) begin
                r_cyc      <= '0;
                r_hit_acc  <= '0;
                r_mask_acc <= '0;
                r_dec_busy <= 1'b0;
            end else if (w_dec_step) begin
                r_cyc <= r_cyc + 1'b1;
            end
            if (w_c_fire && w_count_mode && (N_GRP > 1)) begin
                r_dec_busy <= 1'b1;
            end
            if (w_dec_step && !w_dec_fire) begin
                r_k_mid   <= w_k_next;
                r_hit_acc <= r_hit_acc + w_grp_hits;
                for (int u = 0; u < S; u++) begin
                    if ((u / GRP) == int'(r_cyc)) r_mask_acc[u] <= w_ghit[u % GRP];
                end
            end
        end
    )

    // C registers: the output beat, plus the beat's hit count and last flag for
    // the statistics stage a cycle later
    logic [DATA_WIDTH-1:0] r_c_data;
    logic [S-1:0]          r_c_keep;
    logic                  r_c_last;
    logic [S-1:0]          r_c_erasure;
    logic                  r_s_v, r_s_last;
    logic [7:0]            r_s_hits;
    logic [7:0]            w_blk_total;
    assign w_blk_total = r_blk_errors + r_s_hits;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_c_v <= 1'b0; r_c_data <= '0; r_c_keep <= '0; r_c_last <= 1'b0;
            r_c_erasure <= '0;
            r_s_v <= 1'b0; r_s_last <= 1'b0; r_s_hits <= '0;
            r_e_left            <= '0;
            r_blk_errors        <= '0;
            r_burst_start       <= '0;
            o_inj_symbols       <= '0;
            o_inj_blocks        <= '0;
            o_inj_over_t        <= '0;
            o_last_block_errors <= '0;
        end else begin
            // the beat, released on the final decision group
            if (w_dec_fire) begin
                r_c_v    <= 1'b1;
                r_c_data <= r_b_data ^ w_mask;
                r_c_keep <= r_b_keep;
                r_c_last <= r_b_last;
                r_c_erasure <= r_mark_erasure ? w_hit : '0;
                if (r_b_first) r_burst_start <= r_b_bstart;
                r_e_left <= w_e_after;
            end else if (out_valid && out_ready) begin
                r_c_v <= 1'b0;
            end
            // the statistics, one cycle behind the beat
            r_s_v    <= w_dec_fire;
            r_s_last <= r_b_last;
            r_s_hits <= w_hits;
            if (cfg_clear) begin
                o_inj_symbols       <= '0;
                o_inj_blocks        <= '0;
                o_inj_over_t        <= '0;
                o_last_block_errors <= '0;
                r_blk_errors        <= '0;
            end else if (r_s_v) begin
                o_inj_symbols <= o_inj_symbols + 32'(r_s_hits);
                if (r_s_last) begin
                    r_blk_errors        <= '0;
                    o_last_block_errors <= w_blk_total;
                    if (w_blk_total != 8'd0)         o_inj_blocks <= o_inj_blocks + 32'd1;
                    if (w_blk_total > 8'(T_SYMBOLS)) o_inj_over_t <= o_inj_over_t + 32'd1;
                end else begin
                    r_blk_errors <= w_blk_total;
                end
            end
        end
    )

    assign out_valid   = r_c_v;
    assign out_data    = r_c_data;
    assign out_keep    = r_c_keep;
    assign out_last    = r_c_last;
    assign out_erasure = r_c_erasure;

endmodule : error_injector
