// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rs_error_injector
// Purpose:
//   Test stimulus: corrupts symbols of a coded valid/ready stream between an
//   RS encoder and decoder under host control -- an exact number of errors
//   per block, a burst, or a symbol error rate.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: reed-solomon
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: rs_error_injector
//==============================================================================
// Description:
//   A three-stage valid/ready pipeline on the stream (data XORed, keep/last
//   untouched), so it sits anywhere on a coded stream. Errors must be
//   injected AFTER the encoder -- an error in the generator's data is encoded
//   faithfully and the code cannot see it -- which is why this is its own
//   block and not a mode of the pattern generator.
//
//   Modes (cfg_mode):
//     0 NONE   pass through
//     1 COUNT  exactly cfg_count errors per block at uniformly random distinct
//              positions, by selection sampling (Knuth's Algorithm S): symbol
//              j of n is hit with probability e_left / (n - j), evaluated as
//              r16 * (n - j) < e_left << 16 with a 16-bit random r16; the
//              last positions are hit with certainty when e_left catches up,
//              so the count is exact whenever cfg_count <= n
//     2 BURST  cfg_count consecutive symbols from a random start
//     3 RATE   each symbol independently with probability cfg_rate / 65536
//   The error value is a random nonzero symbol (a zero would be no error).
//   Positions count symbols from the block's first, S lanes per beat, and the
//   block length is taken from `last`, so a mis-framed block simply gets its
//   errors placed against N_SYMBOLS.
//
//   Pipeline (each stage a register with valid/ready, full throughput):
//     A  accept the beat, snapshot the lane generators and the block position
//     B  the per-lane products r16 * (n - pos - u) and the burst start, in
//        DSPs, from A's registers -- the multiply is the long path
//     C  the decisions: for COUNT the lanes are chained only through the
//        number of hits so far, so every lane compares its product against
//        all S candidate thresholds (e_left - k) in parallel and picks by
//        that count; then the XOR mask. The statistics update one cycle
//        later from the registered hit count, and the configuration is
//        re-registered locally, so the CSR block is off every path.
//   The first cut computed all of this combinationally from the input and
//   fed the decoder's syndrome chain in the same cycle: 41 logic levels,
//   WNS -16 ns at 100 MHz on the Nexys A7 loop harness.
//
//   Statistics for the host: total symbols injected, blocks with at least one
//   injected symbol, blocks with more than T_SYMBOLS injected (the ones a
//   decoder must flag), and the count injected into the most recent block.
//   cfg_clear zeroes them; cfg_seed_load reseeds the lane generators.
//
//   Erasure marking (TASK-002): with cfg_mark_erasure set, out_erasure carries
//   the beat's hit mask -- lane u flagged exactly where a symbol was
//   corrupted. Wired to a decoder's in_erasure sideband it turns any
//   placement mode into an erasure run: the positions the decoder is TOLD
//   about are precisely the ones that were hit, which is the information a
//   RAID stripe map or an MC's known-bad column has. With the bit clear
//   out_erasure is all zero and the block is the pre-erasure injector.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   SYMBOL_WIDTH, T_SYMBOLS, N_SYMBOLS, SYMBOLS_PER_BEAT: as the cores.
//
//==============================================================================

module rs_error_injector #(
    parameter int SYMBOL_WIDTH     = 8,
    parameter int T_SYMBOLS        = 8,
    parameter int N_SYMBOLS        = (1 << SYMBOL_WIDTH) - 1,
    parameter int SYMBOLS_PER_BEAT = 1,
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

    input  logic [1:0]                  cfg_mode,
    input  logic [7:0]                  cfg_count,
    input  logic [15:0]                 cfg_rate,
    input  logic [31:0]                 cfg_seed,
    input  logic                        cfg_seed_load,
    input  logic                        cfg_clear,
    input  logic                        cfg_mark_erasure,

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

    // -------------------------------------------------------------------------
    // Configuration, re-registered locally: the values are static during a run
    // and the CSR block sits far away; the copy is one cycle late, which no
    // caller can observe.
    // -------------------------------------------------------------------------
    logic [1:0]  r_mode;
    logic [7:0]  r_count;
    logic [15:0] r_rate;
    logic        r_mark_erasure;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_mode <= '0; r_count <= '0; r_rate <= '0; r_mark_erasure <= 1'b0;
        end else begin
            r_mode <= cfg_mode; r_count <= cfg_count; r_rate <= cfg_rate;
            r_mark_erasure <= cfg_mark_erasure;
        end
    )

    // -------------------------------------------------------------------------
    // Stage A: accept a beat; one 32-bit xorshift generator per lane advances with it
    // -------------------------------------------------------------------------
    logic w_a_fire, w_b_fire, w_c_fire;
    logic r_a_v, r_b_v, r_c_v;
    logic w_a_ready, w_b_ready, w_c_ready;

    assign w_c_ready = !r_c_v || out_ready;
    assign w_b_ready = !r_b_v || w_c_ready;
    assign w_a_ready = !r_a_v || w_b_ready;
    assign in_ready  = w_a_ready;
    assign w_a_fire  = in_valid && w_a_ready;
    assign w_b_fire  = r_a_v && w_b_ready;
    assign w_c_fire  = r_b_v && w_c_ready;

    // One xorshift32 generator per lane (x ^= x << 13; x ^= x >> 17; x ^= x << 5):
    // every bit of the state changes on every step, so consecutive beats draw
    // decorrelated numbers. A one-bit-per-step LFSR was tried first and its
    // 16-bit windows, each the previous one shifted by a bit, clustered the
    // RATE mode's hits (261 in a 204 +- 54 window at S = 1).
    logic [LW-1:0] r_rnd [S];
    logic [LW-1:0] w_rnd [S];
    always_comb begin
        for (int u = 0; u < S; u++) begin
            logic [LW-1:0] x;
            x = r_rnd[u];
            x = x ^ (x << 13);
            x = x ^ (x >> 17);
            x = x ^ (x << 5);
            w_rnd[u] = x;
        end
    end
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int u = 0; u < S; u++) r_rnd[u] <= 32'h9E37_79B9 * 32'(u + 1);
        end else if (cfg_seed_load) begin
            // a zero state would stick at zero; the mix keeps every lane nonzero
            for (int u = 0; u < S; u++) r_rnd[u] <= (cfg_seed ^ (32'h9E37_79B9 * 32'(u + 1))) | 32'h1;
        end else if (w_a_fire) begin
            for (int u = 0; u < S; u++) r_rnd[u] <= w_rnd[u];
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
            for (int u = 0; u < S; u++) begin r_a_r16[u] <= '0; r_a_val[u] <= '0; r_a_rem[u] <= '0; end
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
    logic                  r_b_last, r_b_first;
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
            for (int u = 0; u < S; u++) begin r_b_lhs_hi[u] <= '0; r_b_r16[u] <= '0; r_b_val[u] <= '0; end
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
            end else if (w_c_fire) begin
                r_b_v <= 1'b0;
            end
        end
    )

    // -------------------------------------------------------------------------
    // Stage C: decisions. Per-block state lives here.
    // -------------------------------------------------------------------------
    logic [7:0]       r_e_left;       // COUNT: errors still to place after the previous beat
    logic [7:0]       r_blk_errors;   // injected so far in this block
    logic [POS_W-1:0] r_burst_start;

    logic [S-1:0]          w_hit;
    logic [DATA_WIDTH-1:0] w_mask;
    logic [7:0]            w_hits;
    logic [7:0]            w_e_after;
    logic [S*S-1:0]        w_cmp;          // [u*S+k]: lane u hits if k lanes before it hit (packed: a 2-D unpacked array at the top level breaks the cocotb signal mapper)

    always_comb begin
        logic [7:0]       e_left;
        logic [POS_W-1:0] pos;
        logic [POS_W-1:0] bstart;
        logic [7:0]       k_before;
        e_left = r_b_first ? r_count : r_e_left;
        bstart = r_b_first ? r_b_bstart : r_burst_start;
        // all S x S comparisons in parallel: lane u against threshold e_left - k
        for (int u = 0; u < S; u++) begin
            for (int k = 0; k < S; k++) begin
                w_cmp[u*S+k] = r_b_inrange[u] && (e_left > 8'(k))
                               && (r_b_lhs_hi[u] < 16'(e_left - 8'(k)));
            end
        end
        // the lane chain is only the hit count so far
        k_before = '0;
        w_hits   = '0;
        for (int u = 0; u < S; u++) begin
            pos = r_b_pos + POS_W'(u);
            w_hit[u] = 1'b0;
            if (r_b_keep[u]) begin
                case (r_mode)
                    2'd1: begin
                        w_hit[u] = 1'b0;
                        for (int k = 0; k < S; k++)
                            if (k_before == 8'(k)) w_hit[u] = w_cmp[u*S+k];
                    end
                    2'd2: w_hit[u] = (pos >= bstart) && (pos < bstart + POS_W'(r_count));
                    2'd3: w_hit[u] = (r_b_r16[u] < r_rate);
                    default: w_hit[u] = 1'b0;
                endcase
            end
            w_mask[u*M +: M] = w_hit[u] ? r_b_val[u] : '0;
            if (w_hit[u]) begin
                k_before = k_before + 8'd1;
                w_hits   = w_hits + 8'd1;
            end
        end
        w_e_after = e_left - w_hits;
    end

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
            // the beat
            if (w_c_fire) begin
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
            r_s_v    <= w_c_fire;
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
                    if (w_blk_total != 8'd0)           o_inj_blocks <= o_inj_blocks + 32'd1;
                    if (w_blk_total > 8'(T_SYMBOLS))   o_inj_over_t <= o_inj_over_t + 32'd1;
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

endmodule : rs_error_injector
