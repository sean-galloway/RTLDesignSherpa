// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: bch_error_injector
// Purpose:
//   Test stimulus: corrupts bits of a coded valid/ready stream between a
//   binary BCH encoder and decoder under host control -- an exact number of
//   errors per block, a burst, or a bit error rate.
//
// Documentation: projects/components/ecc-ip/reed-solomon/docs/rs_fub_catalog.md
// Subsystem: bch
//
// Author: sean galloway
// Created: 2026-10-03

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: bch_error_injector
//==============================================================================
// Description:
//   A three-stage valid/ready pipeline on the bit stream (data XORed, keep/last
//   untouched), so it sits anywhere on a coded stream. Errors must be injected
//   AFTER the encoder -- an error in the generator's data is encoded faithfully
//   and the code cannot see it -- which is why this is its own block and not a
//   mode of the pattern generator.
//
//   Modes (cfg_mode):
//     0 NONE   pass through
//     1 COUNT  exactly cfg_count errors per block at uniformly random distinct
//              bit positions, by selection sampling (Knuth's Algorithm S): bit
//              j of n is hit with probability e_left / (n - j), evaluated as
//              r16 * (n - j) < e_left << 16 with a 16-bit random r16; the last
//              positions are hit with certainty when e_left catches up, so the
//              count is exact whenever cfg_count <= n
//     2 BURST  cfg_count consecutive bits from a random start
//     3 RATE   each valid bit independently with probability cfg_rate / 65536
//
//   The BCH code is binary, so a bit error is a simple inversion (XOR 1).
//   Positions count bits from the block's first, B lanes per beat, and the
//   block length is taken from `last`, so a mis-framed block simply gets its
//   errors placed against N_BITS.
//
//   COUNT-mode implementation: RS's streaming selection-sampling structure is
//   adapted bit-granularly.  One xorshift32 generator per bit lane feeds a beat;
//   stage B computes the B products r16 * (n - pos - u), and stage C evaluates
//   all B x B threshold comparisons in parallel so the per-lane hit decision
//   depends only on the actual number of hits in lower lanes.  This keeps the
//   block state to a single e_left register, costs no extra cycles, and is
//   honestly synthesizable for the realistic B (<= 64) and N (<= 8191) of this
//   component.  cfg_count is capped at 255 by its register width; if software
//   requests more errors than the block has positions, the hardware places one
//   error per valid position and the count is truncated naturally.
//
//   Pipeline (each stage a register with valid/ready, full throughput):
//     A  accept the beat, snapshot the lane generators and the block position
//     B  the per-lane products r16 * (n - pos - u) and the burst start, in
//        DSPs, from A's registers -- the multiply is the long path
//     C  the decisions: for COUNT the lanes are chained only through the
//        number of hits so far, so every lane compares its product against
//        all B candidate thresholds (e_left - k) in parallel and picks by
//        that count; then the XOR mask. The statistics update one cycle
//        later from the registered hit count, and the configuration is
//        re-registered locally, so the CSR block is off every path.
//
//   Statistics for the host: total bits injected, blocks with at least one
//   injected bit, blocks with more than T_BITS injected (the ones a decoder
//   must flag), and the count injected into the most recent block.
//   cfg_clear zeroes them; cfg_seed_load reseeds the lane generators.
//
//   The cfg_mark input is provided for register-map compatibility with the RS
//   injector's INJ_CFG but is unused by the binary BCH path (BCH has no
//   erasure sideband at this layer).
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   FIELD_DIM, PRIM_POLY, T_BITS, N_BITS, BITS_PER_BEAT: as the cores.
//
//==============================================================================

module bch_error_injector
    import gf_pkg::*;
#(
    parameter int FIELD_DIM     = bch_pkg::FIELD_DIM,
    parameter int PRIM_POLY     = bch_pkg::PRIM_POLY,
    parameter int T_BITS        = bch_pkg::T_BITS,
    parameter int N_BITS        = bch_pkg::N_BITS,
    parameter int BITS_PER_BEAT = bch_pkg::BITS_PER_BEAT,
    parameter int DATA_WIDTH    = BITS_PER_BEAT
) (
    input  logic                  aclk,
    input  logic                  aresetn,

    input  logic                  in_valid,
    output logic                  in_ready,
    input  logic [DATA_WIDTH-1:0] in_data,
    input  logic [DATA_WIDTH-1:0] in_keep,
    input  logic                  in_last,

    output logic                  out_valid,
    input  logic                  out_ready,
    output logic [DATA_WIDTH-1:0] out_data,
    output logic [DATA_WIDTH-1:0] out_keep,
    output logic                  out_last,

    input  logic [1:0]            cfg_mode,
    input  logic [7:0]            cfg_count,
    input  logic [15:0]           cfg_rate,
    input  logic [31:0]           cfg_seed,
    input  logic                  cfg_seed_load,
    input  logic                  cfg_clear,
    input  logic                  cfg_mark,

    output logic [31:0]           o_inj_bits,
    output logic [31:0]           o_inj_blocks,
    output logic [31:0]           o_inj_over_t,
    output logic [7:0]            o_last_block_errors
);

    localparam int M     = FIELD_DIM;
    localparam int T     = T_BITS;
    localparam int B     = BITS_PER_BEAT;
    localparam int N     = N_BITS;
    localparam int POS_W = 16;
    localparam int LW    = 32;

    // -------------------------------------------------------------------------
    // Elaboration guards
    // -------------------------------------------------------------------------
    initial begin : param_check
        if (M < 3 || M > GF_MAX_M)
            $error("bch_error_injector: FIELD_DIM must be 3..%0d (got %0d)", GF_MAX_M, M);
        if (!gf_is_primitive(M, PRIM_POLY))
            $error("bch_error_injector: PRIM_POLY 0x%0h is not primitive of degree %0d", PRIM_POLY, M);
        if (T < 1 || 2 * T > (1 << M) - 2)
            $error("bch_error_injector: T_BITS %0d out of range for GF(2^%0d)", T, M);
        if (N < 2 * T + 1 || N > (1 << M) - 1)
            $error("bch_error_injector: N_BITS %0d out of range for GF(2^%0d)", N, M);
        if (B < 1 || B > N)
            $error("bch_error_injector: BITS_PER_BEAT %0d out of range 1..N (%0d)", B, N);
        if (DATA_WIDTH != B)
            $error("bch_error_injector: DATA_WIDTH (%0d) must equal BITS_PER_BEAT (%0d)", DATA_WIDTH, B);
    end

    // -------------------------------------------------------------------------
    // Configuration, re-registered locally: the values are static during a run
    // and the CSR block sits far away; the copy is one cycle late, which no
    // caller can observe.
    // -------------------------------------------------------------------------
    logic [1:0]  r_mode;
    logic [7:0]  r_count;
    logic [15:0] r_rate;
    logic        r_mark;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_mode <= '0; r_count <= '0; r_rate <= '0; r_mark <= 1'b0;
        end else begin
            r_mode <= cfg_mode; r_count <= cfg_count; r_rate <= cfg_rate;
            r_mark <= cfg_mark;
        end
    )

    // -------------------------------------------------------------------------
    // Stage A: accept a beat; one 32-bit xorshift generator per bit lane
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

    // One xorshift32 generator per bit lane (x ^= x << 13; x ^= x >> 17; x ^= x << 5):
    // every bit of the state changes on every step, so consecutive beats draw
    // decorrelated numbers.
    logic [LW-1:0] r_rnd [B];
    logic [LW-1:0] w_rnd [B];
    always_comb begin
        for (int u = 0; u < B; u++) begin
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
            for (int u = 0; u < B; u++) r_rnd[u] <= 32'h9E37_79B9 * 32'(u + 1);
        end else if (cfg_seed_load) begin
            // a zero state would stick at zero; the mix keeps every lane nonzero
            for (int u = 0; u < B; u++) r_rnd[u] <= (cfg_seed ^ (32'h9E37_79B9 * 32'(u + 1))) | 32'h1;
        end else if (w_a_fire) begin
            for (int u = 0; u < B; u++) r_rnd[u] <= w_rnd[u];
        end
    )

    // block position of lane 0 for the beat being accepted
    logic [POS_W-1:0] r_pos;
    logic             r_first;

    // A registers
    logic [DATA_WIDTH-1:0] r_a_data;
    logic [B-1:0]          r_a_keep;
    logic                  r_a_last, r_a_first;
    logic [POS_W-1:0]      r_a_pos;
    logic [15:0]           r_a_r16 [B];
    logic [POS_W-1:0]      r_a_rem [B];    // n - pos - u, the selection-sampling denominator
    logic [B-1:0]          r_a_inrange;    // pos + u < n

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_pos   <= '0;
            r_first <= 1'b1;
            r_a_v   <= 1'b0;
            r_a_data <= '0; r_a_keep <= '0; r_a_last <= 1'b0; r_a_first <= 1'b0; r_a_pos <= '0;
            r_a_inrange <= '0;
            for (int u = 0; u < B; u++) begin r_a_r16[u] <= '0; r_a_rem[u] <= '0; end
        end else begin
            if (w_a_fire) begin
                r_a_v     <= 1'b1;
                r_a_data  <= in_data;
                r_a_keep  <= in_keep;
                r_a_last  <= in_last;
                r_a_first <= r_first;
                r_a_pos   <= r_pos;
                for (int u = 0; u < B; u++) begin
                    r_a_r16[u]     <= w_rnd[u][15:0];
                    r_a_rem[u]     <= POS_W'(N) - r_pos - POS_W'(u);
                    r_a_inrange[u] <= (r_pos + POS_W'(u)) < POS_W'(N);
                end
                r_pos   <= in_last ? '0 : r_pos + POS_W'(B);
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
    logic [31:0] w_lhs [B];       // r16 * (n - pos - u)
    logic [31:0] w_bprod;         // r16_0 * (n - e + 1), for the burst start
    logic [15:0] w_bspan;         // n - e + 1, the burst start's range
    always_comb begin
        for (int u = 0; u < B; u++) w_lhs[u] = 32'(r_a_r16[u]) * 32'(r_a_rem[u]);
        w_bspan = 16'(N) - 16'(r_count) + 16'd1;
        w_bprod = 32'(r_a_r16[0]) * 32'(w_bspan);
    end
    logic unused_frac;
    always_comb begin
        unused_frac = ^w_bprod[15:0];
        for (int u = 0; u < B; u++) unused_frac = unused_frac ^ (^w_lhs[u][15:0]);
    end

    logic [DATA_WIDTH-1:0] r_b_data;
    logic [B-1:0]          r_b_keep;
    logic                  r_b_last, r_b_first;
    logic [POS_W-1:0]      r_b_pos;
    logic [B-1:0]          r_b_inrange;
    logic [15:0]           r_b_lhs_hi [B];
    logic [15:0]           r_b_r16 [B];
    logic [POS_W-1:0]      r_b_bstart;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_b_v <= 1'b0;
            r_b_data <= '0; r_b_keep <= '0; r_b_last <= 1'b0; r_b_first <= 1'b0; r_b_pos <= '0;
            r_b_bstart <= '0; r_b_inrange <= '0;
            for (int u = 0; u < B; u++) begin r_b_lhs_hi[u] <= '0; r_b_r16[u] <= '0; end
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
                for (int u = 0; u < B; u++) begin
                    r_b_lhs_hi[u] <= w_lhs[u][31:16];
                    r_b_r16[u] <= r_a_r16[u];
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

    logic [B-1:0]          w_hit;
    logic [DATA_WIDTH-1:0] w_mask;
    logic [7:0]            w_hits;
    logic [7:0]            w_e_after;
    logic [B*B-1:0]        w_cmp;          // [u*B+k]: lane u hits if k lanes before it hit

    always_comb begin
        logic [7:0]       e_left;
        logic [POS_W-1:0] pos;
        logic [POS_W-1:0] bstart;
        logic [7:0]       k_before;
        e_left = r_b_first ? r_count : r_e_left;
        bstart = r_b_first ? r_b_bstart : r_burst_start;
        // all B x B comparisons in parallel: lane u against threshold e_left - k
        for (int u = 0; u < B; u++) begin
            for (int k = 0; k < B; k++) begin
                w_cmp[u*B+k] = r_b_inrange[u] && (e_left > 8'(k))
                               && (r_b_lhs_hi[u] < 16'(e_left - 8'(k)));
            end
        end
        // the lane chain is only the hit count so far
        k_before = '0;
        w_hits   = '0;
        for (int u = 0; u < B; u++) begin
            pos = r_b_pos + POS_W'(u);
            w_hit[u] = 1'b0;
            if (r_b_keep[u]) begin
                case (r_mode)
                    2'd1: begin
                        w_hit[u] = 1'b0;
                        for (int k = 0; k < B; k++)
                            if (k_before == 8'(k)) w_hit[u] = w_cmp[u*B+k];
                    end
                    2'd2: w_hit[u] = (pos >= bstart) && (pos < bstart + POS_W'(r_count));
                    2'd3: w_hit[u] = (r_b_r16[u] < r_rate);
                    default: w_hit[u] = 1'b0;
                endcase
            end
            w_mask[u] = w_hit[u];
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
    logic [B-1:0]          r_c_keep;
    logic                  r_c_last;
    logic                  r_s_v, r_s_last;
    logic [7:0]            r_s_hits;
    logic [7:0]            w_blk_total;
    assign w_blk_total = r_blk_errors + r_s_hits;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_c_v <= 1'b0; r_c_data <= '0; r_c_keep <= '0; r_c_last <= 1'b0;
            r_s_v <= 1'b0; r_s_last <= 1'b0; r_s_hits <= '0;
            r_e_left            <= '0;
            r_blk_errors        <= '0;
            r_burst_start       <= '0;
            o_inj_bits          <= '0;
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
                o_inj_bits          <= '0;
                o_inj_blocks        <= '0;
                o_inj_over_t        <= '0;
                o_last_block_errors <= '0;
                r_blk_errors        <= '0;
            end else if (r_s_v) begin
                o_inj_bits <= o_inj_bits + 32'(r_s_hits);
                if (r_s_last) begin
                    r_blk_errors        <= '0;
                    o_last_block_errors <= w_blk_total;
                    if (w_blk_total != 8'd0)           o_inj_blocks <= o_inj_blocks + 32'd1;
                    if (w_blk_total > 8'(T_BITS))      o_inj_over_t <= o_inj_over_t + 32'd1;
                end else begin
                    r_blk_errors <= w_blk_total;
                end
            end
        end
    )

    assign out_valid = r_c_v;
    assign out_data  = r_c_data;
    assign out_keep  = r_c_keep;
    assign out_last  = r_c_last;

    // cfg_mark is provided for register-map compatibility with the RS injector
    // but has no erasure sideband to drive in the binary BCH path.
    logic unused_mark;
    assign unused_mark = r_mark ^ cfg_mark;

endmodule : bch_error_injector
