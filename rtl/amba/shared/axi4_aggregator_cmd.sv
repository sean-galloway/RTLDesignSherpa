// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi4_aggregator_cmd
// Purpose: The pairing core shared by axi4_wr_aggregator and
//          axi4_rd_aggregator. Merges two adjacent single-beat AXI4 commands
//          ("lo" then "hi", the two halves of a 2-beat-aligned pair) into one
//          2-beat INCR command flagged m_agg. Everything else passes through
//          in order, unaggregated.
//
// Documentation: docs/markdown/rtl-amba/shared/axi4_wr_aggregator.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-10-28
//
// The poor man's aggregator: one held command and a hold counter. No CAM, no
// reordering, no state machine.
//
//   lo  = a single-beat (AxLEN=0), full-width (AxSIZE = log2(DW/8)), INCR,
//         non-locked command whose address is aligned to TWO beats.
//   hi  = the next command, when it has the same ID and qualifiers, is
//         single-beat full-width INCR non-locked, and its address is lo + one
//         beat (full-width on both sides is what makes the sizes equal).
//
// A lo is accepted and HELD. For the next HOLD_CYCLES cycles a hi may pair
// with it: ONE command leaves, lo's address, AxLEN = 1, m_agg = 1, and the hi
// is consumed in the same handshake. If the next command is anything else, the
// lo leaves alone (m_agg = 0) and that command is evaluated the cycle after,
// so order is preserved. If nothing arrives, the lo leaves alone HOLD_CYCLES+1
// cycles after it was captured. Against a pass-through, a lo that pairs costs
// the gap to its hi (1 to HOLD_CYCLES cycles) and a lo that does not pair
// costs HOLD_CYCLES + 1.
//
// Only mergeable commands pair (s_mergeable, AxCACHE[1] in the wrappers): AXI
// forbids merging non-modifiable transactions, and a Device write to 0x100
// followed by one to 0x104 must reach the slave as two writes.
//
//   lo0, hi0, lo1, hi2   -> {lo0+hi0 agg}, lo1, hi2
//   lo0, lo1, hi0, hi1   -> lo0, lo1, hi0, hi1     (nothing adjacent pairs)
//
// A 2-beat burst at a 2-beat-aligned address never crosses a 4 KB boundary,
// so the merged command needs no boundary check. HOLD_CYCLES = 0 makes the
// block a pure pass-through.
//
// AXI valid/ready: m_valid, once high, stays high with a stable payload until
// m_ready. The hold counter freezes while m_valid is high, so a presented pair
// cannot expire into a flush under backpressure; a flush that started from
// expiry cannot become a pair, because pairing is refused once expired and the
// late hi passes through alone the cycle after; a flush started by a
// non-pairing s is stable because s is held until s_ready. Latency of a pair
// seen before expiry is therefore never longer than the slave's backpressure.
//
// Sizing: DATA_WIDTH must be a power of two (FULL_SIZE is log2 of the beat).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_aggregator_cmd
#(
    parameter int ID_WIDTH    = 8,
    parameter int ADDR_WIDTH  = 32,
    parameter int DATA_WIDTH  = 32,
    parameter int QUAL_WIDTH  = 16,   // packed qualifiers that must match (cache, prot, qos, region, user)
    parameter int HOLD_CYCLES = 4,    // how long a lone lo waits for its hi; 0 = never aggregate
    // short names
    parameter int IW = ID_WIDTH,
    parameter int AW = ADDR_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int QW = QUAL_WIDTH
)
(
    input  logic            aclk,
    input  logic            aresetn,

    // upstream command (AW or AR)
    input  logic [IW-1:0]   s_id,
    input  logic [AW-1:0]   s_addr,
    input  logic [7:0]      s_len,
    input  logic [2:0]      s_size,
    input  logic [1:0]      s_burst,
    input  logic            s_lock,
    input  logic            s_mergeable, // AxCACHE[1]: non-modifiable commands never pair
    input  logic [QW-1:0]   s_qual,
    input  logic            s_valid,
    output logic            s_ready,

    // downstream command
    output logic [IW-1:0]   m_id,
    output logic [AW-1:0]   m_addr,
    output logic [7:0]      m_len,
    output logic [2:0]      m_size,
    output logic [1:0]      m_burst,
    output logic            m_lock,
    output logic [QW-1:0]   m_qual,
    output logic            m_agg,      // 1: this command is two upstream commands
    output logic            m_valid,
    input  logic            m_ready
);

    localparam int       BYTES     = DW / 8;
    localparam int       HOLD_BITS = (HOLD_CYCLES > 0) ? $clog2(HOLD_CYCLES + 1) : 1;
    localparam [2:0]     FULL_SIZE = 3'($clog2(BYTES));
    localparam [1:0]     INCR      = 2'b01;
    localparam [AW-1:0]  PAIR_MASK = AW'(2 * BYTES - 1);
    localparam [AW-1:0]  BEAT      = AW'(BYTES);

    // ---- the held lo ---------------------------------------------------------
    logic                 r_pend_valid;
    logic [IW-1:0]        r_pend_id;
    logic [AW-1:0]        r_pend_addr;
    logic [QW-1:0]        r_pend_qual;
    logic [HOLD_BITS-1:0] r_hold_cnt;

    // ---- classification ------------------------------------------------------
    logic w_s_single;      // single-beat, full-width, INCR, non-locked
    logic w_s_lo;          // ... and 2-beat aligned: worth holding
    logic w_pair;          // s is the hi of the held lo
    logic w_hold_expired;
    logic w_flush;         // the held lo leaves alone

    assign w_s_single = s_valid && (s_len == 8'd0) && (s_burst == INCR)
                        && (s_size == FULL_SIZE) && !s_lock && s_mergeable;
    assign w_s_lo     = w_s_single && ((s_addr & PAIR_MASK) == '0)
                        && (HOLD_CYCLES > 0);

    // no pairing once the hold has expired: the flush already presented must
    // not change into a merged command under backpressure
    assign w_pair = r_pend_valid && !w_hold_expired && w_s_single
                    && (s_id   == r_pend_id)
                    && (s_qual == r_pend_qual)
                    && (s_addr == (r_pend_addr + BEAT));

    generate
        if (HOLD_CYCLES > 0) begin : g_hold
            assign w_hold_expired = (r_hold_cnt >= HOLD_BITS'(HOLD_CYCLES));
        end else begin : g_no_hold
            assign w_hold_expired = 1'b1;
        end
    endgenerate
    assign w_flush = r_pend_valid && !w_pair && (s_valid || w_hold_expired);

    // ---- outputs -------------------------------------------------------------
    always_comb begin
        if (r_pend_valid) begin
            // the held lo leaves: merged with s (pair) or alone (flush)
            m_valid = w_pair || w_flush;
            m_id    = r_pend_id;
            m_addr  = r_pend_addr;
            m_len   = w_pair ? 8'd1 : 8'd0;
            m_size  = FULL_SIZE;
            m_burst = INCR;
            m_lock  = 1'b0;
            m_qual  = r_pend_qual;
            m_agg   = w_pair;
            s_ready = w_pair && m_ready;      // the hi rides the merged handshake
        end else if (w_s_lo) begin
            // capture: accept the lo, emit nothing this cycle
            m_valid = 1'b0;
            m_id    = s_id;
            m_addr  = s_addr;
            m_len   = s_len;
            m_size  = s_size;
            m_burst = s_burst;
            m_lock  = s_lock;
            m_qual  = s_qual;
            m_agg   = 1'b0;
            s_ready = 1'b1;
        end else begin
            // pass-through
            m_valid = s_valid;
            m_id    = s_id;
            m_addr  = s_addr;
            m_len   = s_len;
            m_size  = s_size;
            m_burst = s_burst;
            m_lock  = s_lock;
            m_qual  = s_qual;
            m_agg   = 1'b0;
            s_ready = m_ready;
        end
    end

    // ---- hold register -------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_pend_valid <= 1'b0;
            r_pend_id    <= '0;
            r_pend_addr  <= '0;
            r_pend_qual  <= '0;
            r_hold_cnt   <= '0;
        end else if (r_pend_valid) begin
            if (m_valid && m_ready) begin
                r_pend_valid <= 1'b0;
            end else if (!w_hold_expired && !m_valid) begin
                r_hold_cnt   <= r_hold_cnt + 1'b1;   // frozen while a command is presented
            end
        end else if (w_s_lo) begin
            r_pend_valid <= 1'b1;
            r_pend_id    <= s_id;
            r_pend_addr  <= s_addr;
            r_pend_qual  <= s_qual;
            r_hold_cnt   <= '0;
        end
    )

endmodule : axi4_aggregator_cmd
