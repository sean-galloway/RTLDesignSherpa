// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_tile_credits
// Purpose: End-to-end tile credits in the source half (TILE_SPEC 11.9, 11.10)
//
// Description:
//   One credit counter per destination index {ext, n}
//   (rapids_pkg::tile_dest_index), in flits.
//
//   External IDs (ext = 1: cells, tetrad control cores) start at 0 and are
//   filled by the cell or core itself: a credit packet with op = set at
//   boot, op = add as it consumes.
//
//   Internal IDs (ext = 0) are delta nodes. A node only transports and never
//   originates a packet, so it neither advertises nor returns credits; it
//   consumes what is addressed to it on arrival. Its index is legal by
//   topology, a packet to it is never held for credits and never charged,
//   and a credit packet carrying a node's coordinate is ignored.
//
//   Advertisement window: counts cycles from reset to cfg_adv_window. When it
//   closes, every node index is legal and every other counter still at 0 is
//   an illegal destination; the result is saved in dest_legal until the next
//   reset. A later advertisement updates the count but never makes a
//   destination legal. Before the window closes adv_done is 0, dest_legal
//   reads 0 and nothing is spent: the schedulers hold tile descriptors until
//   it closes.
//
//   Spending: each source channel asks for its head packet's flits (header
//   included) against one destination. One request is granted per cycle,
//   round-robin, only when the destination's counter covers all of it; the
//   counter is charged the cycle of the decision and acq_gnt pulses the next.
//   A channel whose grant is pulsing is not considered again that cycle, so
//   one packet is charged once.
//
//   Only class 0 (sink space) credits from an external ID are received here;
//   class 1 (descriptor slots), credits from a node's internal ID and from a
//   coordinate with no index are ignored.
//
// Parameters:
//   - NUM_CHANNELS: source channels, 1..16
//
// Documentation: projects/components/compute-eng-ip/tile/docs/TILE_SPEC.md (Section 11)
// Subsystem: rapids_fub
//
// Author: sean galloway
// Created: 2026-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rapids_tile_credits #(
    parameter int NUM_CHANNELS = 8,
    parameter int NC  = NUM_CHANNELS,
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1,
    parameter int ND  = rapids_pkg::TILE_NUM_DEST,
    parameter int DIW = rapids_pkg::TILE_DEST_W,
    parameter int CRW = rapids_pkg::TILE_CREDIT_W
) (
    input  logic                                 clk,
    input  logic                                 rst_n,

    // Advertisement window length in cycles from reset (CSR)
    input  logic [31:0]                          cfg_adv_window,

    // Credit packets from the sink port (rapids_tile_hdr_rx), one-cycle pulse
    input  logic                                 credit_valid,
    input  logic [rapids_pkg::TILE_COORD_W-1:0]  credit_src,
    input  logic                                 credit_op,      // 0 = add, 1 = set
    input  logic [31:0]                          credit_count,
    input  logic [1:0]                           credit_class,

    // Per source channel: charge acq_flits to acq_dest; acq_gnt pulses once
    // the counter has been charged. Hold acq_req until the grant.
    input  logic [NC-1:0]                        acq_req,
    input  logic [NC-1:0][DIW-1:0]               acq_dest,
    input  logic [NC-1:0][CRW-1:0]               acq_flits,
    output logic [NC-1:0]                        acq_gnt,

    // Saved legal-destination mask, valid once adv_done is 1
    output logic                                 adv_done,
    output logic [ND-1:0]                        dest_legal
);

    initial begin
        if ((NC < 1) || (NC > 16))
            $fatal(1, "rapids_tile_credits: NUM_CHANNELS must be 1..16 (the tile tag is 4 bits)");
    end

    logic [ND-1:0][CRW-1:0] r_cnt;
    logic [31:0]            r_win;
    logic                   r_done;
    logic [ND-1:0]          r_legal;
    logic [CIW-1:0]         r_rr;
    logic [NC-1:0]          r_gnt;

    // Incoming credit
    logic [DIW:0]   w_cmap;
    logic           w_cok;
    logic [DIW-1:0] w_cidx;
    assign w_cmap = rapids_pkg::tile_dest_index(credit_src);
    assign w_cidx = w_cmap[DIW-1:0];
    assign w_cok  = credit_valid && (credit_class == rapids_pkg::TILE_CLASS_SPACE) && w_cmap[DIW]
                 && !rapids_pkg::tile_dest_is_node(w_cidx);

    // Node indices: legal by topology, never gated or charged
    logic [ND-1:0] w_node;
    always_comb begin
        for (int i = 0; i < ND; i++) w_node[i] = rapids_pkg::tile_dest_is_node(DIW'(i));
    end

    // Spend: round-robin over channels whose destination covers the packet
    logic [NC-1:0]  w_cand;
    logic           w_spend;
    logic [CIW-1:0] w_sch;
    always_comb begin
        for (int ch = 0; ch < NC; ch++)
            w_cand[ch] = r_done && acq_req[ch] && !r_gnt[ch]
                      && (w_node[acq_dest[ch]] || (r_cnt[acq_dest[ch]] >= acq_flits[ch]));
        w_spend = 1'b0;
        w_sch   = '0;
        for (int k = 1; k <= NC; k++) begin
            if (w_cand[(int'(r_rr) + k) % NC] && !w_spend) begin
                w_spend = 1'b1;
                w_sch   = CIW'((int'(r_rr) + k) % NC);
            end
        end
    end

    // Next counter values: the credit (set replaces, add saturates), then the
    // spend. The spend was checked against the pre-credit count, so it never
    // overdraws; a set below it clamps at 0.
    logic [ND-1:0][CRW-1:0] w_cnt_n;
    always_comb begin
        for (int i = 0; i < ND; i++) begin
            logic [CRW:0] base;
            base = {1'b0, r_cnt[i]};
            if (w_cok && (w_cidx == DIW'(i))) begin
                if (credit_op) base = {1'b0, CRW'(credit_count)};
                else           base = {1'b0, r_cnt[i]} + (CRW+1)'(credit_count);
                if (base[CRW]) base = {1'b0, {CRW{1'b1}}};
            end
            if (w_spend && (acq_dest[w_sch] == DIW'(i)) && !w_node[i])
                base = (base >= (CRW+1)'(acq_flits[w_sch])) ? (base - (CRW+1)'(acq_flits[w_sch])) : '0;
            w_cnt_n[i] = base[CRW-1:0];
        end
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_cnt   <= '0;
            r_win   <= '0;
            r_done  <= 1'b0;
            r_legal <= '0;
            r_rr    <= '0;
            r_gnt   <= '0;
        end else begin
            r_cnt <= w_cnt_n;
            r_gnt <= '0;
            if (w_spend) begin
                r_gnt[w_sch] <= 1'b1;
                r_rr         <= w_sch;
            end
            if (!r_done) begin
                r_win <= r_win + 32'd1;
                if (r_win >= cfg_adv_window) begin
                    r_done <= 1'b1;
                    for (int i = 0; i < ND; i++) r_legal[i] <= w_node[i] || (r_cnt[i] != '0);
                end
            end
        end
    )

    assign acq_gnt    = r_gnt;
    assign adv_done   = r_done;
    assign dest_legal = r_done ? r_legal : '0;

endmodule : rapids_tile_credits
