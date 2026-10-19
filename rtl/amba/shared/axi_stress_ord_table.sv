// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_stress_ord_table
// Purpose: Outstanding-transaction slots kept in per-key arrival order, for
//          the bus-stress masters (key = AxID: responses of one ID come back
//          in issue order) and slaves (key = AxID, or 0 to answer in request
//          order across all IDs).
//
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Subsystem: amba (shared characterization harness blocks)
//
// Author: sean galloway
// Created: 2026-10-19
//==============================================================================
// Each key's entries form a linked list: the head is the oldest entry of that
// key, the tail the newest. The table holds only the linkage; the user keeps
// each slot's payload in its own arrays, indexed by the slot number.
//
//   alloc   writes a new entry into the lowest free slot (alloc_idx) at the
//           tail of its key's list. alloc_idx is valid whenever !full; do not
//           alloc while full.
//   lookup  lk_key -> the head slot of that key (lk_hit, lk_idx), the only
//           entry of the key a response may legally complete.
//   retire  removes a head slot; the next entry of its key becomes the head.
//
// One alloc and one retire may happen in the same cycle, on the same key or
// not. A slot retiring this cycle is still valid this cycle, so alloc_idx
// never names it. If the retiring slot is the tail of the new entry's key (it
// is then the key's only entry), the new entry starts a fresh list as head.
//
// Parameters:
//   DEPTH - slots, 2..64
//   KW    - key width, >= 1
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_stress_ord_table #(
    parameter int DEPTH = 16,
    parameter int KW    = 8,
    parameter int XW    = $clog2(DEPTH)
) (
    input  logic             aclk,
    input  logic             aresetn,

    input  logic             clear,        // drop every entry

    input  logic             alloc_valid,
    input  logic [KW-1:0]    alloc_key,
    output logic [XW-1:0]    alloc_idx,
    output logic             full,

    input  logic [KW-1:0]    lk_key,
    output logic             lk_hit,
    output logic [XW-1:0]    lk_idx,

    input  logic             retire_valid,
    input  logic [XW-1:0]    retire_idx,

    output logic [DEPTH-1:0] valid_vec,
    output logic [DEPTH-1:0] head_vec,
    output logic [XW:0]      count
);

    logic [DEPTH-1:0] r_valid, r_head, r_tail, r_has_next;
    logic [KW-1:0]    r_key  [DEPTH];
    logic [XW-1:0]    r_next [DEPTH];
    logic [XW:0]      r_count;

    // ---- alloc: lowest free slot, and the tail it links onto ----------------
    logic [DEPTH-1:0] w_tail_hit;
    logic             w_tail_any;
    logic [XW-1:0]    w_free_idx;
    logic             w_free_any;

    always_comb begin
        w_free_idx = '0;
        w_free_any = 1'b0;
        for (int i = DEPTH - 1; i >= 0; i--) begin
            if (!r_valid[i]) begin
                w_free_idx = XW'(i);
                w_free_any = 1'b1;
            end
        end
    end

    always_comb begin
        for (int i = 0; i < DEPTH; i++) begin
            w_tail_hit[i] = r_valid[i] && r_tail[i] && (r_key[i] == alloc_key)
                         && !(retire_valid && (retire_idx == XW'(i)));
        end
        w_tail_any = |w_tail_hit;
    end

    assign alloc_idx = w_free_idx;
    assign full      = !w_free_any;

    // ---- lookup: the head of a key ------------------------------------------
    always_comb begin
        lk_hit = 1'b0;
        lk_idx = '0;
        for (int i = 0; i < DEPTH; i++) begin
            if (r_valid[i] && r_head[i] && (r_key[i] == lk_key)) begin
                lk_hit = 1'b1;
                lk_idx = XW'(i);
            end
        end
    end

    // ---- state ---------------------------------------------------------------
    logic           w_promote;
    logic [XW-1:0]  w_promote_idx;
    assign w_promote     = retire_valid && r_has_next[retire_idx];
    assign w_promote_idx = r_next[retire_idx];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_valid    <= '0;
            r_head     <= '0;
            r_tail     <= '0;
            r_has_next <= '0;
            r_count    <= '0;
        end else if (clear) begin
            r_valid    <= '0;
            r_head     <= '0;
            r_tail     <= '0;
            r_has_next <= '0;
            r_count    <= '0;
        end else begin
            for (int i = 0; i < DEPTH; i++) begin
                if (retire_valid && (retire_idx == XW'(i))) begin
                    r_valid[i]    <= 1'b0;
                    r_head[i]     <= 1'b0;
                    r_tail[i]     <= 1'b0;
                    r_has_next[i] <= 1'b0;
                end
                if (w_promote && (w_promote_idx == XW'(i)))
                    r_head[i] <= 1'b1;
                if (alloc_valid && w_tail_hit[i]) begin
                    r_tail[i]     <= 1'b0;
                    r_has_next[i] <= 1'b1;
                end
                if (alloc_valid && (w_free_idx == XW'(i))) begin
                    r_valid[i]    <= 1'b1;
                    r_head[i]     <= !w_tail_any;
                    r_tail[i]     <= 1'b1;
                    r_has_next[i] <= 1'b0;
                end
            end
            r_count <= r_count + (XW+1)'(alloc_valid) - (XW+1)'(retire_valid);
        end
    )

    // Key and next pointer carry no reset: they are read only under r_valid /
    // r_has_next, which are.
    always_ff @(posedge aclk) begin
        for (int i = 0; i < DEPTH; i++) begin
            if (alloc_valid && (w_free_idx == XW'(i)))
                r_key[i] <= alloc_key;
            if (alloc_valid && w_tail_hit[i])
                r_next[i] <= w_free_idx;
        end
    end

    assign valid_vec = r_valid;
    assign head_vec  = r_head;
    assign count     = r_count;

endmodule : axi_stress_ord_table
