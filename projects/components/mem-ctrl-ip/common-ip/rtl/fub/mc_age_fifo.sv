// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_age_fifo
// Purpose: per-bank command queue with per-entry age, for the aged
//          matrix-arbiter scheduler core (MC-003 2026-10-18, owner
//          architecture; 2026-10-19 contract rework).  Each entry carries:
//            {slot, row, col, id, last}   payload (store slot reference)
//            age                          global-oldest key
//          Age discipline (owner spec): AGE_W bits (6), saturating.  Push
//          age = (queue empty) ? 0 : tail_age + 1.  Ages stay monotone along
//          the queue (each push lands exactly one above the current max and
//          the decrement below is uniform across all entries).  On EVERY
//          pick (global fire strobe, all queues in parallel) all ages
//          decrement toward 0 and saturate, so age 0 marks the current
//          global-oldest head(s); ties (simultaneous arrivals across banks,
//          or a fresh push into an emptied queue) are broken by the matrix
//          arbiter -- fairness, not correctness.  Per-bank order is the
//          only hard order; cross-bank order is a scheduling heuristic.
//          The JEDEC timer masks gate the request at the outlet each cycle.
//
//          CONTRACT (storage<->scheduler interface, MC-003 SS17): the
//          head/head2 views are REGISTERED snapshots, never combinational
//          array reads.  Each shadow register loads the NEXT-state head
//          every cycle -- on a pop it takes the entry behind the head, on
//          a push it can take the pushed payload -- so at the start of
//          every cycle the outputs equal the current head with zero added
//          latency (no fire-pipeline bubble).  The D-input cones (pointer
//          muxes and the decrement over the entry arrays) stay inside this
//          plane; only the shadow flops cross the boundary.  The
//          enqueue-time act decode and its bank-state inputs are gone:
//          hit classification lives in the scheduler plane against the
//          live bank state (owner ruling 2026-10-19).
//
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_age_fifo
#(
    parameter int SLOT_W = 3,
    parameter int ROW_W  = 14,
    parameter int COL_W  = 10,
    parameter int ID_W   = 8,
    parameter int AGE_W  = 6,
    parameter int DEPTH  = 8
)(
    input  logic                 aclk,
    input  logic                 aresetn,

    // ---- enqueue -------------------------------------------------------
    input  logic                 push_i,
    input  logic [SLOT_W-1:0]    push_slot_i,
    input  logic [ROW_W-1:0]     push_row_i,
    input  logic [COL_W-1:0]     push_col_i,
    input  logic [ID_W-1:0]      push_id_i,
    input  logic                 push_last_i,
    output logic                 full_o,

    // ---- global age decrement (every pick, all queues) -----------------
    input  logic                 decr_i,

    // ---- head views (REGISTERED next-state snapshots, contract SS17) ---
    output logic                 head_vld_o,
    output logic [SLOT_W-1:0]    head_slot_o,
    output logic [ROW_W-1:0]     head_row_o,
    output logic [COL_W-1:0]    head_col_o,
    output logic [ID_W-1:0]      head_id_o,
    output logic                 head_last_o,
    output logic [AGE_W-1:0]     head_age_o,
    output logic                 head2_vld_o,
    output logic [SLOT_W-1:0]    head2_slot_o,
    output logic [ROW_W-1:0]     head2_row_o,
    output logic [COL_W-1:0]     head2_col_o,
    output logic [ID_W-1:0]      head2_id_o,
    output logic                 head2_last_o,
    output logic [AGE_W-1:0]     head2_age_o,

    // ---- pop on fire ----------------------------------------------------
    input  logic                 pop_i,
    output logic                 empty_o,
    output logic                 one_o     // count == 1 (CLOSE_ON_DRAIN boundary)
);

    localparam int PTRW  = (DEPTH > 1) ? $clog2(DEPTH) : 1;
    localparam int CNTW  = $clog2(DEPTH+1);

    logic [SLOT_W-1:0] r_slot [DEPTH];
    logic [ROW_W-1:0]  r_row  [DEPTH];
    logic [COL_W-1:0]  r_col  [DEPTH];
    logic [ID_W-1:0]   r_id   [DEPTH];
    logic              r_last [DEPTH];
    logic [AGE_W-1:0]  r_age  [DEPTH];

    logic [PTRW-1:0] r_wptr;
    logic [PTRW-1:0] r_rptr;
    logic [CNTW-1:0] r_count;

    // Tail = last pushed entry = wptr-1 (wrap).
    logic [PTRW-1:0] w_tail_ptr;
    always_comb begin
        w_tail_ptr = (r_wptr == '0) ? PTRW'(DEPTH-1) : r_wptr - PTRW'(1);
    end

    // Push age: 0 into an emptied queue (ties with the global oldest; the
    // matrix arbiter breaks it), else tail_age + 1.  On a simultaneous
    // decrement the tail itself steps down at this edge, so the newcomer
    // lands on the stepped value: (tail_age - 1) + 1 = tail_age.
    logic [AGE_W-1:0] w_push_age;
    always_comb begin
        if (r_count == '0) begin
            w_push_age = AGE_W'(0);
        end else if (decr_i && (r_age[w_tail_ptr] != '0)) begin
            w_push_age = r_age[w_tail_ptr];
        end else begin
            w_push_age = r_age[w_tail_ptr] + AGE_W'(1);
        end
    end

    assign full_o  = (r_count == DEPTH);
    assign empty_o = (r_count == '0);

    // ======================================================================
    // Registered head/head2 snapshots (contract SS17).  Every cycle each
    // shadow loads the entry that WILL hold the position at the next edge:
    // on pop the position advances (head takes the entry behind, head2 the
    // one behind that), and when the advancing index lands on the write
    // pointer the pushed payload is substituted (covers push-to-empty and
    // the count==1 push+pop roll).  The outputs therefore always show the
    // current head at the start of the cycle -- zero added latency vs the
    // old comb views, with pure flops at the plane boundary.
    // ======================================================================
    logic              r_head_vld,  r_head2_vld;
    logic [SLOT_W-1:0] r_head_slot, r_head2_slot;
    logic [ROW_W-1:0]  r_head_row,  r_head2_row;
    logic [COL_W-1:0]  r_head_col,  r_head2_col;
    logic [ID_W-1:0]   r_head_id,   r_head2_id;
    logic              r_head_last, r_head2_last;
    logic [AGE_W-1:0]  r_head_age,  r_head2_age;
    logic              r_one;

    logic            w_push, w_pop;
    logic [CNTW-1:0] w_count_n;
    assign w_push    = push_i && !full_o;
    assign w_pop     = pop_i && (r_count != '0);
    assign w_count_n = r_count + CNTW'(w_push) - CNTW'(w_pop);

    // Post-state position indices (PTRW wraps mod DEPTH; DEPTH is a power
    // of two).  head = position 0 (advanced by a pop), head2 = position 1.
    logic [PTRW-1:0] w_idx_h, w_idx_h2;
    assign w_idx_h  = r_rptr + (w_pop ? PTRW'(1) : PTRW'(0));
    assign w_idx_h2 = r_rptr + (w_pop ? PTRW'(2) : PTRW'(1));

    // Substitution: when the position index coincides with the write
    // pointer, the pushed payload lands there this same edge.  (When full,
    // w_push is 0 and wptr==rptr is harmless; no substitution occurs.)
    logic w_h_is_push, w_h2_is_push;
    assign w_h_is_push  = w_push && (w_idx_h  == r_wptr);
    assign w_h2_is_push = w_push && (w_idx_h2 == r_wptr);

    // Decrement-adjusted age of an EXISTING entry (saturating at 0).
    function automatic logic [AGE_W-1:0] w_age_adj(input logic [PTRW-1:0] idx);
        if (decr_i && (r_age[idx] != '0)) return r_age[idx] - AGE_W'(1);
        else                              return r_age[idx];
    endfunction

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_head_vld   <= 1'b0;
            r_head_slot  <= '0;
            r_head_row   <= '0;
            r_head_col   <= '0;
            r_head_id    <= '0;
            r_head_last  <= 1'b0;
            r_head_age   <= '0;
            r_head2_vld  <= 1'b0;
            r_head2_slot <= '0;
            r_head2_row  <= '0;
            r_head2_col  <= '0;
            r_head2_id   <= '0;
            r_head2_last <= 1'b0;
            r_head2_age  <= '0;
            r_one        <= 1'b0;
        end else begin
            r_head_vld   <= (w_count_n != '0);
            r_head_slot  <= w_h_is_push  ? push_slot_i : r_slot[w_idx_h];
            r_head_row   <= w_h_is_push  ? push_row_i  : r_row [w_idx_h];
            r_head_col   <= w_h_is_push  ? push_col_i  : r_col [w_idx_h];
            r_head_id    <= w_h_is_push  ? push_id_i   : r_id  [w_idx_h];
            r_head_last  <= w_h_is_push  ? push_last_i : r_last[w_idx_h];
            r_head_age   <= w_h_is_push  ? w_push_age  : w_age_adj(w_idx_h);
            r_head2_vld  <= (w_count_n > 1);
            r_head2_slot <= w_h2_is_push ? push_slot_i : r_slot[w_idx_h2];
            r_head2_row  <= w_h2_is_push ? push_row_i  : r_row [w_idx_h2];
            r_head2_col  <= w_h2_is_push ? push_col_i  : r_col [w_idx_h2];
            r_head2_id   <= w_h2_is_push ? push_id_i   : r_id  [w_idx_h2];
            r_head2_last <= w_h2_is_push ? push_last_i : r_last[w_idx_h2];
            r_head2_age  <= w_h2_is_push ? w_push_age  : w_age_adj(w_idx_h2);
            r_one        <= (w_count_n == 1);
        end
    end)

    assign head_vld_o   = r_head_vld;
    assign head_slot_o  = r_head_slot;
    assign head_row_o   = r_head_row;
    assign head_col_o   = r_head_col;
    assign head_id_o    = r_head_id;
    assign head_last_o  = r_head_last;
    assign head_age_o   = r_head_age;
    assign head2_vld_o  = r_head2_vld;
    assign head2_slot_o = r_head2_slot;
    assign head2_row_o  = r_head2_row;
    assign head2_col_o  = r_head2_col;
    assign head2_id_o   = r_head2_id;
    assign head2_last_o = r_head2_last;
    assign head2_age_o  = r_head2_age;
    assign one_o        = r_one;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wptr  <= '0;
            r_rptr  <= '0;
            r_count <= '0;
            for (int i = 0; i < DEPTH; i++) begin
                r_slot[i] <= '0;
                r_row [i] <= '0;
                r_col [i] <= '0;
                r_id  [i] <= '0;
                r_last[i] <= 1'b0;
                r_age [i] <= '0;
            end
        end else begin
            if (push_i && !full_o) begin
                r_slot[r_wptr] <= push_slot_i;
                r_row [r_wptr] <= push_row_i;
                r_col [r_wptr] <= push_col_i;
                r_id  [r_wptr] <= push_id_i;
                r_last[r_wptr] <= push_last_i;
                r_age [r_wptr] <= w_push_age;
                r_wptr <= (r_wptr == PTRW'(DEPTH-1)) ? '0 : r_wptr + PTRW'(1);
            end
            if (pop_i && (r_count != '0)) begin
                r_rptr <= (r_rptr == PTRW'(DEPTH-1)) ? '0 : r_rptr + PTRW'(1);
            end
            case ({push_i && !full_o, pop_i && (r_count != '0)})
                2'b10:   r_count <= r_count + 1'b1;
                2'b01:   r_count <= r_count - 1'b1;
                default: r_count <= r_count;
            endcase
            // Global age decrement on every pick, saturating at 0.  The
            // pushed slot (if any) takes w_push_age, which already folds
            // the simultaneous decrement.
            if (decr_i) begin
                for (int i = 0; i < DEPTH; i++) begin
                    if (push_i && !full_o && (i == int'(r_wptr))) begin
                        r_age[i] <= w_push_age;
                    end else if (r_age[i] != '0) begin
                        r_age[i] <= r_age[i] - AGE_W'(1);
                    end
                end
            end
        end
    )

endmodule : mc_age_fifo
