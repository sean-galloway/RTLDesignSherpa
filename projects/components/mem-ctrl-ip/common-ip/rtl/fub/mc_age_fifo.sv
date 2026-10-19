// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_age_fifo
// Purpose: per-bank command queue with per-entry age and enqueue-time op
//          decode, for the aged matrix-arbiter scheduler core (MC-003
//          2026-10-18, owner architecture).  Each entry carries:
//            {slot, row, col, id, last}   payload (store slot reference)
//            act                          enqueue-time structural decode:
//                                         1 = this entry is not a plain
//                                         column of the row the bank will
//                                         hold open when it is reached (it
//                                         needs a row open: ACT, or PRE+ACT
//                                         per the live bank state at fire
//                                         time).  Computed at push from the
//                                         entry's row versus the tail's row
//                                         -- perfect information at the
//                                         write port, so the scheduler
//                                         outlet only arbitrates.
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
//          The JEDEC timer masks still gate the request at the outlet each
//          cycle; the act tag is structural only (the fire stage
//          revalidates against the live bank state, so a stale tag costs
//          one dropped pick, never a violation).
//          Head and head-plus-one are combinational read views (the array
//          is registered), so back-to-back same-bank columns fire every
//          cycle: the outlet pre-picks head2 on the fire cycle, the same
//          reserve-seat function as the bh2 path this replaces.
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
    input  logic                 push_bank_open_i,    // registered image,
    input  logic [ROW_W-1:0]     push_bank_row_i,     // for the empty-queue
    input  logic                 push_close_pol_i,    // decode
    output logic                 full_o,

    // ---- global age decrement (every pick, all queues) -----------------
    input  logic                 decr_i,

    // ---- head views (combinational, stable within a cycle) -------------
    output logic                 head_vld_o,
    output logic [SLOT_W-1:0]    head_slot_o,
    output logic [ROW_W-1:0]     head_row_o,
    output logic [COL_W-1:0]    head_col_o,
    output logic [ID_W-1:0]      head_id_o,
    output logic                 head_last_o,
    output logic                 head_act_o,
    output logic [AGE_W-1:0]     head_age_o,
    output logic                 head2_vld_o,
    output logic [SLOT_W-1:0]    head2_slot_o,
    output logic [ROW_W-1:0]     head2_row_o,
    output logic [COL_W-1:0]     head2_col_o,
    output logic [ID_W-1:0]      head2_id_o,
    output logic                 head2_last_o,
    output logic [AGE_W-1:0]     head2_age_o,
    output logic                 head2_act_o,

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
    logic              r_act  [DEPTH];
    logic [AGE_W-1:0]  r_age  [DEPTH];

    logic [PTRW-1:0] r_wptr;
    logic [PTRW-1:0] r_rptr;
    logic [CNTW-1:0] r_count;

    // Tail = last pushed entry = wptr-1 (wrap).
    logic [PTRW-1:0] w_tail_ptr;
    always_comb begin
        w_tail_ptr = (r_wptr == '0) ? PTRW'(DEPTH-1) : r_wptr - PTRW'(1);
    end

    // Enqueue-time structural decode (open-page policy): after the queue
    // drains through the tail, the bank holds the tail's row open (a column
    // inherits it; an act entry leaves its own row open), so a same-row
    // successor is a column and anything else needs a row open.  Empty
    // queue: read the registered bank image.  Page-close policy: every
    // entry closes behind itself, so every entry needs a row open.
    logic w_push_act;
    always_comb begin
        if (push_close_pol_i) begin
            w_push_act = 1'b1;
        end else if (r_count == '0) begin
            w_push_act = !(push_bank_open_i && (push_bank_row_i == push_row_i));
        end else begin
            w_push_act = (push_row_i != r_row[w_tail_ptr]);
        end
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
    assign one_o   = (r_count == 1);

    // Head2 = the entry behind the head.
    logic [PTRW-1:0] w_head2_ptr;
    assign w_head2_ptr = r_rptr + PTRW'(1);

    assign head_vld_o  = (r_count != '0);
    assign head_slot_o = r_slot[r_rptr];
    assign head_row_o  = r_row [r_rptr];
    assign head_col_o  = r_col [r_rptr];
    assign head_id_o   = r_id  [r_rptr];
    assign head_last_o = r_last[r_rptr];
    assign head_act_o  = r_act [r_rptr];
    assign head_age_o  = r_age [r_rptr];

    assign head2_vld_o  = (r_count > 1);
    assign head2_slot_o = r_slot[w_head2_ptr];
    assign head2_row_o  = r_row [w_head2_ptr];
    assign head2_col_o  = r_col [w_head2_ptr];
    assign head2_id_o   = r_id  [w_head2_ptr];
    assign head2_last_o = r_last[w_head2_ptr];
    assign head2_act_o  = r_act [w_head2_ptr];
    assign head2_age_o  = r_age [w_head2_ptr];

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
                r_act [i] <= 1'b0;
                r_age [i] <= '0;
            end
        end else begin
            if (push_i && !full_o) begin
                r_slot[r_wptr] <= push_slot_i;
                r_row [r_wptr] <= push_row_i;
                r_col [r_wptr] <= push_col_i;
                r_id  [r_wptr] <= push_id_i;
                r_last[r_wptr] <= push_last_i;
                r_act [r_wptr] <= w_push_act;
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
