// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_bank_head_records
// Purpose: The storage -> scheduler plane contract, derived from a backend's
//          per-entry vectors. For each bank it finds the OLDEST schedulable
//          entry (head) and the one behind it (head2) using the backend's
//          insert-time age matrix, and REGISTERS both as mc_head_rec_t
//          (mc_common_pkg). The scheduler plane sees only these flops: no
//          array view, no pointer-indexed read, no state of another plane
//          crosses the boundary combinationally.
//
//          Why registered: the aged per-bank core (MC-003, 2026-10-19) read
//          its sixteen head views combinationally straight out of the FIFO
//          arrays and reached -35 ns WNS at 75 MHz on a 56-level cone that
//          spanned two planes. A record that changes only on push / pop /
//          aging tick is one flop deep from the scheduler's decode.
//
//          Age semantics: sch_older_i[j*N + i] = 1 means entry j was inserted
//          strictly before entry i (the CAMs' r_older[j][i]). The head of
//          bank b is the candidate with no older candidate in b; head2 has
//          exactly one. behind_empty on head = b has exactly one candidate;
//          on head2 = exactly two.
//
//          Latency: one cycle. A push into an empty bank is visible the cycle
//          after it lands in the backend; a pop (commit / issue) likewise.
//          The scheduler's registered-winner / hold-on-not-fired rule absorbs
//          that (the winner is decided a cycle ahead of its fire anyway).
//
// Documentation: docs/superpowers/plans/2026-10-21-mem-ctrl-recovery.md (section 2.1)
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_bank_head_records
    import mc_common_pkg::*;
#(
    parameter int NUM_ENTRIES = 8,
    parameter int NUM_BANKS   = 8,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    // Derived
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int PTRW = (NUM_ENTRIES > 1) ? $clog2(NUM_ENTRIES) : 1
) (
    input  logic                                clk,
    input  logic                                rst_n,

    // ---- backend per-entry vectors (flops inside the backend) ----
    input  logic [NUM_ENTRIES-1:0]              sch_valid_i,       // schedulable
    input  logic [NUM_ENTRIES*BKW-1:0]          sch_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]    sch_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]    sch_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  sch_older_i,       // [j*N+i]: j older than i
    input  logic [NUM_ENTRIES-1:0]              sch_age_exceed_i,

    // ---- the contract: registered per-bank records ----
    output mc_head_rec_t [NUM_BANKS-1:0]        head_o,
    output mc_head_rec_t [NUM_BANKS-1:0]        head2_o
);

    localparam int CNTW = $clog2(NUM_ENTRIES + 1);

    // ---- per-bank candidate masks and per-entry "older candidates" counts --
    // n_older[b][i] = number of candidates of bank b inserted before entry i.
    // head  = candidate with n_older == 0; head2 = candidate with n_older == 1.
    // NUM_ENTRIES-wide popcounts, one per (bank, entry): shallow, and the
    // result is registered, so the cone never leaves this module.
    mc_head_rec_t [NUM_BANKS-1:0] w_head, w_head2;

    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            automatic logic [NUM_ENTRIES-1:0] cand;
            automatic logic [CNTW-1:0]        n_cand;
            automatic mc_head_rec_t           h, h2;
            h  = '0;
            h2 = '0;
            n_cand = '0;
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                cand[i] = sch_valid_i[i] && (sch_bank_i[i*BKW +: BKW] == BKW'(b));
                n_cand  = n_cand + (cand[i] ? CNTW'(1) : CNTW'(0));
            end
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                automatic logic [CNTW-1:0] n_older;
                n_older = '0;
                for (int j = 0; j < NUM_ENTRIES; j++) begin
                    if ((j != i) && cand[j] && sch_older_i[j*NUM_ENTRIES + i])
                        n_older = n_older + CNTW'(1);
                end
                if (cand[i] && (n_older == '0)) begin
                    h.vld        = 1'b1;
                    h.row        = MC_HEAD_ROW_W'(sch_row_i[i*ROW_WIDTH +: ROW_WIDTH]);
                    h.col        = MC_HEAD_COL_W'(sch_col_i[i*COL_WIDTH +: COL_WIDTH]);
                    h.slot       = MC_HEAD_SLOT_W'(i);
                    h.age_exceed = sch_age_exceed_i[i];
                end
                if (cand[i] && (n_older == CNTW'(1))) begin
                    h2.vld        = 1'b1;
                    h2.row        = MC_HEAD_ROW_W'(sch_row_i[i*ROW_WIDTH +: ROW_WIDTH]);
                    h2.col        = MC_HEAD_COL_W'(sch_col_i[i*COL_WIDTH +: COL_WIDTH]);
                    h2.slot       = MC_HEAD_SLOT_W'(i);
                    h2.age_exceed = sch_age_exceed_i[i];
                end
            end
            h.behind_empty  = h.vld  && (n_cand == CNTW'(1));
            h2.behind_empty = h2.vld && (n_cand == CNTW'(2));
            w_head [b] = h;
            w_head2[b] = h2;
        end
    end

    // ---- the registered edge --------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            head_o  <= '0;
            head2_o <= '0;
        end else begin
            head_o  <= w_head;
            head2_o <= w_head2;
        end
    )

endmodule : mc_bank_head_records
