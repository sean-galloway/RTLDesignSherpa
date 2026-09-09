// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// pumice_row_pred_table — per-row open/close predictor (Happy "Hybrid" class).
//
// PUMICE-006 Axis 2, mode 5 (adapt_access). A tagless direct-mapped table of
// 2-bit saturating counters indexed by {bank, folded row}. Each counter votes
// on what to do the next time its row is ACTIVATED: counter >= 2 means "this
// row historically saw a single access per activation — close it eagerly"
// (auto-precharge on the column op); counter < 2 means "this row gets reuse —
// keep it open". Two PAGE_POLICY_CFG knobs shape it, both "0 = build default":
// ctr_open_max (close when counter >= this; default 2 = the MSB rule) and
// ctr_init (table init value; default weak-open 2'b01). ctr_init is applied
// while the mode is DISABLED, so it takes effect on mode entry.
//
// Learning, at the issued command stream:
//   explicit PRE close   The number of column ops the row served this
//                        activation (a per-bank 2-bit saturating count) is the
//                        outcome: <= 1 access -> counter++ (close-friendly),
//                        >= 2 accesses -> counter-- (open-friendly). PREA
//                        (refresh drain) is policy-neutral: it claims falls
//                        but teaches nothing.
//   auto-precharge close No PRE is ever issued, so the close is detected as
//                        the bank's row-active image falling with no PRE seen:
//                        the closed row is remembered per bank. No counter
//                        update at close time — a correct close is confirmed
//                        by silence. If the NEXT ACT to that bank re-opens the
//                        SAME row, the close was premature: counter-- so a
//                        misclassified row recovers toward open.
//
// Aliasing is accepted (predictor, not correctness): folded rows that collide
// blend their history. Verdict discipline matches pumice_rbl_table: computed
// at ACT time, latched per bank, held while the row is open, so the column
// path reads a flop. Disable drops all state and releases the mask.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_row_pred_table
    import pumice_pkg::*;
#(
    parameter int NUM_BANKS = 8,
    parameter int ROW_WIDTH = 14,
    parameter int ROW_FOLD_LOG2 = 6,   // folded row index width
    parameter int BKW = $clog2(NUM_BANKS)
) (
    input  logic                   aclk,
    input  logic                   aresetn,

    input  logic                   enable_i,          // mode 5 active
    // PAGE_POLICY_CFG counter shape (0 = build default)
    input  logic [3:0]             ctr_thresh_i,      // close at counter >= this
    input  logic [3:0]             ctr_init_i,        // table init value

    // issued command stream (valid && ready)
    input  logic                   cmd_valid_i,
    input  dram_op_e               cmd_op_i,
    input  logic [BKW-1:0]         cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]   cmd_row_i,

    // registered per-bank row state (same bus the arbiter registers)
    input  logic [NUM_BANKS-1:0]                bank_row_active_i,
    input  logic [NUM_BANKS-1:0][ROW_WIDTH-1:0] bank_open_row_i,

    output logic [NUM_BANKS-1:0]   close_pred_o       // open row predicts close
);

    localparam int IDXW = BKW + ROW_FOLD_LOG2;
    localparam int TBL  = 1 << IDXW;

    // XOR-fold a row address down to ROW_FOLD_LOG2 bits.
    function automatic logic [ROW_FOLD_LOG2-1:0] f_fold (
        input logic [ROW_WIDTH-1:0] row
    );
        logic [ROW_FOLD_LOG2-1:0] acc;
        acc = '0;
        for (int i = 0; i < ROW_WIDTH; i += ROW_FOLD_LOG2)
            acc ^= ROW_FOLD_LOG2'(row >> i);
        return acc;
    endfunction

    function automatic logic [IDXW-1:0] f_idx (
        input logic [BKW-1:0]       bank,
        input logic [ROW_WIDTH-1:0] row
    );
        return {bank, f_fold(row)};
    endfunction

    // 2-bit saturating counters; 2'b01 = weak open (reset value).
    logic [TBL-1:0][1:0] r_pred;

    // Effective knob values, clamped into the 2-bit counter range.
    logic [1:0] w_thresh_eff, w_init_eff;
    assign w_thresh_eff = (ctr_thresh_i == 4'd0 || ctr_thresh_i > 4'd3)
                          ? 2'd2 : ctr_thresh_i[1:0];
    assign w_init_eff   = (ctr_init_i == 4'd0 || ctr_init_i > 4'd3)
                          ? 2'd1 : ctr_init_i[1:0];

    // Per-bank activation outcome state.
    logic [NUM_BANKS-1:0][1:0]            r_col_cnt;    // columns this activation
    logic [NUM_BANKS-1:0]                 r_prev_active;
    logic [NUM_BANKS-1:0][ROW_WIDTH-1:0]  r_prev_open_row;
    logic [NUM_BANKS-1:0]                 r_fall_wait;  // fall seen, close cause TBD
    logic [NUM_BANKS-1:0][ROW_WIDTH-1:0]  r_fall_row;
    logic [NUM_BANKS-1:0]                 r_ap_closed;  // last close was auto-PRE
    logic [NUM_BANKS-1:0][ROW_WIDTH-1:0]  r_ap_row;

    // Stream decodes.
    logic w_is_act, w_is_col, w_is_pre, w_is_prea;
    assign w_is_act  = cmd_valid_i && (cmd_op_i == OP_ACT)  && enable_i;
    assign w_is_col  = cmd_valid_i && is_column_op(cmd_op_i) && enable_i;
    assign w_is_pre  = cmd_valid_i && (cmd_op_i == OP_PRE)  && enable_i;
    assign w_is_prea = cmd_valid_i && (cmd_op_i == OP_PREA) && enable_i;

    // The scheduler clears its exported row-active bit when it PICKS a close,
    // so the fall can lead the PRE by a cycle. A fall therefore opens a
    // one-cycle claim window: a PRE (or PREA) to the bank at the fall cycle or
    // the next one claims it as an explicit close; an unclaimed fall was an
    // auto-precharge close.
    logic [NUM_BANKS-1:0] w_fall, w_pre_claims;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            w_fall[b]       = r_prev_active[b] && !bank_row_active_i[b];
            w_pre_claims[b] = (w_is_pre && (int'(cmd_bank_i) == b)) || w_is_prea;
        end
    end

    function automatic logic [1:0] f_inc (input logic [1:0] c);
        return (c == 2'b11) ? c : c + 2'b01;
    endfunction
    function automatic logic [1:0] f_dec (input logic [1:0] c);
        return (c == 2'b00) ? c : c - 2'b01;
    endfunction

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            for (int i = 0; i < TBL; i++) r_pred[i] <= 2'b01;
            r_col_cnt       <= '0;
            r_prev_active   <= '0;
            r_prev_open_row <= '0;
            r_fall_wait     <= '0;
            r_fall_row      <= '0;
            r_ap_closed     <= '0;
            r_ap_row        <= '0;
            close_pred_o    <= '0;
        end else if (!enable_i) begin
            for (int i = 0; i < TBL; i++) r_pred[i] <= w_init_eff;
            r_col_cnt     <= '0;
            r_prev_active <= bank_row_active_i;
            r_fall_wait   <= '0;
            r_ap_closed   <= '0;
            close_pred_o  <= '0;
            for (int b = 0; b < NUM_BANKS; b++)
                r_prev_open_row[b] <= bank_open_row_i[b];
        end else begin
            r_prev_active <= bank_row_active_i;
            for (int b = 0; b < NUM_BANKS; b++)
                r_prev_open_row[b] <= bank_open_row_i[b];

            // ---- verdict latch + premature-reopen learning on ACT ----
            // The verdict uses the value AFTER the premature-reopen decrement,
            // so a corrected row does not thrash one extra activation.
            if (w_is_act) begin
                automatic logic [1:0] pv;
                pv = r_pred[f_idx(cmd_bank_i, cmd_row_i)];
                if (r_ap_closed[cmd_bank_i]
                    && (cmd_row_i == r_ap_row[cmd_bank_i])) begin
                    pv = f_dec(pv);
                    r_pred[f_idx(cmd_bank_i, cmd_row_i)] <= pv;
                end
                close_pred_o[cmd_bank_i] <= (pv >= w_thresh_eff);
                r_col_cnt[cmd_bank_i]    <= '0;
                r_ap_closed[cmd_bank_i]  <= 1'b0;
            end

            if (w_is_col && !(&r_col_cnt[cmd_bank_i]))
                r_col_cnt[cmd_bank_i] <= r_col_cnt[cmd_bank_i] + 2'b01;

            // ---- outcome learning on explicit close ----
            // No row-active guard: the exported active bit is already clear by
            // the time the PRE issues (the scheduler drops it at pick time),
            // but the registered open-row image still holds the row being
            // closed — it only changes on the next ACT.
            if (w_is_pre) begin
                if (r_col_cnt[cmd_bank_i] <= 2'd1)
                    r_pred[f_idx(cmd_bank_i, bank_open_row_i[cmd_bank_i])] <=
                        f_inc(r_pred[f_idx(cmd_bank_i, bank_open_row_i[cmd_bank_i])]);
                else
                    r_pred[f_idx(cmd_bank_i, bank_open_row_i[cmd_bank_i])] <=
                        f_dec(r_pred[f_idx(cmd_bank_i, bank_open_row_i[cmd_bank_i])]);
            end

            // ---- close bookkeeping (fall -> claim window -> classify) ----
            for (int b = 0; b < NUM_BANKS; b++) begin
                if (w_fall[b]) begin
                    close_pred_o[b] <= 1'b0;
                    if (w_pre_claims[b]) begin
                        r_fall_wait[b] <= 1'b0;      // explicit close, resolved
                    end else begin
                        r_fall_wait[b] <= 1'b1;      // cause TBD one more cycle
                        r_fall_row[b]  <= r_prev_open_row[b];
                    end
                end else if (r_fall_wait[b]) begin
                    r_fall_wait[b] <= 1'b0;
                    if (!w_pre_claims[b]) begin
                        // unclaimed fall = auto-precharge close: remember,
                        // judge on reopen (premature-reopen decrement).
                        r_ap_closed[b] <= 1'b1;
                        r_ap_row[b]    <= r_fall_row[b];
                    end
                end
            end
        end
    end)

endmodule : pumice_row_pred_table
