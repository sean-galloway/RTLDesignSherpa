// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_cmd_history_checker
// Purpose: cmd_history_checker
//
// Documentation:
//   projects/components/mem-ctrl-ip/mem-ctrl-research-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// Carried from scoria_cmd_history_checker per andesite HAS ch02 (INHERITED),
// with the one bounded growth the MAS names: DDR4's long/short spacing set
// (tCCD_L/S, tRRD_L/S) as additional runtime parameters plus a bank-group
// command input -- parameter growth, not mechanism change. scoria's nine
// checks are byte-identical; the L/S checks are additive (10)-(13).
//
// Author: sean galloway
// Created: 2026-10-04 (carried + DDR4 spacing growth)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_cmd_history_checker
    import andesite_pkg::*;
#(
    parameter int NUM_RANKS = 1,
    parameter int NUM_BANKS = 8,
    // Depth must cover the longest JEDEC window checked (>= tRC). 0 slots off a
    // check whose window is 0.
    parameter int DEPTH     = 32,
    // JEDEC same-bank windows, in MC (controller) cycles. 0 disables the check.
    parameter int T_RCD     = 0,   // ACT -> RD/WR
    parameter int T_RP      = 0,   // PRE -> ACT
    parameter int T_RAS     = 0,   // ACT -> PRE
    parameter int T_RFC     = 0,   // REF -> ACT (refresh recovery)
    // GLOBAL (rank-wide, cross-bank) direction-turnaround windows. 0 disables.
    // These catch the DQ bus-turnaround class: a RD issued < T_WTR after ANY
    // WR (or WR < T_RTW after ANY RD) collides with the opposite burst's DQ
    // occupancy — the flopped-ok staleness bug (issue #42) the per-bank
    // history above cannot see.
    parameter int T_WTR     = 0,   // WR -> RD (global)
    parameter int T_RTW     = 0,   // RD -> WR (global)
    // GLOBAL (rank-wide, cross-bank) ACTIVATE rate limits. 0 disables.
    // tRRD and tFAW are the two JEDEC windows NO per-bank history can see: they
    // constrain ACTs to DIFFERENT banks, which is the whole reason scoria_global_timers
    // exists alongside scoria_bank_timer. Added for pumice ISSUE-019 -- the arbiter
    // checks both at its STAGE-1b pre-pick, two registers before the command
    // fires, and its final-stage re-validation covers only the per-bank gate, so
    // nothing rechecked cross-bank ACT spacing at the issuing cycle.
    parameter int T_RRD     = 0,   // ACT -> ACT, any bank in the rank
    parameter int T_FAW     = 0,   // at most 4 ACTs per rank in any T_FAW window
    // DDR4 bank-group long/short growth (andesite; 0 = inert, the scoria
    // posture for every timing here). L applies within one bank group, S
    // across bank groups. MAS ch01: parameter growth, not mechanism change.
    parameter int BG_WIDTH  = 2,
    parameter int T_CCD_L   = 0,   // CAS -> CAS, same bank group
    parameter int T_CCD_S   = 0,   // CAS -> CAS, different bank groups
    parameter int T_RRD_L   = 0,   // ACT -> ACT, same bank group
    parameter int T_RRD_S   = 0    // ACT -> ACT, different bank groups
) (
    input  logic       clk,
    input  logic       rst_n,
    // Issued abstract command (arbiter output, single-issue).
    input  logic       cmd_valid_i,
    input  dram_op_e   cmd_op_i,
    input  logic [($clog2(NUM_RANKS < 2 ? 2 : NUM_RANKS))-1:0] cmd_rank_i,
    input  logic [($clog2(NUM_BANKS))-1:0]                     cmd_bank_i,
    // Bank group of the issued command -- feeds the L/S pair checks only.
    input  logic [BG_WIDTH-1:0]                                cmd_bg_i
);

    // WINDOW BOUND: `d < T_x - 1`, not `d < T_x`.
    //
    // Slot d holds the command d+1 cycles ago (the $fatal text prints d+1), so
    // a loop bounded by T_x scans distances 1..T_x and flags a command at
    // EXACTLY T_x -- which is legal. Every one of these constraints is "must be
    // >= T_x cycles after", so only 1..T_x-1 is a violation.
    //
    // This was wrong in all six checks and it matters more than it looks: a
    // well-tuned controller lands ON the minimum, so the false alarm fires
    // precisely where the scheduler is doing its job. Found 2026-09-19 when the
    // new DFI-wire instance reported four "tRTW violation -- WR only 20 cyc
    // after a RD (need 20)" on RTL that is correct -- 20 >= 20.
    //
    // T_x = 1 now yields an empty loop, which is right: commands are one per
    // cycle, so a distance of >= 1 holds by construction.

    // ---- helpers ------------------------------------------------------------
    function automatic logic opens_row (input dram_op_e op);
        return (op == OP_ACT);
    endfunction
    // A row is CLOSED by an explicit precharge, an auto-precharge column op, or a
    // refresh (REFab precharges all banks; a PRE-all also closes every bank).
    function automatic logic closes_row (input dram_op_e op);
        return (op == OP_PRE)  || (op == OP_PREA)
            || (op == OP_RDA)  || (op == OP_WRA)
            || (op == OP_REF)  || (op == OP_REFPB);
    endfunction
    function automatic logic closes_all (input dram_op_e op);
        return (op == OP_PREA) || (op == OP_REF);   // all-bank precharge / REFab
    endfunction

    // ---- per-(rank,bank) command-history shift register ---------------------
    // r_hist[r][b][0] = op issued to bank (r,b) LAST cycle; [DEPTH-1] = oldest.
    dram_op_e r_hist [NUM_RANKS][NUM_BANKS][DEPTH];

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int r = 0; r < NUM_RANKS; r++)
                for (int b = 0; b < NUM_BANKS; b++)
                    for (int d = 0; d < DEPTH; d++)
                        r_hist[r][b][d] <= OP_NOP;
        end else begin
            for (int r = 0; r < NUM_RANKS; r++) begin
                for (int b = 0; b < NUM_BANKS; b++) begin
                    for (int d = DEPTH - 1; d > 0; d--)
                        r_hist[r][b][d] <= r_hist[r][b][d-1];
                    // slot 0: the op issued to THIS bank this cycle, else NOP.
                    // An all-bank op (PREA/REFab) is recorded on every bank so
                    // the row-open scan sees the close on each.
                    if (cmd_valid_i && closes_all(cmd_op_i))
                        r_hist[r][b][0] <= cmd_op_i;
                    else if (cmd_valid_i && (int'(cmd_rank_i) == r)
                                         && (int'(cmd_bank_i) == b))
                        r_hist[r][b][0] <= cmd_op_i;
                    else
                        r_hist[r][b][0] <= OP_NOP;
                end
            end
        end
    )

    // ---- GLOBAL column-direction history (all banks, one stream) ------------
    // r_gdir[d]: 2'b01 = a RD-class column issued d+1 cycles ago, 2'b10 = WR-
    // class, 2'b00 = neither. Feeds the cross-bank tWTR/tRTW checks.
    function automatic logic is_rd_col (input dram_op_e op);
        return (op == OP_RD) || (op == OP_RDA);
    endfunction
    function automatic logic is_wr_col (input dram_op_e op);
        return (op == OP_WR) || (op == OP_WRA);
    endfunction

    logic [1:0] r_gdir [DEPTH];
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int d = 0; d < DEPTH; d++) r_gdir[d] <= 2'b00;
        end else begin
            for (int d = DEPTH - 1; d > 0; d--) r_gdir[d] <= r_gdir[d-1];
            r_gdir[0] <= (cmd_valid_i && is_rd_col(cmd_op_i)) ? 2'b01 :
                         (cmd_valid_i && is_wr_col(cmd_op_i)) ? 2'b10 : 2'b00;
        end
    )

    // ---- GLOBAL per-rank ACTIVATE history (all banks, one stream) -----------
    // r_gact[r][d] = an ACT was issued to rank r, ANY bank, d+1 cycles ago.
    // Separate from r_hist because tRRD/tFAW do not care which bank: recording
    // per bank and scanning one bank's window is exactly what misses them.
    logic r_gact [NUM_RANKS][DEPTH];
    // andesite growth: bank group of each global-ACT slot, for tRRD_L/S.
    logic [BG_WIDTH-1:0] r_gact_bg [NUM_RANKS][DEPTH];
    // andesite growth: ANY-column global stream + bank group, for tCCD_L/S
    // (r_gdir is direction-specific; CAS-to-CAS does not care about direction).
    logic                r_gcol    [DEPTH];
    logic [BG_WIDTH-1:0] r_gcol_bg [DEPTH];
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int r = 0; r < NUM_RANKS; r++)
                for (int d = 0; d < DEPTH; d++) r_gact[r][d] <= 1'b0;
        end else begin
            for (int r = 0; r < NUM_RANKS; r++) begin
                for (int d = DEPTH - 1; d > 0; d--) r_gact[r][d] <= r_gact[r][d-1];
                r_gact[r][0] <= cmd_valid_i && opens_row(cmd_op_i)
                             && (int'(cmd_rank_i) == r);
            end
        end
    )

    // ---- derived: is bank (r,b) currently row-OPEN? -------------------------
    // Scan newest->oldest: the first row-affecting op decides. An ACT more recent
    // than any close => open. Includes a command issued THIS cycle (combinational
    // cmd_*), which has not yet shifted into slot 0.
    function automatic logic bank_row_open (input int r, input int b);
        if (cmd_valid_i && (closes_all(cmd_op_i)
              || ((int'(cmd_rank_i) == r) && (int'(cmd_bank_i) == b)))) begin
            if (closes_row(cmd_op_i)) return 1'b0;
            if (opens_row(cmd_op_i))  return 1'b1;
        end
        for (int d = 0; d < DEPTH; d++) begin
            if (closes_row(r_hist[r][b][d])) return 1'b0;
            if (opens_row(r_hist[r][b][d]))  return 1'b1;
        end
        return 1'b0;
    endfunction

    // ---- assertions (simulation only) ---------------------------------------
`ifndef SYNTHESIS
    // Row-open at the cycle a command is presented, EXCLUDING this cycle's own op
    // (so a REF can check "was a row already open before me").
    function automatic logic row_open_excl_self (input int r, input int b);
        for (int d = 0; d < DEPTH; d++) begin
            if (closes_row(r_hist[r][b][d])) return 1'b0;
            if (opens_row(r_hist[r][b][d]))  return 1'b1;
        end
        return 1'b0;
    endfunction

    // Position (cycles-ago) of the most recent op of a given type on a bank, or
    // DEPTH if not present within the window.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int r = 0; r < NUM_RANKS; r++)
                for (int d = 0; d < DEPTH; d++)
                    r_gact_bg[r][d] <= '0;
        end else begin
            for (int r = 0; r < NUM_RANKS; r++) begin
                for (int d = DEPTH - 1; d > 0; d--)
                    r_gact_bg[r][d] <= r_gact_bg[r][d-1];
                r_gact_bg[r][0] <= (cmd_valid_i && (cmd_op_i == OP_ACT))
                                   ? cmd_bg_i : '0;
            end
        end
    )

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int d = 0; d < DEPTH; d++) begin
                r_gcol[d]    <= 1'b0;
                r_gcol_bg[d] <= '0;
            end
        end else begin
            for (int d = DEPTH - 1; d > 0; d--) begin
                r_gcol[d]    <= r_gcol[d-1];
                r_gcol_bg[d] <= r_gcol_bg[d-1];
            end
            r_gcol[0]    <= cmd_valid_i && (is_rd_col(cmd_op_i) || is_wr_col(cmd_op_i));
            r_gcol_bg[0] <= cmd_bg_i;
        end
    )

    function automatic int last_pos (input int r, input int b, input dram_op_e op);
        for (int d = 0; d < DEPTH; d++)
            if (r_hist[r][b][d] == op) return d + 1;   // +1: slot0 == 1 cyc ago
        return DEPTH;
    endfunction

    // Diagnostic counters (visible via $display at end-of-sim or on demand).
    int dbg_cmd_cnt, dbg_ref_cnt, dbg_ref_openrow;
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            dbg_cmd_cnt <= 0; dbg_ref_cnt <= 0; dbg_ref_openrow <= 0;
        end else if (cmd_valid_i) begin
            dbg_cmd_cnt <= dbg_cmd_cnt + 1;
            if (cmd_op_i == OP_REF) begin
                dbg_ref_cnt <= dbg_ref_cnt + 1;
                for (int r = 0; r < NUM_RANKS; r++)
                    for (int b = 0; b < NUM_BANKS; b++)
                        if (row_open_excl_self(r, b)) dbg_ref_openrow <= dbg_ref_openrow + 1;
                $display("CMD_HISTORY DBG @%0t: OP_REF seen (#%0d); any-row-open example scan follows",
                         $time, dbg_ref_cnt + 1);
            end
        end
    )

    always_ff @(posedge clk) begin
        if (rst_n && cmd_valid_i) begin
            // (1) REFRESH-COLLISION: a REFab requires ALL banks precharged. This
            //     is bug #2 — ACT then REF with no PRE refreshes an open row.
            if (cmd_op_i == OP_REF) begin
                for (int r = 0; r < NUM_RANKS; r++)
                    for (int b = 0; b < NUM_BANKS; b++)
                        assert (!row_open_excl_self(r, b))
                          else $fatal(1, "CMD_HISTORY @%0t: REFab issued with rank%0d bank%0d ROW OPEN (ACT %0d cyc ago, no PRE) -- refresh collides with an open row",
                                      $time, r, b, last_pos(r, b, OP_ACT));
            end
            // (2) tRCD: a column op must be >= T_RCD cycles after its bank's ACT.
            if (T_RCD > 0 && is_column_op(cmd_op_i)) begin
                for (int d = 0; d < T_RCD - 1; d++)
                    assert (r_hist[cmd_rank_i][cmd_bank_i][d] != OP_ACT)
                      else $fatal(1, "CMD_HISTORY @%0t: tRCD violation -- bank%0d %s only %0d cyc after ACT (need %0d)",
                                  $time, cmd_bank_i, cmd_op_i.name(), d + 1, T_RCD);
            end
            // (3) tRP: an ACT must be >= T_RP cycles after its bank's PRE.
            if (T_RP > 0 && (cmd_op_i == OP_ACT)) begin
                for (int d = 0; d < T_RP - 1; d++)
                    assert (r_hist[cmd_rank_i][cmd_bank_i][d] != OP_PRE)
                      else $fatal(1, "CMD_HISTORY @%0t: tRP violation -- bank%0d ACT only %0d cyc after PRE (need %0d)",
                                  $time, cmd_bank_i, d + 1, T_RP);
            end
            // (4) tRAS: a PRE must be >= T_RAS cycles after its bank's ACT.
            if (T_RAS > 0 && (cmd_op_i == OP_PRE)) begin
                for (int d = 0; d < T_RAS - 1; d++)
                    assert (r_hist[cmd_rank_i][cmd_bank_i][d] != OP_ACT)
                      else $fatal(1, "CMD_HISTORY @%0t: tRAS violation -- bank%0d PRE only %0d cyc after ACT (need %0d)",
                                  $time, cmd_bank_i, d + 1, T_RAS);
            end
            // (6) GLOBAL tWTR: a RD-class column must be >= T_WTR cycles
            //     after ANY WR-class column (cross-bank DQ turnaround).
            if (T_WTR > 0 && is_rd_col(cmd_op_i)) begin
                for (int d = 0; d < T_WTR - 1; d++)
                    assert (r_gdir[d] != 2'b10)
                      else $fatal(1, "CMD_HISTORY @%0t: GLOBAL tWTR violation -- RD only %0d cyc after a WR (need %0d) -- DQ bus turnaround contention",
                                  $time, d + 1, T_WTR);
            end
            // (7) GLOBAL tRTW: a WR-class column must be >= T_RTW cycles
            //     after ANY RD-class column.
            if (T_RTW > 0 && is_wr_col(cmd_op_i)) begin
                for (int d = 0; d < T_RTW - 1; d++)
                    assert (r_gdir[d] != 2'b01)
                      else $fatal(1, "CMD_HISTORY @%0t: GLOBAL tRTW violation -- WR only %0d cyc after a RD (need %0d) -- DQ bus turnaround contention",
                                  $time, d + 1, T_RTW);
            end
            // (8) GLOBAL tRRD: an ACT must be >= T_RRD cycles after ANY ACT to
            //     the same rank, whatever bank. pumice ISSUE-019: scoria_bank_timer's
            //     windows are per-bank and cannot see this, and the arbiter's
            //     own check sits two registers before the fire.
            if (T_RRD > 0 && (cmd_op_i == OP_ACT)) begin
                for (int d = 0; d < T_RRD - 1; d++)
                    assert (!r_gact[cmd_rank_i][d])
                      else $fatal(1, "CMD_HISTORY @%0t: GLOBAL tRRD violation -- rank%0d bank%0d ACT only %0d cyc after another ACT (need %0d) -- cross-bank activate rate limit",
                                  $time, cmd_rank_i, cmd_bank_i, d + 1, T_RRD);
            end
            // (9) GLOBAL tFAW: at most FOUR ACTs per rank inside any T_FAW
            //     window. This ACT is the fifth if four already sit in it.
            if (T_FAW > 0 && (cmd_op_i == OP_ACT)) begin
                automatic int faw_n = 0;
                for (int d = 0; d < T_FAW - 1; d++)
                    if (r_gact[cmd_rank_i][d]) faw_n++;
                assert (faw_n < 4)
                  else $fatal(1, "CMD_HISTORY @%0t: GLOBAL tFAW violation -- rank%0d bank%0d is the %0dth ACT inside a %0d-cycle window (max 4)",
                              $time, cmd_rank_i, cmd_bank_i, faw_n + 1, T_FAW);
            end
            // (10) GLOBAL tCCD_L: a CAS must be >= T_CCD_L cycles after a CAS
            //     to the SAME bank group (DDR4 long window).
            if (T_CCD_L > 0 && (is_rd_col(cmd_op_i) || is_wr_col(cmd_op_i))) begin
                for (int d = 0; d < T_CCD_L - 1; d++)
                    assert (!(r_gcol[d] && (r_gcol_bg[d] == cmd_bg_i)))
                      else $fatal(1, "CMD_HISTORY @%0t: tCCD_L violation -- CAS to bank group %0d only %0d cyc after a CAS in the same group (need %0d)",
                                  $time, cmd_bg_i, d + 1, T_CCD_L);
            end
            // (11) GLOBAL tCCD_S: a CAS must be >= T_CCD_S cycles after a CAS
            //     to a DIFFERENT bank group (DDR4 short window).
            if (T_CCD_S > 0 && (is_rd_col(cmd_op_i) || is_wr_col(cmd_op_i))) begin
                for (int d = 0; d < T_CCD_S - 1; d++)
                    assert (!(r_gcol[d] && (r_gcol_bg[d] != cmd_bg_i)))
                      else $fatal(1, "CMD_HISTORY @%0t: tCCD_S violation -- CAS to bank group %0d only %0d cyc after a CAS in another group (need %0d)",
                                  $time, cmd_bg_i, d + 1, T_CCD_S);
            end
            // (12) GLOBAL tRRD_L: an ACT must be >= T_RRD_L cycles after an ACT
            //     to the SAME bank group (the L/S growth of scoria's (8)).
            if (T_RRD_L > 0 && (cmd_op_i == OP_ACT)) begin
                for (int d = 0; d < T_RRD_L - 1; d++)
                    assert (!(r_gact[cmd_rank_i][d] && (r_gact_bg[cmd_rank_i][d] == cmd_bg_i)))
                      else $fatal(1, "CMD_HISTORY @%0t: tRRD_L violation -- rank%0d group%0d ACT only %0d cyc after an ACT in the same group (need %0d)",
                                  $time, cmd_rank_i, cmd_bg_i, d + 1, T_RRD_L);
            end
            // (13) GLOBAL tRRD_S: an ACT must be >= T_RRD_S cycles after an ACT
            //     to a DIFFERENT bank group.
            if (T_RRD_S > 0 && (cmd_op_i == OP_ACT)) begin
                for (int d = 0; d < T_RRD_S - 1; d++)
                    assert (!(r_gact[cmd_rank_i][d] && (r_gact_bg[cmd_rank_i][d] != cmd_bg_i)))
                      else $fatal(1, "CMD_HISTORY @%0t: tRRD_S violation -- rank%0d group%0d ACT only %0d cyc after an ACT in another group (need %0d)",
                                  $time, cmd_rank_i, cmd_bg_i, d + 1, T_RRD_S);
            end
            // (5) tRFC: an ACT must be >= T_RFC cycles after a REFab (refresh
            //     recovery). REFab is recorded on every bank's history, so the
            //     ACT's own bank window carries it. A too-soon ACT means the DRAM
            //     is still refreshing -> the following read returns garbage.
            if (T_RFC > 0 && (cmd_op_i == OP_ACT)) begin
                for (int d = 0; d < T_RFC - 1; d++)
                    assert (r_hist[cmd_rank_i][cmd_bank_i][d] != OP_REF)
                      else $fatal(1, "CMD_HISTORY @%0t: tRFC violation -- bank%0d ACT only %0d cyc after REFab (need %0d) -- refresh recovery not enforced",
                                  $time, cmd_bank_i, d + 1, T_RFC);
            end
        end
    end
`endif

endmodule : andesite_cmd_history_checker
