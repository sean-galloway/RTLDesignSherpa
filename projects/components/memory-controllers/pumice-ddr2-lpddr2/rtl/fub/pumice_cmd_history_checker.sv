// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// pumice_cmd_history_checker — FINE-GRAINED per-bank command-history scoreboard.
//
// Purpose: audit the arbiter's issued abstract-command stream against JEDEC
// same-bank sequencing. The functional "safe signals" (pumice_bank_timers
// readiness + the class-A/B/C hazard framework) are COARSE — they gate "may a
// command-class issue to this bank now", and they are REGISTERED (2-cycle
// event->ready latency, see pumice_cmd_arbiter r_guard). A combinational picker
// fed by that registered readiness can therefore issue a command the coarse gate
// has not yet accounted for — e.g. ACT a bank, then (next cycle) grant a REFab
// while that row is still OPEN (no PRE). The coarse gate never sees it; the read
// that follows the refresh returns garbage.
//
// This scoreboard is the FINE-GRAINED complement: a per-(rank,bank) shift
// register recording EXACTLY what was issued each cycle (slot 0 = this cycle,
// shifting right, falling off after DEPTH). Slot position == cycles-since-issue,
// so every JEDEC same-bank rule is a positional lookup, and violations the
// coarse gate misses are caught at the issuing cycle with the offending bank +
// prior command named.
//
// Intended use: `bind pumice_cmd_arbiter` (or the scheduler). The history is
// plain synthesizable logic (usable as an on-silicon debug trace too); the
// assertions are simulation-only.
//
// Scope note: this catches command-SEQUENCING defects. It does NOT catch data-
// path de-interleave/skew (e.g. the DFI read device-word order) — pair it with
// the DFI-read-boundary device-word data check for that class.

`timescale 1ns / 1ps

module pumice_cmd_history_checker
    import pumice_pkg::*;
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
    parameter int T_RTW     = 0    // RD -> WR (global)
) (
    input  logic       clk,
    input  logic       rst_n,
    // Issued abstract command (arbiter output, single-issue).
    input  logic       cmd_valid_i,
    input  dram_op_e   cmd_op_i,
    input  logic [($clog2(NUM_RANKS < 2 ? 2 : NUM_RANKS))-1:0] cmd_rank_i,
    input  logic [($clog2(NUM_BANKS))-1:0]                     cmd_bank_i
);

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

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
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
    end

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
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int d = 0; d < DEPTH; d++) r_gdir[d] <= 2'b00;
        end else begin
            for (int d = DEPTH - 1; d > 0; d--) r_gdir[d] <= r_gdir[d-1];
            r_gdir[0] <= (cmd_valid_i && is_rd_col(cmd_op_i)) ? 2'b01 :
                         (cmd_valid_i && is_wr_col(cmd_op_i)) ? 2'b10 : 2'b00;
        end
    end

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
    function automatic int last_pos (input int r, input int b, input dram_op_e op);
        for (int d = 0; d < DEPTH; d++)
            if (r_hist[r][b][d] == op) return d + 1;   // +1: slot0 == 1 cyc ago
        return DEPTH;
    endfunction

    // Diagnostic counters (visible via $display at end-of-sim or on demand).
    int dbg_cmd_cnt, dbg_ref_cnt, dbg_ref_openrow;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
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
    end

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
                for (int d = 0; d < T_RCD; d++)
                    assert (r_hist[cmd_rank_i][cmd_bank_i][d] != OP_ACT)
                      else $fatal(1, "CMD_HISTORY @%0t: tRCD violation -- bank%0d %s only %0d cyc after ACT (need %0d)",
                                  $time, cmd_bank_i, cmd_op_i.name(), d + 1, T_RCD);
            end
            // (3) tRP: an ACT must be >= T_RP cycles after its bank's PRE.
            if (T_RP > 0 && (cmd_op_i == OP_ACT)) begin
                for (int d = 0; d < T_RP; d++)
                    assert (r_hist[cmd_rank_i][cmd_bank_i][d] != OP_PRE)
                      else $fatal(1, "CMD_HISTORY @%0t: tRP violation -- bank%0d ACT only %0d cyc after PRE (need %0d)",
                                  $time, cmd_bank_i, d + 1, T_RP);
            end
            // (4) tRAS: a PRE must be >= T_RAS cycles after its bank's ACT.
            if (T_RAS > 0 && (cmd_op_i == OP_PRE)) begin
                for (int d = 0; d < T_RAS; d++)
                    assert (r_hist[cmd_rank_i][cmd_bank_i][d] != OP_ACT)
                      else $fatal(1, "CMD_HISTORY @%0t: tRAS violation -- bank%0d PRE only %0d cyc after ACT (need %0d)",
                                  $time, cmd_bank_i, d + 1, T_RAS);
            end
            // (6) GLOBAL tWTR: a RD-class column must be >= T_WTR cycles
            //     after ANY WR-class column (cross-bank DQ turnaround).
            if (T_WTR > 0 && is_rd_col(cmd_op_i)) begin
                for (int d = 0; d < T_WTR; d++)
                    assert (r_gdir[d] != 2'b10)
                      else $fatal(1, "CMD_HISTORY @%0t: GLOBAL tWTR violation -- RD only %0d cyc after a WR (need %0d) -- DQ bus turnaround contention",
                                  $time, d + 1, T_WTR);
            end
            // (7) GLOBAL tRTW: a WR-class column must be >= T_RTW cycles
            //     after ANY RD-class column.
            if (T_RTW > 0 && is_wr_col(cmd_op_i)) begin
                for (int d = 0; d < T_RTW; d++)
                    assert (r_gdir[d] != 2'b01)
                      else $fatal(1, "CMD_HISTORY @%0t: GLOBAL tRTW violation -- WR only %0d cyc after a RD (need %0d) -- DQ bus turnaround contention",
                                  $time, d + 1, T_RTW);
            end
            // (5) tRFC: an ACT must be >= T_RFC cycles after a REFab (refresh
            //     recovery). REFab is recorded on every bank's history, so the
            //     ACT's own bank window carries it. A too-soon ACT means the DRAM
            //     is still refreshing -> the following read returns garbage.
            if (T_RFC > 0 && (cmd_op_i == OP_ACT)) begin
                for (int d = 0; d < T_RFC; d++)
                    assert (r_hist[cmd_rank_i][cmd_bank_i][d] != OP_REF)
                      else $fatal(1, "CMD_HISTORY @%0t: tRFC violation -- bank%0d ACT only %0d cyc after REFab (need %0d) -- refresh recovery not enforced",
                                  $time, cmd_bank_i, d + 1, T_RFC);
            end
        end
    end
`endif

endmodule : pumice_cmd_history_checker
