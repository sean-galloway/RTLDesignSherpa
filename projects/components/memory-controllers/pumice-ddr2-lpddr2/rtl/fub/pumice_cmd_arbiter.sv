// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_cmd_arbiter
// Purpose: The command arbiter for the pumice scheduler layer. Each cycle it
//          picks ONE abstract DRAM command and pushes it into the scheduler->DFI
//          command interface. PHY/nphases-agnostic; single-issue. JEDEC timing
//          is enforced via the per-bank (pumice_bank_timers) and global
//          (global_timers) readiness inputs.
//
// Priority per cycle:
//   1. init      : !init_done -> forward the init_sequencer command.
//   2. refresh   : refresh_req -> PRE active banks (one/cycle), then REF+grant.
//   3. column    : row-hit RD/WR to an open row (bank_rdwr_ready & tCCD & turn-
//                  around). READ-PRIORITY; OLDEST (CAM age) tie-break.
//   4. fallback  : no ready row-hit -> ACT the oldest pending op's row (idle
//                  bank) or PRE a bank open on the wrong row.
//
// Page policy (page_policy_i): OPEN (ap=0, rows stay open) | CLOSE (ap=1, every
// column op auto-precharges) | HAPPY_HYBRID (v1: treated as OPEN — page_predictor
// hook is a TODO).
//
// v1 scope: single-rank pick (rank 0); write-drain watermark + multi-rank +
// powerdown are TODO. Documentation: rtl/PUMICE_MEM_CMD_SCHEDULER_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_cmd_arbiter
    import pumice_pkg::*;
#(
    parameter int NUM_RANKS  = 1,
    parameter int NUM_BANKS  = 8,
    parameter int ROW_WIDTH  = 14,
    parameter int COL_WIDTH  = 10,
    parameter int AXI_ID_WIDTH = 8,
    parameter int NUM_ENTRIES = 8,
    parameter int AGE_WIDTH  = 16,
    parameter int N_LU       = NUM_BANKS,          // one lookup per bank
    parameter int RKW  = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int PTRW = $clog2(NUM_ENTRIES),
    parameter int IW   = AXI_ID_WIDTH
) (
    input  logic                      aclk,
    input  logic                      aresetn,
    input  page_policy_e              page_policy_i,

    // ---- init passthrough (from init_sequencer) ----
    input  logic                      init_done_i,
    input  logic                      init_cmd_valid_i,
    input  dram_op_e                  init_cmd_op_i,
    input  logic [BKW-1:0]            init_cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]      init_cmd_row_i,

    // ---- refresh (from refresh_ctrl) ----
    input  logic                      refresh_req_i,
    input  logic                      refresh_drain_i,
    output logic                      refresh_grant_o,

    // ---- per-bank readiness (from pumice_bank_timers) ----
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_act_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_rdwr_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_pre_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_row_active_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]  bank_open_row_i,

    // ---- global readiness (from global_timers) ----
    input  logic [NUM_RANKS-1:0]      tfaw_ok_i,
    input  logic [NUM_RANKS-1:0]      trrd_ok_i,
    input  logic                      twtr_ok_i,
    input  logic                      trtw_ok_i,
    input  logic                      tccd_ok_i,

    // ---- wr CAM sched lookup (drive queries, read results) ----
    output logic [N_LU-1:0]           wr_lu_valid_o,
    output logic [N_LU*BKW-1:0]       wr_lu_bank_o,
    output logic [N_LU*ROW_WIDTH-1:0] wr_lu_row_o,
    input  logic [N_LU-1:0]           wr_lu_hit_i,
    input  logic [N_LU*PTRW-1:0]      wr_lu_slot_i,
    input  logic [N_LU*COL_WIDTH-1:0] wr_lu_col_i,
    input  logic [N_LU*IW-1:0]        wr_lu_id_i,
    input  logic [N_LU*AGE_WIDTH-1:0] wr_lu_age_i,
    input  logic                      wr_oldest_valid_i,
    input  logic [BKW-1:0]            wr_oldest_bank_i,
    input  logic [ROW_WIDTH-1:0]      wr_oldest_row_i,
    input  logic [PTRW-1:0]           wr_oldest_slot_i,
    output logic                      wr_commit_valid_o,
    output logic [PTRW-1:0]           wr_commit_slot_o,

    // ---- rd CAM sched lookup ----
    output logic [N_LU-1:0]           rd_lu_valid_o,
    output logic [N_LU*BKW-1:0]       rd_lu_bank_o,
    output logic [N_LU*ROW_WIDTH-1:0] rd_lu_row_o,
    input  logic [N_LU-1:0]           rd_lu_hit_i,
    input  logic [N_LU*PTRW-1:0]      rd_lu_slot_i,
    input  logic [N_LU*COL_WIDTH-1:0] rd_lu_col_i,
    input  logic [N_LU*IW-1:0]        rd_lu_id_i,
    input  logic [N_LU*AGE_WIDTH-1:0] rd_lu_age_i,
    input  logic                      rd_oldest_valid_i,
    input  logic [BKW-1:0]            rd_oldest_bank_i,
    input  logic [ROW_WIDTH-1:0]      rd_oldest_row_i,
    input  logic [PTRW-1:0]           rd_oldest_slot_i,
    output logic                      rd_issue_valid_o,
    output logic [PTRW-1:0]           rd_issue_slot_o,

    // ---- event strobes to bank + global timers ----
    output logic                      evt_act_o,
    output logic                      evt_rd_o,
    output logic                      evt_wr_o,
    output logic                      evt_pre_o,
    output logic                      evt_ap_o,
    output logic [RKW-1:0]            evt_rank_o,
    output logic [BKW-1:0]            evt_bank_o,
    output logic [ROW_WIDTH-1:0]      evt_row_o,

    // ---- command push (scheduler -> DFI command FIFO) ----
    output logic                      cmd_valid_o,
    input  logic                      cmd_ready_i,
    output dram_op_e                  cmd_op_o,
    output logic [RKW-1:0]            cmd_rank_o,
    output logic [BKW-1:0]            cmd_bank_o,
    output logic [ROW_WIDTH-1:0]      cmd_row_o,
    output logic [COL_WIDTH-1:0]      cmd_col_o,
    output logic                      cmd_ap_o
);

    localparam int RK0 = 0;   // v1 single-rank pick

    // Column auto-precharge bit from the page policy.
    logic w_ap;
    assign w_ap = (page_policy_i == PAGE_POLICY_CLOSE);

    // Per-bank ACT/PRE re-issue GUARD. The bank timers register their readiness
    // outputs (2-cycle latency from an evt to act/pre_ready dropping), so a
    // stateless combinational arbiter would re-issue ACT/PRE to the same bank
    // before the timers reflect it. Guard a bank for 2 cycles after issuing an
    // ACT/PRE to it. (Column ops self-limit: the CAM retires the entry on
    // commit/issue, so no guard needed there.)
    logic [NUM_BANKS-1:0] r_guard0, r_guard1;
    logic [NUM_BANKS-1:0] w_guarded;
    assign w_guarded = r_guard0 | r_guard1;
    // NOTE: no global column guard is needed. Both CAMs exclude a just-committed/
    // issued slot from sched_lu/oldest the next cycle (wr r_sched, rd r_issued),
    // so the arbiter never re-issues the same slot and columns flow 1/clock.
    // tCCD (=2 CK) is sub-controller-cycle at nphases>=2, enforced by
    // tccd_ok_i without throttling consecutive controller cycles.

    // ---- drive the per-bank lookups: query {bank j, its open row} ----------
    always_comb begin
        for (int j = 0; j < N_LU; j++) begin
            wr_lu_valid_o[j]                     = bank_row_active_i[RK0][j];
            wr_lu_bank_o[j*BKW +: BKW]           = BKW'(j);
            wr_lu_row_o[j*ROW_WIDTH +: ROW_WIDTH] = bank_open_row_i[RK0][j];
            rd_lu_valid_o[j]                     = bank_row_active_i[RK0][j];
            rd_lu_bank_o[j*BKW +: BKW]           = BKW'(j);
            rd_lu_row_o[j*ROW_WIDTH +: ROW_WIDTH] = bank_open_row_i[RK0][j];
        end
    end

    // ---- scan for oldest ready row-hit RD and WR ---------------------------
    // A hit is issuable when the bank is column-ready and the shared-bus
    // turnaround/pacing timers allow it. OLDEST (max CAM rel-age) wins.
    logic            w_rd_found, w_wr_found;
    logic [BKW-1:0]  w_rd_bank,  w_wr_bank;
    logic [PTRW-1:0] w_rd_slot,  w_wr_slot;
    logic [COL_WIDTH-1:0] w_rd_col, w_wr_col;
    logic [AGE_WIDTH-1:0] w_rd_best, w_wr_best;

    always_comb begin
        w_rd_found = 1'b0; w_rd_bank = '0; w_rd_slot = '0; w_rd_col = '0; w_rd_best = '0;
        w_wr_found = 1'b0; w_wr_bank = '0; w_wr_slot = '0; w_wr_col = '0; w_wr_best = '0;
        for (int j = 0; j < N_LU; j++) begin
            automatic logic [AGE_WIDTH-1:0] rd_age = rd_lu_age_i[j*AGE_WIDTH +: AGE_WIDTH];
            automatic logic [AGE_WIDTH-1:0] wr_age = wr_lu_age_i[j*AGE_WIDTH +: AGE_WIDTH];
            // RD candidate
            if (rd_lu_hit_i[j] && bank_rdwr_ready_i[RK0][j] && tccd_ok_i && twtr_ok_i) begin
                if (!w_rd_found || rd_age > w_rd_best) begin
                    w_rd_found = 1'b1;  w_rd_best = rd_age;  w_rd_bank = BKW'(j);
                    w_rd_slot  = rd_lu_slot_i[j*PTRW +: PTRW];
                    w_rd_col   = rd_lu_col_i [j*COL_WIDTH +: COL_WIDTH];
                end
            end
            // WR candidate
            if (wr_lu_hit_i[j] && bank_rdwr_ready_i[RK0][j] && tccd_ok_i && trtw_ok_i) begin
                if (!w_wr_found || wr_age > w_wr_best) begin
                    w_wr_found = 1'b1;  w_wr_best = wr_age;  w_wr_bank = BKW'(j);
                    w_wr_slot  = wr_lu_slot_i[j*PTRW +: PTRW];
                    w_wr_col   = wr_lu_col_i [j*COL_WIDTH +: COL_WIDTH];
                end
            end
        end
    end

    // ---- refresh: pick the lowest active bank that can precharge ------------
    logic            w_any_active, w_rfsh_pre_found;
    logic [BKW-1:0]  w_rfsh_pre_bank;
    always_comb begin
        w_any_active     = |bank_row_active_i[RK0];
        w_rfsh_pre_found = 1'b0;
        w_rfsh_pre_bank  = '0;
        for (int j = NUM_BANKS-1; j >= 0; j--)
            if (bank_row_active_i[RK0][j] && bank_pre_ready_i[RK0][j] && !w_guarded[j]) begin
                w_rfsh_pre_found = 1'b1;
                w_rfsh_pre_bank  = BKW'(j);
            end
    end

    // ---- fallback target (read-priority): oldest pending op ----------------
    logic            w_fb_valid;
    logic [BKW-1:0]  w_fb_bank;
    logic [ROW_WIDTH-1:0] w_fb_row;
    always_comb begin
        if (rd_oldest_valid_i) begin
            w_fb_valid = 1'b1; w_fb_bank = rd_oldest_bank_i; w_fb_row = rd_oldest_row_i;
        end else begin
            w_fb_valid = wr_oldest_valid_i; w_fb_bank = wr_oldest_bank_i; w_fb_row = wr_oldest_row_i;
        end
    end

    // ========================================================================
    // Priority pick (combinational). Produces the abstract command + the
    // side-effects (evt / commit / issue / grant), all gated on cmd accept.
    // ========================================================================
    dram_op_e        w_op;
    logic [BKW-1:0]  w_bank;
    logic [ROW_WIDTH-1:0] w_row;
    logic [COL_WIDTH-1:0] w_col;
    logic            w_ap_out;
    logic            w_valid;
    logic            w_do_act, w_do_rd, w_do_wr, w_do_pre, w_grant;
    logic            w_wr_commit, w_rd_issue;
    logic [PTRW-1:0] w_commit_slot, w_issue_slot;

    always_comb begin
        w_op = OP_NOP; w_bank = '0; w_row = '0; w_col = '0; w_ap_out = 1'b0;
        w_valid = 1'b0;
        w_do_act = 1'b0; w_do_rd = 1'b0; w_do_wr = 1'b0; w_do_pre = 1'b0; w_grant = 1'b0;
        w_wr_commit = 1'b0; w_rd_issue = 1'b0; w_commit_slot = '0; w_issue_slot = '0;

        if (!init_done_i) begin
            // 1. INIT — forward the sequencer command verbatim.
            if (init_cmd_valid_i) begin
                w_valid = 1'b1; w_op = init_cmd_op_i;
                w_bank = init_cmd_bank_i; w_row = init_cmd_row_i;
            end
        end else if (refresh_req_i || refresh_drain_i) begin
            // 2. REFRESH — precharge active banks first, then REF + grant.
            if (w_any_active) begin
                if (w_rfsh_pre_found) begin
                    w_valid = 1'b1; w_op = OP_PRE; w_bank = w_rfsh_pre_bank;
                    w_do_pre = 1'b1;
                end
            end else begin
                w_valid = 1'b1; w_op = OP_REF; w_grant = 1'b1;
            end
        end else if (w_rd_found) begin
            // 3a. READ row-hit (read-priority).
            w_valid = 1'b1; w_op = w_ap ? OP_RDA : OP_RD;
            w_bank = w_rd_bank; w_col = w_rd_col; w_ap_out = w_ap;
            w_do_rd = 1'b1; w_rd_issue = 1'b1; w_issue_slot = w_rd_slot;
        end else if (w_wr_found) begin
            // 3b. WRITE row-hit.
            w_valid = 1'b1; w_op = w_ap ? OP_WRA : OP_WR;
            w_bank = w_wr_bank; w_col = w_wr_col; w_ap_out = w_ap;
            w_do_wr = 1'b1; w_wr_commit = 1'b1; w_commit_slot = w_wr_slot;
        end else if (w_fb_valid) begin
            // 4. FALLBACK — open the oldest op's row, or close a conflicting row.
            //    Guarded banks (recent ACT/PRE) are skipped so we don't re-issue
            //    before the timers reflect the previous command.
            if (!bank_row_active_i[RK0][w_fb_bank] && !w_guarded[w_fb_bank]
                && bank_act_ready_i[RK0][w_fb_bank] && tfaw_ok_i[RK0] && trrd_ok_i[RK0]) begin
                w_valid = 1'b1; w_op = OP_ACT; w_bank = w_fb_bank; w_row = w_fb_row;
                w_do_act = 1'b1;
            end else if (bank_row_active_i[RK0][w_fb_bank] && !w_guarded[w_fb_bank]
                         && (bank_open_row_i[RK0][w_fb_bank] != w_fb_row)
                         && bank_pre_ready_i[RK0][w_fb_bank]) begin
                w_valid = 1'b1; w_op = OP_PRE; w_bank = w_fb_bank;
                w_do_pre = 1'b1;
            end
        end
    end

    // Issue only when the command sink accepts the push.
    logic w_fire;
    assign w_fire = w_valid && cmd_ready_i;

    // ---- command push outputs ----
    assign cmd_valid_o = w_valid;
    assign cmd_op_o    = w_op;
    assign cmd_rank_o  = RKW'(RK0);
    assign cmd_bank_o  = w_bank;
    assign cmd_row_o   = w_row;
    assign cmd_col_o   = w_col;
    assign cmd_ap_o    = w_ap_out;

    // ---- event strobes (only on accepted issue) ----
    assign evt_act_o = w_fire && w_do_act;
    assign evt_rd_o  = w_fire && w_do_rd;
    assign evt_wr_o  = w_fire && w_do_wr;
    assign evt_pre_o = w_fire && w_do_pre;
    assign evt_ap_o  = w_ap_out;
    assign evt_rank_o = RKW'(RK0);
    assign evt_bank_o = w_bank;
    assign evt_row_o  = w_row;

    // ---- CAM commit / issue / refresh grant (only on accepted issue) ----
    assign wr_commit_valid_o = w_fire && w_wr_commit;
    assign wr_commit_slot_o  = w_commit_slot;
    assign rd_issue_valid_o  = w_fire && w_rd_issue;
    assign rd_issue_slot_o   = w_issue_slot;
    assign refresh_grant_o   = w_fire && w_grant;

    // ---- guard update: 2-cycle per-bank block after an accepted ACT/PRE ----
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_guard0 <= '0;
            r_guard1 <= '0;
        end else begin
            r_guard1 <= r_guard0;
            r_guard0 <= '0;
            if (w_fire && (w_do_act || w_do_pre))
                r_guard0 <= (NUM_BANKS'(1) << w_bank);
        end
    )

    wire unused = &{1'b0, wr_lu_id_i, rd_lu_id_i, wr_oldest_slot_i, rd_oldest_slot_i, 1'b0};

endmodule : pumice_cmd_arbiter
