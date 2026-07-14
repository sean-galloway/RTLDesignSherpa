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
// The arbiter reads the CAMs' per-entry state as flat REGISTERED vectors
// ({valid,bank,row,col,age} indexed by entry) and does the match + argmax
// itself. No sched-lookup query round-trip into the CAMs, and — crucially —
// it can ACTIVATE MANY BANKS IN PARALLEL: the fallback opens the oldest pending
// op's row among ANY idle+ready bank, not just the single global-oldest bank.
// That bank-parallel activation is what removes the per-transaction bubble
// (previously bank N sat through its whole tRCD before bank N+1 was even
// activated, serializing every access to full ACT->data latency).
//
// Priority per cycle:
//   1. init      : !init_done -> forward the init_sequencer command.
//   2. refresh   : refresh_req -> PRE active banks (one/cycle), then REF+grant.
//   3. column    : row-hit RD/WR to an open, tRCD-met row (READ-priority;
//                  OLDEST CAM age tie-break). Streams at tCCD rate.
//   4. activate  : oldest pending op whose bank is idle+act-ready -> ACT it.
//                  Scans ALL entries, so successive cycles open DIFFERENT banks
//                  (their tRCDs overlap) => no activate bubble.
//   5. precharge : oldest pending op whose bank is open on the WRONG row -> PRE.
//
// Page policy (page_policy_i): OPEN (ap=0, rows stay open) | CLOSE (ap=1, every
// column op auto-precharges) | HAPPY_HYBRID (v1: treated as OPEN).
//
// v1 scope: single-rank pick (rank 0). Documentation:
// rtl/PUMICE_MEM_CMD_SCHEDULER_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_cmd_arbiter
    import pumice_pkg::*;
#(
    parameter int NUM_RANKS   = 1,
    parameter int NUM_BANKS   = 8,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int AXI_ID_WIDTH = 8,
    parameter int NUM_ENTRIES = 8,
    parameter int AGE_WIDTH   = 16,
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

    // ---- wr CAM per-entry vectors (registered) + commit ----
    input  logic [NUM_ENTRIES-1:0]              wr_sch_valid_i,
    input  logic [NUM_ENTRIES*BKW-1:0]          wr_sch_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]    wr_sch_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]    wr_sch_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  wr_sch_older_i,
    input  logic                                wr_commit_ready_i,   // wr CAM drain-FIFO room
    output logic                                wr_commit_valid_o,
    output logic [PTRW-1:0]                     wr_commit_slot_o,

    // ---- rd CAM per-entry vectors (registered) + issue ----
    input  logic [NUM_ENTRIES-1:0]              rd_sch_valid_i,
    input  logic [NUM_ENTRIES*BKW-1:0]          rd_sch_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]    rd_sch_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]    rd_sch_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  rd_sch_older_i,
    input  logic                                rd_issue_ready_i,    // rd CAM issue-FIFO room
    output logic                                rd_issue_valid_o,
    output logic [PTRW-1:0]                     rd_issue_slot_o,

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
    // commit/issue, so sch_valid drops the next cycle => no re-issue.)
    logic [NUM_BANKS-1:0] r_guard0, r_guard1;
    logic [NUM_BANKS-1:0] w_guarded;
    assign w_guarded = r_guard0 | r_guard1;

    // ---- per-entry field extractors --------------------------------------
    function automatic logic [BKW-1:0]       f_bank(input logic [NUM_ENTRIES*BKW-1:0] v, input logic [PTRW-1:0] e);
        return v[e*BKW +: BKW];
    endfunction
    function automatic logic [ROW_WIDTH-1:0] f_row (input logic [NUM_ENTRIES*ROW_WIDTH-1:0] v, input logic [PTRW-1:0] e);
        return v[e*ROW_WIDTH +: ROW_WIDTH];
    endfunction
    function automatic logic [COL_WIDTH-1:0] f_col (input logic [NUM_ENTRIES*COL_WIDTH-1:0] v, input logic [PTRW-1:0] e);
        return v[e*COL_WIDTH +: COL_WIDTH];
    endfunction

    // ---- classify each entry into column / activate / precharge -----------
    // Mutually exclusive per entry: an open bank is either on the right row
    // (column) or the wrong row (precharge); a closed bank activates.
    logic [NUM_ENTRIES-1:0] rd_col_m, rd_act_m, rd_pre_m;
    logic [NUM_ENTRIES-1:0] wr_col_m, wr_act_m, wr_pre_m;
    always_comb begin
        rd_col_m = '0; rd_act_m = '0; rd_pre_m = '0;
        wr_col_m = '0; wr_act_m = '0; wr_pre_m = '0;
        for (int e = 0; e < NUM_ENTRIES; e++) begin
            automatic logic [PTRW-1:0]      ei = PTRW'(e);
            automatic logic [BKW-1:0]       rb = f_bank(rd_sch_bank_i, ei);
            automatic logic [BKW-1:0]       wb = f_bank(wr_sch_bank_i, ei);
            automatic logic                 rhit = bank_row_active_i[RK0][rb]
                                                   && (f_row(rd_sch_row_i, ei) == bank_open_row_i[RK0][rb]);
            automatic logic                 whit = bank_row_active_i[RK0][wb]
                                                   && (f_row(wr_sch_row_i, ei) == bank_open_row_i[RK0][wb]);
            // READ entry. The column (RD) commit enqueues into the rd CAM's
            // issue-order FIFO, so it may ONLY fire when that FIFO has room
            // (rd_issue_ready_i) — otherwise the read would issue to DRAM but
            // the CAM would drop it (double-issue + misrouted return). ACT/PRE
            // don't touch the CAM, so they stay free -> the arbiter does other
            // work while the FIFO is full (no bubble).
            if (rd_sch_valid_i[e]) begin
                rd_col_m[e] = rhit && bank_rdwr_ready_i[RK0][rb] && tccd_ok_i && twtr_ok_i
                              && rd_issue_ready_i;
                rd_act_m[e] = !bank_row_active_i[RK0][rb] && !w_guarded[rb]
                              && bank_act_ready_i[RK0][rb] && tfaw_ok_i[RK0] && trrd_ok_i[RK0];
                rd_pre_m[e] = bank_row_active_i[RK0][rb] && !w_guarded[rb] && !rhit
                              && bank_pre_ready_i[RK0][rb];
            end
            // WRITE entry. The column (WR) commit enqueues into the wr CAM's
            // drain FIFO, so gate it on drain-FIFO room (wr_commit_ready_i) —
            // else the write issues to DRAM but its data never drains (stale
            // DRAM) and the slot re-issues. ACT/PRE stay free.
            if (wr_sch_valid_i[e]) begin
                wr_col_m[e] = whit && bank_rdwr_ready_i[RK0][wb] && tccd_ok_i && trtw_ok_i
                              && wr_commit_ready_i;
                wr_act_m[e] = !bank_row_active_i[RK0][wb] && !w_guarded[wb]
                              && bank_act_ready_i[RK0][wb] && tfaw_ok_i[RK0] && trrd_ok_i[RK0];
                wr_pre_m[e] = bank_row_active_i[RK0][wb] && !w_guarded[wb] && !whit
                              && bank_pre_ready_i[RK0][wb];
            end
        end
    end

    // ---- oldest-in-mask via the age-order matrix : returns {found, slot} ----
    // Entry i is the oldest of `mask` iff it is masked AND older than every
    // OTHER masked entry (older[i][j] for all masked j != i). With a total
    // insertion order exactly one entry qualifies -> `is_old` is one-hot. All
    // 1-bit ops (an N-input AND per entry) — no wide age compares.
    function automatic logic [PTRW:0] arg_oldest(
        input logic [NUM_ENTRIES-1:0]              mask,
        input logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  older
    );
        logic                   found;
        logic [PTRW-1:0]        slot;
        logic [NUM_ENTRIES-1:0] is_old;
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            automatic logic [NUM_ENTRIES-1:0] orow = older[i*NUM_ENTRIES +: NUM_ENTRIES];
            automatic logic ge_all = 1'b1;
            for (int j = 0; j < NUM_ENTRIES; j++)
                if ((j != i) && mask[j] && !orow[j]) ge_all = 1'b0;
            is_old[i] = mask[i] && ge_all;
        end
        found = |is_old;
        slot  = '0;
        for (int i = NUM_ENTRIES-1; i >= 0; i--)
            if (is_old[i]) slot = PTRW'(i);
        return {found, slot};
    endfunction

    logic            rd_col_f, wr_col_f, rd_act_f, wr_act_f, rd_pre_f, wr_pre_f;
    logic [PTRW-1:0] rd_col_s, wr_col_s, rd_act_s, wr_act_s, rd_pre_s, wr_pre_s;
    always_comb begin
        {rd_col_f, rd_col_s} = arg_oldest(rd_col_m, rd_sch_older_i);
        {wr_col_f, wr_col_s} = arg_oldest(wr_col_m, wr_sch_older_i);
        {rd_act_f, rd_act_s} = arg_oldest(rd_act_m, rd_sch_older_i);
        {wr_act_f, wr_act_s} = arg_oldest(wr_act_m, wr_sch_older_i);
        {rd_pre_f, rd_pre_s} = arg_oldest(rd_pre_m, rd_sch_older_i);
        {wr_pre_f, wr_pre_s} = arg_oldest(wr_pre_m, wr_sch_older_i);
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
        end else if (rd_col_f) begin
            // 3a. READ row-hit (read-priority).
            w_valid = 1'b1; w_op = w_ap ? OP_RDA : OP_RD;
            w_bank = f_bank(rd_sch_bank_i, rd_col_s); w_col = f_col(rd_sch_col_i, rd_col_s);
            w_ap_out = w_ap; w_do_rd = 1'b1; w_rd_issue = 1'b1; w_issue_slot = rd_col_s;
        end else if (wr_col_f) begin
            // 3b. WRITE row-hit.
            w_valid = 1'b1; w_op = w_ap ? OP_WRA : OP_WR;
            w_bank = f_bank(wr_sch_bank_i, wr_col_s); w_col = f_col(wr_sch_col_i, wr_col_s);
            w_ap_out = w_ap; w_do_wr = 1'b1; w_wr_commit = 1'b1; w_commit_slot = wr_col_s;
        end else if (rd_act_f) begin
            // 4a. ACTIVATE the oldest pending READ's idle bank (bank-parallel).
            w_valid = 1'b1; w_op = OP_ACT;
            w_bank = f_bank(rd_sch_bank_i, rd_act_s); w_row = f_row(rd_sch_row_i, rd_act_s);
            w_do_act = 1'b1;
        end else if (wr_act_f) begin
            // 4b. ACTIVATE the oldest pending WRITE's idle bank.
            w_valid = 1'b1; w_op = OP_ACT;
            w_bank = f_bank(wr_sch_bank_i, wr_act_s); w_row = f_row(wr_sch_row_i, wr_act_s);
            w_do_act = 1'b1;
        end else if (rd_pre_f) begin
            // 5a. PRECHARGE a bank open on the wrong row for a pending read.
            w_valid = 1'b1; w_op = OP_PRE; w_bank = f_bank(rd_sch_bank_i, rd_pre_s);
            w_do_pre = 1'b1;
        end else if (wr_pre_f) begin
            // 5b. PRECHARGE a bank open on the wrong row for a pending write.
            w_valid = 1'b1; w_op = OP_PRE; w_bank = f_bank(wr_sch_bank_i, wr_pre_s);
            w_do_pre = 1'b1;
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

endmodule : pumice_cmd_arbiter
