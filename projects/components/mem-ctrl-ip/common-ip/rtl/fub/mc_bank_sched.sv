// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_bank_sched
// Purpose: per-bank in-order pick core for the scheduler plane (the family
//          design -- see common-ip/docs/mc_scheduler_plane_v2.md). Each
//          (direction, bank) keeps its head entry in a small skid fed by the
//          storage's per-bank head views (oldest + second-oldest); each bank
//          independently decodes its head's next op (ACT / columns / PRE),
//          a round-robin mux selects one ready op per cycle, and a
//          COMBINATIONAL fire stage re-checks the LIVE bank and global timer
//          gates -- the same "final stage is the JEDEC authority" contract
//          as the FRFCFS core, without a shared multi-stage pipeline. A
//          blocked op simply holds in its bank's skid (never dropped, no
//          pipeline to drain), so single-bank throughput is tCCD-bound, not
//          pipeline-depth-bound.
//
//          CLOSE_ON_DRAIN is exact here: a bank's last schedulable entry
//          (store empty flag = one entry in the bank) carries the
//          auto-precharge on its column -- no youngest-same-row heuristic.
//
//          The FRFCFS research core (mc_cmd_arbiter) remains available via
//          the plane's SCHED_CORE parameter; this core is the product
//          scheduler for the family.
//
//          v1 scope notes: generic maintenance requests issue only while all
//          banks are idle (maint_busy_i blocks demand classes, as the FRFCFS
//          core); HAS_ZQ windows are carried for port-shape compatibility.
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_bank_sched
    import mc_common_pkg::*;
#(
    parameter int NUM_RANKS   = 1,
    parameter int NUM_BANKS   = 8,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int AXI_ID_WIDTH = 8,
    parameter int NUM_ENTRIES = 16,
    parameter bit HAS_ZQ      = 1'b0,
    parameter bit CLOSE_ON_DRAIN = 1'b1,
    parameter int MAINT_EXTRA_WIDTH = 1,

    parameter int RKW  = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int PTRW = (NUM_ENTRIES > 1) ? $clog2(NUM_ENTRIES) : 1,
    parameter int IW   = AXI_ID_WIDTH
) (
    input  logic                      aclk,
    input  logic                      aresetn,
    input  page_policy_e              page_policy_i,

    // ---- storage per-bank head views (mc_xddr2_entry_store) ---------------
    input  logic [NUM_BANKS-1:0]      wr_bh_valid_i,
    input  logic [NUM_BANKS*PTRW-1:0] wr_bh_slot_i,
    input  logic [NUM_BANKS*ROW_WIDTH-1:0] wr_bh_row_i,
    input  logic [NUM_BANKS*COL_WIDTH-1:0] wr_bh_col_i,
    input  logic [NUM_BANKS*IW-1:0]   wr_bh_id_i,
    input  logic [NUM_BANKS-1:0]      wr_bh_last_i,
    input  logic [NUM_BANKS-1:0]      wr_bh_empty_i,
    input  logic [NUM_BANKS-1:0]      wr_bh_act_i,
    input  logic [NUM_BANKS*6-1:0]    wr_bh_age_i,
    input  logic [NUM_BANKS-1:0]      rd_bh_valid_i,
    input  logic [NUM_BANKS*PTRW-1:0] rd_bh_slot_i,
    input  logic [NUM_BANKS*ROW_WIDTH-1:0] rd_bh_row_i,
    input  logic [NUM_BANKS*COL_WIDTH-1:0] rd_bh_col_i,
    input  logic [NUM_BANKS*IW-1:0]   rd_bh_id_i,
    input  logic [NUM_BANKS-1:0]      rd_bh_empty_i,
    input  logic [NUM_BANKS-1:0]      rd_bh_act_i,
    input  logic [NUM_BANKS*6-1:0]    rd_bh_age_i,
    input  logic [NUM_BANKS-1:0]      wr_bh2_valid_i,
    input  logic [NUM_BANKS*PTRW-1:0] wr_bh2_slot_i,
    input  logic [NUM_BANKS*ROW_WIDTH-1:0] wr_bh2_row_i,
    input  logic [NUM_BANKS*COL_WIDTH-1:0] wr_bh2_col_i,
    input  logic [NUM_BANKS*IW-1:0]   wr_bh2_id_i,
    input  logic [NUM_BANKS-1:0]      wr_bh2_last_i,
    input  logic [NUM_BANKS-1:0]      wr_bh2_act_i,
    input  logic [NUM_BANKS*6-1:0]    wr_bh2_age_i,
    input  logic [NUM_BANKS-1:0]      rd_bh2_valid_i,
    input  logic [NUM_BANKS*PTRW-1:0] rd_bh2_slot_i,
    input  logic [NUM_BANKS*ROW_WIDTH-1:0] rd_bh2_row_i,
    input  logic [NUM_BANKS*COL_WIDTH-1:0] rd_bh2_col_i,
    input  logic [NUM_BANKS*IW-1:0]   rd_bh2_id_i,
    input  logic [NUM_BANKS-1:0]      rd_bh2_act_i,
    input  logic [NUM_BANKS*6-1:0]    rd_bh2_age_i,

    // ---- storage commit / issue handshake (same contract as the FRFCFS core)
    input  logic                      wr_commit_ready_i,
    output logic                      wr_commit_valid_o,
    output logic [PTRW-1:0]           wr_commit_slot_o,
    input  logic                      rd_issue_ready_i,
    output logic                      rd_issue_valid_o,
    output logic [PTRW-1:0]           rd_issue_slot_o,
    output logic                      sched_decr_o,

    // ---- init passthrough ----
    input  logic                      init_done_i,
    input  logic                      init_cmd_valid_i,
    input  dram_op_e                  init_cmd_op_i,
    input  logic [BKW-1:0]            init_cmd_bank_i,
    input  logic [ROW_WIDTH-1:0]      init_cmd_row_i,

    // ---- refresh ----
    input  logic                      refresh_req_i,
    input  logic                      refresh_drain_i,
    input  logic                      refresh_kind_i,
    input  logic [BKW-1:0]            refresh_bank_i,
    output logic                      refresh_grant_o,
    input  logic [15:0]               t_rfc_i,
    input  logic [7:0]                t_rfc_pb_i,

    // ---- read-return busy from DFI plane (keeps REF out of open return window)
    input  logic                      rd_ret_busy_i,

    // ---- ZQ (present when HAS_ZQ=1; granite ties off) ----
    input  logic                      zq_req_i,
    output logic                      zq_grant_o,
    input  logic [15:0]               t_zqcs_i,

    // ---- generic maintenance ----
    input  logic                      maint_req_i,
    output logic                      maint_grant_o,
    input  dram_op_e                  maint_op_i,
    input  logic [BKW-1:0]            maint_bank_i,
    input  logic [ROW_WIDTH-1:0]      maint_row_i,
    input  logic [COL_WIDTH-1:0]      maint_col_i,
    input  logic [MAINT_EXTRA_WIDTH-1:0] maint_extra_i,
    input  logic                      maint_busy_i,

    // ---- per-bank readiness (registered image; the FIRE re-checks live) ---
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_act_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_rdwr_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_pre_ready_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_act_ready_la_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_rdwr_ready_la_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_pre_ready_la_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                 bank_row_active_i,
    input  logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0]  bank_open_row_i,

    // ---- global readiness ----
    input  logic [NUM_RANKS-1:0]      tfaw_ok_i,
    input  logic [NUM_RANKS-1:0]      trrd_ok_i,
    input  logic                      twtr_ok_i,
    input  logic                      trtw_ok_i,
    // Raw tCCD CSR value for the FORWARD column-spacing counter: the flopped
    // tccd_ok_i window carries a built-in +1 lag (see "ONE NEXT-STATE
    // FUNCTION, TWO FLOPS" in mc_global_timers.sv), which a 0-stage
    // pick==fire core eats as real spacing -- tCCD=1 became 2-cycle gaps and
    // halved single-bank streaming bandwidth (MC-003 2026-10-17: row_major
    // 289 vs 568 MB/s, uniform gap-2 histogram, zero ACTs). The FRFCFS core
    // gates on its own r_tccd_fwd forward counter instead; this core mirrors
    // that accounting exactly (spacing = tCCD for tCCD > 1, full rate for
    // tCCD <= 1 -- the board- and model-validated semantics).
    input  logic [7:0]                t_ccd_i,

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
    output logic                      cmd_ap_o,
    output logic [MAINT_EXTRA_WIDTH-1:0] cmd_extra_o,

    // ---- stall-cause attribution ----
    output logic [31:0]               stall_bp_o,
    output logic [31:0]               stall_refresh_o,
    output logic [31:0]               stall_turnaround_o,
    output logic [31:0]               stall_tccd_o,
    output logic [31:0]               stall_actlimit_o,
    output logic [31:0]               stall_banktimer_o,
    output logic [31:0]               stall_noreq_o,
    output logic [31:0]               stall_zq_o
);

    localparam int RK0   = 0;
    localparam int NPAIR = 2*NUM_BANKS;
    localparam int PAIRW = (NPAIR > 1) ? $clog2(NPAIR) : 1;

    // ======================================================================
    // Registered bank-timer image (advisory decode; the fire stage re-checks
    // the LIVE inputs, so this stage cannot violate JEDEC).
    // ======================================================================
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                r_act_rdy, r_rdwr_rdy, r_pre_rdy, r_row_act;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0] r_open_row;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_act_rdy <= '0; r_rdwr_rdy <= '0; r_pre_rdy <= '0;
            r_row_act <= '0; r_open_row <= '0;
        end else begin
            r_act_rdy  <= bank_act_ready_la_i;
            r_rdwr_rdy <= bank_rdwr_ready_la_i;
            r_pre_rdy  <= bank_pre_ready_la_i;
            r_row_act  <= bank_row_active_i;
            r_open_row <= bank_open_row_i;
        end
    )

    // ======================================================================
    // tRFC / tZQCS recovery counters (all-banks-idle gate inputs)
    // ======================================================================
    logic [15:0] r_rfc_cnt, r_zqcs_cnt;
    logic        w_rfc_busy, w_zq_busy;
    assign w_rfc_busy = (r_rfc_cnt  != 16'd0);
    assign w_zq_busy  = (r_zqcs_cnt != 16'd0);

    // Refresh-episode demand block — the FRFCFS core's w_ref_col_block
    // (mc_cmd_arbiter.sv), extended from columns to ALL demand classes.
    // While a refresh is requested or draining, demand ops to the affected
    // bank(s) must not fire: a column launched into the refresh window
    // returns data the aligner mis-captures and the AR-order return ring
    // wedges behind the lost beat (MC-003 2026-10-15: READ ENGINE HANG +
    // mismatched beats under tight tREFI; the FRFCFS core has always blocked
    // these). REFab blocks all banks; REFpb blocks only the target bank.
    //
    // ACT/PRE are blocked too, not just columns (MC-003 2026-10-17, the
    // tREFI=100 corner): the drain closes every active bank and grants REF
    // from the rows-closed image, but in the gap cycles where the override
    // holds no op (REF deferred by the read-return window, w_ref_safe low)
    // a demand ACT still fired. It entered the command FIFO AHEAD of the
    // deferred REF, the REF closed the bank at the model, and the RTL row
    // state stayed open (REF sends no row-clear to the bank timers):
    // post-tRFC columns fired into a model-closed bank (row-0 fallback
    // data, no_act_before_rd), with duplicate ACTs as the downstream
    // fallout. Pending heads simply wait out the tRFC in their skids —
    // no deadlock: the all-idle grant does not depend on demand firing
    // (the 2026-10-15 all-idle ruling carries; the override still owns the
    // episode: drain PREs and the REF itself are override ops).
    logic [NUM_BANKS-1:0] w_ref_dmd_block;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++)
            w_ref_dmd_block[b] = (refresh_req_i || refresh_drain_i)
                              && (!refresh_kind_i || (BKW'(b) == refresh_bank_i));
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))      r_rfc_cnt <= '0;
        else if (refresh_grant_o)
            r_rfc_cnt <= (cmd_op_o == OP_REFPB && t_rfc_pb_i != 8'd0)
                         ? {8'h0, t_rfc_pb_i} : t_rfc_i;
        else if (w_rfc_busy)             r_rfc_cnt <= r_rfc_cnt - 16'd1;
    )

    // tRFC window demand block (the per-bank core half of the fix; the other
    // half is w_ref_dmd_block above). The granted refresh closes the affected
    // bank(s) at the DEVICE, but the bank timers keep serving their rows
    // (row state is only cleared by PRE/AP -- REF sends no row-clear), so a
    // demand column decoded against an "open" row image fires into a
    // refreshing/closed bank at the model (row-0 fallback data,
    // cmd_during_refresh, MC-003 2026-10-17 tREFI=100: 1527 model violations,
    // 24 corrupted beats; cycle-cited: ACT 1 cyc before REFab, RD 2 cyc after
    // into a closed bank). The FRFCFS core avoids this only structurally (its
    // all-idle grant leaves every row closed, so safe_rd self-blocks); the
    // per-bank core must close the same hole explicitly because a slipped ACT
    // (previously) could open a row inside the window. REFab blocks all banks;
    // REFpb blocks only the target -- other banks stay accessible per-bank
    // refresh's whole point (parity with the FRFCFS core's behavior there).
    logic r_rfc_ab;
    logic [BKW-1:0] r_rfc_bank;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rfc_ab    <= 1'b1;
            r_rfc_bank  <= '0;
        end else if (refresh_grant_o) begin
            r_rfc_ab   <= (cmd_op_o == OP_REF);
            r_rfc_bank <= refresh_bank_i;
        end
    )
    logic [NUM_BANKS-1:0] w_rfc_dmd_block;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++)
            w_rfc_dmd_block[b] = w_rfc_busy
                              && (r_rfc_ab || (BKW'(b) == r_rfc_bank));
    end
    generate if (HAS_ZQ) begin : g_zq
        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn))  r_zqcs_cnt <= '0;
            else if (zq_grant_o)         r_zqcs_cnt <= t_zqcs_i;
            else if (w_zq_busy)          r_zqcs_cnt <= r_zqcs_cnt - 16'd1;
        )
    end else begin : g_no_zq
        `ALWAYS_FF_RST(aclk, aresetn,
            if (`RST_ASSERTED(aresetn))  r_zqcs_cnt <= '0;
        )
    end endgenerate

    // ======================================================================
    // Aged matrix-arbiter pick core.  The store keeps one age-ordered fifo per
    // (direction,bank); this core sees only the head/head2 views plus the
    // enqueue-time act tag and 6-bit age.  A 16-requester matrix arbiter picks
    // among the entries whose decoded op is non-NOP and whose presented age
    // equals the global minimum; the winner registers, is re-checked against
    // the LIVE JEDEC gates, and fires combinationally.  Head2 is pre-picked
    // for the pair whose registered winner fires this cycle so back-to-back
    // same-bank columns run at one command per cycle.
    // ======================================================================
    typedef struct packed {
        logic                 vld;
        logic [PTRW-1:0]      slot;
        logic [ROW_WIDTH-1:0] row;
        logic [COL_WIDTH-1:0] col;
        logic [IW-1:0]        id;
        logic                 last;
    } head_t;

    function automatic head_t wr_cand(input int b);
        head_t h;
        h.vld  = wr_bh_valid_i[b];
        h.slot = wr_bh_slot_i[b*PTRW +: PTRW];
        h.row  = wr_bh_row_i [b*ROW_WIDTH +: ROW_WIDTH];
        h.col  = wr_bh_col_i [b*COL_WIDTH +: COL_WIDTH];
        h.id   = wr_bh_id_i  [b*IW +: IW];
        h.last = wr_bh_last_i[b];
        return h;
    endfunction
    function automatic head_t rd_cand(input int b);
        head_t h;
        h.vld  = rd_bh_valid_i[b];
        h.slot = rd_bh_slot_i[b*PTRW +: PTRW];
        h.row  = rd_bh_row_i [b*ROW_WIDTH +: ROW_WIDTH];
        h.col  = rd_bh_col_i [b*COL_WIDTH +: COL_WIDTH];
        h.id   = rd_bh_id_i  [b*IW +: IW];
        h.last = 1'b0;
        return h;
    endfunction
    function automatic head_t wr_cand2(input int b);
        head_t h;
        h.vld  = wr_bh2_valid_i[b];
        h.slot = wr_bh2_slot_i[b*PTRW +: PTRW];
        h.row  = wr_bh2_row_i [b*ROW_WIDTH +: ROW_WIDTH];
        h.col  = wr_bh2_col_i [b*COL_WIDTH +: COL_WIDTH];
        h.id   = wr_bh2_id_i  [b*IW +: IW];
        h.last = wr_bh2_last_i[b];
        return h;
    endfunction
    function automatic head_t rd_cand2(input int b);
        head_t h;
        h.vld  = rd_bh2_valid_i[b];
        h.slot = rd_bh2_slot_i[b*PTRW +: PTRW];
        h.row  = rd_bh2_row_i [b*ROW_WIDTH +: ROW_WIDTH];
        h.col  = rd_bh2_col_i [b*COL_WIDTH +: COL_WIDTH];
        h.id   = rd_bh2_id_i  [b*IW +: IW];
        h.last = 1'b0;
        return h;
    endfunction

    // Per-bank op decode on the LIVE timer outputs.  The request mask uses the
    // presented candidate (head or head2) for each pair, so both are decoded.
    dram_op_e w_op  [NUM_BANKS];
    dram_op_e r_op  [NUM_BANKS];
    dram_op_e w_op2 [NUM_BANKS];
    dram_op_e r_op2 [NUM_BANKS];
    logic     w_ap  [NUM_BANKS];
    logic     r_ap  [NUM_BANKS];
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            automatic head_t wc  = wr_cand(b);
            automatic head_t rc  = rd_cand(b);
            automatic head_t wc2 = wr_cand2(b);
            automatic head_t rc2 = rd_cand2(b);
            w_op[b]  = OP_NOP;
            r_op[b]  = OP_NOP;
            w_op2[b] = OP_NOP;
            r_op2[b] = OP_NOP;
            if (wc.vld) begin
                if (bank_row_active_i[RK0][b]
                    && (bank_open_row_i[RK0][b] == wc.row)
                    && bank_rdwr_ready_i[RK0][b]) begin
                    w_op[b] = OP_WR;
                end else if (bank_row_active_i[RK0][b]
                             && bank_pre_ready_i[RK0][b]) begin
                    w_op[b] = OP_PRE;
                end else if (!bank_row_active_i[RK0][b]
                             && bank_act_ready_i[RK0][b]) begin
                    w_op[b] = OP_ACT;
                end
            end
            if (wc2.vld) begin
                if (bank_row_active_i[RK0][b]
                    && (bank_open_row_i[RK0][b] == wc2.row)
                    && bank_rdwr_ready_i[RK0][b]) begin
                    w_op2[b] = OP_WR;
                end else if (bank_row_active_i[RK0][b]
                             && bank_pre_ready_i[RK0][b]) begin
                    w_op2[b] = OP_PRE;
                end else if (!bank_row_active_i[RK0][b]
                             && bank_act_ready_i[RK0][b]) begin
                    w_op2[b] = OP_ACT;
                end
            end
            if (rc.vld) begin
                if (bank_row_active_i[RK0][b]
                    && (bank_open_row_i[RK0][b] == rc.row)
                    && bank_rdwr_ready_i[RK0][b]) begin
                    r_op[b] = OP_RD;
                end else if (bank_row_active_i[RK0][b]
                             && bank_pre_ready_i[RK0][b]) begin
                    r_op[b] = OP_PRE;
                end else if (!bank_row_active_i[RK0][b]
                             && bank_act_ready_i[RK0][b]) begin
                    r_op[b] = OP_ACT;
                end
            end
            if (rc2.vld) begin
                if (bank_row_active_i[RK0][b]
                    && (bank_open_row_i[RK0][b] == rc2.row)
                    && bank_rdwr_ready_i[RK0][b]) begin
                    r_op2[b] = OP_RD;
                end else if (bank_row_active_i[RK0][b]
                             && bank_pre_ready_i[RK0][b]) begin
                    r_op2[b] = OP_PRE;
                end else if (!bank_row_active_i[RK0][b]
                             && bank_act_ready_i[RK0][b]) begin
                    r_op2[b] = OP_ACT;
                end
            end
            w_ap[b] = (page_policy_i == PAGE_POLICY_CLOSE)
                   || (CLOSE_ON_DRAIN && wr_bh_empty_i[b]);
            r_ap[b] = (page_policy_i == PAGE_POLICY_CLOSE)
                   || (CLOSE_ON_DRAIN && rd_bh_empty_i[b]);
        end
    end

    // ======================================================================
    // Maintenance override: init passthrough; refresh (per-bank drain PREs,
    // then grant when all idle); generic maintenance when all idle. Same
    // all-banks-idle safety contracts as the FRFCFS core.
    // ======================================================================
    // Registered demand winner (matrix-arbiter grant held for fire-check).
    typedef struct packed {
        logic                 vld;
        logic                 is_rd;
        logic [BKW-1:0]       bank;
        dram_op_e             op;
        logic [PTRW-1:0]      slot;
        logic [ROW_WIDTH-1:0] row;
        logic [COL_WIDTH-1:0] col;
        logic [IW-1:0]        id;
        logic                 last;
        logic                 ap;
    } winner_t;

    winner_t r_winner;

    logic any_head_vld;
    always_comb begin
        any_head_vld = r_winner.vld;
        for (int b = 0; b < NUM_BANKS; b++)
            if (wr_bh_valid_i[b] || rd_bh_valid_i[b]) any_head_vld = 1'b1;
    end

    logic w_any_active, w_rfsh_pre_found;
    logic [BKW-1:0] w_rfsh_pre_bank;
    always_comb begin
        w_any_active     = |r_row_act[RK0];
        w_rfsh_pre_found = 1'b0;
        w_rfsh_pre_bank  = '0;
        for (int j = NUM_BANKS-1; j >= 0; j--)
            if (r_row_act[RK0][j] && r_pre_rdy[RK0][j]) begin
                w_rfsh_pre_found = 1'b1;
                w_rfsh_pre_bank  = BKW'(j);
            end
    end

    // Read-return window tracking. The DFI-side rd_aligner derives rd_last
    // from a modulo word counter (r_rcnt == BL_WORDS-1) with NO resync: if a
    // REF fires while a read's return window is open, the clipped return
    // shortens the count, rd_last reframes onto the wrong word, and every
    // later read lands mis-framed in the return ring (MC-003 2026-10-15: a
    // couple of mismatched beats + the final txn's RLAST never firing = read-
    // engine hang; the per-bank core hits the read-in-flight-across-REF window
    // every refresh boundary because its decode-to-fire path is 0-cycle, where
    // the FRFCFS 5-stage pipe almost never does). So the controller must never
    // grant REF into an open return window.
    //
    // The DFI plane supplies rd_ret_busy_i = (aligner r_outstanding != 0), true
    // from the first read admitted by the aligner until the last burst word is
    // captured. That is exact for the return window, but a read issued by this
    // scheduler takes several cycles to reach the aligner (command FIFO + DFI
    // cmd path). To cover that scheduler-to-DFI pipeline, arm a local
    // aclk-domain flag on rd_issue_valid_o and hold it until rd_ret_busy_i has
    // been low for at least one cycle. The combined w_rdret_busy therefore stays
    // asserted from scheduler issue through aligner completion, preventing REF
    // from clipping either the in-flight command or the returning data.
    //
    // JEDEC-wise this is refresh postponement (tREFI is a maximum; the refresh
    // controller's own postpone/pending credits are the upstream bound against
    // starvation).
    logic r_rd_pipe_busy;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))            r_rd_pipe_busy <= 1'b0;
        else if (rd_issue_valid_o)             r_rd_pipe_busy <= 1'b1;
        else if (!rd_ret_busy_i)               r_rd_pipe_busy <= 1'b0;
    )
    logic w_rdret_busy;
    assign w_rdret_busy = r_rd_pipe_busy || rd_ret_busy_i;

    // Demand-ACT fire history. The registered row-active image (r_row_act)
    // lags one cycle behind a demand ACT fire, so a refresh request asserting
    // in that window used to grant REFab with a bank actually ACTIVE at the
    // model: ACT@X, REF@X+1, the bank closed at the model while the RTL image
    // still showed it open, and the squeezed-through head's columns fired
    // post-tRFC into the closed bank (row-0 fallback -> one miswritten burst
    // per episode plus a clobbered row 0; 72 beats at col_major txn=256,
    // MC-003 2026-10-17). Same fire-history shape as r_wrfire0/r_rdfire0.
    logic           r_actfire0;
    logic [BKW-1:0] r_actfire0_bank;

    // All-idle gates for the override grants. Rows closed (+ recovery windows)
    // is the JEDEC requirement and matches the FRFCFS core's w_ref_safe /
    // w_maint_safe exactly: PENDING DEMAND DOES NOT BLOCK REFRESH. A pending
    // head here would deadlock -- the override has priority, so a head that
    // cannot fire while the override is active (e.g. its column gated)
    // holds any_head_vld forever and REFab can never grant (found on the A7:
    // engines hung from the first scenario under the real tREFI=585,
    // 2026-10-15). The pending entries simply wait out the tRFC.
    //
    // w_rdret_busy additionally holds REF out of the open read-return window
    // (see above) -- its own slip would reframe the aligner's last framing.
    logic w_ref_safe, w_refpb_safe, w_maint_safe;
    assign w_ref_safe   = !w_any_active && !r_actfire0
                       && !w_rfc_busy && !w_rdret_busy;
    assign w_refpb_safe = !r_row_act[RK0][refresh_bank_i] && !w_rfc_busy && !w_rdret_busy
                       && !(r_actfire0 && (r_actfire0_bank == refresh_bank_i));
    assign w_maint_safe = !w_any_active && !w_rfc_busy && !w_zq_busy && !maint_busy_i;

    logic        w_ovr_vld;
    dram_op_e    w_ovr_op;
    logic [BKW-1:0] w_ovr_bank;
    logic [ROW_WIDTH-1:0] w_ovr_row;
    logic [COL_WIDTH-1:0] w_ovr_col;
    always_comb begin
        w_ovr_vld  = 1'b0;
        w_ovr_op   = OP_NOP;
        w_ovr_bank = '0;
        w_ovr_row  = '0;
        w_ovr_col  = '0;
        if (!init_done_i) begin
            if (init_cmd_valid_i) begin
                w_ovr_vld  = 1'b1;
                w_ovr_op   = init_cmd_op_i;
                w_ovr_bank = init_cmd_bank_i;
                w_ovr_row  = init_cmd_row_i;
            end
        end else if (refresh_req_i || refresh_drain_i) begin
            if (refresh_kind_i) begin
                if (r_row_act[RK0][refresh_bank_i]) begin
                    if (r_pre_rdy[RK0][refresh_bank_i]) begin
                        w_ovr_vld  = 1'b1;
                        w_ovr_op   = OP_PRE;
                        w_ovr_bank = refresh_bank_i;
                    end
                end else if (w_refpb_safe) begin
                    w_ovr_vld  = 1'b1;
                    w_ovr_op   = OP_REFPB;
                    w_ovr_bank = refresh_bank_i;
                end
            end else if (w_any_active) begin
                if (w_rfsh_pre_found) begin
                    w_ovr_vld  = 1'b1;
                    w_ovr_op   = OP_PRE;
                    w_ovr_bank = w_rfsh_pre_bank;
                end
            end else if (w_ref_safe) begin
                w_ovr_vld = 1'b1;
                w_ovr_op  = OP_REF;
            end
        end else if (HAS_ZQ && zq_req_i && w_maint_safe) begin
            w_ovr_vld = 1'b1;
            w_ovr_op  = OP_ZQCS;
        end else if (maint_req_i && w_maint_safe) begin
            w_ovr_vld  = 1'b1;
            w_ovr_op   = maint_op_i;
            w_ovr_bank = maint_bank_i;
            w_ovr_row  = maint_row_i;
            w_ovr_col  = maint_col_i;
        end
    end

    // ======================================================================
    // Aged matrix-arbiter request mask.  Each (dir,bank) pair presents the
    // head normally; the pair whose registered winner is firing this cycle
    // presents head2 instead, so the reserve becomes visible one cycle early.
    // Requests are valid op + age==global-minimum.  The matrix grants exactly
    // one requester (round-robin fairness via pairwise state); the grant is
    // consumed on demand fire.
    // ======================================================================
    localparam int AGEW = 6;

    // Forward declaration — assigned at the fire logic below; the head2
    // pre-pick mux (declare-before-use) consumes it.
    logic             w_demand_fire;

    logic [NPAIR-1:0] w_use_head2;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            w_use_head2[2*b]   = w_demand_fire && r_winner.is_rd
                              && (r_winner.bank == BKW'(b));
            w_use_head2[2*b+1] = w_demand_fire && !r_winner.is_rd
                              && (r_winner.bank == BKW'(b));
        end
    end

    logic [AGEW-1:0] w_pres_age [NPAIR];
    logic            w_pres_vld [NPAIR];
    dram_op_e        w_pres_op  [NPAIR];
    head_t           w_pres_head [NPAIR];
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            // RD pair = 2*b
            w_pres_age[2*b]   = w_use_head2[2*b] ? rd_bh2_age_i[b*AGEW +: AGEW]
                                                 : rd_bh_age_i [b*AGEW +: AGEW];
            w_pres_vld[2*b]   = w_use_head2[2*b] ? rd_bh2_valid_i[b]
                                                 : rd_bh_valid_i[b];
            w_pres_op [2*b]   = w_use_head2[2*b] ? r_op2[b] : r_op[b];
            w_pres_head[2*b]  = w_use_head2[2*b] ? rd_cand2(b) : rd_cand(b);
            // WR pair = 2*b+1
            w_pres_age[2*b+1] = w_use_head2[2*b+1] ? wr_bh2_age_i[b*AGEW +: AGEW]
                                                   : wr_bh_age_i [b*AGEW +: AGEW];
            w_pres_vld[2*b+1] = w_use_head2[2*b+1] ? wr_bh2_valid_i[b]
                                                   : wr_bh_valid_i[b];
            w_pres_op [2*b+1] = w_use_head2[2*b+1] ? w_op2[b] : w_op[b];
            w_pres_head[2*b+1]= w_use_head2[2*b+1] ? wr_cand2(b) : wr_cand(b);
        end
    end

    logic [AGEW-1:0] w_min_age;
    always_comb begin
        w_min_age = '1;
        for (int p = 0; p < NPAIR; p++)
            if (w_pres_vld[p] && (w_pres_op[p] != OP_NOP)
                && (w_pres_age[p] < w_min_age))
                w_min_age = w_pres_age[p];
    end

    logic [NPAIR-1:0] w_req;
    always_comb begin
        for (int p = 0; p < NPAIR; p++)
            w_req[p] = w_pres_vld[p] && (w_pres_op[p] != OP_NOP)
                    && (w_pres_age[p] == w_min_age);
    end

    logic [NPAIR-1:0] w_gnt;
    mc_matrix_arbiter #(.N(NPAIR)) u_matrix (
        .aclk  (aclk),
        .aresetn(aresetn),
        .req_i (w_req),
        .gnt_o (w_gnt),
        .upd_i (w_demand_fire)
    );

    logic [PAIRW-1:0] w_pick_pair;
    logic             w_pick_vld;
    always_comb begin
        w_pick_vld  = 1'b0;
        w_pick_pair = '0;
        for (int p = 0; p < NPAIR; p++)
            if (w_gnt[p]) begin
                w_pick_vld  = 1'b1;
                w_pick_pair = PAIRW'(p);
            end
    end

    // ======================================================================
    // Live fire-stage authority. The registered winner is re-checked against
    // the LIVE timer outputs and the command FIFO; a failing gate does not
    // fire and the winner simply holds.  No drop, no pipeline drain.
    // ======================================================================
    logic r_wrfire0, r_rdfire0;
    logic w_rd_turn_block, w_wr_turn_block;
    assign w_rd_turn_block = r_wrfire0;
    assign w_wr_turn_block = r_rdfire0;

    logic [BKW-1:0]  w_sel_bank;
    logic            w_sel_is_rd;
    dram_op_e        w_sel_op;
    head_t           w_sel_head;
    always_comb begin
        w_sel_bank  = BKW'(w_pick_pair >> 1);
        w_sel_is_rd = ~w_pick_pair[0];
        w_sel_op    = w_pres_op[w_pick_pair];
        w_sel_head  = w_pres_head[w_pick_pair];
    end

    // Winner-stale detect — the store's live head view for this pair no
    // longer matches the slot+row that was captured when the winner registered.
    // The winner also goes stale on an override request, which owns the cycle.
    logic winner_stale;
    always_comb begin
        winner_stale = 1'b0;
        if (r_winner.vld) begin
            automatic logic [PTRW-1:0] cur_slot;
            automatic logic [ROW_WIDTH-1:0] cur_row;
            automatic logic cur_vld;
            if (r_winner.is_rd) begin
                cur_vld  = rd_bh_valid_i[r_winner.bank];
                cur_slot = rd_bh_slot_i[r_winner.bank*PTRW +: PTRW];
                cur_row  = rd_bh_row_i [r_winner.bank*ROW_WIDTH +: ROW_WIDTH];
            end else begin
                cur_vld  = wr_bh_valid_i[r_winner.bank];
                cur_slot = wr_bh_slot_i[r_winner.bank*PTRW +: PTRW];
                cur_row  = wr_bh_row_i [r_winner.bank*ROW_WIDTH +: ROW_WIDTH];
            end
            winner_stale = !cur_vld
                        || (cur_slot != r_winner.slot)
                        || (cur_row  != r_winner.row)
                        || w_ovr_vld;
            if (!winner_stale) begin
                automatic dram_op_e redec = r_winner.is_rd ? r_op[r_winner.bank]
                                                           : w_op[r_winner.bank];
                winner_stale = (redec != r_winner.op);
            end
        end
    end

    // Declared ahead of the forward tCCD counter (which keys w_col_fire_now
    // off w_fire/w_fis_col) and the matrix arbiter update; assigned below.
    logic        w_fis_col, w_fis_act, w_fis_pre;
    logic        w_fsafe;
    logic        w_fire;

    // FORWARD tCCD counter (column spacing at fire time). Replaces the raw
    // tccd_ok_i window in the column gate — that output is a flopped
    // next-state whose +1 lag doubles as real spacing for this 0-stage core
    // (tCCD=1 -> 2-cycle gaps -> half-rate single-bank streaming, MC-003
    // 2026-10-17). Accounting mirrors the FRFCFS core's r_tccd_fwd
    // (mc_cmd_arbiter.sv): load tCCD-1 on a demand column fire (so tCCD<=1
    // reloads to 0 = full rate; tCCD=N>1 enforces N-cycle spacing), free-run
    // down to 0, gate the next column on r_tccd_fwd==0. A demand RD and WR
    // in consecutive cycles are spaced by the direction turnarounds
    // (tWTR/tRTW + the 1-deep fire history), not by this counter — same as
    // the FRFCFS core, where w_col_sel_now also counts both directions and
    // the turnarounds cover the mix.
    logic [7:0] r_tccd_fwd;
    logic       w_col_fire_now, w_tccd_fwd_ok;
    assign w_col_fire_now = w_fire && !w_ovr_vld && w_fis_col;
    assign w_tccd_fwd_ok  = (r_tccd_fwd == 8'd0);
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))  r_tccd_fwd <= 8'd0;
        else if (w_col_fire_now)
            r_tccd_fwd <= (t_ccd_i > 8'd1) ? (t_ccd_i - 8'd1) : 8'd0;
        else if (r_tccd_fwd != 8'd0) r_tccd_fwd <= r_tccd_fwd - 8'd1;
    )

    always_comb begin
        w_fis_col = is_column_op(r_winner.op);
        w_fis_act = (r_winner.op == OP_ACT);
        w_fis_pre = (r_winner.op == OP_PRE);
        w_fsafe   = 1'b1;
        if (w_ovr_vld) begin
            // override ops carry their own all-banks-idle / drain predicates
            // (decoded on the registered image, as the FRFCFS core does);
            // drain PREs re-check the live pre gate.
            if (w_ovr_op == OP_PRE)
                w_fsafe = bank_pre_ready_i[RK0][w_ovr_bank];
        end else if (r_winner.vld && !winner_stale) begin
            if (w_fis_act)
                w_fsafe = bank_act_ready_i[RK0][r_winner.bank] && tfaw_ok_i[RK0]
                          && trrd_ok_i[RK0] && !w_rfc_busy && !maint_busy_i
                          && !w_ref_dmd_block[r_winner.bank];
            else if (w_fis_col)
                w_fsafe = bank_rdwr_ready_i[RK0][r_winner.bank] && w_tccd_fwd_ok
                          && (r_winner.is_rd ? (twtr_ok_i && !w_rd_turn_block)
                                             : (trtw_ok_i && !w_wr_turn_block))
                          && !w_ref_dmd_block[r_winner.bank]
                          && !w_rfc_dmd_block[r_winner.bank]
                          && (r_winner.is_rd ? rd_issue_ready_i
                                             : wr_commit_ready_i);
            else if (w_fis_pre)
                w_fsafe = bank_pre_ready_i[RK0][r_winner.bank]
                          && !w_ref_dmd_block[r_winner.bank]
                          && !w_rfc_dmd_block[r_winner.bank];
        end
    end

    assign w_demand_fire = r_winner.vld && !w_ovr_vld && !winner_stale
                           && w_fsafe && cmd_ready_i;
    assign w_fire        = (w_ovr_vld && w_fsafe && cmd_ready_i) || w_demand_fire;
    assign cmd_valid_o   = w_fire;

    // AP is recomputed from the live empty flag at fire time (CLOSE_ON_DRAIN).
    logic w_live_ap;
    always_comb begin
        w_live_ap = (page_policy_i == PAGE_POLICY_CLOSE)
                 || (CLOSE_ON_DRAIN
                     && (r_winner.is_rd ? rd_bh_empty_i[r_winner.bank]
                                        : wr_bh_empty_i[r_winner.bank]));
    end

    always_comb begin
        cmd_op_o    = OP_NOP;
        cmd_bank_o  = '0;
        cmd_row_o   = '0;
        cmd_col_o   = '0;
        cmd_ap_o    = 1'b0;
        cmd_extra_o = '0;
        if (w_ovr_vld) begin
            cmd_op_o    = w_ovr_op;
            cmd_bank_o  = w_ovr_bank;
            cmd_row_o   = w_ovr_row;
            cmd_col_o   = w_ovr_col;
            cmd_extra_o = maint_extra_i;
        end else if (r_winner.vld && !winner_stale) begin
            cmd_bank_o = r_winner.bank;
            cmd_row_o  = r_winner.row;
            cmd_col_o  = r_winner.col;
            if (w_fis_act) begin
                cmd_op_o = OP_ACT;
            end else if (w_fis_pre) begin
                cmd_op_o = OP_PRE;
            end else begin
                cmd_ap_o = w_live_ap;
                cmd_op_o = r_winner.is_rd ? (cmd_ap_o ? OP_RDA : OP_RD)
                                          : (cmd_ap_o ? OP_WRA : OP_WR);
            end
        end
    end
    assign cmd_rank_o = RKW'(RK0);

    // ==================================================================
    // Strobes: storage handshake, grants, timer events, fire history
    // ==================================================================
    assign wr_commit_valid_o = w_demand_fire && w_fis_col && !r_winner.is_rd;
    assign wr_commit_slot_o  = r_winner.slot;
    assign rd_issue_valid_o  = w_demand_fire && w_fis_col &&  r_winner.is_rd;
    assign rd_issue_slot_o   = r_winner.slot;
    assign sched_decr_o      = w_fire;

    assign refresh_grant_o = w_fire && w_ovr_vld
                          && ((w_ovr_op == OP_REF) || (w_ovr_op == OP_REFPB));
    assign zq_grant_o      = w_fire && w_ovr_vld && (w_ovr_op == OP_ZQCS);
    assign maint_grant_o   = w_fire && w_ovr_vld && maint_req_i
                          && !refresh_req_i && !refresh_drain_i
                          && !(HAS_ZQ && zq_req_i);

    assign evt_act_o  = w_fire && !w_ovr_vld && w_fis_act;
    assign evt_rd_o   = w_fire && !w_ovr_vld && w_fis_col &&  r_winner.is_rd;
    assign evt_wr_o   = w_fire && !w_ovr_vld && w_fis_col && !r_winner.is_rd;
    assign evt_pre_o  = w_fire && (w_ovr_vld ? (w_ovr_op == OP_PRE)
                                             : w_fis_pre);
    assign evt_ap_o   = w_fire && !w_ovr_vld && w_fis_col && cmd_ap_o;
    assign evt_rank_o = RKW'(RK0);
    assign evt_bank_o = cmd_bank_o;
    assign evt_row_o  = cmd_row_o;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_winner <= '0;
            r_wrfire0 <= 1'b0;
            r_rdfire0 <= 1'b0;
            r_actfire0      <= 1'b0;
            r_actfire0_bank <= '0;
        end else begin
            // Load the matrix-arbiter winner whenever the current winner fires
            // (so the reserve behind it becomes visible), goes stale, or is
            // absent.  Hold otherwise.
            if (w_demand_fire || !r_winner.vld || winner_stale) begin
                r_winner.vld   <= w_pick_vld;
                r_winner.is_rd <= w_sel_is_rd;
                r_winner.bank  <= w_sel_bank;
                r_winner.op    <= w_sel_op;
                r_winner.slot  <= w_sel_head.slot;
                r_winner.row   <= w_sel_head.row;
                r_winner.col   <= w_sel_head.col;
                r_winner.id    <= w_sel_head.id;
                r_winner.last  <= w_sel_head.last;
                r_winner.ap    <= r_winner.is_rd ? r_ap[w_sel_bank] : w_ap[w_sel_bank];
            end
            r_wrfire0 <= w_fire && !w_ovr_vld && w_fis_col && !r_winner.is_rd;
            r_rdfire0 <= w_fire && !w_ovr_vld && w_fis_col &&  r_winner.is_rd;
            r_actfire0      <= w_fire && !w_ovr_vld && w_fis_act;
            r_actfire0_bank <= r_winner.bank;
        end
    )

    // ======================================================================
    // Stall-cause attribution (same buckets as the FRFCFS core)
    // ======================================================================
    // any_head_vld includes the registered winner, so a held demand that is
    // waiting out a JEDEC gate is still counted as pending here.
    logic w_any_pending;
    assign w_any_pending = (|wr_bh_valid_i) || (|rd_bh_valid_i) || any_head_vld;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            stall_bp_o <= '0; stall_refresh_o <= '0; stall_turnaround_o <= '0;
            stall_tccd_o <= '0; stall_actlimit_o <= '0; stall_banktimer_o <= '0;
            stall_noreq_o <= '0; stall_zq_o <= '0;
        end else if (!w_fire) begin
            if (refresh_req_i || refresh_drain_i)        stall_refresh_o    <= stall_refresh_o + 1;
            else if (!w_any_pending)                     stall_noreq_o      <= stall_noreq_o + 1;
            else if (!twtr_ok_i || !trtw_ok_i)           stall_turnaround_o <= stall_turnaround_o + 1;
            else if (!w_tccd_fwd_ok)                     stall_tccd_o       <= stall_tccd_o + 1;
            else if (!tfaw_ok_i[RK0] || !trrd_ok_i[RK0]) stall_actlimit_o   <= stall_actlimit_o + 1;
            else                                         stall_banktimer_o  <= stall_banktimer_o + 1;
        end
    )

endmodule : mc_bank_sched
