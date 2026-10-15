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
    input  logic [NUM_BANKS-1:0]      rd_bh_valid_i,
    input  logic [NUM_BANKS*PTRW-1:0] rd_bh_slot_i,
    input  logic [NUM_BANKS*ROW_WIDTH-1:0] rd_bh_row_i,
    input  logic [NUM_BANKS*COL_WIDTH-1:0] rd_bh_col_i,
    input  logic [NUM_BANKS*IW-1:0]   rd_bh_id_i,
    input  logic [NUM_BANKS-1:0]      rd_bh_empty_i,
    input  logic [NUM_BANKS-1:0]      wr_bh2_valid_i,
    input  logic [NUM_BANKS*PTRW-1:0] wr_bh2_slot_i,
    input  logic [NUM_BANKS*ROW_WIDTH-1:0] wr_bh2_row_i,
    input  logic [NUM_BANKS*COL_WIDTH-1:0] wr_bh2_col_i,
    input  logic [NUM_BANKS*IW-1:0]   wr_bh2_id_i,
    input  logic [NUM_BANKS-1:0]      wr_bh2_last_i,
    input  logic [NUM_BANKS-1:0]      rd_bh2_valid_i,
    input  logic [NUM_BANKS*PTRW-1:0] rd_bh2_slot_i,
    input  logic [NUM_BANKS*ROW_WIDTH-1:0] rd_bh2_row_i,
    input  logic [NUM_BANKS*COL_WIDTH-1:0] rd_bh2_col_i,
    input  logic [NUM_BANKS*IW-1:0]   rd_bh2_id_i,

    // ---- storage commit / issue handshake (same contract as the FRFCFS core)
    input  logic                      wr_commit_ready_i,
    output logic                      wr_commit_valid_o,
    output logic [PTRW-1:0]           wr_commit_slot_o,
    input  logic                      rd_issue_ready_i,
    output logic                      rd_issue_valid_o,
    output logic [PTRW-1:0]           rd_issue_slot_o,

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
    input  logic                      tccd_ok_i,

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

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))      r_rfc_cnt <= '0;
        else if (refresh_grant_o)
            r_rfc_cnt <= (cmd_op_o == OP_REFPB && t_rfc_pb_i != 8'd0)
                         ? {8'h0, t_rfc_pb_i} : t_rfc_i;
        else if (w_rfc_busy)             r_rfc_cnt <= r_rfc_cnt - 16'd1;
    )
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
    // Per-(dir,bank) head skid. Slot 1 is the candidate; when empty the mux
    // reads the store's head view combinationally (zero-load-latency start);
    // on the head's COLUMN fire, slot 1 seats the second-oldest view so the
    // successor is already in place next cycle -- sustaining 1 command/cycle
    // on a single bank with no store round-trip per pick. ACT/PRE fires do
    // NOT release the head (its columns are still to come).
    // ======================================================================
    typedef struct packed {
        logic                 vld;
        logic [PTRW-1:0]      slot;
        logic [ROW_WIDTH-1:0] row;
        logic [COL_WIDTH-1:0] col;
        logic [IW-1:0]        id;
        logic                 last;
    } head_t;

    head_t r_ws [NUM_BANKS];
    head_t r_rs [NUM_BANKS];

    function automatic head_t wr_cand(input int b);
        head_t c;
        c = r_ws[b];
        if (!c.vld && wr_bh_valid_i[b]) begin
            c.vld  = 1'b1;
            c.slot = wr_bh_slot_i[b*PTRW +: PTRW];
            c.row  = wr_bh_row_i [b*ROW_WIDTH +: ROW_WIDTH];
            c.col  = wr_bh_col_i [b*COL_WIDTH +: COL_WIDTH];
            c.id   = wr_bh_id_i  [b*IW +: IW];
            c.last = wr_bh_last_i[b];
        end
        return c;
    endfunction
    function automatic head_t rd_cand(input int b);
        head_t c;
        c = r_rs[b];
        if (!c.vld && rd_bh_valid_i[b]) begin
            c.vld  = 1'b1;
            c.slot = rd_bh_slot_i[b*PTRW +: PTRW];
            c.row  = rd_bh_row_i [b*ROW_WIDTH +: ROW_WIDTH];
            c.col  = rd_bh_col_i [b*COL_WIDTH +: COL_WIDTH];
            c.id   = rd_bh_id_i  [b*IW +: IW];
            c.last = 1'b0;
        end
        return c;
    endfunction

    // Per-bank op decode on the registered image. In-order queue => when the
    // head's row differs from the open row, every older same-bank request has
    // issued: PRE is always safe to decide immediately (no demand wait).
    // CLOSE_ON_DRAIN uses the LIVE store empty flag (count==1 in the bank).
    dram_op_e w_op [NUM_BANKS];
    dram_op_e r_op [NUM_BANKS];
    logic     w_ap [NUM_BANKS];
    logic     r_ap [NUM_BANKS];
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            automatic head_t wc = wr_cand(b);
            automatic head_t rc = rd_cand(b);
            w_op[b] = OP_NOP;
            r_op[b] = OP_NOP;
            w_ap[b] = (page_policy_i == PAGE_POLICY_CLOSE);
            r_ap[b] = (page_policy_i == PAGE_POLICY_CLOSE);
            if (wc.vld) begin
                if (r_row_act[RK0][b] && (r_open_row[RK0][b] == wc.row)
                    && r_rdwr_rdy[RK0][b]) begin
                    w_op[b] = OP_WR;
                    w_ap[b] = (page_policy_i == PAGE_POLICY_CLOSE)
                            || (CLOSE_ON_DRAIN && wr_bh_empty_i[b]);
                end else if (r_row_act[RK0][b] && r_pre_rdy[RK0][b]) begin
                    w_op[b] = OP_PRE;
                end else if (!r_row_act[RK0][b] && r_act_rdy[RK0][b]) begin
                    w_op[b] = OP_ACT;
                end
            end
            if (rc.vld) begin
                if (r_row_act[RK0][b] && (r_open_row[RK0][b] == rc.row)
                    && r_rdwr_rdy[RK0][b]) begin
                    r_op[b] = OP_RD;
                    r_ap[b] = (page_policy_i == PAGE_POLICY_CLOSE)
                            || (CLOSE_ON_DRAIN && rd_bh_empty_i[b]);
                end else if (r_row_act[RK0][b] && r_pre_rdy[RK0][b]) begin
                    r_op[b] = OP_PRE;
                end else if (!r_row_act[RK0][b] && r_act_rdy[RK0][b]) begin
                    r_op[b] = OP_ACT;
                end
            end
        end
    end

    // ======================================================================
    // Maintenance override: init passthrough; refresh (per-bank drain PREs,
    // then grant when all idle); generic maintenance when all idle. Same
    // all-banks-idle safety contracts as the FRFCFS core.
    // ======================================================================
    logic any_head_vld;
    always_comb begin
        any_head_vld = 1'b0;
        for (int b = 0; b < NUM_BANKS; b++) begin
            if (wr_bh_valid_i[b] || rd_bh_valid_i[b]) any_head_vld = 1'b1;
            if (r_ws[b].vld || r_rs[b].vld)           any_head_vld = 1'b1;
        end
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

    logic w_ref_safe, w_refpb_safe, w_maint_safe;
    assign w_ref_safe   = !w_any_active && !any_head_vld && !w_rfc_busy;
    assign w_refpb_safe = !r_row_act[RK0][refresh_bank_i] && !any_head_vld
                       && !w_rfc_busy;
    assign w_maint_safe = !w_any_active && !any_head_vld
                       && !w_rfc_busy && !w_zq_busy && !maint_busy_i;

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
    // Cross-bank demand mux: round-robin rotor over (dir,bank) pairs whose
    // decoded op is non-NOP. Columns add the sink gate (drain-FIFO /
    // return-ring room) so a column can never fire into a full sink.
    // ======================================================================
    logic [NPAIR-1:0] w_pair_ready;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            w_pair_ready[2*b]   = (r_op[b] != OP_NOP)
                                && ((r_op[b] != OP_RD) || rd_issue_ready_i);
            w_pair_ready[2*b+1] = (w_op[b] != OP_NOP)
                                && ((w_op[b] != OP_WR) || wr_commit_ready_i);
        end
    end

    logic [PAIRW-1:0] r_rotor;
    logic [NPAIR-1:0] w_rot_mask;
    always_comb begin
        w_rot_mask = '0;
        for (int p = 0; p < NPAIR; p++)
            w_rot_mask[PAIRW'(p) + r_rotor] = 1'b1;   // 4-bit wrap = rotation
    end

    logic [PAIRW-1:0] w_pick_pair;
    logic             w_pick_vld;
    always_comb begin
        w_pick_vld  = 1'b0;
        w_pick_pair = '0;
        for (int p = 0; p < NPAIR; p++)
            if (w_pair_ready[p] && w_rot_mask[p]) begin
                w_pick_vld  = 1'b1;
                w_pick_pair = PAIRW'(p);
            end
    end

    // ======================================================================
    // Live fire-stage authority. The selected op is re-checked against the
    // LIVE timer outputs; a failing gate does not fire and the head holds in
    // its skid. No drop, no pipeline drain, no hold-freeze. Pick == fire in
    // the same cycle, so opposite-direction turnarounds are covered by the
    // 1-deep fire history + the global tWTR/tRTW windows (there is no
    // pick-ahead seam to close).
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
        w_sel_op    = w_sel_is_rd ? r_op[w_sel_bank] : w_op[w_sel_bank];
        w_sel_head  = w_sel_is_rd ? rd_cand(int'(w_sel_bank))
                                  : wr_cand(int'(w_sel_bank));
    end

    logic        w_fis_col, w_fis_act, w_fis_pre;
    logic        w_fsafe;
    always_comb begin
        w_fis_col = (w_sel_op == OP_RD) || (w_sel_op == OP_WR);
        w_fis_act = (w_sel_op == OP_ACT);
        w_fis_pre = (w_sel_op == OP_PRE);
        w_fsafe   = 1'b1;
        if (w_ovr_vld) begin
            // override ops carry their own all-banks-idle / drain predicates
            // (decoded on the registered image, as the FRFCFS core does);
            // drain PREs re-check the live pre gate.
            if (w_ovr_op == OP_PRE)
                w_fsafe = bank_pre_ready_i[RK0][w_ovr_bank];
        end else if (w_pick_vld) begin
            if (w_fis_act)
                w_fsafe = bank_act_ready_i[RK0][w_sel_bank] && tfaw_ok_i[RK0]
                          && trrd_ok_i[RK0] && !w_rfc_busy && !maint_busy_i;
            else if (w_fis_col)
                w_fsafe = bank_rdwr_ready_i[RK0][w_sel_bank] && tccd_ok_i
                          && (w_sel_is_rd ? (twtr_ok_i && !w_rd_turn_block)
                                          : (trtw_ok_i && !w_wr_turn_block));
            else if (w_fis_pre)
                w_fsafe = bank_pre_ready_i[RK0][w_sel_bank];
        end
    end

    logic w_fire;
    assign w_fire      = (w_ovr_vld || w_pick_vld) && w_fsafe && cmd_ready_i;
    assign cmd_valid_o = w_fire;

    logic w_fis_rd;
    assign w_fis_rd = w_ovr_vld ? 1'b0 : w_sel_is_rd;

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
        end else if (w_pick_vld) begin
            cmd_bank_o = w_sel_bank;
            cmd_row_o  = w_sel_head.row;
            cmd_col_o  = w_sel_head.col;
            if (w_fis_act) begin
                cmd_op_o = OP_ACT;
            end else if (w_fis_pre) begin
                cmd_op_o = OP_PRE;
            end else begin
                // AP was fully decided at decode (static CLOSE policy OR the
                // exact per-bank queue-empty CLOSE_ON_DRAIN term).
                cmd_ap_o = w_sel_is_rd ? r_ap[w_sel_bank] : w_ap[w_sel_bank];
                cmd_op_o = w_sel_is_rd ? (cmd_ap_o ? OP_RDA : OP_RD)
                                       : (cmd_ap_o ? OP_WRA : OP_WR);
            end
        end
    end
    assign cmd_rank_o = RKW'(RK0);

    // ======================================================================
    // Strobes: storage handshake, grants, timer events, fire history, skid
    // ======================================================================
    assign wr_commit_valid_o = w_fire && !w_ovr_vld && w_fis_col && !w_fis_rd;
    assign wr_commit_slot_o  = w_sel_head.slot;
    assign rd_issue_valid_o  = w_fire && !w_ovr_vld && w_fis_col &&  w_fis_rd;
    assign rd_issue_slot_o   = w_sel_head.slot;

    assign refresh_grant_o = w_fire && w_ovr_vld
                          && ((w_ovr_op == OP_REF) || (w_ovr_op == OP_REFPB));
    assign zq_grant_o      = w_fire && w_ovr_vld && (w_ovr_op == OP_ZQCS);
    assign maint_grant_o   = w_fire && w_ovr_vld && maint_req_i
                          && !refresh_req_i && !refresh_drain_i
                          && !(HAS_ZQ && zq_req_i);

    assign evt_act_o  = w_fire && !w_ovr_vld && w_fis_act;
    assign evt_rd_o   = w_fire && !w_ovr_vld && w_fis_col &&  w_fis_rd;
    assign evt_wr_o   = w_fire && !w_ovr_vld && w_fis_col && !w_fis_rd;
    assign evt_pre_o  = w_fire && (w_ovr_vld ? (w_ovr_op == OP_PRE)
                                             : w_fis_pre);
    assign evt_ap_o   = w_fire && !w_ovr_vld && w_fis_col && cmd_ap_o;
    assign evt_rank_o = RKW'(RK0);
    assign evt_bank_o = cmd_bank_o;
    assign evt_row_o  = cmd_row_o;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int b = 0; b < NUM_BANKS; b++) begin
                r_ws[b] <= '0;
                r_rs[b] <= '0;
            end
            r_rotor   <= '0;
            r_wrfire0 <= 1'b0;
            r_rdfire0 <= 1'b0;
        end else begin
            for (int b = 0; b < NUM_BANKS; b++) begin
                // WR skid: column fire releases the head (seat the reserve);
                // otherwise load the head view when empty. ACT/PRE fires hold.
                if (w_fire && !w_ovr_vld && (cmd_bank_o == BKW'(b))
                    && (w_op[b] == OP_WR)) begin
                    r_ws[b].vld  <= wr_bh2_valid_i[b];
                    r_ws[b].slot <= wr_bh2_slot_i[b*PTRW +: PTRW];
                    r_ws[b].row  <= wr_bh2_row_i [b*ROW_WIDTH +: ROW_WIDTH];
                    r_ws[b].col  <= wr_bh2_col_i [b*COL_WIDTH +: COL_WIDTH];
                    r_ws[b].id   <= wr_bh2_id_i  [b*IW +: IW];
                    r_ws[b].last <= wr_bh2_last_i[b];
                end else if (!r_ws[b].vld) begin
                    r_ws[b].vld  <= wr_bh_valid_i[b];
                    r_ws[b].slot <= wr_bh_slot_i[b*PTRW +: PTRW];
                    r_ws[b].row  <= wr_bh_row_i [b*ROW_WIDTH +: ROW_WIDTH];
                    r_ws[b].col  <= wr_bh_col_i [b*COL_WIDTH +: COL_WIDTH];
                    r_ws[b].id   <= wr_bh_id_i  [b*IW +: IW];
                    r_ws[b].last <= wr_bh_last_i[b];
                end
                // RD skid: same discipline.
                if (w_fire && !w_ovr_vld && (cmd_bank_o == BKW'(b))
                    && (w_op[b] == OP_RD)) begin
                    r_rs[b].vld  <= rd_bh2_valid_i[b];
                    r_rs[b].slot <= rd_bh2_slot_i[b*PTRW +: PTRW];
                    r_rs[b].row  <= rd_bh2_row_i [b*ROW_WIDTH +: ROW_WIDTH];
                    r_rs[b].col  <= rd_bh2_col_i [b*COL_WIDTH +: COL_WIDTH];
                    r_rs[b].id   <= rd_bh2_id_i  [b*IW +: IW];
                    r_rs[b].last <= 1'b0;
                end else if (!r_rs[b].vld) begin
                    r_rs[b].vld  <= rd_bh_valid_i[b];
                    r_rs[b].slot <= rd_bh_slot_i[b*PTRW +: PTRW];
                    r_rs[b].row  <= rd_bh_row_i [b*ROW_WIDTH +: ROW_WIDTH];
                    r_rs[b].col  <= rd_bh_col_i [b*COL_WIDTH +: COL_WIDTH];
                    r_rs[b].id   <= rd_bh_id_i  [b*IW +: IW];
                    r_rs[b].last <= 1'b0;
                end
            end
            if (w_fire && w_pick_vld)
                r_rotor <= w_pick_pair + PAIRW'(1);
            r_wrfire0 <= w_fire && !w_ovr_vld && w_fis_col && !w_fis_rd;
            r_rdfire0 <= w_fire && !w_ovr_vld && w_fis_col &&  w_fis_rd;
        end
    )

    // ======================================================================
    // Stall-cause attribution (same buckets as the FRFCFS core)
    // ======================================================================
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
            else if (!tccd_ok_i)                         stall_tccd_o       <= stall_tccd_o + 1;
            else if (!tfaw_ok_i[RK0] || !trrd_ok_i[RK0]) stall_actlimit_o   <= stall_actlimit_o + 1;
            else                                         stall_banktimer_o  <= stall_banktimer_o + 1;
        end
    )

endmodule : mc_bank_sched
