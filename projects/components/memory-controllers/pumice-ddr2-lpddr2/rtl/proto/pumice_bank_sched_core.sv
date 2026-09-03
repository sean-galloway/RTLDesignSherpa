// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: pumice_bank_sched_core  (PROTOTYPE / depth-measurement scaffold)
// Purpose: The trimmed final scheduler. It arbitrates among NUM_BANKS
//   REGISTERED per-bank candidates (from pumice_bank_cmd_picker) plus the
//   refresh/init streams, applies the GLOBAL timing constraints (bus 1/cyc,
//   tRRD, tFAW, tWTR/tRTW turnaround, tCCD) that a single bank cannot see,
//   RE-CHECKS each candidate against live per-bank readiness (a flopped
//   candidate can go illegal in one cycle), and emits one DRAM command plus
//   the per-bank issued_o strobe that advances the winning picker.
//
// Because the candidates are pre-selected and registered, this is an 8-way
// pick, not the full cross-bank associative cone.
`timescale 1ns/1ps

module pumice_bank_sched_core #(
    parameter int NUM_BANKS  = 8,
    parameter int ROW_WIDTH  = 14,
    parameter int COL_WIDTH  = 10,
    parameter int BKW        = 3,
    parameter int PTRW       = 3,
    parameter int AGE_WIDTH  = 16
) (
    input  logic                             aclk,
    input  logic                             aresetn,

    // ---- per-bank registered candidates ----
    input  logic [NUM_BANKS-1:0]             cand_valid_i,
    input  logic [NUM_BANKS-1:0][2:0]        cand_op_i,
    input  logic [NUM_BANKS-1:0][ROW_WIDTH-1:0] cand_row_i,
    input  logic [NUM_BANKS-1:0][COL_WIDTH-1:0] cand_col_i,
    input  logic [NUM_BANKS-1:0][PTRW-1:0]   cand_slot_i,
    input  logic [NUM_BANKS-1:0]             cand_is_rd_i,
    input  logic [NUM_BANKS-1:0][AGE_WIDTH-1:0] cand_pri_i,

    // ---- live per-bank re-check (candidate may have gone illegal) ----
    input  logic [NUM_BANKS-1:0]             bank_act_ready_i,
    input  logic [NUM_BANKS-1:0]             bank_rdwr_ready_i,
    input  logic [NUM_BANKS-1:0]             bank_pre_ready_i,

    // ---- global constraints (from global_timers) ----
    input  logic                             tfaw_ok_i,
    input  logic                             trrd_ok_i,
    input  logic                             twtr_ok_i,
    input  logic                             trtw_ok_i,
    input  logic                             tccd_ok_i,
    input  logic                             rfc_busy_i,

    // ---- refresh / init override (highest priority) ----
    input  logic                             ovr_valid_i,
    input  logic [2:0]                        ovr_op_i,
    input  logic [BKW-1:0]                    ovr_bank_i,
    input  logic [ROW_WIDTH-1:0]              ovr_row_i,

    // ---- direction turnaround history (2-flop) ----
    input  logic                             rd_fired_i,
    input  logic                             wr_fired_i,

    input  logic                             cmd_ready_i,

    // ---- outputs ----
    output logic                             cmd_valid_o,
    output logic [2:0]                        cmd_op_o,
    output logic [BKW-1:0]                    cmd_bank_o,
    output logic [ROW_WIDTH-1:0]              cmd_row_o,
    output logic [COL_WIDTH-1:0]              cmd_col_o,
    output logic [NUM_BANKS-1:0]             issued_o,
    output logic [PTRW-1:0]                   issued_slot_o,
    output logic                             issued_is_rd_o
);
    localparam logic [2:0] OP_ACT=3'd1, OP_RD=3'd2, OP_WR=3'd3, OP_PRE=3'd4;

    // ---- re-check each registered candidate against live readiness + global
    logic [NUM_BANKS-1:0] elig;
    always_comb begin
        for (int b=0;b<NUM_BANKS;b++) begin
            automatic logic is_col = (cand_op_i[b]==OP_RD)||(cand_op_i[b]==OP_WR);
            automatic logic is_act =  cand_op_i[b]==OP_ACT;
            automatic logic is_pre =  cand_op_i[b]==OP_PRE;
            automatic logic okc = is_col && bank_rdwr_ready_i[b] && tccd_ok_i
                                   && (cand_is_rd_i[b] ? (twtr_ok_i && !wr_fired_i)
                                                       : (trtw_ok_i && !rd_fired_i));
            automatic logic oka = is_act && bank_act_ready_i[b] && tfaw_ok_i && trrd_ok_i && !rfc_busy_i;
            automatic logic okp = is_pre && bank_pre_ready_i[b];
            elig[b] = cand_valid_i[b] && (okc||oka||okp);
        end
    end

    // ---- 8-way pick among eligible candidates: oldest priority wins --------
    // (column > act > pre already resolved inside each picker; here we just
    // pick the highest-priority eligible bank.)
    //
    // PUMICE-017 anti-pattern: the obvious serial reduce
    //   for b: if elig[b] && pri[b]>best: best=pri[b]; sel=b;
    // chains NUM_BANKS dependent AGE_WIDTH compares (each iteration reads the
    // previous `best`) -> a compare/mux chain NUM_BANKS deep. The same serial
    // max that PUMICE-017 replaced on sch_head_rel. Rewrite as a balanced
    // TOURNAMENT TREE: each level's compares are independent and only depend on
    // the prior level, so depth is clog2(NUM_BANKS) compares, not NUM_BANKS.
    localparam int LV = $clog2(NUM_BANKS);
    logic                 tv [0:LV][0:NUM_BANKS-1];
    logic [AGE_WIDTH-1:0] tp [0:LV][0:NUM_BANKS-1];
    logic [BKW-1:0]       tb [0:LV][0:NUM_BANKS-1];
    logic                sel_valid;
    logic [BKW-1:0]      sel_bank;
    logic [AGE_WIDTH-1:0] best_pri;
    always_comb begin
        // leaves
        for (int b=0;b<NUM_BANKS;b++) begin
            tv[0][b]=elig[b]; tp[0][b]=cand_pri_i[b]; tb[0][b]=BKW'(b);
        end
        // reduce pairwise, halving each level (winner = valid one; both valid ->
        // higher priority; tie/none -> lower index via prefer-left)
        for (int l=1;l<=LV;l++) begin
            for (int i=0;i<(NUM_BANKS>>l);i++) begin
                automatic logic av = tv[l-1][2*i];
                automatic logic bv = tv[l-1][2*i+1];
                // choose the right child only if left is invalid, or right is
                // valid and strictly higher priority (prefer-left on ties)
                automatic logic pick_r = (!av) || (bv && (tp[l-1][2*i+1] > tp[l-1][2*i]));
                tv[l][i] = av || bv;
                tp[l][i] = pick_r ? tp[l-1][2*i+1] : tp[l-1][2*i];
                tb[l][i] = pick_r ? tb[l-1][2*i+1] : tb[l-1][2*i];
            end
        end
        sel_valid = tv[LV][0];
        best_pri  = tp[LV][0];
        sel_bank  = tb[LV][0];
    end

    // ---- drive command: override (refresh/init) beats the bank pick --------
    always_comb begin
        issued_o='0; issued_slot_o='0; issued_is_rd_o=1'b0;
        if (ovr_valid_i) begin
            cmd_valid_o=1'b1; cmd_op_o=ovr_op_i; cmd_bank_o=ovr_bank_i;
            cmd_row_o=ovr_row_i; cmd_col_o='0;
        end else begin
            cmd_valid_o=sel_valid;
            cmd_op_o   =cand_op_i[sel_bank];
            cmd_bank_o =sel_bank;
            cmd_row_o  =cand_row_i[sel_bank];
            cmd_col_o  =cand_col_i[sel_bank];
            if (sel_valid && cmd_ready_i) begin
                issued_o[sel_bank]=1'b1;
                issued_slot_o=cand_slot_i[sel_bank];
                issued_is_rd_o=cand_is_rd_i[sel_bank];
            end
        end
    end
endmodule
