// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// Module: pumice_bank_cmd_picker  (PROTOTYPE / depth-measurement scaffold)
// Purpose: Per-bank command selection, ONE instance per DRAM bank. Each cycle
//   it looks at only THIS bank's rd + wr CAM entries, classifies each into
//   column / activate / precharge against this bank's (fixed) open-row image
//   and per-bank timers, picks the bank's single best legal command, and
//   REGISTERS it as this bank's candidate. The final scheduler then arbitrates
//   among the NUM_BANKS registered candidates -- an 8-way pick, not the full
//   cross-bank associative cone.
//
// This partitions the old 81-level arbiter cone: BANK_ID is a constant here,
// so the per-entry open_row mux collapses (no bank lookup) and the oldest
// reduction spans only this bank's entries. Both rd and wr are considered
// together (one command bus -> a bank does one thing per opportunity).
//
// Scaffold notes: op/policy modelled as plain logic (no pumice_pkg) so it
// elaborates standalone for the mux-level depth tool. Guards are the dominant
// structural ones; the shallow turnaround/AP overlays are folded into gate_i.
`timescale 1ns/1ps

module pumice_bank_cmd_picker #(
    parameter int BANK_ID     = 0,
    parameter int NUM_ENTRIES = 8,
    parameter int ROW_WIDTH   = 14,
    parameter int COL_WIDTH   = 10,
    parameter int BKW         = 3,
    parameter int PTRW        = 3,
    parameter int AGE_WIDTH   = 16
) (
    input  logic                              aclk,
    input  logic                              aresetn,

    // ---- this bank's live state (from pumice_bank_timers) ----
    input  logic                              bank_act_ready_i,
    input  logic                              bank_rdwr_ready_i,
    input  logic                              bank_pre_ready_i,
    input  logic                              bank_row_active_i,
    input  logic [ROW_WIDTH-1:0]              bank_open_row_i,

    // ---- rd CAM per-entry vectors (registered, whole CAM) ----
    input  logic [NUM_ENTRIES-1:0]            rd_valid_i,
    input  logic [NUM_ENTRIES*BKW-1:0]        rd_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]  rd_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]  rd_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0] rd_older_i,
    input  logic                              rd_issue_ready_i,

    // ---- wr CAM per-entry vectors (registered, whole CAM) ----
    input  logic [NUM_ENTRIES-1:0]            wr_valid_i,
    input  logic [NUM_ENTRIES*BKW-1:0]        wr_bank_i,
    input  logic [NUM_ENTRIES*ROW_WIDTH-1:0]  wr_row_i,
    input  logic [NUM_ENTRIES*COL_WIDTH-1:0]  wr_col_i,
    input  logic [NUM_ENTRIES*NUM_ENTRIES-1:0] wr_older_i,
    input  logic                              wr_commit_ready_i,

    // ---- policy + shallow overlay guards folded to one gate ----
    input  logic [2:0]                        page_policy_i,
    input  logic                              gate_i,     // turnaround/AP/rfc: block columns
    input  logic                              read_pref_i,

    // ---- final-scheduler feedback ----
    input  logic                              issued_i,   // my candidate accepted

    // ---- registered candidate out ----
    output logic                              cand_valid_o,
    output logic [2:0]                        cand_op_o,   // 1=ACT 2=RD 3=WR 4=PRE
    output logic [ROW_WIDTH-1:0]              cand_row_o,
    output logic [COL_WIDTH-1:0]              cand_col_o,
    output logic [PTRW-1:0]                   cand_slot_o,
    output logic                              cand_is_rd_o,
    output logic [AGE_WIDTH-1:0]              cand_pri_o
);
    localparam logic [2:0] OP_ACT=3'd1, OP_RD=3'd2, OP_WR=3'd3, OP_PRE=3'd4;
    localparam int RK0 = 0;

    function automatic logic [BKW-1:0]       f_bank(input logic [NUM_ENTRIES*BKW-1:0] v, input int e);
        return v[e*BKW +: BKW]; endfunction
    function automatic logic [ROW_WIDTH-1:0] f_row (input logic [NUM_ENTRIES*ROW_WIDTH-1:0] v, input int e);
        return v[e*ROW_WIDTH +: ROW_WIDTH]; endfunction
    function automatic logic [COL_WIDTH-1:0] f_col (input logic [NUM_ENTRIES*COL_WIDTH-1:0] v, input int e);
        return v[e*COL_WIDTH +: COL_WIDTH]; endfunction

    // oldest-in-mask via the age-order matrix -> one-hot is_old, then slot.
    // Written with REDUCTION operators (&terms, |bmask) not accumulator loops:
    // at the mux-level a reduce is one $reduce_* cell (depth 1), whereas the
    // obvious `for j: if(...) ge=0` / `for i: if(old) slot=i` synthesize as
    // NUM_ENTRIES-deep mux chains (the PUMICE-017 anti-pattern one level down).
    function automatic logic [PTRW:0] arg_oldest(
        input logic [NUM_ENTRIES-1:0] mask,
        input logic [NUM_ENTRIES*NUM_ENTRIES-1:0] older);
        logic found; logic [PTRW-1:0] slot; logic [NUM_ENTRIES-1:0] is_old;
        for (int i=0;i<NUM_ENTRIES;i++) begin
            automatic logic [NUM_ENTRIES-1:0] orow = older[i*NUM_ENTRIES +: NUM_ENTRIES];
            automatic logic [NUM_ENTRIES-1:0] terms;
            // i is >= entry j iff j is itself, not masked, or i is older than j
            for (int j=0;j<NUM_ENTRIES;j++) terms[j] = (j==i) || !mask[j] || orow[j];
            is_old[i] = mask[i] && (&terms);        // one reduce-AND
        end
        found = |is_old;                            // one reduce-OR
        // one-hot -> binary: each index bit is a masked reduce-OR
        for (int b=0;b<PTRW;b++) begin
            automatic logic [NUM_ENTRIES-1:0] bmask;
            for (int i=0;i<NUM_ENTRIES;i++) bmask[i] = is_old[i] && i[b];
            slot[b] = |bmask;
        end
        return {found,slot};
    endfunction


    // ---- classify THIS bank's entries (BANK_ID fixed: open_row is direct) ---
    logic [NUM_ENTRIES-1:0] rd_col_m, rd_act_m, rd_pre_m;
    logic [NUM_ENTRIES-1:0] wr_col_m, wr_act_m, wr_pre_m;
    logic w_open = page_policy_i != 3'd0;  // scaffold: nonzero == open-ish
    always_comb begin
        rd_col_m='0; rd_act_m='0; rd_pre_m='0;
        wr_col_m='0; wr_act_m='0; wr_pre_m='0;
        for (int e=0;e<NUM_ENTRIES;e++) begin
            automatic logic mine_r = rd_valid_i[e] && (f_bank(rd_bank_i,e)==BKW'(BANK_ID));
            automatic logic mine_w = wr_valid_i[e] && (f_bank(wr_bank_i,e)==BKW'(BANK_ID));
            automatic logic rhit = bank_row_active_i && (f_row(rd_row_i,e)==bank_open_row_i);
            automatic logic whit = bank_row_active_i && (f_row(wr_row_i,e)==bank_open_row_i);
            if (mine_r) begin
                rd_col_m[e]=rhit && bank_rdwr_ready_i && rd_issue_ready_i && !gate_i;
                rd_act_m[e]=!bank_row_active_i && bank_act_ready_i;
                rd_pre_m[e]=bank_row_active_i && !rhit && bank_pre_ready_i;
            end
            if (mine_w) begin
                wr_col_m[e]=whit && bank_rdwr_ready_i && wr_commit_ready_i && !gate_i;
                wr_act_m[e]=!bank_row_active_i && bank_act_ready_i;
                wr_pre_m[e]=bank_row_active_i && !whit && bank_pre_ready_i;
            end
        end
    end

    // ---- oldest-per-class {found,slot}, all six computed in parallel -------
    logic [PTRW:0] rc=arg_oldest(rd_col_m,rd_older_i), ra=arg_oldest(rd_act_m,rd_older_i), rp=arg_oldest(rd_pre_m,rd_older_i);
    logic [PTRW:0] wc=arg_oldest(wr_col_m,wr_older_i), wa=arg_oldest(wr_act_m,wr_older_i), wp=arg_oldest(wr_pre_m,wr_older_i);
    logic rc_f, wc_f, ra_f, wa_f, rp_f, wp_f;
    assign rc_f=rc[PTRW]; assign wc_f=wc[PTRW]; assign ra_f=ra[PTRW];
    assign wa_f=wa[PTRW]; assign rp_f=rp[PTRW]; assign wp_f=wp[PTRW];

    // ---- PARALLEL winner select (replaces the 6-deep priority branch chain) -
    // The class order (column > activate > precharge) and rd/wr preference are
    // resolved as 1-bit logic on the six FOUND flags (~3 levels), NOT by
    // re-muxing the wide fields six times. Fields are then extracted ONCE, by a
    // single variable part-select on the winning slot (log-depth 8:1).
    logic col_any, act_any;
    assign col_any = rc_f|wc_f;
    assign act_any = ra_f|wa_f;
    logic sel_col_rd, sel_col_wr, sel_act_rd, sel_act_wr, sel_pre_rd, sel_pre_wr;
    assign sel_col_rd = read_pref_i ? (rc_f && !wc_f) : rc_f;
    assign sel_col_wr = read_pref_i ? wc_f            : (wc_f && !rc_f);
    assign sel_act_rd = ra_f            && !col_any;
    assign sel_act_wr = (wa_f && !ra_f) && !col_any;
    assign sel_pre_rd = rp_f            && !col_any && !act_any;
    assign sel_pre_wr = (wp_f && !rp_f) && !col_any && !act_any;

    logic n_is_rd = sel_col_rd | sel_act_rd | sel_pre_rd;
    logic n_valid = col_any | act_any | rp_f | wp_f;
    logic [2:0] n_op = (sel_col_rd) ? OP_RD : (sel_col_wr) ? OP_WR
                     : (sel_act_rd|sel_act_wr) ? OP_ACT : OP_PRE;
    // winning slot inside each CAM (small 3:1 mux of PTRW-bit slots), then ONE
    // part-select per field on the chosen CAM/slot.
    logic [PTRW-1:0] rd_slot = sel_col_rd ? rc[PTRW-1:0] : sel_act_rd ? ra[PTRW-1:0] : rp[PTRW-1:0];
    logic [PTRW-1:0] wr_slot = sel_col_wr ? wc[PTRW-1:0] : sel_act_wr ? wa[PTRW-1:0] : wp[PTRW-1:0];
    logic [PTRW-1:0]      n_slot = n_is_rd ? rd_slot : wr_slot;
    logic [ROW_WIDTH-1:0] n_row  = n_is_rd ? f_row(rd_row_i,rd_slot) : f_row(wr_row_i,wr_slot);
    logic [COL_WIDTH-1:0] n_col  = n_is_rd ? f_col(rd_col_i,rd_slot) : f_col(wr_col_i,wr_slot);

    // ---- register this bank's candidate (advances on issued_i / new pick) ---
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            cand_valid_o<=1'b0; cand_op_o<=OP_ACT; cand_row_o<='0; cand_col_o<='0;
            cand_slot_o<='0; cand_is_rd_o<=1'b1; cand_pri_o<='0;
        end else begin
            // if my last candidate was just issued, take the freshly-picked next
            // one; otherwise re-register the current best (it stays legal-checked
            // at the final stage).
            cand_valid_o<=n_valid;
            cand_op_o   <=n_op;
            cand_row_o  <=n_row;
            cand_col_o  <=n_col;
            cand_slot_o <=n_slot;
            cand_is_rd_o<=n_is_rd;
            cand_pri_o  <=n_slot;  // scaffold priority proxy
        end
    end
endmodule
