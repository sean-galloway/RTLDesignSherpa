// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_rd_cmd_cam
// Purpose: Read SCHEDULING window for the AXI4 interface (the MISS path).
//          Mirror of pumice_wr_data_cam's scheduling side: entries keyed
//          {bank,row,col} with a free-running age, an age-order matrix, and the
//          per-entry scheduling vectors the arbiter picks from.
//
//          An entry lives from INSERT to ISSUE only. The read's return is owned
//          by pumice_rd_return_ring: the ring hands out a TICKET at insert (AR
//          order), the CAM stores it, and on the arbiter's issue notify the CAM
//          frees the entry and forwards the ticket to the ring's issue-order
//          FIFO. So NUM_ENTRIES is the scheduling window and nothing else; the
//          in-flight read count is the ring's DEPTH.
//
//          (Until 2026-09-08 this CAM also buffered the returned data and
//          drained it in AR order, so an entry lived for the whole DRAM round
//          trip and eight entries bounded read bandwidth by Little's law to
//          ~180 MB/s on the board. See design/README.md.)
//
// Age (wrap-safe via rel = age_ctr - entry_age):
//   * issue-side oldest/lookups -> oldest valid entry [max rel]
//
// Documentation: rtl/PUMICE_AXI4_IFC_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_rd_cmd_cam #(
    parameter int NUM_ENTRIES     = 8,
    parameter int N_SCHED_LU      = 4,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int AXI_ID_WIDTH    = 8,
    parameter int AGE_WIDTH       = 16,
    parameter int RD_RET_DEPTH    = 32,   // pumice_rd_return_ring DEPTH (ticket space)

    parameter int IW    = AXI_ID_WIDTH,
    parameter int BKW   = $clog2(NUM_BANKS),
    parameter int PTRW  = $clog2(NUM_ENTRIES),
    parameter int TW    = $clog2(RD_RET_DEPTH)
) (
    input  logic                          aclk,
    input  logic                          aresetn,

    //=========================================================================
    // Insert (from pumice_rd_intake ar_push, in AR order) + the ring's ticket
    //=========================================================================
    input  logic                          ins_valid_i,
    output logic                          ins_ready_o,
    input  logic [BKW-1:0]                ins_bank_i,
    input  logic [ROW_WIDTH-1:0]          ins_row_i,
    input  logic [COL_WIDTH-1:0]          ins_col_i,
    input  logic [IW-1:0]                 ins_id_i,
    input  logic [3:0]                    ins_qos_i,     // AxQOS (QOS_EN pick)
    input  logic [TW-1:0]                 ins_ticket_i,  // return-ring slot

    //=========================================================================
    // Scheduler lookups (N generic, keyed {bank,row}) — oldest match
    //=========================================================================
    input  logic [N_SCHED_LU-1:0]             sched_lu_valid_i,
    input  logic [N_SCHED_LU*BKW-1:0]         sched_lu_bank_i,
    input  logic [N_SCHED_LU*ROW_WIDTH-1:0]   sched_lu_row_i,
    output logic [N_SCHED_LU-1:0]             sched_lu_hit_o,
    output logic [N_SCHED_LU*PTRW-1:0]        sched_lu_slot_o,
    output logic [N_SCHED_LU*COL_WIDTH-1:0]   sched_lu_col_o,
    output logic [N_SCHED_LU*IW-1:0]          sched_lu_id_o,
    output logic [N_SCHED_LU*AGE_WIDTH-1:0]   sched_lu_age_o,

    //=========================================================================
    // Per-entry scheduling vectors (registered fields; the scheduler does the
    // match + argmax itself -> bank-parallel activation, no lookup round-trip).
    // Indexed by entry slot. sch_valid = schedulable (valid; issue frees).
    //=========================================================================
    output logic [NUM_ENTRIES-1:0]              sch_valid_o,
    output logic [NUM_ENTRIES*BKW-1:0]          sch_bank_o,
    output logic [NUM_ENTRIES*ROW_WIDTH-1:0]    sch_row_o,
    output logic [NUM_ENTRIES*COL_WIDTH-1:0]    sch_col_o,
    // age-order matrix (flattened): bit [i*NUM_ENTRIES + j] = entry i is OLDER
    // than entry j. 1-bit compares on the scheduler path (vs a 16-bit age key).
    output logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  sch_older_o,
    // SCHED_POLICY.age_thresh (MC cycles / 16; 0 = off): per-entry flag that
    // the entry's relative age crossed the threshold — the 1-bit "boost" key
    // for the age_threshold order mode (numeric ages never leave the CAM).
    input  logic [7:0]                          age_thresh_i,
    output logic [NUM_ENTRIES-1:0]              sch_age_exceed_o,
    // per-entry AxQOS, flattened (QOS_EN arbiter key)
    output logic [NUM_ENTRIES*4-1:0]            sch_qos_o,
    // relative age of the oldest SCHEDULABLE entry (0 when none): the
    // cross-CAM ordering key for the in_order mode. Comparable across CAMs
    // because every CAM age counter free-runs from reset (same epoch).
    output logic [AGE_WIDTH-1:0]                sch_head_rel_o,

    //=========================================================================
    // Oldest port (scheduler fallback)
    //=========================================================================
    output logic                          oldest_valid_o,
    output logic [BKW-1:0]                oldest_bank_o,
    output logic [ROW_WIDTH-1:0]          oldest_row_o,
    output logic [COL_WIDTH-1:0]          oldest_col_o,
    output logic [IW-1:0]                 oldest_id_o,
    output logic [PTRW-1:0]               oldest_slot_o,

    //=========================================================================
    // Issue notify (scheduler tells the CAM which slot it issued to DRAM).
    // Frees the entry and forwards its ticket to the return ring, which is
    // where issue_ready comes from (the ring's issue-order FIFO).
    //=========================================================================
    input  logic                          issue_valid_i,
    output logic                          issue_ready_o,
    input  logic [PTRW-1:0]               issue_slot_i,
    output logic                          iss_valid_o,
    input  logic                          iss_ready_i,
    output logic [TW-1:0]                 iss_ticket_o,

    output logic                          busy_o
);

    import pumice_pkg::*;

    // ---- entry state -------------------------------------------------------
    logic                 r_valid  [NUM_ENTRIES];
    logic [BKW-1:0]       r_bank   [NUM_ENTRIES];
    logic [ROW_WIDTH-1:0] r_row    [NUM_ENTRIES];
    logic [COL_WIDTH-1:0] r_col    [NUM_ENTRIES];
    logic [IW-1:0]        r_id     [NUM_ENTRIES];
    logic [3:0]           r_qos    [NUM_ENTRIES];
    logic [TW-1:0]        r_ticket [NUM_ENTRIES];
    logic [AGE_WIDTH-1:0] r_age    [NUM_ENTRIES];
    logic [AGE_WIDTH-1:0] r_age_ctr;

    // Age-order matrix: r_older[i][j] = entry i inserted strictly before j (i
    // older). Maintained on INSERT only; replaces the 16-bit age argmax key on
    // the scheduler path with 1-bit compares.
    logic [NUM_ENTRIES-1:0] r_older [NUM_ENTRIES];

    logic [AGE_WIDTH-1:0] w_rel [NUM_ENTRIES];
    always_comb
        for (int i = 0; i < NUM_ENTRIES; i++)
            w_rel[i] = r_age_ctr - r_age[i];

    // ---- free-slot allocation ----------------------------------------------
    logic            w_have_free;
    logic [PTRW-1:0] w_free_slot;
    always_comb begin
        w_have_free = 1'b0;
        w_free_slot = '0;
        for (int i = NUM_ENTRIES-1; i >= 0; i--)
            if (!r_valid[i]) begin
                w_have_free = 1'b1;
                w_free_slot = PTRW'(i);
            end
    end

    logic w_ins_fire;
    assign ins_ready_o = w_have_free;
    assign w_ins_fire  = ins_valid_i && ins_ready_o;

    // ---- issue: free the entry, forward its ticket -------------------------
    logic w_issue_fire;
    assign issue_ready_o = iss_ready_i;
    assign w_issue_fire  = issue_valid_i && issue_ready_o;
    assign iss_valid_o   = issue_valid_i;
    assign iss_ticket_o  = r_ticket[issue_slot_i];

    // ---- issue-side oldest valid (max rel) ---------------------------------
    logic            w_old_found;
    logic [PTRW-1:0] w_old_slot;
    logic [AGE_WIDTH-1:0] w_old_best;
    always_comb begin
        w_old_found = 1'b0; w_old_slot = '0; w_old_best = '0;
        for (int i = 0; i < NUM_ENTRIES; i++)
            if (r_valid[i] && (!w_old_found || w_rel[i] > w_old_best)) begin
                w_old_found = 1'b1; w_old_best = w_rel[i]; w_old_slot = PTRW'(i);
            end
    end
    assign oldest_valid_o = w_old_found;
    assign oldest_slot_o  = w_old_slot;
    assign oldest_bank_o  = r_bank[w_old_slot];
    assign oldest_row_o   = r_row[w_old_slot];
    assign oldest_col_o   = r_col[w_old_slot];
    assign oldest_id_o    = r_id[w_old_slot];

    // ---- scheduler lookups : oldest match per port -------------------------
    always_comb begin
        for (int j = 0; j < N_SCHED_LU; j++) begin
            logic                 found;
            logic [PTRW-1:0]      slot;
            logic [AGE_WIDTH-1:0] best;
            logic [BKW-1:0]       qbank;
            logic [ROW_WIDTH-1:0] qrow;
            found = 1'b0; slot = '0; best = '0;
            qbank = sched_lu_bank_i[j*BKW +: BKW];
            qrow  = sched_lu_row_i [j*ROW_WIDTH +: ROW_WIDTH];
            for (int i = 0; i < NUM_ENTRIES; i++)
                if (r_valid[i] && r_bank[i] == qbank && r_row[i] == qrow)
                    if (!found || w_rel[i] > best) begin
                        found = 1'b1; best = w_rel[i]; slot = PTRW'(i);
                    end
            sched_lu_hit_o [j]                        = sched_lu_valid_i[j] && found;
            sched_lu_slot_o[j*PTRW      +: PTRW]      = slot;
            sched_lu_col_o [j*COL_WIDTH +: COL_WIDTH] = r_col[slot];
            sched_lu_id_o  [j*IW        +: IW]        = r_id[slot];
            sched_lu_age_o [j*AGE_WIDTH +: AGE_WIDTH] = best;
        end
    end

    // ---- scheduler-side oldest SCHEDULABLE entry, via the age-order matrix --
    // The obvious form -- a max-reduce over w_rel[] -- is a SERIAL chain of
    // NUM_ENTRIES x (AGE_WIDTH subtract + compare + mux) that puts the
    // free-running r_age_ctr straight onto the w_sys_i scheduling path (63.6 ns
    // against a 15 ns period on the first synthesis after the mode work,
    // PUMICE-017). The matrix is registered and its compares are 1 bit, so the
    // oldest costs a shallow NUM_ENTRIES^2 AND-reduce; only the winner's
    // relative age needs the AGE_WIDTH subtract.
    logic            w_sho_found;
    logic [PTRW-1:0] w_sho_slot;
    always_comb begin
        automatic logic [NUM_ENTRIES-1:0] w_sho_is;
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            automatic logic ge_all = 1'b1;
            for (int j = 0; j < NUM_ENTRIES; j++)
                if ((j != i) && r_valid[j] && !r_older[i][j]) ge_all = 1'b0;
            w_sho_is[i] = r_valid[i] && ge_all;
        end
        w_sho_found = |w_sho_is;
        w_sho_slot  = '0;
        for (int i = NUM_ENTRIES-1; i >= 0; i--)
            if (w_sho_is[i]) w_sho_slot = PTRW'(i);
    end

    // ---- per-entry scheduling vectors (registered fields, 1-level derive) ---
    always_comb begin
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            sch_valid_o[i]                        = r_valid[i];
            sch_bank_o [i*BKW       +: BKW]       = r_bank[i];
            sch_row_o  [i*ROW_WIDTH +: ROW_WIDTH] = r_row[i];
            sch_col_o  [i*COL_WIDTH +: COL_WIDTH] = r_col[i];
            sch_older_o[i*NUM_ENTRIES +: NUM_ENTRIES] = r_older[i];
            sch_qos_o[i*4 +: 4] = r_qos[i];
            sch_age_exceed_o[i] = r_valid[i]
                                && (age_thresh_i != 8'd0)
                                && (w_rel[i] >= AGE_WIDTH'({age_thresh_i, 4'h0}));
        end
        sch_head_rel_o = w_sho_found ? w_rel[w_sho_slot] : '0;
    end

    always_comb begin
        busy_o = 1'b0;
        for (int i = 0; i < NUM_ENTRIES; i++)
            if (r_valid[i]) busy_o = 1'b1;
    end

    // ---- sequential --------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_age_ctr <= '0;
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                r_valid[i] <= 1'b0;
                r_older[i] <= '0;
            end
        end else begin
            r_age_ctr <= r_age_ctr + 1'b1;

            // insert
            if (w_ins_fire) begin
                r_valid [w_free_slot] <= 1'b1;
                r_bank  [w_free_slot] <= ins_bank_i;
                r_row   [w_free_slot] <= ins_row_i;
                r_col   [w_free_slot] <= ins_col_i;
                r_id    [w_free_slot] <= ins_id_i;
                r_qos   [w_free_slot] <= ins_qos_i;
                r_ticket[w_free_slot] <= ins_ticket_i;
                r_age   [w_free_slot] <= r_age_ctr;
                // age matrix: new slot is YOUNGEST -> older than nobody, and
                // every other slot is older than it.
                for (int j = 0; j < NUM_ENTRIES; j++) begin
                    r_older[w_free_slot][j] <= 1'b0;
                    if (j != int'(w_free_slot)) r_older[j][w_free_slot] <= 1'b1;
                end
            end

            // issue -> the entry is done here; the ring owns the return
            if (w_issue_fire)
                r_valid[issue_slot_i] <= 1'b0;
        end
    )

`ifndef SYNTHESIS
    always @(posedge aclk)
        if (aresetn) begin
            assert (!(w_issue_fire && !r_valid[issue_slot_i]))
              else $error("RD_CAM @%0t: issue of slot %0d which is NOT valid", $time, issue_slot_i);
        end
`endif

endmodule : pumice_rd_cmd_cam
