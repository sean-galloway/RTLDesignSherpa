// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_wr_data_cam
// Purpose: Write-command CAM + wr-data SRAM for the AXI4 interface. Holds
//          pending writes keyed on {bank,row,col} with a free-running age, and
//          the burst data in an SRAM slot. Three data movers over the SRAM:
//          fill (on insert), snarf-stream (read-your-writes), commit-stream
//          (drain to DFI write). Plus associative query ports.
//
// Age & selectors (wrap-safe via relative age = age_ctr - entry_age):
//   * snarf lookup      -> YOUNGEST match (latest data for a read)  [min rel]
//   * scheduler lookup  -> OLDEST match   (in-order commit per row) [max rel]
//   * oldest port       -> OLDEST valid   (scheduler fallback)      [max rel]
//
// Documentation: rtl/PUMICE_AXI4_IFC_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_wr_data_cam #(
    parameter int NUM_ENTRIES     = 8,
    parameter int N_SCHED_LU      = 4,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int AXI_ID_WIDTH    = 8,
    parameter int AXI_DATA_WIDTH  = 64,
    parameter int BL              = 4,
    parameter int AGE_WIDTH       = 16,
    parameter int N_SRAM_SLOTS    = NUM_ENTRIES,  // may be < NUM_ENTRIES

    // Derived
    parameter int IW    = AXI_ID_WIDTH,
    parameter int DW    = AXI_DATA_WIDTH,
    parameter int SW    = AXI_DATA_WIDTH / 8,
    parameter int BKW   = $clog2(NUM_BANKS),
    parameter int PTRW  = $clog2(NUM_ENTRIES),
    parameter int SPTRW = $clog2(N_SRAM_SLOTS),
    parameter int BCW   = (BL > 1) ? $clog2(BL) : 1   // beat-counter width (BL=1 => 1b)
) (
    input  logic                          aclk,
    input  logic                          aresetn,

    //=========================================================================
    // Insert command (from pumice_wr_intake aw_push) — allocate a slot
    //=========================================================================
    input  logic                          ins_valid_i,
    output logic                          ins_ready_o,
    input  logic [BKW-1:0]                ins_bank_i,
    input  logic [ROW_WIDTH-1:0]          ins_row_i,
    input  logic [COL_WIDTH-1:0]          ins_col_i,
    input  logic [IW-1:0]                 ins_id_i,

    //=========================================================================
    // Fill data (from wr_intake wdata pop) — written to SRAM in insert order
    //=========================================================================
    input  logic                          wd_valid_i,
    output logic                          wd_ready_o,
    input  logic [DW-1:0]                 wd_data_i,
    input  logic [SW-1:0]                 wd_strb_i,
    input  logic                          wd_last_i,

    //=========================================================================
    // Snarf lookup (from pumice_rd_intake) — youngest match, non-destructive
    //=========================================================================
    input  logic                          snarf_probe_valid_i,
    input  logic [BKW-1:0]                snarf_probe_bank_i,
    input  logic [ROW_WIDTH-1:0]          snarf_probe_row_i,
    input  logic [COL_WIDTH-1:0]          snarf_probe_col_i,
    input  logic [IW-1:0]                 snarf_probe_id_i,   // read AXI id
    input  logic [7:0]                    snarf_probe_len_i,  // read AXI arlen
    output logic                          snarf_hit_o,
    input  logic                          snarf_accept_i,   // admitted as snarf

    // Snarf data stream (accept order)
    output logic                          snarf_rd_valid_o,
    input  logic                          snarf_rd_ready_i,
    output logic [DW-1:0]                 snarf_rd_data_o,
    output logic                          snarf_rd_last_o,

    //=========================================================================
    // Oldest-entry port (always presents min-age valid entry; sched fallback)
    //=========================================================================
    output logic                          oldest_valid_o,
    output logic [BKW-1:0]                oldest_bank_o,
    output logic [ROW_WIDTH-1:0]          oldest_row_o,
    output logic [COL_WIDTH-1:0]          oldest_col_o,
    output logic [IW-1:0]                 oldest_id_o,
    output logic [PTRW-1:0]               oldest_slot_o,

    //=========================================================================
    // Scheduler lookup ports (N generic, keyed {bank,row}) — oldest match
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
    // Commit — stream SRAM[slot] to wr_beat_sequencer, then evict on last
    //=========================================================================
    input  logic                          commit_valid_i,
    output logic                          commit_ready_o,
    input  logic [PTRW-1:0]               commit_slot_i,
    output logic                          cm_rd_valid_o,
    input  logic                          cm_rd_ready_i,
    output logic [DW-1:0]                 cm_rd_data_o,
    output logic [SW-1:0]                 cm_rd_strb_o,
    output logic                          cm_rd_last_o,

    // Commit-done strobe (on evict) -> drives wr_intake B response
    output logic                          commit_done_valid_o,
    output logic [IW-1:0]                 commit_done_id_o,

    output logic                          busy_o
);

    import pumice_pkg::*;

    // ---- entry state -------------------------------------------------------
    logic                    r_valid [NUM_ENTRIES];
    logic [BKW-1:0]          r_bank  [NUM_ENTRIES];
    logic [ROW_WIDTH-1:0]    r_row   [NUM_ENTRIES];
    logic [COL_WIDTH-1:0]    r_col   [NUM_ENTRIES];
    logic [IW-1:0]           r_id    [NUM_ENTRIES];
    logic [AGE_WIDTH-1:0]    r_age   [NUM_ENTRIES];
    logic [SPTRW-1:0]        r_ptr   [NUM_ENTRIES];   // SRAM slot; set on 1st write
    logic                    r_pv    [NUM_ENTRIES];   // ptr_valid (1st beat filled)
    logic                    r_fdone [NUM_ENTRIES];   // fill COMPLETE (wd_last seen)
                                                      // -> only then may the entry be
                                                      // scheduled/snarfed; otherwise the
                                                      // commit-drain can outrun a gapped
                                                      // fill and read stale SRAM beats.
    logic                    r_sched [NUM_ENTRIES];   // scheduler committed this
                                                      // slot -> exclude from
                                                      // sched_lu/oldest (so the
                                                      // arbiter can pick the next
                                                      // entry the very next cycle
                                                      // => clean 1 cmd/clock).
    logic [AGE_WIDTH-1:0]    r_age_ctr;

    // SRAM slot occupancy (pre-allocator), 1 = occupied
    logic [N_SRAM_SLOTS-1:0] r_sram_occ;
    logic                    w_slot_free_found;
    logic [SPTRW-1:0]        w_slot_free;
    always_comb begin
        w_slot_free_found = 1'b0;
        w_slot_free       = '0;
        for (int s = N_SRAM_SLOTS-1; s >= 0; s--)
            if (!r_sram_occ[s]) begin
                w_slot_free_found = 1'b1;
                w_slot_free       = SPTRW'(s);
            end
    end

    // relative age (how long ago inserted) — wrap-safe ordering
    logic [AGE_WIDTH-1:0]    w_rel [NUM_ENTRIES];
    always_comb
        for (int i = 0; i < NUM_ENTRIES; i++)
            w_rel[i] = r_age_ctr - r_age[i];

    // ---- SRAM (NUM_ENTRIES * BL beats) -------------------------------------
    (* ram_style = "distributed" *)
    logic [DW-1:0] r_sram  [N_SRAM_SLOTS*BL];
    logic [SW-1:0] r_strb  [N_SRAM_SLOTS*BL];

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

    // ---- fill FIFO (slots pending data) ------------------------------------
    logic             w_fq_wr_valid, w_fq_wr_ready, w_fq_rd_valid, w_fq_rd_ready;
    logic [PTRW-1:0]  w_fq_wr_slot,  w_fq_rd_slot;

    assign ins_ready_o   = w_have_free && w_fq_wr_ready;
    assign w_fq_wr_valid = ins_valid_i && w_have_free;
    assign w_fq_wr_slot  = w_free_slot;

    gaxi_fifo_sync #(.DATA_WIDTH(PTRW), .DEPTH(NUM_ENTRIES)) u_fill_q (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(w_fq_wr_valid), .wr_ready(w_fq_wr_ready), .wr_data(w_fq_wr_slot),
        .rd_ready(w_fq_rd_ready), .count(), .rd_valid(w_fq_rd_valid), .rd_data(w_fq_rd_slot)
    );

    logic w_ins_fire;
    assign w_ins_fire = ins_valid_i && ins_ready_o;

    // ---- fill engine : write burst into SRAM[ptr] --------------------------
    // On the first beat a free SRAM slot must be available (pre-allocate).
    logic [BCW-1:0] r_fill_beat;
    assign wd_ready_o = w_fq_rd_valid && (r_fill_beat != '0 || w_slot_free_found);
    logic w_wd_fire;
    assign w_wd_fire = wd_valid_i && wd_ready_o;
    assign w_fq_rd_ready = w_wd_fire && wd_last_i;

    // ---- snarf youngest-match (combinational) ------------------------------
    // Read-your-write forwarding is LIMITED to the safe case: the read may snarf
    // a write only when
    //   (1) the write is NOT yet scheduled (!r_sched) — a scheduled write is
    //       draining/evicting to DRAM, so its CAM data is racy;
    //   (2) the AXI ids match — same-id W-before-R is the only AXI-ordered case
    //       where the read is REQUIRED to see the write (cross-id has no ordering
    //       guarantee, so the read takes the DRAM path instead);
    //   (3) the read's burst length equals the write's. Every admitted write is
    //       exactly BL beats (ragged bursts are rejected in pumice_wr_intake), so
    //       this reduces to arlen == BL-1 — a short/long read must not snarf a
    //       full-BL write.
    logic            w_sn_found;
    logic [PTRW-1:0] w_sn_slot;
    logic [AGE_WIDTH-1:0] w_sn_best;   // min rel among matches
    logic            w_sn_len_ok;
    assign w_sn_len_ok = (snarf_probe_len_i == 8'(BL - 1));
    always_comb begin
        w_sn_found = 1'b0;
        w_sn_slot  = '0;
        w_sn_best  = '0;
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            if (r_valid[i] && r_fdone[i] && !r_sched[i] &&
                r_id[i]  == snarf_probe_id_i &&
                r_bank[i] == snarf_probe_bank_i &&
                r_row[i] == snarf_probe_row_i && r_col[i] == snarf_probe_col_i) begin
                if (!w_sn_found || w_rel[i] < w_sn_best) begin
                    w_sn_found = 1'b1;
                    w_sn_best  = w_rel[i];
                    w_sn_slot  = PTRW'(i);
                end
            end
        end
    end
    assign snarf_hit_o = snarf_probe_valid_i && w_sn_found && w_sn_len_ok;

    // ---- oldest valid (max rel) --------------------------------------------
    logic            w_old_found;
    logic [PTRW-1:0] w_old_slot;
    logic [AGE_WIDTH-1:0] w_old_best;
    always_comb begin
        w_old_found = 1'b0;
        w_old_slot  = '0;
        w_old_best  = '0;
        // exclude already-scheduled + not-yet-fully-filled entries so the arbiter
        // never commits a write whose data isn't fully staged (drain-vs-fill race).
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            if (r_valid[i] && r_fdone[i] && !r_sched[i] && (!w_old_found || w_rel[i] > w_old_best)) begin
                w_old_found = 1'b1;
                w_old_best  = w_rel[i];
                w_old_slot  = PTRW'(i);
            end
        end
    end
    assign oldest_valid_o = w_old_found;
    assign oldest_slot_o  = w_old_slot;
    assign oldest_bank_o  = r_bank[w_old_slot];
    assign oldest_row_o   = r_row[w_old_slot];
    assign oldest_col_o   = r_col[w_old_slot];
    assign oldest_id_o    = r_id[w_old_slot];

    // ---- scheduler lookups : oldest match per port (max rel) ---------------
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
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                if (r_valid[i] && r_fdone[i] && !r_sched[i] && r_bank[i] == qbank && r_row[i] == qrow) begin
                    if (!found || w_rel[i] > best) begin
                        found = 1'b1; best = w_rel[i]; slot = PTRW'(i);
                    end
                end
            end
            sched_lu_hit_o [j]                     = sched_lu_valid_i[j] && found;
            sched_lu_slot_o[j*PTRW      +: PTRW]   = slot;
            sched_lu_col_o [j*COL_WIDTH +: COL_WIDTH] = r_col[slot];
            sched_lu_id_o  [j*IW        +: IW]     = r_id[slot];
            sched_lu_age_o [j*AGE_WIDTH +: AGE_WIDTH] = best;
        end
    end

    // ---- snarf-stream request FIFO (slots to stream, in accept order) ------
    logic            w_sq_wr_valid, w_sq_wr_ready, w_sq_rd_valid, w_sq_rd_ready;
    logic [PTRW-1:0] w_sq_rd_slot;

    assign w_sq_wr_valid = snarf_accept_i && snarf_hit_o;

    gaxi_fifo_sync #(.DATA_WIDTH(PTRW), .DEPTH(NUM_ENTRIES)) u_snarf_q (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(w_sq_wr_valid), .wr_ready(w_sq_wr_ready), .wr_data(w_sn_slot),
        .rd_ready(w_sq_rd_ready), .count(), .rd_valid(w_sq_rd_valid), .rd_data(w_sq_rd_slot)
    );

    // ---- commit (scheduled-slot) drain FIFO --------------------------------
    // The arbiter's commit marks a slot scheduled (1 cycle, excluded from
    // sched_lu/oldest immediately => 1 cmd/clock) and enqueues it here. The
    // drain read-engine works through scheduled slots at its own pace, streaming
    // cm_rd to the DFI layer and evicting on last. Decouples marking from drain.
    logic            w_dq_wr_valid, w_dq_wr_ready, w_dq_rd_valid, w_dq_rd_ready;
    logic [PTRW-1:0] w_dq_rd_slot;

    logic w_commit_fire;
    assign w_commit_fire = commit_valid_i && commit_ready_o;
    assign commit_ready_o = w_dq_wr_ready;    // room in the drain FIFO
    assign w_dq_wr_valid  = commit_valid_i;

    gaxi_fifo_sync #(.DATA_WIDTH(PTRW), .DEPTH(NUM_ENTRIES)) u_drain_q (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(w_dq_wr_valid), .wr_ready(w_dq_wr_ready), .wr_data(commit_slot_i),
        .rd_ready(w_dq_rd_ready), .count(), .rd_valid(w_dq_rd_valid), .rd_data(w_dq_rd_slot)
    );

    // Fill target SRAM slot: allocate a free slot on the first beat, else reuse
    // the slot already recorded in the entry's ptr.
    logic            w_fill_first;
    logic [SPTRW-1:0] w_fill_slot;
    assign w_fill_first = (r_fill_beat == '0);
    assign w_fill_slot  = w_fill_first ? w_slot_free : r_ptr[w_fq_rd_slot];

    // Engine state: just a burst beat-counter each — NO active/slot FSM. Both
    // readers stream straight off their request-FIFO head (stable until popped),
    // exactly like the fill engine reads its fill FIFO. The head slot IS the
    // "active" slot; "active" == FIFO non-empty; the slot FIFO is popped on the
    // last beat. (declared before the index helpers that reference them)
    logic [BCW-1:0]  r_sn_beat;   // snarf-stream beat within the burst
    logic [BCW-1:0]  r_cm_beat;   // commit-drain beat within the burst

    // SRAM flat-index helpers (index by the FIFO-head slot's ptr; 32-bit width)
    logic [31:0] w_sn_idx, w_cm_idx, w_fill_idx;
    assign w_sn_idx   = 32'(r_ptr[w_sq_rd_slot]) * 32'(BL) + 32'(r_sn_beat);
    assign w_cm_idx   = 32'(r_ptr[w_dq_rd_slot]) * 32'(BL) + 32'(r_cm_beat);
    assign w_fill_idx = 32'(w_fill_slot)         * 32'(BL) + 32'(r_fill_beat);

    // ---- snarf read engine (FIFO-fed, beat-counter only) -------------------
    assign snarf_rd_valid_o = w_sq_rd_valid;                 // a slot is queued
    assign snarf_rd_data_o  = r_sram[w_sn_idx];
    assign snarf_rd_last_o  = (r_sn_beat == BCW'(BL-1));

    // ---- commit drain read-engine + evict (FIFO-fed, beat-counter only) ----
    assign cm_rd_valid_o  = w_dq_rd_valid;                   // a slot is queued
    assign cm_rd_data_o   = r_sram[w_cm_idx];
    assign cm_rd_strb_o   = r_strb[w_cm_idx];
    assign cm_rd_last_o   = (r_cm_beat == BCW'(BL-1));

    logic w_sn_fire, w_cm_fire;
    assign w_sn_fire = snarf_rd_valid_o && snarf_rd_ready_i;
    assign w_cm_fire = cm_rd_valid_o    && cm_rd_ready_i;

    // pop the request FIFO once the final beat of the burst is accepted
    assign w_sq_rd_ready  = w_sn_fire && snarf_rd_last_o;
    assign w_dq_rd_ready  = w_cm_fire && cm_rd_last_o;

    assign commit_done_valid_o = w_cm_fire && cm_rd_last_o;
    assign commit_done_id_o    = r_id[w_dq_rd_slot];

    assign busy_o = w_old_found || w_sq_rd_valid || w_dq_rd_valid || w_fq_rd_valid;

    // ---- sequential --------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_age_ctr   <= '0;
            r_fill_beat <= '0;
            r_sn_beat   <= '0;
            r_cm_beat   <= '0;
            r_sram_occ  <= '0;
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                r_valid[i] <= 1'b0;
                r_pv[i]    <= 1'b0;
                r_fdone[i] <= 1'b0;
                r_sched[i] <= 1'b0;
            end
        end else begin
            r_age_ctr <= r_age_ctr + 1'b1;

            // insert : allocate + capture key/id/age; fill not yet done
            if (w_ins_fire) begin
                r_valid[w_free_slot] <= 1'b1;
                r_bank [w_free_slot] <= ins_bank_i;
                r_row  [w_free_slot] <= ins_row_i;
                r_col  [w_free_slot] <= ins_col_i;
                r_id   [w_free_slot] <= ins_id_i;
                r_age  [w_free_slot] <= r_age_ctr;
                r_fdone[w_free_slot] <= 1'b0;
            end

            // fill : allocate SRAM slot on first beat, then write burst. Mark the
            // entry fill-COMPLETE on the last beat so it becomes schedulable/
            // snarfable only once every beat is staged in SRAM.
            if (w_wd_fire) begin
                if (w_fill_first) begin
                    r_ptr[w_fq_rd_slot]  <= w_slot_free;
                    r_pv [w_fq_rd_slot]  <= 1'b1;
                    r_sram_occ[w_slot_free] <= 1'b1;
                end
                r_sram[w_fill_idx] <= wd_data_i;
                r_strb[w_fill_idx] <= wd_strb_i;
                r_fill_beat <= wd_last_i ? '0 : (r_fill_beat + 1'b1);
                if (wd_last_i) r_fdone[w_fq_rd_slot] <= 1'b1;
            end

            // snarf read engine: advance the beat counter; the head slot is
            // popped combinationally (w_sq_rd_ready) on the last beat.
            if (w_sn_fire)
                r_sn_beat <= snarf_rd_last_o ? '0 : (r_sn_beat + 1'b1);

            // commit MARK: the arbiter's commit sets scheduled (immediate) +
            // enqueues the slot into the drain FIFO. Excluded from sched_lu/
            // oldest next cycle => arbiter can pick another slot right away.
            if (w_commit_fire)
                r_sched[commit_slot_i] <= 1'b1;

            // commit DRAIN read-engine + evict on last (sourced from drain FIFO;
            // the head slot is popped combinationally on the last beat). The
            // draining slot is the FIFO head (w_dq_rd_slot), stable until pop.
            if (w_cm_fire) begin
                if (cm_rd_last_o) begin
                    r_cm_beat              <= '0;
                    r_valid[w_dq_rd_slot]  <= 1'b0;          // evict entry
                    r_pv   [w_dq_rd_slot]  <= 1'b0;
                    r_fdone[w_dq_rd_slot]  <= 1'b0;
                    r_sched[w_dq_rd_slot]  <= 1'b0;
                    r_sram_occ[r_ptr[w_dq_rd_slot]] <= 1'b0; // free SRAM slot
                end else begin
                    r_cm_beat <= r_cm_beat + 1'b1;
                end
            end
        end
    )

endmodule : pumice_wr_data_cam
