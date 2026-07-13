// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_rd_cmd_cam
// Purpose: Outstanding-DRAM-read tracker for the AXI4 interface (the MISS
//          path). Mirror of pumice_wr_data_cam: entries keyed {bank,row,col}
//          with a free-running age, an oldest port, and N scheduler lookups so
//          reads row-hit-schedule like writes. Acts as a REORDER BUFFER:
//          DRAM read data returns in ISSUE order and is buffered per entry;
//          it drains to pumice_rd_intake in AR (insert) order.
//
// Data direction (vs the wr CAM): data comes IN from the DFI read return and
// drains OUT to rd_intake. There is no snarf port (that is a write-CAM concept).
//
// Age (wrap-safe via rel = age_ctr - entry_age):
//   * issue-side oldest/lookups -> oldest NOT-YET-ISSUED entry [max rel]
//   * drain-side                -> oldest valid entry, gated on data-ready
//                                  (enforces AR-order release / reorder)
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
    parameter int AXI_DATA_WIDTH  = 64,
    parameter int BL              = 4,
    parameter int AGE_WIDTH       = 16,
    parameter int N_SRAM_SLOTS    = NUM_ENTRIES,

    parameter int IW    = AXI_ID_WIDTH,
    parameter int DW    = AXI_DATA_WIDTH,
    parameter int BKW   = $clog2(NUM_BANKS),
    parameter int PTRW  = $clog2(NUM_ENTRIES),
    parameter int SPTRW = $clog2(N_SRAM_SLOTS),
    parameter int BCW   = $clog2(BL)
) (
    input  logic                          aclk,
    input  logic                          aresetn,

    //=========================================================================
    // Insert (from pumice_rd_intake ar_push, in AR order)
    //=========================================================================
    input  logic                          ins_valid_i,
    output logic                          ins_ready_o,
    input  logic [BKW-1:0]                ins_bank_i,
    input  logic [ROW_WIDTH-1:0]          ins_row_i,
    input  logic [COL_WIDTH-1:0]          ins_col_i,
    input  logic [IW-1:0]                 ins_id_i,

    //=========================================================================
    // Scheduler lookups (N generic, keyed {bank,row}) — oldest NOT-ISSUED match
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
    // Oldest not-issued port (scheduler fallback)
    //=========================================================================
    output logic                          oldest_valid_o,
    output logic [BKW-1:0]                oldest_bank_o,
    output logic [ROW_WIDTH-1:0]          oldest_row_o,
    output logic [COL_WIDTH-1:0]          oldest_col_o,
    output logic [IW-1:0]                 oldest_id_o,
    output logic [PTRW-1:0]               oldest_slot_o,

    //=========================================================================
    // Issue notify (scheduler tells the CAM which slot it issued to DRAM).
    // Records issue order so returns fill the right slot.
    //=========================================================================
    input  logic                          issue_valid_i,
    output logic                          issue_ready_o,
    input  logic [PTRW-1:0]               issue_slot_i,

    //=========================================================================
    // DFI read return (data in, ISSUE order) -> buffered into the issued slot
    //=========================================================================
    input  logic                          dfi_ret_valid_i,
    output logic                          dfi_ret_ready_o,
    input  logic [DW-1:0]                 dfi_ret_data_i,
    input  logic [1:0]                    dfi_ret_resp_i,
    input  logic                          dfi_ret_last_i,

    //=========================================================================
    // Drain to rd_intake dfi_rd source (AR order, oldest-first, ready-gated)
    //=========================================================================
    output logic                          drain_valid_o,
    input  logic                          drain_ready_i,
    output logic [DW-1:0]                 drain_data_o,
    output logic [IW-1:0]                 drain_id_o,
    output logic [1:0]                    drain_resp_o,
    output logic                          drain_last_o,

    output logic                          busy_o
);

    import pumice_pkg::*;

    // ---- entry state -------------------------------------------------------
    logic                 r_valid  [NUM_ENTRIES];
    logic                 r_issued [NUM_ENTRIES];
    logic                 r_ready  [NUM_ENTRIES];   // data complete
    logic [BKW-1:0]       r_bank   [NUM_ENTRIES];
    logic [ROW_WIDTH-1:0] r_row    [NUM_ENTRIES];
    logic [COL_WIDTH-1:0] r_col    [NUM_ENTRIES];
    logic [IW-1:0]        r_id     [NUM_ENTRIES];
    logic [1:0]           r_resp   [NUM_ENTRIES];
    logic [AGE_WIDTH-1:0] r_age    [NUM_ENTRIES];
    logic [SPTRW-1:0]     r_ptr    [NUM_ENTRIES];   // SRAM slot; set on 1st return
    logic                 r_pv     [NUM_ENTRIES];   // ptr_valid
    logic [AGE_WIDTH-1:0] r_age_ctr;

    logic [AGE_WIDTH-1:0] w_rel [NUM_ENTRIES];
    always_comb
        for (int i = 0; i < NUM_ENTRIES; i++)
            w_rel[i] = r_age_ctr - r_age[i];

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

    (* ram_style = "distributed" *)
    logic [DW-1:0] r_sram [N_SRAM_SLOTS*BL];

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

    // ---- issue-order FIFO (slots awaiting DFI return) ----------------------
    logic            w_iq_wr_valid, w_iq_wr_ready, w_iq_rd_valid, w_iq_rd_ready;
    logic [PTRW-1:0] w_iq_rd_slot;

    assign issue_ready_o = w_iq_wr_ready;
    assign w_iq_wr_valid = issue_valid_i;

    gaxi_fifo_sync #(.DATA_WIDTH(PTRW), .DEPTH(NUM_ENTRIES)) u_issue_q (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(w_iq_wr_valid), .wr_ready(w_iq_wr_ready), .wr_data(issue_slot_i),
        .rd_ready(w_iq_rd_ready), .count(), .rd_valid(w_iq_rd_valid), .rd_data(w_iq_rd_slot)
    );

    logic w_issue_fire;
    assign w_issue_fire = issue_valid_i && issue_ready_o;

    // ---- return-fill engine : write DFI data into issue_q head slot --------
    // Pre-allocate a free SRAM slot on the first return beat.
    logic [BCW-1:0] r_ret_beat;
    logic            w_ret_first;
    logic [SPTRW-1:0] w_ret_slot;
    assign w_ret_first = (r_ret_beat == '0);
    assign w_ret_slot  = w_ret_first ? w_slot_free : r_ptr[w_iq_rd_slot];
    assign dfi_ret_ready_o = w_iq_rd_valid && (r_ret_beat != '0 || w_slot_free_found);
    logic w_ret_fire;
    assign w_ret_fire     = dfi_ret_valid_i && dfi_ret_ready_o;
    assign w_iq_rd_ready  = w_ret_fire && dfi_ret_last_i;

    logic [31:0] w_ret_idx;
    assign w_ret_idx = 32'(w_ret_slot) * 32'(BL) + 32'(r_ret_beat);

    // ---- issue-side oldest NOT-ISSUED (max rel among valid && !issued) -----
    logic            w_old_found;
    logic [PTRW-1:0] w_old_slot;
    logic [AGE_WIDTH-1:0] w_old_best;
    always_comb begin
        w_old_found = 1'b0; w_old_slot = '0; w_old_best = '0;
        for (int i = 0; i < NUM_ENTRIES; i++)
            if (r_valid[i] && !r_issued[i] && (!w_old_found || w_rel[i] > w_old_best)) begin
                w_old_found = 1'b1; w_old_best = w_rel[i]; w_old_slot = PTRW'(i);
            end
    end
    assign oldest_valid_o = w_old_found;
    assign oldest_slot_o  = w_old_slot;
    assign oldest_bank_o  = r_bank[w_old_slot];
    assign oldest_row_o   = r_row[w_old_slot];
    assign oldest_col_o   = r_col[w_old_slot];
    assign oldest_id_o    = r_id[w_old_slot];

    // ---- scheduler lookups : oldest NOT-ISSUED match per port --------------
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
                if (r_valid[i] && !r_issued[i] && r_bank[i] == qbank && r_row[i] == qrow)
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

    // ---- drain-side oldest valid (max rel among ALL valid) -----------------
    logic            w_dro_found;
    logic [PTRW-1:0] w_dro_slot;
    logic [AGE_WIDTH-1:0] w_dro_best;
    always_comb begin
        w_dro_found = 1'b0; w_dro_slot = '0; w_dro_best = '0;
        for (int i = 0; i < NUM_ENTRIES; i++)
            if (r_valid[i] && (!w_dro_found || w_rel[i] > w_dro_best)) begin
                w_dro_found = 1'b1; w_dro_best = w_rel[i]; w_dro_slot = PTRW'(i);
            end
    end

    // ---- drain engine : oldest-first, gated on data-ready (AR-order) -------
    // NO active/slot FSM — the draining slot IS the oldest-valid pick
    // (w_dro_slot), which is stable across a burst: the entry stays valid until
    // its own last-beat evict, and later inserts are younger so they can never
    // become "more oldest". Only a burst beat-counter is registered.
    logic [BCW-1:0]  r_dr_beat;
    logic            w_dr_go;
    logic [31:0]     w_dr_idx;
    assign w_dr_go  = w_dro_found && r_ready[w_dro_slot];   // oldest + data staged
    assign w_dr_idx = 32'(r_ptr[w_dro_slot]) * 32'(BL) + 32'(r_dr_beat);

    assign drain_valid_o = w_dr_go;
    assign drain_data_o  = r_sram[w_dr_idx];
    assign drain_id_o    = r_id[w_dro_slot];
    assign drain_resp_o  = r_resp[w_dro_slot];
    assign drain_last_o  = (r_dr_beat == BCW'(BL-1));

    logic w_dr_fire;
    assign w_dr_fire = drain_valid_o && drain_ready_i;

    assign busy_o = w_dro_found || w_iq_rd_valid;

    // ---- sequential --------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_age_ctr   <= '0;
            r_ret_beat  <= '0;
            r_dr_beat   <= '0;
            r_sram_occ  <= '0;
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                r_valid[i]  <= 1'b0;
                r_issued[i] <= 1'b0;
                r_ready[i]  <= 1'b0;
                r_pv[i]     <= 1'b0;
            end
        end else begin
            r_age_ctr <= r_age_ctr + 1'b1;

            // insert
            if (w_ins_fire) begin
                r_valid [w_free_slot] <= 1'b1;
                r_issued[w_free_slot] <= 1'b0;
                r_ready [w_free_slot] <= 1'b0;
                r_bank  [w_free_slot] <= ins_bank_i;
                r_row   [w_free_slot] <= ins_row_i;
                r_col   [w_free_slot] <= ins_col_i;
                r_id    [w_free_slot] <= ins_id_i;
                r_age   [w_free_slot] <= r_age_ctr;
            end

            // issue notify -> mark issued (issue_q push is handled by the FIFO)
            if (w_issue_fire)
                r_issued[issue_slot_i] <= 1'b1;

            // return-fill : allocate SRAM slot on first beat, then write
            if (w_ret_fire) begin
                if (w_ret_first) begin
                    r_ptr[w_iq_rd_slot] <= w_slot_free;
                    r_pv [w_iq_rd_slot] <= 1'b1;
                    r_sram_occ[w_slot_free] <= 1'b1;
                end
                r_sram[w_ret_idx] <= dfi_ret_data_i;
                if (dfi_ret_last_i) begin
                    r_ready[w_iq_rd_slot] <= 1'b1;
                    r_resp [w_iq_rd_slot] <= dfi_ret_resp_i;
                    r_ret_beat <= '0;
                end else begin
                    r_ret_beat <= r_ret_beat + 1'b1;
                end
            end

            // drain (oldest-first, gated on ready): advance the beat counter;
            // evict the head (w_dro_slot) on the last beat. No active latch.
            if (w_dr_fire) begin
                if (drain_last_o) begin
                    r_dr_beat             <= '0;
                    r_valid[w_dro_slot]   <= 1'b0;           // evict entry
                    r_pv   [w_dro_slot]   <= 1'b0;
                    r_sram_occ[r_ptr[w_dro_slot]] <= 1'b0;   // free SRAM slot
                end else begin
                    r_dr_beat <= r_dr_beat + 1'b1;
                end
            end
        end
    )

endmodule : pumice_rd_cmd_cam
