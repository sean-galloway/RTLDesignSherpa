// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_xddr2_entry_store
// Purpose: Minimal in-order entry store for the storage-less v2 product SKU
//          (granite).  Holds one entry per direction (WR and RD) — enough to
//          satisfy common_has ch5.2's "entry store can shrink toward one, never
//          to zero" rule while presenting the scheduler's 1-wide schedulable-
//          entry vectors.  Write data is staged in a small parameterised FIFO
//          so the DFI write path never runs dry.
//
//          The AXI4 layer pushes descriptors (aw_push / ar_push) and write-data
//          beats; the scheduler commits issues and the entry store drains write
//          data to the DFI layer.  Read tickets are passed through to the AXI4
//          return ring at issue time.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_xddr2_entry_store
    import mc_common_pkg::*;
#(
    parameter int NUM_ENTRIES        = 1,   // ch5.2: never zero
    parameter int AXI_ID_WIDTH       = 8,
    parameter int AXI_DATA_WIDTH     = 64,
    parameter int NUM_RANKS          = 1,
    parameter int NUM_BANKS          = 8,
    parameter int ROW_WIDTH          = 14,
    parameter int COL_WIDTH          = 10,
    parameter int AXI_BEATS_PER_BURST = 4,
    parameter int RD_RET_DEPTH       = 32,
    parameter int WR_DATA_BUF_WORDS  = 16,

    // Derived
    parameter int IW   = AXI_ID_WIDTH,
    parameter int DW   = AXI_DATA_WIDTH,
    parameter int SW   = AXI_DATA_WIDTH / 8,
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int PTRW = (NUM_ENTRIES > 1) ? $clog2(NUM_ENTRIES) : 1,
    parameter int RTW  = $clog2(RD_RET_DEPTH)
) (
    input  logic                     aclk,
    input  logic                     aresetn,

    //=========================================================================
    // WR descriptor push from mc_axi4_layer
    //=========================================================================
    input  logic                aw_push_valid_i,
    output logic                aw_push_ready_o,
    input  logic [BKW-1:0]      aw_push_bank_i,
    input  logic [ROW_WIDTH-1:0]aw_push_row_i,
    input  logic [COL_WIDTH-1:0]aw_push_col_i,
    input  logic [IW-1:0]       aw_push_id_i,
    input  logic [3:0]          aw_push_qos_i,
    input  logic                aw_push_agg_i,
    input  logic                aw_push_last_i,

    //=========================================================================
    // WR data from mc_axi4_layer -> staging FIFO
    //=========================================================================
    input  logic                wd_valid_i,
    output logic                wd_ready_o,
    input  logic [DW-1:0]       wd_data_i,
    input  logic [SW-1:0]       wd_strb_i,
    input  logic                wd_last_i,

    //=========================================================================
    // WR done back to mc_axi4_layer (B response trigger)
    //=========================================================================
    output logic                wr_done_valid_o,
    output logic [IW-1:0]       wr_done_id_o,

    //=========================================================================
    // RD snarf probe from mc_axi4_layer (storage-lite: hit tied off)
    //=========================================================================
    input  logic                snarf_probe_valid_i,
    input  logic [BKW-1:0]      snarf_probe_bank_i,
    input  logic [ROW_WIDTH-1:0]snarf_probe_row_i,
    input  logic [COL_WIDTH-1:0]snarf_probe_col_i,
    input  logic [IW-1:0]       snarf_probe_id_i,
    input  logic [7:0]          snarf_probe_len_i,
    output logic                snarf_hit_o,
    input  logic                snarf_accept_i,
    output logic                snarf_rd_valid_o,
    input  logic                snarf_rd_ready_i,
    output logic [DW-1:0]       snarf_rd_data_o,
    output logic                snarf_rd_last_o,

    //=========================================================================
    // RD descriptor push from mc_axi4_layer
    //=========================================================================
    input  logic                ar_push_valid_i,
    output logic                ar_push_ready_o,
    input  logic [BKW-1:0]      ar_push_bank_i,
    input  logic [ROW_WIDTH-1:0]ar_push_row_i,
    input  logic [COL_WIDTH-1:0]ar_push_col_i,
    input  logic [IW-1:0]       ar_push_id_i,
    input  logic [3:0]          ar_push_qos_i,

    //=========================================================================
    // Return-ring allocation/issue handshake with mc_axi4_layer
    //=========================================================================
    input  logic                rt_alloc_ready_i,
    input  logic [RTW-1:0]      rt_alloc_ticket_i,
    input  logic                rd_iss_ready_i,
    output logic                rd_iss_valid_o,
    output logic [RTW-1:0]      rd_iss_ticket_o,
    output logic                rd_cam_ins_ready_o,

    //=========================================================================
    // Scheduler commit / issue
    //=========================================================================
    input  logic [7:0]          sched_age_thresh_i,
    input  logic                wr_commit_valid_i,
    output logic                wr_commit_ready_o,
    input  logic [PTRW-1:0]     wr_commit_slot_i,
    input  logic                rd_issue_valid_i,
    output logic                rd_issue_ready_o,
    input  logic [PTRW-1:0]     rd_issue_slot_i,

    //=========================================================================
    // Scheduler vectors (NUM_ENTRIES-wide; only slot 0 is populated)
    //=========================================================================
    output logic [NUM_ENTRIES-1:0]              wr_sch_valid_o,
    output logic [NUM_ENTRIES*BKW-1:0]          wr_sch_bank_o,
    output logic [NUM_ENTRIES*ROW_WIDTH-1:0]    wr_sch_row_o,
    output logic [NUM_ENTRIES*COL_WIDTH-1:0]    wr_sch_col_o,
    output logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  wr_sch_older_o,
    output logic [NUM_ENTRIES-1:0]              wr_sch_age_exceed_o,
    output logic [NUM_ENTRIES*4-1:0]            wr_sch_qos_o,
    output logic [15:0]                         wr_sch_head_rel_o,

    output logic [NUM_ENTRIES-1:0]              rd_sch_valid_o,
    output logic [NUM_ENTRIES*BKW-1:0]          rd_sch_bank_o,
    output logic [NUM_ENTRIES*ROW_WIDTH-1:0]    rd_sch_row_o,
    output logic [NUM_ENTRIES*COL_WIDTH-1:0]    rd_sch_col_o,
    output logic [NUM_ENTRIES*NUM_ENTRIES-1:0]  rd_sch_older_o,
    output logic [NUM_ENTRIES-1:0]              rd_sch_age_exceed_o,
    output logic [NUM_ENTRIES*4-1:0]            rd_sch_qos_o,
    output logic [15:0]                         rd_sch_head_rel_o,

    //=========================================================================
    // WR commit data to DFI layer
    //=========================================================================
    output logic                wr_cm_rd_valid_o,
    input  logic                wr_cm_rd_ready_i,
    output logic [DW-1:0]       wr_cm_rd_data_o,
    output logic [SW-1:0]       wr_cm_rd_strb_o,
    output logic                wr_cm_rd_last_o,

    output logic                busy_o
);

    localparam int WDFIFO_DW = 1 + SW + DW; // {last, strb, data}

    // ======================================================================
    // WR entry register
    // ======================================================================
    logic                r_wr_valid;
    logic                r_wr_fdone;
    logic                r_wr_sched;
    logic [BKW-1:0]      r_wr_bank;
    logic [ROW_WIDTH-1:0]r_wr_row;
    logic [COL_WIDTH-1:0]r_wr_col;
    logic [IW-1:0]       r_wr_id;
    logic [3:0]          r_wr_qos;
    logic                r_wr_agg;
    logic                r_wr_last;

    logic                w_aw_fire;
    logic                w_wd_fire;
    logic                w_commit_fire;
    logic                w_cm_fire;
    logic                w_last_beat;

    // WR data staging FIFO nets (declared before use by wd_ready_o)
    logic                w_wdfifo_wr_valid, w_wdfifo_wr_ready;
    logic [WDFIFO_DW-1:0] w_wdfifo_wr_data;
    logic                w_wdfifo_rd_valid, w_wdfifo_rd_ready;
    logic [WDFIFO_DW-1:0] w_wdfifo_rd_raw;
    logic                w_wdfifo_rd_last;
    logic [SW-1:0]       w_wdfifo_rd_strb;
    logic [DW-1:0]       w_wdfifo_rd_data;

    assign w_aw_fire    = aw_push_valid_i && aw_push_ready_o;
    assign w_wd_fire    = wd_valid_i && wd_ready_o;
    assign w_commit_fire= wr_commit_valid_i && wr_commit_ready_o;
    assign w_cm_fire    = wr_cm_rd_valid_o && wr_cm_rd_ready_i;

    assign aw_push_ready_o = !r_wr_valid;
    assign wd_ready_o      = r_wr_valid && w_wdfifo_wr_ready;
    assign wr_commit_ready_o = r_wr_valid && r_wr_fdone && !r_wr_sched;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_valid <= 1'b0;
            r_wr_fdone <= 1'b0;
            r_wr_sched <= 1'b0;
        end else begin
            if (w_aw_fire) begin
                r_wr_valid <= 1'b1;
                r_wr_fdone <= 1'b0;
                r_wr_sched <= 1'b0;
            end else if (w_cm_fire && w_last_beat) begin
                r_wr_valid <= 1'b0;
                r_wr_fdone <= 1'b0;
                r_wr_sched <= 1'b0;
            end

            if (w_wd_fire && wd_last_i)
                r_wr_fdone <= 1'b1;

            if (w_commit_fire)
                r_wr_sched <= 1'b1;
        end
    end)

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_bank <= '0; r_wr_row <= '0; r_wr_col <= '0;
            r_wr_id   <= '0; r_wr_qos <= '0;
            r_wr_agg  <= 1'b0; r_wr_last <= 1'b0;
        end else if (w_aw_fire) begin
            r_wr_bank <= aw_push_bank_i;
            r_wr_row  <= aw_push_row_i;
            r_wr_col  <= aw_push_col_i;
            r_wr_id   <= aw_push_id_i;
            r_wr_qos  <= aw_push_qos_i;
            r_wr_agg  <= aw_push_agg_i;
            r_wr_last <= aw_push_last_i;
        end
    end)

    // ======================================================================
    // WR data staging FIFO
    // ======================================================================
    assign w_wdfifo_wr_valid = w_wd_fire;
    assign w_wdfifo_wr_data  = {wd_last_i, wd_strb_i, wd_data_i};

    assign w_wdfifo_rd_ready = w_cm_fire;
    assign {w_wdfifo_rd_last, w_wdfifo_rd_strb, w_wdfifo_rd_data} = w_wdfifo_rd_raw;
    assign w_last_beat       = w_wdfifo_rd_last;

    gaxi_fifo_sync #(.DATA_WIDTH(WDFIFO_DW), .DEPTH(WR_DATA_BUF_WORDS)) u_wr_data_fifo (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_wdfifo_wr_valid),
        .wr_ready   (w_wdfifo_wr_ready),
        .wr_data    (w_wdfifo_wr_data),
        .rd_ready   (w_wdfifo_rd_ready),
        .count      (),
        .rd_valid   (w_wdfifo_rd_valid),
        .rd_data    (w_wdfifo_rd_raw)
    );

    assign wr_cm_rd_valid_o = r_wr_valid && r_wr_sched && w_wdfifo_rd_valid;
    assign wr_cm_rd_data_o  = w_wdfifo_rd_data;
    assign wr_cm_rd_strb_o  = w_wdfifo_rd_strb;
    assign wr_cm_rd_last_o  = w_wdfifo_rd_last;

    assign wr_done_valid_o  = w_cm_fire && w_last_beat;
    assign wr_done_id_o     = r_wr_id;

    // ======================================================================
    // RD entry register
    // ======================================================================
    logic                r_rd_valid;
    logic                r_rd_issued;
    logic [BKW-1:0]      r_rd_bank;
    logic [ROW_WIDTH-1:0]r_rd_row;
    logic [COL_WIDTH-1:0]r_rd_col;
    logic [IW-1:0]       r_rd_id;
    logic [3:0]          r_rd_qos;
    logic [RTW-1:0]      r_rd_ticket;

    logic                w_ar_fire;
    logic                w_rd_issue_fire;
    logic                w_rd_iss_fire;

    assign w_ar_fire      = ar_push_valid_i && ar_push_ready_o;
    assign w_rd_issue_fire= rd_issue_valid_i && rd_issue_ready_o;
    assign w_rd_iss_fire  = rd_iss_valid_o && rd_iss_ready_i;

    assign ar_push_ready_o    = !r_rd_valid && rt_alloc_ready_i;
    assign rd_cam_ins_ready_o = !r_rd_valid;
    assign rd_issue_ready_o   = r_rd_valid && !r_rd_issued;
    assign rd_iss_valid_o     = r_rd_issued;
    assign rd_iss_ticket_o    = r_rd_ticket;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_rd_valid  <= 1'b0;
            r_rd_issued <= 1'b0;
        end else begin
            if (w_ar_fire) begin
                r_rd_valid  <= 1'b1;
                r_rd_issued <= 1'b0;
            end else if (w_rd_iss_fire) begin
                r_rd_valid  <= 1'b0;
                r_rd_issued <= 1'b0;
            end

            if (w_rd_issue_fire)
                r_rd_issued <= 1'b1;
        end
    end)

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_rd_bank <= '0; r_rd_row <= '0; r_rd_col <= '0;
            r_rd_id   <= '0; r_rd_qos <= '0; r_rd_ticket <= '0;
        end else if (w_ar_fire) begin
            r_rd_bank   <= ar_push_bank_i;
            r_rd_row    <= ar_push_row_i;
            r_rd_col    <= ar_push_col_i;
            r_rd_id     <= ar_push_id_i;
            r_rd_qos    <= ar_push_qos_i;
            r_rd_ticket <= rt_alloc_ticket_i;
        end
    end)

    wire _unused_age = &{1'b0, sched_age_thresh_i};
    wire _unused_wr_slot = &{1'b0, wr_commit_slot_i};
    wire _unused_rd_slot = &{1'b0, rd_issue_slot_i};

    // Storage-lite: no read-your-write forwarding in this SKU.
    assign snarf_hit_o      = 1'b0;
    assign snarf_rd_valid_o = 1'b0;
    assign snarf_rd_data_o  = '0;
    assign snarf_rd_last_o  = 1'b0;
    wire _unused_snarf = &{1'b0, snarf_probe_valid_i, snarf_probe_bank_i,
                           snarf_probe_row_i, snarf_probe_col_i,
                           snarf_probe_id_i, snarf_probe_len_i,
                           snarf_accept_i, snarf_rd_ready_i};

    // ======================================================================
    // Scheduler vectors (only slot 0 populated)
    // ======================================================================
    always_comb begin
        wr_sch_valid_o     = '0;
        wr_sch_bank_o      = '0;
        wr_sch_row_o       = '0;
        wr_sch_col_o       = '0;
        wr_sch_older_o     = '0;
        wr_sch_age_exceed_o= '0;
        wr_sch_qos_o       = '0;
        wr_sch_head_rel_o  = '0;

        rd_sch_valid_o     = '0;
        rd_sch_bank_o      = '0;
        rd_sch_row_o       = '0;
        rd_sch_col_o       = '0;
        rd_sch_older_o     = '0;
        rd_sch_age_exceed_o= '0;
        rd_sch_qos_o       = '0;
        rd_sch_head_rel_o  = '0;

        if (NUM_ENTRIES > 0) begin
            wr_sch_valid_o[0]      = r_wr_valid && r_wr_fdone && !r_wr_sched;
            wr_sch_bank_o[0*BKW +: BKW]            = r_wr_bank;
            wr_sch_row_o[0*ROW_WIDTH +: ROW_WIDTH]  = r_wr_row;
            wr_sch_col_o[0*COL_WIDTH +: COL_WIDTH]  = r_wr_col;
            wr_sch_qos_o[0*4 +: 4]                  = r_wr_qos;

            rd_sch_valid_o[0]      = r_rd_valid && !r_rd_issued;
            rd_sch_bank_o[0*BKW +: BKW]            = r_rd_bank;
            rd_sch_row_o[0*ROW_WIDTH +: ROW_WIDTH]  = r_rd_row;
            rd_sch_col_o[0*COL_WIDTH +: COL_WIDTH]  = r_rd_col;
            rd_sch_qos_o[0*4 +: 4]                  = r_rd_qos;
        end
    end

    assign busy_o = r_wr_valid || r_rd_valid;

endmodule : mc_xddr2_entry_store
