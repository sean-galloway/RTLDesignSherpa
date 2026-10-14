// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_xddr2_entry_store
// Purpose: N-deep in-order entry store for the storage-less v2 product SKU
//          (granite).  Allocates read and write descriptors in FIFO order and
//          presents the scheduler with N-wide schedulable-entry vectors plus
//          the age-order matrix it expects.  Read tickets are forwarded to the
//          return ring at issue time; write descriptors are freed when their
//          last beat drains to the DFI plane.
//
//          Write data is staged PER ENTRY (AXI4 W beats are non-interleaved
//          and arrive in AW order, so each burst's beats go to the oldest
//          incomplete entry).  Per-entry storage lets the scheduler commit
//          writes in any order it picks (FR-FCFS by page hit) without
//          head-of-line blocking; committed slots queue in a drain FIFO and
//          each drains its own beats to the DFI plane.  The write-completion
//          (B) pulse fires once per host burst on the final sub-burst's last
//          beat -- exactly the silicon-proven B-fix semantics.
//
//          The AXI4 plane pushes descriptors (aw_push / ar_push) and write
//          beats; the scheduler commits/issues and the entry store drains
//          write data to the DFI plane.  Read tickets are passed through to
//          the AXI4 return ring at issue time.

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
    // WR descriptor push from mc_axi4_plane
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
    // WR data from mc_axi4_plane -> per-entry staging
    //=========================================================================
    input  logic                wd_valid_i,
    output logic                wd_ready_o,
    input  logic [DW-1:0]       wd_data_i,
    input  logic [SW-1:0]       wd_strb_i,
    input  logic                wd_last_i,

    //=========================================================================
    // WR done back to mc_axi4_plane (B response trigger)
    //=========================================================================
    output logic                wr_done_valid_o,
    output logic [IW-1:0]       wr_done_id_o,

    //=========================================================================
    // RD snarf probe from mc_axi4_plane (storage-lite: hit tied off)
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
    // RD descriptor push from mc_axi4_plane
    //=========================================================================
    input  logic                ar_push_valid_i,
    output logic                ar_push_ready_o,
    input  logic [BKW-1:0]      ar_push_bank_i,
    input  logic [ROW_WIDTH-1:0]ar_push_row_i,
    input  logic [COL_WIDTH-1:0]ar_push_col_i,
    input  logic [IW-1:0]       ar_push_id_i,
    input  logic [3:0]          ar_push_qos_i,

    //=========================================================================
    // Return-ring allocation/issue handshake with mc_axi4_plane
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
    // Scheduler vectors (NUM_ENTRIES-wide)
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
    // WR commit data to DFI plane
    //=========================================================================
    output logic                wr_cm_rd_valid_o,
    input  logic                wr_cm_rd_ready_i,
    output logic [DW-1:0]       wr_cm_rd_data_o,
    output logic [SW-1:0]       wr_cm_rd_strb_o,
    output logic                wr_cm_rd_last_o,

    output logic                busy_o
);

    localparam int AGEW = 16;
    localparam int BCW  = (AXI_BEATS_PER_BURST > 1) ? $clog2(AXI_BEATS_PER_BURST) : 1;
    localparam int DQ_DEPTH = (NUM_ENTRIES > 1) ? NUM_ENTRIES : 2;  // gaxi_fifo_sync needs AW>=1

    // ======================================================================
    // Common free-running age counter (shared epoch for cross-direction rel)
    // ======================================================================
    logic [AGEW-1:0] r_age_ctr;

    // ======================================================================
    // WR entry state
    // ======================================================================
    logic                 r_wr_valid  [NUM_ENTRIES];
    logic                 r_wr_fdone  [NUM_ENTRIES];
    logic                 r_wr_sched  [NUM_ENTRIES];
    logic [BKW-1:0]       r_wr_bank   [NUM_ENTRIES];
    logic [ROW_WIDTH-1:0] r_wr_row    [NUM_ENTRIES];
    logic [COL_WIDTH-1:0] r_wr_col    [NUM_ENTRIES];
    logic [IW-1:0]        r_wr_id     [NUM_ENTRIES];
    logic [3:0]           r_wr_qos    [NUM_ENTRIES];
    logic                 r_wr_agg    [NUM_ENTRIES];
    logic                 r_wr_last   [NUM_ENTRIES];
    logic [AGEW-1:0]      r_wr_age    [NUM_ENTRIES];
    logic [BCW-1:0]       r_wr_bcnt   [NUM_ENTRIES];   // beats received
    logic [BCW-1:0]       r_wr_dbcnt  [NUM_ENTRIES];   // beats drained

    // Per-entry write-data array.  AXI W beats are non-interleaved and arrive
    // in AW order, so only one entry fills at a time; per-entry storage lets
    // the scheduler commit/drain entries out of descriptor order without
    // head-of-line blocking from the shared W stream.
    logic [DW-1:0]        r_wr_data   [NUM_ENTRIES][AXI_BEATS_PER_BURST];
    logic [SW-1:0]        r_wr_strb   [NUM_ENTRIES][AXI_BEATS_PER_BURST];

    // Age-order matrix per WR direction: r_wr_older[i][j] = entry i was inserted
    // strictly before entry j.
    logic [NUM_ENTRIES-1:0] r_wr_older [NUM_ENTRIES];

    // WR free-slot allocation (lowest free index wins).
    logic            w_wr_have_free;
    logic [PTRW-1:0] w_wr_free_slot;
    always_comb begin
        w_wr_have_free = 1'b0;
        w_wr_free_slot = '0;
        for (int i = NUM_ENTRIES-1; i >= 0; i--)
            if (!r_wr_valid[i]) begin
                w_wr_have_free = 1'b1;
                w_wr_free_slot = PTRW'(i);
            end
    end

    // WR fill target: oldest valid entry that has not yet seen its last beat.
    // AXI4 write data is non-interleaved and arrives in AW order, so the
    // filling entry is the lowest-index valid !fdone one (allocation is
    // lowest-first). First match wins -- a newer descriptor may be pushed
    // while an older burst is still filling, and its beats must not be
    // redirected.
    logic            w_fill_vld;
    logic [PTRW-1:0] w_fill_slot;
    always_comb begin
        w_fill_vld  = 1'b0;
        w_fill_slot = '0;
        for (int i = 0; i < NUM_ENTRIES; i++)
            if (!w_fill_vld && r_wr_valid[i] && !r_wr_fdone[i]) begin
                w_fill_vld  = 1'b1;
                w_fill_slot = PTRW'(i);
            end
    end

    logic w_aw_fire;
    logic w_wd_fire;
    assign w_aw_fire = aw_push_valid_i && aw_push_ready_o;
    assign w_wd_fire = wd_valid_i && wd_ready_o;

    assign aw_push_ready_o = w_wr_have_free;
    assign wd_ready_o      = w_fill_vld;

    // ======================================================================
    // WR commit -> drain queue (slots drain in scheduler commit order)
    // ======================================================================
    logic            w_dq_wr_valid, w_dq_wr_ready, w_dq_rd_valid, w_dq_rd_ready;
    logic [PTRW-1:0] w_dq_wr_slot,  w_dq_rd_slot;

    // COMMIT-READY IS STRUCTURAL, NOT SLOT-QUALIFIED -- this is the silicon-
    // proven mc_wr_data_cam contract and it is NOT negotiable. The arbiter's
    // column mask gates on wr_commit_ready_i (mc_cmd_arbiter pool_col_m), so a
    // ready that qualifies r_wr_valid[wr_commit_slot_i] closes a combinational
    // circle: mask needs ready, ready needs the arbiter's CURRENT slot pointer,
    // and that register goes stale the moment a committed slot drains and frees.
    // At NUM_ENTRIES=1 the next push re-validates slot 0 and the loop self-heals
    // (which is why the N=1 build passed); at N>=2, once the pool drains with
    // the pointer on a freed slot, ready collapses to 0, the mask zeroes, and
    // no pick ever fires again -- 9 commits then a permanent stall, granite
    // N=8 sim hang 2026-10-13, root-caused on waves. Slot eligibility is
    // implied instead: the arbiter only asserts wr_commit_valid_i for a slot it
    // picked out of wr_sch_valid_o (valid && fdone && !sched), and nothing but
    // commit/drain can clear those bits between the pick and the fire.
    //
    // The occupancy look-ahead mirrors mc_wr_data_cam's rate-matched predicate:
    // ready answers "will a commit decided now still fit when it fires one
    // cycle later", counting this cycle's own accept and pop. The classify-to-
    // fire window is at most one enqueue deep (picks fire 1/cycle and each
    // enqueue lands on the next edge), so occ_next < DEPTH cannot overflow.
    logic            w_wr_commit_fire;
    logic            w_dq_pop;
    logic [PTRW:0]   r_dq_occ;
    logic [PTRW:0]   w_dq_occ_next;
    assign w_wr_commit_fire = wr_commit_valid_i && w_dq_wr_ready
                            && (r_dq_occ < (PTRW+1)'(DQ_DEPTH));
    assign w_dq_wr_valid    = w_wr_commit_fire;
    assign w_dq_pop         = w_dq_rd_valid && w_dq_rd_ready;
    assign w_dq_occ_next    = r_dq_occ + (w_wr_commit_fire ? (PTRW+1)'(1) : (PTRW+1)'(0))
                                       - (w_dq_pop         ? (PTRW+1)'(1) : (PTRW+1)'(0));
    assign wr_commit_ready_o = w_dq_wr_ready
                            && (w_dq_occ_next < (PTRW+1)'(DQ_DEPTH));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_dq_occ <= '0;
        else                        r_dq_occ <= w_dq_occ_next;
    )

    assign w_dq_wr_slot  = wr_commit_slot_i;

    gaxi_fifo_sync #(.DATA_WIDTH(PTRW), .DEPTH(DQ_DEPTH)) u_wr_drain_q (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_dq_wr_valid),
        .wr_ready   (w_dq_wr_ready),
        .wr_data    (w_dq_wr_slot),
        .rd_ready   (w_dq_rd_ready),
        .count      (),
        .rd_valid   (w_dq_rd_valid),
        .rd_data    (w_dq_rd_slot)
    );

    // ======================================================================
    // WR data drain to DFI plane (per-entry storage; valid held until fire)
    // ======================================================================
    logic w_cm_fire;
    logic w_last_beat;

    assign w_cm_fire     = wr_cm_rd_valid_o && wr_cm_rd_ready_i;
    assign w_last_beat   = (r_wr_dbcnt[w_dq_rd_slot] == BCW'(AXI_BEATS_PER_BURST - 1));

    assign wr_cm_rd_valid_o = w_dq_rd_valid && r_wr_valid[w_dq_rd_slot];
    assign wr_cm_rd_data_o  = r_wr_data[w_dq_rd_slot][r_wr_dbcnt[w_dq_rd_slot]];
    assign wr_cm_rd_strb_o  = r_wr_strb[w_dq_rd_slot][r_wr_dbcnt[w_dq_rd_slot]];
    assign wr_cm_rd_last_o  = w_last_beat;

    assign w_dq_rd_ready = w_cm_fire && w_last_beat;

    // B consolidation: the host burst AW was chopped by mc_wr_splitter into
    // AXI_BEATS_PER_BURST-sized sub-bursts (agg=1, last=1 only on the final
    // chunk; an unsplit burst arrives as agg=0, last=1). The AXI slave owes
    // the host exactly ONE B per host AW -- emitting wr_done per sub-burst
    // returns N B's for one AW, the engine's outstanding count desyncs, and
    // the run hangs with everything drained (granite A7 bring-up, 2026-10-12;
    // the pumice storage plane's wr data CAM aggregates instead, which is why
    // only the storage-less SKU saw it).
    assign wr_done_valid_o = w_cm_fire && w_last_beat
                           && r_wr_last[w_dq_rd_slot];
    assign wr_done_id_o    = r_wr_id[w_dq_rd_slot];

    // ======================================================================
    // WR sequential logic
    // ======================================================================
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_age_ctr <= '0;
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                r_wr_valid[i] <= 1'b0;
                r_wr_fdone[i] <= 1'b0;
                r_wr_sched[i] <= 1'b0;
                r_wr_bcnt[i]  <= '0;
                r_wr_dbcnt[i] <= '0;
                r_wr_older[i] <= '0;
            end
        end else begin
            r_age_ctr <= r_age_ctr + 1'b1;

            // insert descriptor
            if (w_aw_fire) begin
                r_wr_valid[w_wr_free_slot] <= 1'b1;
                r_wr_fdone[w_wr_free_slot] <= 1'b0;
                r_wr_sched[w_wr_free_slot] <= 1'b0;
                r_wr_bcnt [w_wr_free_slot] <= '0;
                r_wr_dbcnt[w_wr_free_slot] <= '0;
                r_wr_bank [w_wr_free_slot] <= aw_push_bank_i;
                r_wr_row  [w_wr_free_slot] <= aw_push_row_i;
                r_wr_col  [w_wr_free_slot] <= aw_push_col_i;
                r_wr_id   [w_wr_free_slot] <= aw_push_id_i;
                r_wr_qos  [w_wr_free_slot] <= aw_push_qos_i;
                r_wr_agg  [w_wr_free_slot] <= aw_push_agg_i;
                r_wr_last [w_wr_free_slot] <= aw_push_last_i;
                r_wr_age  [w_wr_free_slot] <= r_age_ctr;
                // age matrix: new slot is YOUNGEST -> older than nobody, and
                // every other live slot is older than it.
                for (int j = 0; j < NUM_ENTRIES; j++) begin
                    r_wr_older[w_wr_free_slot][j] <= 1'b0;
                    if (j != int'(w_wr_free_slot))
                        r_wr_older[j][w_wr_free_slot] <= 1'b1;
                end
            end

            // fill data beat into the oldest incomplete entry
            if (w_wd_fire) begin
                r_wr_data[w_fill_slot][r_wr_bcnt[w_fill_slot]] <= wd_data_i;
                r_wr_strb[w_fill_slot][r_wr_bcnt[w_fill_slot]] <= wd_strb_i;
                if (wd_last_i || (r_wr_bcnt[w_fill_slot] == BCW'(AXI_BEATS_PER_BURST - 1))) begin
                    r_wr_fdone[w_fill_slot] <= 1'b1;
                    r_wr_bcnt [w_fill_slot] <= '0;
                end else begin
                    r_wr_bcnt[w_fill_slot] <= r_wr_bcnt[w_fill_slot] + 1'b1;
                end
            end

            // scheduler commit: mark scheduled and queue for drain
            if (w_wr_commit_fire) begin
                r_wr_sched[wr_commit_slot_i] <= 1'b1;
                r_wr_dbcnt[wr_commit_slot_i] <= '0;
            end

            // drain beat; free entry on its last beat
            if (w_cm_fire) begin
                if (w_last_beat) begin
                    r_wr_valid[w_dq_rd_slot] <= 1'b0;
                    r_wr_fdone[w_dq_rd_slot] <= 1'b0;
                    r_wr_sched[w_dq_rd_slot] <= 1'b0;
                    r_wr_bcnt [w_dq_rd_slot] <= '0;
                    r_wr_dbcnt[w_dq_rd_slot] <= '0;
                end else begin
                    r_wr_dbcnt[w_dq_rd_slot] <= r_wr_dbcnt[w_dq_rd_slot] + 1'b1;
                end
            end
        end
    end)

    // ======================================================================
    // RD entry state
    // ======================================================================
    logic                 r_rd_valid  [NUM_ENTRIES];
    logic [BKW-1:0]       r_rd_bank   [NUM_ENTRIES];
    logic [ROW_WIDTH-1:0] r_rd_row    [NUM_ENTRIES];
    logic [COL_WIDTH-1:0] r_rd_col    [NUM_ENTRIES];
    logic [IW-1:0]        r_rd_id     [NUM_ENTRIES];
    logic [3:0]           r_rd_qos    [NUM_ENTRIES];
    logic [RTW-1:0]       r_rd_ticket [NUM_ENTRIES];
    logic [AGEW-1:0]      r_rd_age    [NUM_ENTRIES];

    // Age-order matrix per RD direction.
    logic [NUM_ENTRIES-1:0] r_rd_older [NUM_ENTRIES];

    // RD free-slot allocation.
    logic            w_rd_have_free;
    logic [PTRW-1:0] w_rd_free_slot;
    always_comb begin
        w_rd_have_free = 1'b0;
        w_rd_free_slot = '0;
        for (int i = NUM_ENTRIES-1; i >= 0; i--)
            if (!r_rd_valid[i]) begin
                w_rd_have_free = 1'b1;
                w_rd_free_slot = PTRW'(i);
            end
    end

    logic w_ar_fire;
    logic w_rd_issue_fire;

    assign w_ar_fire       = ar_push_valid_i && ar_push_ready_o;
    assign w_rd_issue_fire = rd_issue_valid_i && rd_issue_ready_o;

    // Structural, exactly like mc_rd_cmd_cam's issue_ready_o = iss_ready_i: the
    // arbiter's column mask gates on rd_issue_ready_i, so qualifying it with
    // r_rd_valid[rd_issue_slot_i] re-creates the commit-ready circularity (see
    // the WR comment above) the first time a slot frees while the arbiter's
    // slot pointer still references it. The arbiter only asserts
    // rd_issue_valid_i for a slot it picked out of rd_sch_valid_o.
    assign ar_push_ready_o    = w_rd_have_free && rt_alloc_ready_i;
    assign rd_cam_ins_ready_o = w_rd_have_free;
    assign rd_issue_ready_o   = rd_iss_ready_i;
    assign rd_iss_valid_o     = w_rd_issue_fire;
    assign rd_iss_ticket_o    = r_rd_ticket[rd_issue_slot_i];

    // ======================================================================
    // RD sequential logic
    // ======================================================================
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            for (int i = 0; i < NUM_ENTRIES; i++)
                r_rd_valid[i] <= 1'b0;
        end else begin
            // insert descriptor + capture return-ring ticket
            if (w_ar_fire) begin
                r_rd_valid[w_rd_free_slot] <= 1'b1;
                r_rd_bank  [w_rd_free_slot] <= ar_push_bank_i;
                r_rd_row   [w_rd_free_slot] <= ar_push_row_i;
                r_rd_col   [w_rd_free_slot] <= ar_push_col_i;
                r_rd_id    [w_rd_free_slot] <= ar_push_id_i;
                r_rd_qos   [w_rd_free_slot] <= ar_push_qos_i;
                r_rd_ticket[w_rd_free_slot] <= rt_alloc_ticket_i;
                r_rd_age   [w_rd_free_slot] <= r_age_ctr;
                // age matrix: new slot is YOUNGEST.
                for (int j = 0; j < NUM_ENTRIES; j++) begin
                    r_rd_older[w_rd_free_slot][j] <= 1'b0;
                    if (j != int'(w_rd_free_slot))
                        r_rd_older[j][w_rd_free_slot] <= 1'b1;
                end
            end

            // issue -> free entry immediately; ticket forwarded combinationally
            // this cycle via rd_iss_valid_o / rd_iss_ticket_o.
            if (w_rd_issue_fire)
                r_rd_valid[rd_issue_slot_i] <= 1'b0;
        end
    end)

    // ======================================================================
    // Relative age (used for head_rel and age-exceed)
    // ======================================================================
    logic [AGEW-1:0] w_wr_rel [NUM_ENTRIES];
    logic [AGEW-1:0] w_rd_rel [NUM_ENTRIES];
    always_comb
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            w_wr_rel[i] = r_age_ctr - r_wr_age[i];
            w_rd_rel[i] = r_age_ctr - r_rd_age[i];
        end

    // ======================================================================
    // Registered age-exceed flags (one-cycle stale, matching reference CAMs)
    // ======================================================================
    logic [NUM_ENTRIES-1:0] r_wr_age_exceed;
    logic [NUM_ENTRIES-1:0] r_rd_age_exceed;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_age_exceed <= '0;
            r_rd_age_exceed <= '0;
        end else begin
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                r_wr_age_exceed[i] <= r_wr_valid[i] && r_wr_fdone[i] && !r_wr_sched[i]
                                   && (sched_age_thresh_i != 8'd0)
                                   && (w_wr_rel[i] >= AGEW'({sched_age_thresh_i, 4'h0}));
                r_rd_age_exceed[i] <= r_rd_valid[i]
                                   && (sched_age_thresh_i != 8'd0)
                                   && (w_rd_rel[i] >= AGEW'({sched_age_thresh_i, 4'h0}));
            end
            if (w_aw_fire) r_wr_age_exceed[w_wr_free_slot] <= 1'b0;
            if (w_ar_fire) r_rd_age_exceed[w_rd_free_slot] <= 1'b0;
        end
    end)

    // ======================================================================
    // Scheduler vectors + oldest-head relative age
    // ======================================================================
    logic            w_wr_sho_found, w_rd_sho_found;
    logic [PTRW-1:0] w_wr_sho_slot,  w_rd_sho_slot;

    always_comb begin
        automatic logic [NUM_ENTRIES-1:0] w_wr_sched, w_rd_sched;
        automatic logic [NUM_ENTRIES-1:0] w_wr_is,    w_rd_is;

        for (int i = 0; i < NUM_ENTRIES; i++) begin
            w_wr_sched[i] = r_wr_valid[i] && r_wr_fdone[i] && !r_wr_sched[i];
            w_rd_sched[i] = r_rd_valid[i];
        end

        for (int i = 0; i < NUM_ENTRIES; i++) begin
            automatic logic wr_ge_all = 1'b1;
            automatic logic rd_ge_all = 1'b1;
            for (int j = 0; j < NUM_ENTRIES; j++) begin
                if ((j != i) && w_wr_sched[j] && !r_wr_older[i][j]) wr_ge_all = 1'b0;
                if ((j != i) && w_rd_sched[j] && !r_rd_older[i][j]) rd_ge_all = 1'b0;
            end
            w_wr_is[i] = w_wr_sched[i] && wr_ge_all;
            w_rd_is[i] = w_rd_sched[i] && rd_ge_all;
        end

        w_wr_sho_found = |w_wr_is;
        w_wr_sho_slot  = '0;
        w_rd_sho_found = |w_rd_is;
        w_rd_sho_slot  = '0;
        for (int i = NUM_ENTRIES-1; i >= 0; i--) begin
            if (w_wr_is[i]) w_wr_sho_slot = PTRW'(i);
            if (w_rd_is[i]) w_rd_sho_slot = PTRW'(i);
        end
    end

    always_comb begin
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            wr_sch_valid_o[i]      = r_wr_valid[i] && r_wr_fdone[i] && !r_wr_sched[i];
            wr_sch_bank_o [i*BKW       +: BKW]       = r_wr_bank[i];
            wr_sch_row_o  [i*ROW_WIDTH +: ROW_WIDTH] = r_wr_row[i];
            wr_sch_col_o  [i*COL_WIDTH +: COL_WIDTH] = r_wr_col[i];
            wr_sch_older_o[i*NUM_ENTRIES +: NUM_ENTRIES] = r_wr_older[i];
            wr_sch_qos_o  [i*4 +: 4]                 = r_wr_qos[i];
            wr_sch_age_exceed_o[i] = r_wr_age_exceed[i];

            rd_sch_valid_o[i]      = r_rd_valid[i];
            rd_sch_bank_o [i*BKW       +: BKW]       = r_rd_bank[i];
            rd_sch_row_o  [i*ROW_WIDTH +: ROW_WIDTH] = r_rd_row[i];
            rd_sch_col_o  [i*COL_WIDTH +: COL_WIDTH] = r_rd_col[i];
            rd_sch_older_o[i*NUM_ENTRIES +: NUM_ENTRIES] = r_rd_older[i];
            rd_sch_qos_o  [i*4 +: 4]                 = r_rd_qos[i];
            rd_sch_age_exceed_o[i] = r_rd_age_exceed[i];
        end
        wr_sch_head_rel_o = w_wr_sho_found ? w_wr_rel[w_wr_sho_slot] : '0;
        rd_sch_head_rel_o = w_rd_sho_found ? w_rd_rel[w_rd_sho_slot] : '0;
    end

    // ======================================================================
    // Snarf (storage-less SKU: disabled)
    // ======================================================================
    assign snarf_hit_o      = 1'b0;
    assign snarf_rd_valid_o = 1'b0;
    assign snarf_rd_data_o  = '0;
    assign snarf_rd_last_o  = 1'b0;

    // ======================================================================
    // Busy: any valid entry or data draining
    // ======================================================================
    always_comb begin
        busy_o = w_dq_rd_valid;
        for (int i = 0; i < NUM_ENTRIES; i++)
            if (r_wr_valid[i] || r_rd_valid[i]) busy_o = 1'b1;
    end

    // Unused inputs (kept for port compatibility)
    wire _unused = &{1'b0, snarf_probe_valid_i, snarf_probe_bank_i,
                     snarf_probe_row_i, snarf_probe_col_i,
                     snarf_probe_id_i, snarf_probe_len_i,
                     snarf_accept_i, snarf_rd_ready_i, wd_last_i};

`ifndef SYNTHESIS
    always @(posedge aclk)
        if (aresetn) begin
            assert (!(w_wr_commit_fire && (!r_wr_valid[wr_commit_slot_i]
                                       || !r_wr_fdone[wr_commit_slot_i]
                                       || r_wr_sched[wr_commit_slot_i])))
              else $error("ENTRY_STORE @%0t: commit of WR slot %0d not schedulable (valid=%b fdone=%b sched=%b)",
                          $time, wr_commit_slot_i,
                          r_wr_valid[wr_commit_slot_i], r_wr_fdone[wr_commit_slot_i],
                          r_wr_sched[wr_commit_slot_i]);
            assert (!(w_rd_issue_fire && !r_rd_valid[rd_issue_slot_i]))
              else $error("ENTRY_STORE @%0t: issue of RD slot %0d which is NOT valid", $time, rd_issue_slot_i);
            assert (!(w_wd_fire && !w_fill_vld))
              else $error("ENTRY_STORE @%0t: W beat with no filling entry", $time);
        end
`endif

endmodule : mc_xddr2_entry_store
