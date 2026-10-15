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
//          last beat has been FETCHED from the data SRAM (see below).
//
//          Write BEAT DATA lives in ONE simple-dual-port BRAM — one word per
//          (slot, beat), {strb,data} packed, synchronous (registered) read.
//          Pattern ported from mc_wr_data_cam (pumice, silicon-proven): the
//          earlier per-entry flop arrays cost ~2.3k FFs (+3.6k LUTs on the
//          A7 build) for exactly zero bandwidth.  A 2-deep prefetch skid over
//          the 1-cycle-latency read keeps the drain stream at 1 beat/cycle
//          across entry boundaries (beat-0 of the next entry fetches while
//          the current tail drains), and full tags ride each buffered beat so
//          the consume side needs no entry state.
//
//          Fill/drain collision freedom: AXI4 W beats are non-interleaved and
//          arrive in AW order, so the filling entry (valid && !fdone) and the
//          draining entry (committed => fdone && sched) are always different
//          entries — the write port and the read port never touch the same
//          region in the same cycle.
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
    // Scheduler vectors (NUM_ENTRIES-wide) — FRFCFS pick core
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
    // Per-bank head views — BANK_FIFO pick core (mc_scheduler_plane v2).
    // Purely combinational off the entry arrays; the core latches a bank's
    // head into its own sequencer register and drives the SAME commit/issue
    // strobes above (head slot), so no store state changes here.
    //   head  = oldest schedulable entry of the bank (wr: valid && fdone &&
    //           !sched; rd: valid), via the age matrix.
    //   empty = exactly one schedulable entry in the bank (CLOSE_ON_DRAIN:
    //           the head's close is exact when its queue drains behind it).
    //=========================================================================
    output logic [NUM_BANKS-1:0]                wr_bh_valid_o,
    output logic [NUM_BANKS*PTRW-1:0]           wr_bh_slot_o,
    output logic [NUM_BANKS*ROW_WIDTH-1:0]      wr_bh_row_o,
    output logic [NUM_BANKS*COL_WIDTH-1:0]      wr_bh_col_o,
    output logic [NUM_BANKS*IW-1:0]             wr_bh_id_o,
    output logic [NUM_BANKS-1:0]                wr_bh_last_o,
    output logic [NUM_BANKS-1:0]                wr_bh_empty_o,

    output logic [NUM_BANKS-1:0]                rd_bh_valid_o,
    output logic [NUM_BANKS*PTRW-1:0]           rd_bh_slot_o,
    output logic [NUM_BANKS*ROW_WIDTH-1:0]      rd_bh_row_o,
    output logic [NUM_BANKS*COL_WIDTH-1:0]      rd_bh_col_o,
    output logic [NUM_BANKS*IW-1:0]             rd_bh_id_o,
    output logic [NUM_BANKS-1:0]                rd_bh_empty_o,

    // Second-oldest per bank (the reserve behind the head). Fields mirror the
    // head outputs; the BANK_FIFO core's 2-deep head skid needs it to sustain
    // 1 command/cycle on a single bank without a store round-trip per pick.
    output logic [NUM_BANKS-1:0]                wr_bh2_valid_o,
    output logic [NUM_BANKS*PTRW-1:0]           wr_bh2_slot_o,
    output logic [NUM_BANKS*ROW_WIDTH-1:0]      wr_bh2_row_o,
    output logic [NUM_BANKS*COL_WIDTH-1:0]      wr_bh2_col_o,
    output logic [NUM_BANKS*IW-1:0]             wr_bh2_id_o,
    output logic [NUM_BANKS-1:0]                wr_bh2_last_o,
    output logic [NUM_BANKS-1:0]                rd_bh2_valid_o,
    output logic [NUM_BANKS*PTRW-1:0]           rd_bh2_slot_o,
    output logic [NUM_BANKS*ROW_WIDTH-1:0]      rd_bh2_row_o,
    output logic [NUM_BANKS*COL_WIDTH-1:0]      rd_bh2_col_o,
    output logic [NUM_BANKS*IW-1:0]             rd_bh2_id_o,

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

    // WR beat-data SRAM: ONE simple-dual-port BRAM, one word per (slot, beat),
    // {strb,data} packed so a read returns them atomically.  The write port is
    // the fill engine; the read port is the commit-drain fetch engine.  Fill
    // and drain are always different entries (fill target is !fdone, drain
    // target is committed => fdone && sched), so the ports never collide on a
    // region.  Synchronous read (1-cycle latency) -> the 2-deep prefetch skid
    // below decouples fetch from consume.
    localparam int SRW = DW + SW;
    (* ram_style = "block" *)
    logic [SRW-1:0]  r_mem [NUM_ENTRIES*AXI_BEATS_PER_BURST];
    logic [SRW-1:0]  r_rd_q;    // BRAM read-data register (output of the sync read)

    // 2-deep prefetch skid over the BRAM (commit drain only — this SKU has no
    // snarf stream sharing the read port, so mc_wr_data_cam's port arbitration
    // and anti-starvation logic is intentionally absent).  Each buffered beat
    // carries its full tag {blast, slast, id} so the consume side needs no
    // entry state: the entry itself is evicted at FETCH-last, one pipeline
    // earlier than consume-last (Little's law on the write side; see
    // mc_wr_data_cam).  A credit count bounds (outstanding + buffered) <=
    // SKID_DEPTH so a stalled DFI plane never loses a beat.
    localparam int SKID_DEPTH = 2;
    logic [SRW-1:0]  r_sk_data  [SKID_DEPTH];
    logic            r_sk_blast [SKID_DEPTH]; // last beat of this entry's burst
    logic            r_sk_slast [SKID_DEPTH]; // entry r_wr_last: final sub of host AW
    logic [IW-1:0]   r_sk_id    [SKID_DEPTH];
    logic            r_sk_rd;                 // head pointer (1 bit; DEPTH=2)
    logic            r_sk_wr;                 // tail pointer
    logic [1:0]      r_sk_cnt;                // occupancy 0..2
    logic [1:0]      r_credits;               // SKID_DEPTH - (outstanding + buffered)

    // in-flight read (issued last cycle; its data lands in r_rd_q this cycle)
    logic            r_if_valid;
    logic            r_if_blast;
    logic            r_if_slast;
    logic [IW-1:0]   r_if_id;

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

    // SRAM flat index of the fill beat (32-bit width, mirroring mc_wr_data_cam)
    logic [31:0] w_fill_idx;
    assign w_fill_idx = 32'(w_fill_slot) * 32'(AXI_BEATS_PER_BURST) + 32'(r_wr_bcnt[w_fill_slot]);

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
    // The occupancy look-ahead mirrors mc_wr_data_cam's rate-matched predicate
    // for the FRFCFS core's decide-one-cycle-early pipeline:
    // ready answers "will a commit decided now still fit when it fires one
    // cycle later", counting this cycle's own accept and pop. The classify-to-
    // fire window is at most one enqueue deep (picks fire 1/cycle and each
    // enqueue lands on the next edge), so occ_next < DEPTH cannot overflow.
    //
    // 2026-10-15 (mc_bank_sched): the per-bank core fires COMBINATIONALLY
    // (decide == fire), so a ready that includes this cycle's own accept
    // closes a combinational loop (valid -> store.fire -> occ_next -> ready
    // -> core.valid). The registered occupancy alone is exact for decide==
    // fire (one commit/cycle can never overflow a slot it already counted),
    // and remains safe for the FRFCFS core (at most one undecided commit, so
    // occ at fire <= occ at decide + 1 <= DEPTH). Gate on r_dq_occ directly.
    logic            w_wr_commit_fire;
    logic            w_dq_pop;
    logic [PTRW:0]   r_dq_occ;
    assign w_wr_commit_fire = wr_commit_valid_i && w_dq_wr_ready
                            && (r_dq_occ < (PTRW+1)'(DQ_DEPTH));
    assign w_dq_wr_valid    = w_wr_commit_fire;
    assign w_dq_pop         = w_dq_rd_valid && w_dq_rd_ready;
    assign wr_commit_ready_o = w_dq_wr_ready
                            && (r_dq_occ < (PTRW+1)'(DQ_DEPTH));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_dq_occ <= '0;
        else                        r_dq_occ <= r_dq_occ
                                               + (w_wr_commit_fire ? (PTRW+1)'(1) : (PTRW+1)'(0))
                                               - (w_dq_pop         ? (PTRW+1)'(1) : (PTRW+1)'(0));
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
    // WR drain to DFI plane: consume side reads the skid head (declared
    // before the fetch engine below — the house lint requires declaration
    // before use)
    // ======================================================================
    logic w_cm_fire;
    logic            w_hd_vld, w_hd_blast, w_hd_slast;
    logic [SRW-1:0]  w_hd_data;
    logic [IW-1:0]   w_hd_id;

    assign w_hd_vld   = (r_sk_cnt != 2'd0);
    assign w_hd_data  = r_sk_data [r_sk_rd];
    assign w_hd_blast = r_sk_blast[r_sk_rd];
    assign w_hd_slast = r_sk_slast[r_sk_rd];
    assign w_hd_id    = r_sk_id   [r_sk_rd];

    assign wr_cm_rd_valid_o = w_hd_vld;
    assign wr_cm_rd_data_o  = w_hd_data[DW-1:0];
    assign wr_cm_rd_strb_o  = w_hd_data[SRW-1:DW];
    assign wr_cm_rd_last_o  = w_hd_blast;

    assign w_cm_fire = wr_cm_rd_valid_o && wr_cm_rd_ready_i;

    // ======================================================================
    // WR drain fetch engine : stream committed entries (drain FIFO order) out
    // of the BRAM through the prefetch skid.  The fetch beat pointer runs one
    // beat AHEAD of the presented beat so the read port stays busy across
    // entry boundaries (beat-0 of the next entry fetches while the current
    // tail drains -> no per-entry bubble, 1 beat/cycle sustained).
    // ======================================================================
    logic [BCW-1:0]  r_cm_fbeat;   // commit fetch beat (next beat to issue)
    logic [31:0]     w_cm_idx;
    assign w_cm_idx = 32'(w_dq_rd_slot) * 32'(AXI_BEATS_PER_BURST) + 32'(r_cm_fbeat);

    // Room for one more outstanding fetch: a free credit, or a consume this
    // cycle returns one.
    logic w_fetch, w_room, w_fetch_last;
    assign w_room       = (r_credits != 2'd0) || w_cm_fire;
    assign w_fetch      = w_room && w_dq_rd_valid;
    assign w_fetch_last = w_fetch && (r_cm_fbeat == BCW'(AXI_BEATS_PER_BURST-1));

    // Pop the drain queue at FETCH-last so the head advances to the next entry
    // on the next edge and its beat-0 fetches immediately (no cross-entry
    // bubble; same idiom as mc_wr_data_cam's w_dq_rd_ready).
    assign w_dq_rd_ready = w_fetch_last;

    // ======================================================================
    // WR sequential logic
    // ======================================================================
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_age_ctr   <= '0;
            r_cm_fbeat  <= '0;
            r_sk_rd     <= 1'b0;
            r_sk_wr     <= 1'b0;
            r_sk_cnt    <= 2'd0;
            r_credits   <= 2'(SKID_DEPTH);
            r_if_valid  <= 1'b0;
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                r_wr_valid[i] <= 1'b0;
                r_wr_fdone[i] <= 1'b0;
                r_wr_sched[i] <= 1'b0;
                r_wr_bcnt [i] <= '0;
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

            // fill data beat bookkeeping (the beat itself is written into the
            // BRAM in the reset-free process below)
            if (w_wd_fire) begin
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
            end

            // ---- fetch engine: issue BRAM reads one beat ahead -------------
            r_if_valid <= w_fetch;
            if (w_fetch) begin
                r_if_blast <= (r_cm_fbeat == BCW'(AXI_BEATS_PER_BURST-1));
                r_if_slast <= r_wr_last[w_dq_rd_slot];
                r_if_id    <= r_wr_id [w_dq_rd_slot];
                if (r_cm_fbeat == BCW'(AXI_BEATS_PER_BURST-1)) r_cm_fbeat <= '0;
                else                                           r_cm_fbeat <= r_cm_fbeat + 1'b1;
            end

            // ---- skid pipeline ----------------------------------------------
            // Stage 1 (issue, above): latch the BRAM read + its tag as in-flight.
            // Stage 2 (capture, next cycle): r_rd_q holds the data and r_if_* the
            // tag -> push into the skid FIFO.  Credits bound the pipeline so a
            // stalled consumer never overruns.
            if (r_if_valid) begin
                r_sk_data [r_sk_wr] <= r_rd_q;
                r_sk_blast[r_sk_wr] <= r_if_blast;
                r_sk_slast[r_sk_wr] <= r_if_slast;
                r_sk_id   [r_sk_wr] <= r_if_id;
                r_sk_wr             <= r_sk_wr + 1'b1;
            end
            if (w_cm_fire) r_sk_rd <= r_sk_rd + 1'b1;
            r_sk_cnt  <= r_sk_cnt  + (r_if_valid ? 2'd1 : 2'd0) - (w_cm_fire ? 2'd1 : 2'd0);
            r_credits <= r_credits - (w_fetch    ? 2'd1 : 2'd0) + (w_cm_fire ? 2'd1 : 2'd0);

            // commit DRAIN evict at FETCH-last (mc_wr_data_cam semantics): the
            // burst's last word is read out of the SRAM this cycle, so the entry
            // is free from the next edge -- the command delay + DFI serializer
            // wait leaves the entry lifetime and Little's-law write headroom
            // widens.  The B response still rides the skid tag at consume-last.
            if (w_fetch_last) begin
                r_wr_valid[w_dq_rd_slot] <= 1'b0;
                r_wr_fdone[w_dq_rd_slot] <= 1'b0;
                r_wr_sched[w_dq_rd_slot] <= 1'b0;
                r_wr_bcnt [w_dq_rd_slot] <= '0;
            end
        end
    end)

    // -------------------------------------------------------------------------
    // Data storage: a dedicated, RESET-FREE clocked process so Vivado maps it to
    // Block RAM. RAM contents cannot be async-reset; a memory written inside an
    // async-reset process reports "RAM is sensitive to asynchronous reset signal"
    // and dissolves into fabric flip-flops -- defeating the whole point of the
    // change. One write port (fill) + one registered read port (drain fetch) =
    // simple dual-port BRAM. (Identical structure and rationale to
    // mc_wr_data_cam's r_mem process.)
    //
    // READ LATENCY IS EXACTLY 1 CYCLE and the skid pipeline depends on it: the
    // address (w_cm_idx / w_fill_idx) is combinational, the output r_rd_q is a
    // single register, so data for the address issued in cycle T lands in
    // r_rd_q in T+1 -- which is when the 1-deep in-flight tag (r_if_*) is
    // paired with it and pushed into the skid. Do NOT register the read address
    // or add an output-register stage unless you deepen the r_if_* tag pipeline
    // to match: otherwise every captured beat pairs with the WRONG tag (last /
    // B id) -> silent corruption, with no elaboration error.
    // -------------------------------------------------------------------------
    always_ff @(posedge aclk) begin
        if (w_wd_fire) r_mem[w_fill_idx] <= {wd_strb_i, wd_data_i};
        if (w_fetch)   r_rd_q            <= r_mem[w_cm_idx];
    end

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
    // Per-bank head views (BANK_FIFO pick core) — oldest schedulable entry
    // of each bank + queue-empty flags + the second-oldest (reserve). Purely
    // combinational.
    // ======================================================================
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            automatic logic            wv  = 1'b0;
            automatic logic [PTRW-1:0] ws  = '0;
            automatic logic            wv2 = 1'b0;
            automatic logic [PTRW-1:0] ws2 = '0;
            automatic int              wc  = 0;
            automatic logic            rv  = 1'b0;
            automatic logic [PTRW-1:0] rs  = '0;
            automatic logic            rv2 = 1'b0;
            automatic logic [PTRW-1:0] rs2 = '0;
            automatic int              rc  = 0;
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                if (r_wr_valid[i] && r_wr_fdone[i] && !r_wr_sched[i]
                    && (int'(r_wr_bank[i]) == b)) begin
                    automatic int n_older = 0;
                    wc = wc + 1;
                    for (int j = 0; j < NUM_ENTRIES; j++)
                        if ((j != i) && r_wr_valid[j] && r_wr_fdone[j] && !r_wr_sched[j]
                            && (int'(r_wr_bank[j]) == b) && r_wr_older[j][i])
                            n_older = n_older + 1;
                    if (n_older == 0) begin
                        wv = 1'b1;  ws = PTRW'(i);
                    end else if (n_older == 1) begin
                        wv2 = 1'b1; ws2 = PTRW'(i);
                    end
                end
                if (r_rd_valid[i] && (int'(r_rd_bank[i]) == b)) begin
                    automatic int n_older = 0;
                    rc = rc + 1;
                    for (int j = 0; j < NUM_ENTRIES; j++)
                        if ((j != i) && r_rd_valid[j]
                            && (int'(r_rd_bank[j]) == b) && r_rd_older[j][i])
                            n_older = n_older + 1;
                    if (n_older == 0) begin
                        rv = 1'b1;  rs = PTRW'(i);
                    end else if (n_older == 1) begin
                        rv2 = 1'b1; rs2 = PTRW'(i);
                    end
                end
            end
            wr_bh_valid_o[b] = wv;
            wr_bh_slot_o [b*PTRW +: PTRW]           = ws;
            wr_bh_row_o  [b*ROW_WIDTH +: ROW_WIDTH] = r_wr_row[ws];
            wr_bh_col_o  [b*COL_WIDTH +: COL_WIDTH] = r_wr_col[ws];
            wr_bh_id_o   [b*IW +: IW]               = r_wr_id [ws];
            wr_bh_last_o [b]                        = r_wr_last[ws];
            wr_bh_empty_o[b]                        = wv && (wc == 1);
            rd_bh_valid_o[b] = rv;
            rd_bh_slot_o [b*PTRW +: PTRW]           = rs;
            rd_bh_row_o  [b*ROW_WIDTH +: ROW_WIDTH] = r_rd_row[rs];
            rd_bh_col_o  [b*COL_WIDTH +: COL_WIDTH] = r_rd_col[rs];
            rd_bh_id_o   [b*IW +: IW]               = r_rd_id [rs];
            rd_bh_empty_o[b]                        = rv && (rc == 1);
            wr_bh2_valid_o[b] = wv2;
            wr_bh2_slot_o [b*PTRW +: PTRW]           = ws2;
            wr_bh2_row_o  [b*ROW_WIDTH +: ROW_WIDTH] = r_wr_row[ws2];
            wr_bh2_col_o  [b*COL_WIDTH +: COL_WIDTH] = r_wr_col[ws2];
            wr_bh2_id_o   [b*IW +: IW]               = r_wr_id [ws2];
            wr_bh2_last_o [b]                        = r_wr_last[ws2];
            rd_bh2_valid_o[b] = rv2;
            rd_bh2_slot_o [b*PTRW +: PTRW]           = rs2;
            rd_bh2_row_o  [b*ROW_WIDTH +: ROW_WIDTH] = r_rd_row[rs2];
            rd_bh2_col_o  [b*COL_WIDTH +: COL_WIDTH] = r_rd_col[rs2];
            rd_bh2_id_o   [b*IW +: IW]               = r_rd_id [rs2];
        end
    end

    // ======================================================================
    // Snarf (storage-less SKU: disabled)
    // ======================================================================
    assign snarf_hit_o      = 1'b0;
    assign snarf_rd_valid_o = 1'b0;
    assign snarf_rd_data_o  = '0;
    assign snarf_rd_last_o  = 1'b0;

    // ======================================================================
    // B consolidation: the host burst AW was chopped by mc_wr_splitter into
    // AXI_BEATS_PER_BURST-sized sub-bursts (agg=1, last=1 only on the final
    // chunk; an unsplit burst arrives as agg=0, last=1). The AXI slave owes
    // the host exactly ONE B per host AW -- emitting wr_done per sub-burst
    // returns N B's for one AW, the engine's outstanding count desyncs, and
    // the run hangs with everything drained (granite A7 bring-up, 2026-10-12;
    // the pumice storage plane's wr data CAM aggregates instead, which is why
    // only the storage-less SKU saw it).  Sourced from the CARRIED skid tag
    // (the entry is evicted at fetch-last, long before consume), exactly
    // mc_wr_data_cam's scheme.
    // ======================================================================
    assign wr_done_valid_o = w_cm_fire && w_hd_blast && w_hd_slast;
    assign wr_done_id_o    = w_hd_id;

    // ======================================================================
    // Busy: any valid entry, drain queue, skid, or in-flight fetch
    // ======================================================================
    always_comb begin
        busy_o = w_dq_rd_valid || w_hd_vld || r_if_valid;
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
            assert (!(w_wr_commit_fire && !r_wr_valid[wr_commit_slot_i]))
              else $error("ENTRY_STORE @%0t: commit of WR slot %0d which is NOT valid", $time, wr_commit_slot_i);
            assert (!(w_rd_issue_fire && !r_rd_valid[rd_issue_slot_i]))
              else $error("ENTRY_STORE @%0t: issue of RD slot %0d which is NOT valid", $time, rd_issue_slot_i);
            assert (!(w_wd_fire && !w_fill_vld))
              else $error("ENTRY_STORE @%0t: W beat with no filling entry", $time);
        end
`endif

endmodule : mc_xddr2_entry_store
