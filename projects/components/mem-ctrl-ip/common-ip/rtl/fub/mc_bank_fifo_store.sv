// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_bank_fifo_store
// Purpose: Per-bank FIFO storage backend for the product SKU (granite); the
//          recovery plan's section 2.4 "FIFO backend", Phase 4.
//
//          Same ports and the same data path as mc_xddr2_entry_store (write
//          beats in one simple-dual-port BRAM, 2-deep prefetch skid, drain
//          queue in commit order, B consolidation from the carried skid tag,
//          read tickets forwarded at issue), but the scheduler's view is not
//          derived from an N x N age matrix. Descriptors are slots in a pool;
//          each (direction, bank) keeps a FIFO of slots in arrival order, and
//          the per-bank head records of the plane contract (mc_head_rec_t:
//          head and second head, same-row-behind, empty-behind, hit, age
//          flag) are read off the FIFO fronts and registered at the edge.
//          Write data arrives in AW order, so a global fill-order FIFO names
//          the slot each W beat belongs to; an older write in a bank is
//          therefore always filled before a younger one, and a bank FIFO head
//          that is still filling has nothing schedulable behind it.
//
//          same-row-behind is a stored bit, not a compare matrix: at push the
//          incoming row is compared with the bank's tail row (one compare per
//          direction per cycle) and the result rides the queue position. The
//          pick core reads the flag as "the entry behind this one shares its
//          row" (mc_bank_pick, the speculation note), which for an in-order
//          per-bank queue is exactly that bit. The only compares per cycle are
//          the two heads' row hits against the scheduler's open-row image.
//
//          A commit or issue always names the HEAD of its bank queue: the pick
//          core fires the head record, or in the one cycle after a pop (the
//          record's registered latency) the second record, which by then is
//          the head (mc_bank_pick, r_shadow). So each bank queue is a plain
//          circular FIFO of slot pointers -- pop is a pointer increment, the
//          records read three positions from the read pointer -- and no
//          pack-on-pop network exists. The first pool-deep cut packed the
//          queues on every pop and that network alone cost ~800 LUT on the
//          board (5 822 vs 5 035 at depth 4, 2026-10-23). The records cost
//          nothing per depth, so the bank FIFOs are pool-deep by default and
//          admission is the pool's, exactly as the entry store's.
//
//          The records carry vld, slot, the behind flags, hit and the age flag,
//          and NO row or column: the pick core looks the command payload up by
//          slot from wr_sch_row_o / wr_sch_col_o / rd_sch_row_o / rd_sch_col_o
//          (one lookup per direction). Materialising row + col in 32 records
//          was most of this module's LUTs on the board (3 894 at N = 8 with
//          them; report 5.11 has the number without).
//
//          Depth cap (BANK_FIFO_DEPTH < NUM_ENTRIES) is measured, not
//          recommended: at 4 per (direction, bank) on the board geometry an
//          8-beat AXI burst chops into 8 same-bank entries, the cap blocked
//          the address channel half way through every burst, and eight
//          threads lost 23% (429 vs 557 MB/s) while the mixed family
//          deadlocked (2026-10-23, report 5.10).
//
//          The FR-FCFS core's N-wide vectors are not produced here; this
//          backend pairs with SCHED_CORE = BANK_PICK (granite_core checks).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_bank_fifo_store
    import mc_common_pkg::*;
#(
    parameter int NUM_ENTRIES        = 8,   // descriptor slots per direction (the write-data buffer size)
    parameter int BANK_FIFO_DEPTH    = 0,   // per (direction, bank) queue depth; 0 = NUM_ENTRIES (pool-only admission)
    parameter int AXI_ID_WIDTH       = 8,
    parameter int AXI_DATA_WIDTH     = 64,
    parameter int NUM_RANKS          = 1,
    parameter int NUM_BANKS          = 8,
    parameter int ROW_WIDTH          = 14,
    parameter int COL_WIDTH          = 10,
    parameter int AXI_BEATS_PER_BURST = 4,
    parameter int RD_RET_DEPTH       = 32,
    parameter int WR_DATA_BUF_WORDS  = 16,  // port compatibility with mc_xddr2_entry_store (unused there too)

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

    // WR descriptor push from mc_axi4_plane
    input  logic                aw_push_valid_i,
    output logic                aw_push_ready_o,
    input  logic [BKW-1:0]      aw_push_bank_i,
    input  logic [ROW_WIDTH-1:0]aw_push_row_i,
    input  logic [COL_WIDTH-1:0]aw_push_col_i,
    input  logic [IW-1:0]       aw_push_id_i,
    input  logic [3:0]          aw_push_qos_i,
    input  logic                aw_push_agg_i,
    input  logic                aw_push_last_i,

    // WR data from mc_axi4_plane
    input  logic                wd_valid_i,
    output logic                wd_ready_o,
    input  logic [DW-1:0]       wd_data_i,
    input  logic [SW-1:0]       wd_strb_i,
    input  logic                wd_last_i,

    // WR done back to mc_axi4_plane (B response trigger)
    output logic                wr_done_valid_o,
    output logic [IW-1:0]       wr_done_id_o,

    // RD snarf probe (storage-lite: hit tied off, as in the entry store)
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

    // RD descriptor push from mc_axi4_plane
    input  logic                ar_push_valid_i,
    output logic                ar_push_ready_o,
    input  logic [BKW-1:0]      ar_push_bank_i,
    input  logic [ROW_WIDTH-1:0]ar_push_row_i,
    input  logic [COL_WIDTH-1:0]ar_push_col_i,
    input  logic [IW-1:0]       ar_push_id_i,
    input  logic [3:0]          ar_push_qos_i,

    // Return-ring allocation / issue handshake with mc_axi4_plane
    input  logic                rt_alloc_ready_i,
    input  logic [RTW-1:0]      rt_alloc_ticket_i,
    input  logic                rd_iss_ready_i,
    output logic                rd_iss_valid_o,
    output logic [RTW-1:0]      rd_iss_ticket_o,
    output logic                rd_cam_ins_ready_o,

    // Scheduler commit / issue
    input  logic [7:0]          sched_age_thresh_i,
    input  logic                wr_commit_valid_i,
    output logic                wr_commit_ready_o,
    output logic                wr_commit_ready_now_o,
    input  logic [PTRW-1:0]     wr_commit_slot_i,
    input  logic                rd_issue_valid_i,
    output logic                rd_issue_ready_o,
    input  logic [PTRW-1:0]     rd_issue_slot_i,

    // The scheduler's registered row image (bank timers' flops), for the
    // records' hit flag -- one cycle stale by contract, like the records module
    input  logic [NUM_BANKS-1:0]           bank_row_active_i,
    input  logic [NUM_BANKS*ROW_WIDTH-1:0] bank_open_row_i,

    // The plane contract: registered per-bank records
    output mc_head_rec_t [NUM_BANKS-1:0]   wr_head_o,
    output mc_head_rec_t [NUM_BANKS-1:0]   wr_head2_o,
    output mc_head_rec_t [NUM_BANKS-1:0]   rd_head_o,
    output mc_head_rec_t [NUM_BANKS-1:0]   rd_head2_o,
    // Slot fields for the pick core's payload lookup (row / col by slot; the
    // records above carry no row / col -- see mc_bank_pick, 2026-10-24).
    output logic [NUM_ENTRIES*ROW_WIDTH-1:0] wr_sch_row_o,
    output logic [NUM_ENTRIES*COL_WIDTH-1:0] wr_sch_col_o,
    output logic [NUM_ENTRIES*ROW_WIDTH-1:0] rd_sch_row_o,
    output logic [NUM_ENTRIES*COL_WIDTH-1:0] rd_sch_col_o,

    // WR commit data to DFI plane
    output logic                wr_cm_rd_valid_o,
    input  logic                wr_cm_rd_ready_i,
    output logic [DW-1:0]       wr_cm_rd_data_o,
    output logic [SW-1:0]       wr_cm_rd_strb_o,
    output logic                wr_cm_rd_last_o,

    output logic                busy_o
);

    localparam int AGEW = 16;
    localparam int BCW  = (AXI_BEATS_PER_BURST > 1) ? $clog2(AXI_BEATS_PER_BURST) : 1;
    localparam int DQ_DEPTH = (NUM_ENTRIES > 1) ? NUM_ENTRIES : 2;
    localparam int QD   = ((BANK_FIFO_DEPTH <= 0) || (BANK_FIFO_DEPTH > NUM_ENTRIES))
                        ? NUM_ENTRIES : BANK_FIFO_DEPTH;
    localparam int QPW  = (QD > 1) ? $clog2(QD) : 1;   // queue position pointer
    localparam int QCW  = $clog2(QD + 1);          // per-bank occupancy 0..QD
    localparam int FOW  = $clog2(NUM_ENTRIES + 1); // fill-order occupancy 0..N

    // ======================================================================
    // Shared age counter
    // ======================================================================
    logic [AGEW-1:0] r_age_ctr;

    // ======================================================================
    // WR slots
    // ======================================================================
    logic                 r_wr_valid [NUM_ENTRIES];
    logic                 r_wr_fdone [NUM_ENTRIES];
    logic [BKW-1:0]       r_wr_bank  [NUM_ENTRIES];
    logic [ROW_WIDTH-1:0] r_wr_row   [NUM_ENTRIES];
    logic [COL_WIDTH-1:0] r_wr_col   [NUM_ENTRIES];
    logic [IW-1:0]        r_wr_id    [NUM_ENTRIES];
    logic                 r_wr_last  [NUM_ENTRIES];
    logic [AGEW-1:0]      r_wr_age   [NUM_ENTRIES];
    logic [BCW-1:0]       r_wr_bcnt  [NUM_ENTRIES];

    // Write-beat BRAM and its prefetch skid: identical to mc_xddr2_entry_store
    localparam int SRW = DW + SW;
    (* ram_style = "block" *)
    logic [SRW-1:0]  r_mem [NUM_ENTRIES*AXI_BEATS_PER_BURST];
    logic [SRW-1:0]  r_rd_q;
    localparam int SKID_DEPTH = 2;
    logic [SRW-1:0]  r_sk_data  [SKID_DEPTH];
    logic            r_sk_blast [SKID_DEPTH];
    logic            r_sk_slast [SKID_DEPTH];
    logic [IW-1:0]   r_sk_id    [SKID_DEPTH];
    logic            r_sk_rd, r_sk_wr;
    logic [1:0]      r_sk_cnt;
    logic [1:0]      r_credits;
    logic            r_if_valid, r_if_blast, r_if_slast;
    logic [IW-1:0]   r_if_id;

    // Free slot: lowest free index
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

    // Fill-order FIFO: slots in AW order; the head is the slot the next W beat
    // belongs to (AXI4 write data is non-interleaved and arrives in AW order).
    logic [PTRW-1:0] r_fo     [NUM_ENTRIES];
    logic [FOW-1:0]  r_fo_cnt;
    logic            w_fill_vld;
    logic [PTRW-1:0] w_fill_slot;
    assign w_fill_vld  = (r_fo_cnt != '0);
    assign w_fill_slot = r_fo[0];

    // Per-bank WR FIFOs of slots: circular, r_wq_rd = head position, entries
    // at rd .. rd+cnt-1 (mod QD). r_wq_sp[pos] = that position's row equals
    // the row of the position before it (stored at push against the bank's
    // registered tail row); r_wq_tail_row = row of the last pushed.
    logic [PTRW-1:0]      r_wq          [NUM_BANKS][QD];
    logic                 r_wq_sp       [NUM_BANKS][QD];
    logic [QPW-1:0]       r_wq_rd       [NUM_BANKS];
    logic [QCW-1:0]       r_wq_cnt      [NUM_BANKS];
    logic [ROW_WIDTH-1:0] r_wq_tail_row [NUM_BANKS];

    function automatic logic [QPW-1:0] qpos(input logic [QPW-1:0] base, input int off);
        int v;
        v = int'(base) + off;
        if (v >= QD) v = v - QD;
        return QPW'(v);
    endfunction

    logic [31:0] w_fill_idx;
    assign w_fill_idx = 32'(w_fill_slot) * 32'(AXI_BEATS_PER_BURST) + 32'(r_wr_bcnt[w_fill_slot]);

    logic w_aw_fire, w_wd_fire, w_fill_done;
    assign w_aw_fire   = aw_push_valid_i && aw_push_ready_o;
    assign w_wd_fire   = wd_valid_i && wd_ready_o;
    assign w_fill_done = w_wd_fire && (wd_last_i || (r_wr_bcnt[w_fill_slot] == BCW'(AXI_BEATS_PER_BURST - 1)));

    assign aw_push_ready_o = w_wr_have_free && (r_wq_cnt[aw_push_bank_i] != QCW'(QD));
    assign wd_ready_o      = w_fill_vld;

    // ======================================================================
    // WR commit -> drain queue (slots drain in scheduler commit order).
    // Commit-ready is structural (registers only): see the entry store's
    // long note -- a slot-qualified ready closes a combinational circle with
    // the pick core's column mask.
    // ======================================================================
    logic            w_dq_wr_valid, w_dq_wr_ready, w_dq_rd_valid, w_dq_rd_ready;
    logic [PTRW-1:0] w_dq_wr_slot,  w_dq_rd_slot;
    logic            w_wr_commit_fire, w_dq_pop;
    logic [PTRW:0]   r_dq_occ;
    assign w_wr_commit_fire = wr_commit_valid_i && w_dq_wr_ready
                            && (r_dq_occ < (PTRW+1)'(DQ_DEPTH));
    assign w_dq_wr_valid    = w_wr_commit_fire;
    assign w_dq_pop         = w_dq_rd_valid && w_dq_rd_ready;
    assign wr_commit_ready_o     = w_dq_wr_ready && (r_dq_occ < (PTRW+1)'(DQ_DEPTH));
    assign wr_commit_ready_now_o = w_dq_wr_ready && (r_dq_occ < (PTRW+1)'(DQ_DEPTH));

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_dq_occ <= '0;
        else                        r_dq_occ <= r_dq_occ
                                               + (w_wr_commit_fire ? (PTRW+1)'(1) : (PTRW+1)'(0))
                                               - (w_dq_pop         ? (PTRW+1)'(1) : (PTRW+1)'(0));
    )

    assign w_dq_wr_slot = wr_commit_slot_i;

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
    // WR drain: consume side reads the skid head
    // ======================================================================
    logic            w_cm_fire;
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
    assign w_cm_fire        = wr_cm_rd_valid_o && wr_cm_rd_ready_i;

    // Fetch engine: one beat ahead of the presented beat
    logic [BCW-1:0]  r_cm_fbeat;
    logic [31:0]     w_cm_idx;
    assign w_cm_idx = 32'(w_dq_rd_slot) * 32'(AXI_BEATS_PER_BURST) + 32'(r_cm_fbeat);

    logic w_fetch, w_room, w_fetch_last;
    assign w_room       = (r_credits != 2'd0) || w_cm_fire;
    assign w_fetch      = w_room && w_dq_rd_valid;
    assign w_fetch_last = w_fetch && (r_cm_fbeat == BCW'(AXI_BEATS_PER_BURST-1));
    assign w_dq_rd_ready = w_fetch_last;

    // ======================================================================
    // Per-bank WR FIFO next-state: remove the committed slot wherever it sits,
    // close up, append the pushed slot. QD-wide, per bank.
    // ======================================================================
    logic [BKW-1:0]  w_commit_bank;
    assign w_commit_bank = r_wr_bank[wr_commit_slot_i];

    // Pop = head pointer + 1 (a commit always names the head: see the header);
    // push writes position rd + cnt. The same-as-previous bit of the pushed
    // position compares the incoming row with the registered tail row; it is
    // meaningful only when something is ahead of it after this cycle's pop.
    logic [NUM_BANKS-1:0] w_wq_pop, w_wq_push;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            w_wq_pop [b] = w_wr_commit_fire && (w_commit_bank == BKW'(b));
            w_wq_push[b] = w_aw_fire && (aw_push_bank_i == BKW'(b));
        end
    end

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
            r_fo_cnt    <= '0;
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                r_wr_valid[i] <= 1'b0;
                r_wr_fdone[i] <= 1'b0;
                r_wr_bcnt [i] <= '0;
                r_fo[i]       <= '0;
            end
            for (int b = 0; b < NUM_BANKS; b++) begin
                r_wq_cnt[b]      <= '0;
                r_wq_rd[b]       <= '0;
                r_wq_tail_row[b] <= '0;
                for (int k = 0; k < QD; k++) begin
                    r_wq[b][k]    <= '0;
                    r_wq_sp[b][k] <= 1'b0;
                end
            end
        end else begin
            r_age_ctr <= r_age_ctr + 1'b1;

            // descriptor insert
            if (w_aw_fire) begin
                r_wr_valid[w_wr_free_slot] <= 1'b1;
                r_wr_fdone[w_wr_free_slot] <= 1'b0;
                r_wr_bcnt [w_wr_free_slot] <= '0;
                r_wr_bank [w_wr_free_slot] <= aw_push_bank_i;
                r_wr_row  [w_wr_free_slot] <= aw_push_row_i;
                r_wr_col  [w_wr_free_slot] <= aw_push_col_i;
                r_wr_id   [w_wr_free_slot] <= aw_push_id_i;
                r_wr_last [w_wr_free_slot] <= aw_push_last_i;
                r_wr_age  [w_wr_free_slot] <= r_age_ctr;
            end

            // fill-order FIFO: pop at fill-done (shift), push at insert
            begin
                automatic int fidx;
                automatic logic [PTRW-1:0] fo_next [NUM_ENTRIES];
                fidx = 0;
                for (int i = 0; i < NUM_ENTRIES; i++) fo_next[i] = r_fo[i];
                for (int i = 0; i < NUM_ENTRIES; i++) begin
                    if ((i < int'(r_fo_cnt)) && !(w_fill_done && (i == 0))) begin
                        fo_next[fidx] = r_fo[i];
                        fidx++;
                    end
                end
                if (w_aw_fire && (fidx < NUM_ENTRIES)) begin
                    fo_next[fidx] = w_wr_free_slot;
                    fidx++;
                end
                for (int i = 0; i < NUM_ENTRIES; i++) r_fo[i] <= fo_next[i];
                r_fo_cnt <= FOW'(fidx);
            end

            // fill bookkeeping (the beat itself lands in the BRAM below)
            if (w_wd_fire) begin
                if (w_fill_done) begin
                    r_wr_fdone[w_fill_slot] <= 1'b1;
                    r_wr_bcnt [w_fill_slot] <= '0;
                end else begin
                    r_wr_bcnt[w_fill_slot] <= r_wr_bcnt[w_fill_slot] + 1'b1;
                end
            end

            // per-bank circular FIFOs
            for (int b = 0; b < NUM_BANKS; b++) begin
                automatic logic [QPW-1:0] wpos;
                automatic int cnt_after_pop;
                cnt_after_pop = int'(r_wq_cnt[b]) - (w_wq_pop[b] ? 1 : 0);
                wpos = qpos(r_wq_rd[b], int'(r_wq_cnt[b]));
                if (w_wq_pop[b]) r_wq_rd[b] <= qpos(r_wq_rd[b], 1);
                r_wq_cnt[b] <= QCW'(cnt_after_pop + (w_wq_push[b] ? 1 : 0));
                if (w_wq_push[b]) begin
                    r_wq   [b][wpos] <= w_wr_free_slot;
                    r_wq_sp[b][wpos] <= (cnt_after_pop > 0) && (aw_push_row_i == r_wq_tail_row[b]);
                    r_wq_tail_row[b] <= aw_push_row_i;
                end
            end

            // fetch engine
            r_if_valid <= w_fetch;
            if (w_fetch) begin
                r_if_blast <= (r_cm_fbeat == BCW'(AXI_BEATS_PER_BURST-1));
                r_if_slast <= r_wr_last[w_dq_rd_slot];
                r_if_id    <= r_wr_id [w_dq_rd_slot];
                if (r_cm_fbeat == BCW'(AXI_BEATS_PER_BURST-1)) r_cm_fbeat <= '0;
                else                                           r_cm_fbeat <= r_cm_fbeat + 1'b1;
            end

            // skid pipeline
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

            // slot evicted at FETCH-last (the B rides the skid tag)
            if (w_fetch_last) begin
                r_wr_valid[w_dq_rd_slot] <= 1'b0;
                r_wr_fdone[w_dq_rd_slot] <= 1'b0;
                r_wr_bcnt [w_dq_rd_slot] <= '0;
            end
        end
    end)

    // Data storage: reset-free so it maps to block RAM; read latency exactly
    // one cycle, paired with the one-deep in-flight tag above.
    always_ff @(posedge aclk) begin
        if (w_wd_fire) r_mem[w_fill_idx] <= {wd_strb_i, wd_data_i};
        if (w_fetch)   r_rd_q            <= r_mem[w_cm_idx];
    end

    // ======================================================================
    // RD slots and per-bank RD FIFOs
    // ======================================================================
    logic                 r_rd_valid  [NUM_ENTRIES];
    logic [BKW-1:0]       r_rd_bank   [NUM_ENTRIES];
    logic [ROW_WIDTH-1:0] r_rd_row    [NUM_ENTRIES];
    logic [COL_WIDTH-1:0] r_rd_col    [NUM_ENTRIES];
    logic [RTW-1:0]       r_rd_ticket [NUM_ENTRIES];
    logic [AGEW-1:0]      r_rd_age    [NUM_ENTRIES];
    logic [PTRW-1:0]      r_rq        [NUM_BANKS][QD];
    logic                 r_rq_sp     [NUM_BANKS][QD];
    logic [QPW-1:0]       r_rq_rd     [NUM_BANKS];
    logic [QCW-1:0]       r_rq_cnt    [NUM_BANKS];
    logic [ROW_WIDTH-1:0] r_rq_tail_row [NUM_BANKS];

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

    logic w_ar_fire, w_rd_issue_fire;
    assign w_ar_fire       = ar_push_valid_i && ar_push_ready_o;
    assign w_rd_issue_fire = rd_issue_valid_i && rd_issue_ready_o;

    assign ar_push_ready_o    = w_rd_have_free && (r_rq_cnt[ar_push_bank_i] != QCW'(QD)) && rt_alloc_ready_i;
    assign rd_cam_ins_ready_o = w_rd_have_free && (r_rq_cnt[ar_push_bank_i] != QCW'(QD));
    assign rd_issue_ready_o   = rd_iss_ready_i;
    assign rd_iss_valid_o     = w_rd_issue_fire;
    assign rd_iss_ticket_o    = r_rd_ticket[rd_issue_slot_i];

    logic [BKW-1:0]  w_issue_bank;
    assign w_issue_bank = r_rd_bank[rd_issue_slot_i];

    logic [NUM_BANKS-1:0] w_rq_pop, w_rq_push;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            w_rq_pop [b] = w_rd_issue_fire && (w_issue_bank == BKW'(b));
            w_rq_push[b] = w_ar_fire && (ar_push_bank_i == BKW'(b));
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            for (int i = 0; i < NUM_ENTRIES; i++) r_rd_valid[i] <= 1'b0;
            for (int b = 0; b < NUM_BANKS; b++) begin
                r_rq_cnt[b]      <= '0;
                r_rq_rd[b]       <= '0;
                r_rq_tail_row[b] <= '0;
                for (int k = 0; k < QD; k++) begin
                    r_rq[b][k]    <= '0;
                    r_rq_sp[b][k] <= 1'b0;
                end
            end
        end else begin
            if (w_ar_fire) begin
                r_rd_valid [w_rd_free_slot] <= 1'b1;
                r_rd_bank  [w_rd_free_slot] <= ar_push_bank_i;
                r_rd_row   [w_rd_free_slot] <= ar_push_row_i;
                r_rd_col   [w_rd_free_slot] <= ar_push_col_i;
                r_rd_ticket[w_rd_free_slot] <= rt_alloc_ticket_i;
                r_rd_age   [w_rd_free_slot] <= r_age_ctr;
            end
            if (w_rd_issue_fire) r_rd_valid[rd_issue_slot_i] <= 1'b0;
            for (int b = 0; b < NUM_BANKS; b++) begin
                automatic logic [QPW-1:0] wpos;
                automatic int cnt_after_pop;
                cnt_after_pop = int'(r_rq_cnt[b]) - (w_rq_pop[b] ? 1 : 0);
                wpos = qpos(r_rq_rd[b], int'(r_rq_cnt[b]));
                if (w_rq_pop[b]) r_rq_rd[b] <= qpos(r_rq_rd[b], 1);
                r_rq_cnt[b] <= QCW'(cnt_after_pop + (w_rq_push[b] ? 1 : 0));
                if (w_rq_push[b]) begin
                    r_rq   [b][wpos] <= w_rd_free_slot;
                    r_rq_sp[b][wpos] <= (cnt_after_pop > 0) && (ar_push_row_i == r_rq_tail_row[b]);
                    r_rq_tail_row[b] <= ar_push_row_i;
                end
            end
        end
    end)

    // ======================================================================
    // Age-exceed flags per slot (one-cycle stale, like the reference stores)
    // ======================================================================
    logic [NUM_ENTRIES-1:0] r_wr_agex, r_rd_agex;
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_agex <= '0;
            r_rd_agex <= '0;
        end else begin
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                r_wr_agex[i] <= r_wr_valid[i] && r_wr_fdone[i]
                             && (sched_age_thresh_i != 8'd0)
                             && ((r_age_ctr - r_wr_age[i]) >= AGEW'({sched_age_thresh_i, 4'h0}));
                r_rd_agex[i] <= r_rd_valid[i]
                             && (sched_age_thresh_i != 8'd0)
                             && ((r_age_ctr - r_rd_age[i]) >= AGEW'({sched_age_thresh_i, 4'h0}));
            end
            if (w_aw_fire) r_wr_agex[w_wr_free_slot] <= 1'b0;
            if (w_ar_fire) r_rd_agex[w_rd_free_slot] <= 1'b0;
        end
    end)

    // ======================================================================
    // Records off the FIFO fronts, registered at the edge. A write record is
    // schedulable only once its data has landed; nothing schedulable can sit
    // behind an unfilled head (fill order == arrival order), so a head that
    // is still filling simply has vld = 0, and the filled entries of a bank
    // are a prefix of its queue: behind_empty is "the next position is not
    // filled". behind_same_row is the stored same-as-previous bit of the next
    // position (filled or pending), the exact close-on-drain term.
    // ======================================================================
    mc_head_rec_t [NUM_BANKS-1:0] w_wr_head, w_wr_head2, w_rd_head, w_rd_head2;

    // Row / col by slot for the pick core's payload (registers, no mux).
    always_comb begin
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            wr_sch_row_o[i*ROW_WIDTH +: ROW_WIDTH] = r_wr_row[i];
            wr_sch_col_o[i*COL_WIDTH +: COL_WIDTH] = r_wr_col[i];
            rd_sch_row_o[i*ROW_WIDTH +: ROW_WIDTH] = r_rd_row[i];
            rd_sch_col_o[i*COL_WIDTH +: COL_WIDTH] = r_rd_col[i];
        end
    end

    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            automatic mc_head_rec_t h, h2;
            automatic logic [PTRW-1:0] s0, s1, s2;
            automatic logic has1, has2;
            automatic logic [ROW_WIDTH-1:0] orow;
            orow = bank_open_row_i[b*ROW_WIDTH +: ROW_WIDTH];
            s0 = r_wq[b][r_wq_rd[b]];
            s1 = r_wq[b][qpos(r_wq_rd[b], 1)];
            s2 = r_wq[b][qpos(r_wq_rd[b], 2)];
            has1 = (int'(r_wq_cnt[b]) > 1);
            has2 = (int'(r_wq_cnt[b]) > 2);
            h = '0;
            h.vld             = (r_wq_cnt[b] != '0) && r_wr_fdone[s0];
            h.slot            = MC_HEAD_SLOT_W'(s0);
            h.behind_empty    = h.vld && !(has1 && r_wr_fdone[s1]);
            h.behind_same_row = h.vld && has1 && r_wq_sp[b][qpos(r_wq_rd[b], 1)];
            h.age_exceed      = r_wr_agex[s0];
            h.hit             = bank_row_active_i[b] && (r_wr_row[s0] == orow);
            h2 = '0;
            h2.vld             = has1 && r_wr_fdone[s1];
            h2.slot            = MC_HEAD_SLOT_W'(s1);
            h2.behind_empty    = h2.vld && !(has2 && r_wr_fdone[s2]);
            h2.behind_same_row = h2.vld && has2 && r_wq_sp[b][qpos(r_wq_rd[b], 2)];
            h2.age_exceed      = r_wr_agex[s1];
            h2.hit             = bank_row_active_i[b] && (r_wr_row[s1] == orow);
            w_wr_head [b] = h;
            w_wr_head2[b] = h2;
        end
    end

    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            automatic mc_head_rec_t h, h2;
            automatic logic [PTRW-1:0] s0, s1;
            automatic logic has1, has2;
            automatic logic [ROW_WIDTH-1:0] orow;
            orow = bank_open_row_i[b*ROW_WIDTH +: ROW_WIDTH];
            s0 = r_rq[b][r_rq_rd[b]];
            s1 = r_rq[b][qpos(r_rq_rd[b], 1)];
            has1 = (int'(r_rq_cnt[b]) > 1);
            has2 = (int'(r_rq_cnt[b]) > 2);
            h = '0;
            h.vld             = (r_rq_cnt[b] != '0);
            h.slot            = MC_HEAD_SLOT_W'(s0);
            h.behind_empty    = (int'(r_rq_cnt[b]) == 1);
            h.behind_same_row = h.vld && has1 && r_rq_sp[b][qpos(r_rq_rd[b], 1)];
            h.age_exceed      = r_rd_agex[s0];
            h.hit             = bank_row_active_i[b] && (r_rd_row[s0] == orow);
            h2 = '0;
            h2.vld             = has1;
            h2.slot            = MC_HEAD_SLOT_W'(s1);
            h2.behind_empty    = (int'(r_rq_cnt[b]) == 2);
            h2.behind_same_row = h2.vld && has2 && r_rq_sp[b][qpos(r_rq_rd[b], 2)];
            h2.age_exceed      = r_rd_agex[s1];
            h2.hit             = bank_row_active_i[b] && (r_rd_row[s1] == orow);
            w_rd_head [b] = h;
            w_rd_head2[b] = h2;
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            wr_head_o  <= '0;
            wr_head2_o <= '0;
            rd_head_o  <= '0;
            rd_head2_o <= '0;
        end else begin
            wr_head_o  <= w_wr_head;
            wr_head2_o <= w_wr_head2;
            rd_head_o  <= w_rd_head;
            rd_head2_o <= w_rd_head2;
        end
    )

    // ======================================================================
    // Snarf (storage-lite: disabled), B consolidation, busy
    // ======================================================================
    assign snarf_hit_o      = 1'b0;
    assign snarf_rd_valid_o = 1'b0;
    assign snarf_rd_data_o  = '0;
    assign snarf_rd_last_o  = 1'b0;

    assign wr_done_valid_o = w_cm_fire && w_hd_blast && w_hd_slast;
    assign wr_done_id_o    = w_hd_id;

    always_comb begin
        busy_o = w_dq_rd_valid || w_hd_vld || r_if_valid;
        for (int i = 0; i < NUM_ENTRIES; i++)
            if (r_wr_valid[i] || r_rd_valid[i]) busy_o = 1'b1;
    end

    wire _unused = &{1'b0, snarf_probe_valid_i, snarf_probe_bank_i, snarf_probe_row_i,
                     snarf_probe_col_i, snarf_probe_id_i, snarf_probe_len_i,
                     snarf_accept_i, snarf_rd_ready_i, aw_push_qos_i, aw_push_agg_i,
                     ar_push_qos_i, ar_push_id_i};

endmodule : mc_bank_fifo_store
