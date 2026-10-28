// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_wr_data_cam
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
// Documentation: docs/uarch/PUMICE_AXI4_IFC_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_wr_data_cam #(
    parameter int NUM_ENTRIES     = 8,
    parameter int N_SCHED_LU      = 4,
    parameter int NUM_BANKS       = 8,
    parameter int ROW_WIDTH       = 14,
    parameter int COL_WIDTH       = 10,
    parameter int AXI_ID_WIDTH    = 8,
    parameter int AXI_DATA_WIDTH  = 64,
    parameter int AXI_BEATS_PER_BURST              = 4,
    parameter int AGE_WIDTH       = 16,
    parameter int N_SRAM_SLOTS    = NUM_ENTRIES,  // may be < NUM_ENTRIES
    // bursts allowed in the commit drain queue, incl. the one being fetched
    parameter int WR_DRAIN_AHEAD  = 2,
    // Write combining (pumice TASK-060). 1 = a write whose {bank,row,col} matches a
    // live, unscheduled, un-merged entry MERGES into it at fill time: its bytes are
    // written into the entry's SRAM slot under their strobes, the strobes are ORed,
    // the entry commits ONCE as one DRAM burst and answers TWO Bs (its own id, then
    // the merged id). The merge window is "the first half has not committed": a
    // commit decided before the merge is seen waits for the merge fill (bounded,
    // behind the DFI write-staged gate), a target that is gone by fill time falls
    // back to a fresh entry. Blocked while another live write carries the merged
    // write's AXI id (same-id B order) or any snarf stream is in flight. 0 = today's
    // behaviour, bit for bit.
    parameter bit MERGE_EN        = 1'b0,

    // Derived
    parameter int IW    = AXI_ID_WIDTH,
    parameter int DW    = AXI_DATA_WIDTH,
    parameter int SW    = AXI_DATA_WIDTH / 8,
    parameter int BKW   = $clog2(NUM_BANKS),
    parameter int PTRW  = $clog2(NUM_ENTRIES),
    parameter int SPTRW = $clog2(N_SRAM_SLOTS),
    parameter int BCW   = (AXI_BEATS_PER_BURST > 1) ? $clog2(AXI_BEATS_PER_BURST) : 1   // beat-counter width (AXI_BEATS_PER_BURST=1 => 1b)
) (
    input  logic                          aclk,
    input  logic                          aresetn,

    //=========================================================================
    // Insert command (from mc_wr_intake aw_push) — allocate a slot
    //=========================================================================
    input  logic                          ins_valid_i,
    output logic                          ins_ready_o,
    input  logic [BKW-1:0]                ins_bank_i,
    input  logic [ROW_WIDTH-1:0]          ins_row_i,
    input  logic [COL_WIDTH-1:0]          ins_col_i,
    input  logic [IW-1:0]                 ins_id_i,
    input  logic [3:0]                    ins_qos_i,     // AxQOS (QOS_EN pick)
    input  logic                          ins_agg_i,   // part of a split burst
    input  logic                          ins_last_i,  // final sub of the burst

    //=========================================================================
    // Fill data (from wr_intake wdata pop) — written to SRAM in insert order
    //=========================================================================
    input  logic                          wd_valid_i,
    output logic                          wd_ready_o,
    input  logic [DW-1:0]                 wd_data_i,
    input  logic [SW-1:0]                 wd_strb_i,
    input  logic                          wd_last_i,

    //=========================================================================
    // Snarf lookup (from mc_rd_intake) — youngest match, non-destructive
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
    // Per-entry scheduling vectors (registered fields; the scheduler does the
    // match + argmax itself, so it can pick a row-hit column OR activate any
    // idle bank in parallel — and there is NO cross-module lookup round-trip).
    // Indexed by entry slot. sch_valid = schedulable (filled, not yet committed).
    //=========================================================================
    output logic [NUM_ENTRIES-1:0]              sch_valid_o,
    // allocated but NOT yet schedulable (data still landing). Read by the
    // per-bank head records' behind_same_row term only: a same-row write
    // still filling behind a head must hold the row open (BUG-027).
    output logic [NUM_ENTRIES-1:0]              sch_pend_o,
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
    // Commit — stream SRAM[slot] to wr_beat_sequencer, then evict on last
    //=========================================================================
    input  logic                          commit_valid_i,
    output logic                          commit_ready_o,
    output logic                          commit_ready_now_o,    // room for a commit THIS cycle, registers only (no commit_valid, no pop term)
    input  logic [PTRW-1:0]               commit_slot_i,
    output logic                          cm_rd_valid_o,
    input  logic                          cm_rd_ready_i,
    output logic [DW-1:0]                 cm_rd_data_o,
    output logic [SW-1:0]                 cm_rd_strb_o,
    output logic                          cm_rd_last_o,

    // Commit-done strobe (on evict) -> drives wr_intake B response
    output logic                          commit_done_valid_o,
    output logic [IW-1:0]                 commit_done_id_o,
    // write-combining telemetry (free-running): merges performed
    output logic [31:0]                   stat_merge_o,

    output logic                          busy_o
);

    import mc_common_pkg::*;

    // ---- entry state -------------------------------------------------------
    logic                    r_valid [NUM_ENTRIES];
    logic [BKW-1:0]          r_bank  [NUM_ENTRIES];
    logic [ROW_WIDTH-1:0]    r_row   [NUM_ENTRIES];
    logic [COL_WIDTH-1:0]    r_col   [NUM_ENTRIES];
    logic [IW-1:0]           r_id    [NUM_ENTRIES];
    logic [3:0]              r_qos   [NUM_ENTRIES];
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
    logic                    r_agg   [NUM_ENTRIES];   // part of a split host burst
    logic                    r_last  [NUM_ENTRIES];   // final sub of that burst
    logic                    r_mgv   [NUM_ENTRIES];   // a second write merged in: commit owes a 2nd B
    logic [IW-1:0]           r_mgid  [NUM_ENTRIES];   // ... with this AXI id
    logic                    r_mgfill[NUM_ENTRIES];   // merge fill in progress: the drain fetch waits
    logic [AGE_WIDTH-1:0]    r_age_ctr;

    // Age-order matrix: r_older[i][j] = entry i was inserted strictly before
    // entry j (i is "older"). The relative order of two live entries never
    // changes, so this is maintained on INSERT only. It replaces the
    // free-running-age argmax key on the scheduler path with 1-bit compares;
    // r_age/r_age_ctr/w_rel are kept only for the snarf youngest-match (which is
    // off the scheduler/bank-timer critical path).
    logic [NUM_ENTRIES-1:0]  r_older [NUM_ENTRIES];

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
    logic [NUM_ENTRIES-1:0]  r_age_exceed;   // registered age flags (see sch_age_exceed_o)
    always_comb
        for (int i = 0; i < NUM_ENTRIES; i++)
            w_rel[i] = r_age_ctr - r_age[i];

    // ---- data SRAM (N_SRAM_SLOTS * AXI_BEATS_PER_BURST beats) ----------------
    // Was a distributed flop array {r_sram,r_strb} with COMBINATIONAL multi-port
    // reads -- LUT-heavy (the wide read muxes) and 0 BRAM used. Now ONE BRAM word
    // per (slot,beat) holding {strb,data} packed, with a SYNCHRONOUS (registered)
    // read -> infers block RAM. One write port (fill) + one read port SHARED by
    // the snarf and commit streams (never concurrent; commit has priority).
    // The synchronous read has 1-cycle latency; a 2-DEEP PREFETCH SKID (below)
    // decouples fetch from consume so the read port stays busy across burst
    // boundaries (beat-0 of the next burst prefetches while the current tail
    // drains). {strb,data} stay in the same word so a read returns them
    // atomically (strobes in sync with data).
    // Data only in the BRAM (byte-enable writes, so a merge lands its strobed bytes
    // without a read-modify-write); the strobes live in flops beside it, ORed on a
    // merge, and are snapshotted at fetch issue into the skid tag with the data.
    localparam int SRW = DW;
    (* ram_style = "block" *)
    logic [DW-1:0]   r_mem  [N_SRAM_SLOTS*AXI_BEATS_PER_BURST];
    logic [SW-1:0]   r_strb [N_SRAM_SLOTS*AXI_BEATS_PER_BURST];
    logic [DW-1:0]   r_rd_q;    // BRAM read-data register (output of the sync read)

    // ---- 2-deep prefetch skid FIFO (cross-burst) ---------------------------
    // Decouples FETCH from CONSUME so beat-0 of the NEXT burst can be prefetched
    // while the current burst's tail still drains -> no per-burst bubble. Each
    // entry carries a full tag so the consume side never needs the source-FIFO
    // head (which has already advanced to the next burst). One BRAM read port,
    // 1-cycle latency, tracked by an in-flight register (r_if_*); a credit count
    // bounds (outstanding + buffered) <= SKID_DEPTH so a stalled consumer never
    // loses a beat.
    localparam int SKID_DEPTH = 2;
    logic [SRW-1:0]  r_sk_data  [SKID_DEPTH];
    logic [SW-1:0]   r_sk_strb  [SKID_DEPTH]; // strobes (flops), snapshotted at issue
    logic            r_sk_mgv   [SKID_DEPTH]; // entry owes a second B
    logic [IW-1:0]   r_sk_mgid  [SKID_DEPTH]; // ... with this id
    logic            r_sk_iscm  [SKID_DEPTH]; // commit (else snarf)
    logic [PTRW-1:0] r_sk_slot  [SKID_DEPTH]; // entry slot (eviction / SRAM free)
    logic            r_sk_blast [SKID_DEPTH]; // last beat of the burst
    logic            r_sk_agg   [SKID_DEPTH]; // r_agg of the entry (B consolidation)
    logic            r_sk_slast [SKID_DEPTH]; // r_last of the entry (final sub-cmd)
    logic [IW-1:0]   r_sk_id    [SKID_DEPTH]; // r_id  of the entry (B id)
    logic            r_sk_rd;                 // head pointer (1 bit; DEPTH=2)
    logic            r_sk_wr;                 // tail pointer
    logic [1:0]      r_sk_cnt;                // occupancy 0..2
    logic [1:0]      r_credits;               // SKID_DEPTH - (outstanding + buffered)

    // Snarf anti-starvation. The single BRAM read port is shared by the commit
    // (write-drain) and snarf (read-your-write forward) streams with COMMIT
    // PRIORITY -- the DRAM write-drain is the bandwidth path. Unbounded priority
    // would let a sustained commit drain starve a pending snarf forever (a
    // multi-ID out-of-order master keeps the drain FIFO non-empty). r_sn_wait
    // counts cycles a pending snarf is preempted by commit; at SN_STARVE_LIMIT
    // the snarf is granted one fetch, bounding forwarded-read latency without a
    // second read port (a RAMB36 cannot do 2 reads + 1 write).
    localparam int   SN_STARVE_LIMIT = 16;
    logic [4:0]      r_sn_wait;
    logic            w_sn_starved;

    // in-flight read (issued last cycle; its data lands in r_rd_q this cycle)
    logic            r_if_valid;
    logic            r_if_iscm;
    logic [PTRW-1:0] r_if_slot;
    logic            r_if_blast;
    logic            r_if_agg;
    logic            r_if_slast;
    logic [IW-1:0]   r_if_id;
    logic [SW-1:0]   r_if_strb;
    logic            r_if_mgv;
    logic [IW-1:0]   r_if_mgid;

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
    // Record = {merge, bank, row, col, id, qos, slot}. A merge record allocated no
    // entry at insert; it carries the write's key so the fill engine can find its
    // target (or allocate afresh if the target is gone) when the data arrives.
    localparam int FQW = 1 + BKW + ROW_WIDTH + COL_WIDTH + IW + 4 + PTRW;
    logic             w_fq_wr_valid, w_fq_wr_ready, w_fq_rd_valid, w_fq_rd_ready;
    logic [PTRW-1:0]  w_fq_rd_slot;
    logic [FQW-1:0]   w_fq_wr_data,  w_fq_rd_data;
    logic             w_fq_merge;
    logic [BKW-1:0]   w_fq_bank;
    logic [ROW_WIDTH-1:0] w_fq_row;
    logic [COL_WIDTH-1:0] w_fq_col;
    logic [IW-1:0]    w_fq_id;
    logic [3:0]       w_fq_qos;
    // declared here (used by the fill-time merge decision below, assigned in the
    // commit section): the arbiter's commit accept this cycle
    logic w_commit_fire, w_dq_pop;
    // ---- insert-time merge candidate (pumice TASK-060) ------------------------
    // Youngest live, unscheduled, un-merged, non-split entry with the same key.
    // No entry is allocated for a merge; the decision is re-made at fill time
    // against the live entry (the arbiter sees sch_valid one cycle stale, so an
    // entry can still be committed after we chose it -- the fill side handles it).
    logic [NUM_ENTRIES-1:0] w_mg_match;
    logic                   w_mg_found, w_mg_idclash, w_sn_idle, w_mg_hit;
    logic                   w_fb_alloc;   // fill-time fallback allocation this cycle
    always_comb begin
        automatic logic [NUM_ENTRIES-1:0] yg;
        for (int i = 0; i < NUM_ENTRIES; i++)
            w_mg_match[i] = MERGE_EN && r_valid[i] && !r_sched[i] && !r_mgv[i] && !r_mgfill[i]
                            && !r_agg[i] && !ins_agg_i
                            && (r_bank[i] == ins_bank_i) && (r_row[i] == ins_row_i)
                            && (r_col[i] == ins_col_i);
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            automatic logic y = 1'b1;
            for (int j = 0; j < NUM_ENTRIES; j++)
                if ((j != i) && w_mg_match[j] && !r_older[j][i]) y = 1'b0;
            yg[i] = w_mg_match[i] && y;
        end
        w_mg_found = |yg;
        // another live write with the merged write's id (not the target) would get
        // its B after ours although its AW came first -- same-id B order forbids it
        w_mg_idclash = 1'b0;
        for (int j = 0; j < NUM_ENTRIES; j++)
            if (r_valid[j] && !yg[j] && (r_id[j] == ins_id_i)) w_mg_idclash = 1'b1;
    end
    assign w_mg_hit = w_mg_found && !w_mg_idclash && w_sn_idle;
    assign ins_ready_o   = (w_have_free || w_mg_hit) && w_fq_wr_ready && !w_fb_alloc;
    assign w_fq_wr_valid = ins_valid_i && ins_ready_o;
    assign w_fq_wr_data  = {w_mg_hit, ins_bank_i, ins_row_i, ins_col_i, ins_id_i, ins_qos_i,
                            (w_mg_hit ? PTRW'(0) : w_free_slot)};
    gaxi_fifo_sync #(.DATA_WIDTH(FQW), .DEPTH(NUM_ENTRIES)) u_fill_q (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_fq_wr_valid),
        .wr_ready   (w_fq_wr_ready),
        .wr_data    (w_fq_wr_data),
        .rd_ready   (w_fq_rd_ready),
        .count      (),
        .rd_valid   (w_fq_rd_valid),
        .rd_data    (w_fq_rd_data)
    );
    assign {w_fq_merge, w_fq_bank, w_fq_row, w_fq_col, w_fq_id, w_fq_qos, w_fq_rd_slot} = w_fq_rd_data;
    logic w_ins_fire, w_ins_alloc;
    assign w_ins_fire  = ins_valid_i && ins_ready_o;
    assign w_ins_alloc = w_ins_fire && !w_mg_hit;          // allocates an entry

    // ---- fill engine : write burst into SRAM[ptr] --------------------------
    // On the first beat a free SRAM slot must be available (pre-allocate).
    logic [BCW-1:0] r_fill_beat;
    // ---- fill-time merge decision (first beat of a merge record) -------------
    // Re-find the target from the record's key among the LIVE entries. Gone, or
    // being committed this very cycle, or now carrying another merge, or an id
    // clash that arose meanwhile -> fall back to a fresh entry for this write.
    logic [NUM_ENTRIES-1:0] w_mgt_match;
    logic                   w_mgt_found, w_mgt_idclash;
    logic [PTRW-1:0]        w_mgt_slot;
    always_comb begin
        automatic logic [NUM_ENTRIES-1:0] yg;
        for (int i = 0; i < NUM_ENTRIES; i++)
            w_mgt_match[i] = MERGE_EN && r_valid[i] && !r_sched[i] && !r_mgv[i] && !r_mgfill[i]
                             && !r_agg[i] && r_fdone[i]
                             && !(w_commit_fire && (commit_slot_i == PTRW'(i)))
                             && (r_bank[i] == w_fq_bank) && (r_row[i] == w_fq_row)
                             && (r_col[i] == w_fq_col);
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            automatic logic y = 1'b1;
            for (int j = 0; j < NUM_ENTRIES; j++)
                if ((j != i) && w_mgt_match[j] && !r_older[j][i]) y = 1'b0;
            yg[i] = w_mgt_match[i] && y;
        end
        w_mgt_found = |yg;
        w_mgt_slot  = '0;
        for (int i = NUM_ENTRIES-1; i >= 0; i--) if (yg[i]) w_mgt_slot = PTRW'(i);
        w_mgt_idclash = 1'b0;
        for (int j = 0; j < NUM_ENTRIES; j++)
            if (r_valid[j] && !yg[j] && (r_id[j] == w_fq_id)) w_mgt_idclash = 1'b1;
    end
    logic            w_fill_first;
    logic            w_fill_merge_now;   // first beat: this record merges into w_mgt_slot
    logic            r_fill_merge;       // latched for beats 2..N
    logic [PTRW-1:0] r_fill_eslot;       // latched entry slot for beats 2..N
    logic            w_fill_merge;       // this beat is a merge write
    logic [PTRW-1:0] w_fill_eslot;       // entry slot this beat belongs to
    assign w_fill_first     = (r_fill_beat == '0);
    assign w_fill_merge_now = w_fq_merge && w_mgt_found && !w_mgt_idclash && w_sn_idle;
    assign w_fill_merge     = w_fill_first ? w_fill_merge_now : r_fill_merge;
    assign w_fill_eslot     = w_fill_first ? (w_fill_merge_now ? w_mgt_slot
                                             : (w_fq_merge ? w_free_slot : w_fq_rd_slot))
                                           : r_fill_eslot;
    // a merge record whose target is gone allocates its own entry on its first beat
    assign w_fb_alloc = w_fq_rd_valid && w_fill_first && w_fq_merge && !w_fill_merge_now
                        && wd_valid_i && w_have_free && w_slot_free_found;
    assign wd_ready_o = w_fq_rd_valid
                        && (!w_fill_first
                            || (w_fill_merge_now ? 1'b1
                                : (w_slot_free_found && (!w_fq_merge || w_have_free))));
    logic w_wd_fire;
    assign w_wd_fire = wd_valid_i && wd_ready_o;
    assign w_fq_rd_ready = w_wd_fire && wd_last_i;
    // byte enables: a merge writes only its strobed bytes; a fresh fill writes all
    logic [SW-1:0] w_fill_we;
    assign w_fill_we = w_fill_merge ? wd_strb_i : {SW{1'b1}};

    // ---- snarf youngest-match (combinational) ------------------------------
    // Read-your-write forwarding is LIMITED to the safe case: the read may snarf
    // a write only when
    //   (1) the write is NOT yet scheduled (!r_sched) — a scheduled write is
    //       draining/evicting to DRAM, so its CAM data is racy;
    //   (2) the AXI ids match — same-id W-before-R is the only AXI-ordered case
    //       where the read is REQUIRED to see the write (cross-id has no ordering
    //       guarantee, so the read takes the DRAM path instead);
    //   (3) the read's burst length equals the write's. Every admitted write is
    //       exactly AXI_BEATS_PER_BURST beats (ragged bursts are rejected in mc_wr_intake), so
    //       this reduces to arlen == AXI_BEATS_PER_BURST-1 — a short/long read must not snarf a
    //       full-AXI_BEATS_PER_BURST write.
    // The probe from mc_rd_intake is REGISTERED here (r_sp_*) before the
    // associative compare, so the rd_intake->wr_cam cross-module route (the
    // worst w_sys_i path) gets a full cycle. Youngest match uses the age-order
    // matrix (i is youngest iff every OTHER matched j is older: r_older[j][i])
    // instead of a 16-bit rel-age argmin. snarf_hit_o is thus valid one cycle
    // after the probe is presented; rd_intake holds the AR and admits on it.
    logic                 r_sp_valid;
    logic [BKW-1:0]       r_sp_bank;
    logic [ROW_WIDTH-1:0] r_sp_row;
    logic [COL_WIDTH-1:0] r_sp_col;
    logic [IW-1:0]        r_sp_id;
    logic [7:0]           r_sp_len;

    logic [NUM_ENTRIES-1:0] w_sn_match;
    logic            w_sn_found;
    logic [PTRW-1:0] w_sn_slot;
    logic            w_sn_len_ok;
    assign w_sn_len_ok = (r_sp_len == 8'(AXI_BEATS_PER_BURST - 1));
    always_comb begin
        automatic logic [NUM_ENTRIES-1:0] is_young;
        for (int i = 0; i < NUM_ENTRIES; i++)
            w_sn_match[i] = r_valid[i] && r_fdone[i] && !r_sched[i]
                            && (r_id[i]   == r_sp_id)
                            && (r_bank[i] == r_sp_bank)
                            && (r_row[i]  == r_sp_row)
                            && (r_col[i]  == r_sp_col);
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            automatic logic yg = 1'b1;
            for (int j = 0; j < NUM_ENTRIES; j++)
                if ((j != i) && w_sn_match[j] && !r_older[j][i]) yg = 1'b0;
            is_young[i] = w_sn_match[i] && yg;
        end
        w_sn_found = |is_young;
        w_sn_slot  = '0;
        for (int i = NUM_ENTRIES-1; i >= 0; i--)
            if (is_young[i]) w_sn_slot = PTRW'(i);
    end
    assign snarf_hit_o = r_sp_valid && w_sn_found && w_sn_len_ok;

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

    // ---- per-entry scheduling vectors (registered fields, 1-level derive) ---
    // ---- scheduler-side oldest SCHEDULABLE entry, via the age-order matrix --
    // Same idiom as the drain-side oldest-valid pick above, and for the same
    // reason: the obvious form -- a max-reduce over w_rel[] -- is a SERIAL
    // chain of NUM_ENTRIES x (AGE_WIDTH subtract + compare + mux), and it puts
    // the free-running r_age_ctr straight onto the w_sys_i scheduling path.
    //
    // That is not theoretical. It was the worst path in the whole design on
    // the first synthesis since the mode work landed: 63.6 ns against a 15 ns
    // period, 89 logic levels, 30 carry chains, and 17.8 ns of LOGIC alone --
    // unfixable by placement. See pumice ISSUE-005 (was PUMICE-017).
    //
    // The matrix is registered and its compares are 1 bit, so finding the
    // oldest costs a shallow NUM_ENTRIES^2 AND-reduce; only the winner's
    // relative age needs the AGE_WIDTH subtract. Identical value, no pipeline
    // stage, no staleness.
    logic            w_sho_found;
    logic [PTRW-1:0] w_sho_slot;
    always_comb begin
        automatic logic [NUM_ENTRIES-1:0] w_sho_sched;
        automatic logic [NUM_ENTRIES-1:0] w_sho_is;
        for (int i = 0; i < NUM_ENTRIES; i++)
            w_sho_sched[i] = r_valid[i] && r_fdone[i] && !r_sched[i];
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            automatic logic ge_all = 1'b1;
            for (int j = 0; j < NUM_ENTRIES; j++)
                if ((j != i) && w_sho_sched[j] && !r_older[i][j]) ge_all = 1'b0;
            w_sho_is[i] = w_sho_sched[i] && ge_all;
        end
        w_sho_found = |w_sho_is;
        w_sho_slot  = '0;
        for (int i = NUM_ENTRIES-1; i >= 0; i--)
            if (w_sho_is[i]) w_sho_slot = PTRW'(i);
    end

    always_comb begin
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            sch_valid_o[i]                       = r_valid[i] && r_fdone[i] && !r_sched[i];
            sch_pend_o [i]                       = r_valid[i] && !r_fdone[i];
            sch_bank_o [i*BKW       +: BKW]      = r_bank[i];
            sch_row_o  [i*ROW_WIDTH +: ROW_WIDTH] = r_row[i];
            sch_col_o  [i*COL_WIDTH +: COL_WIDTH] = r_col[i];
            sch_older_o[i*NUM_ENTRIES +: NUM_ENTRIES] = r_older[i];
            sch_qos_o[i*4 +: 4] = r_qos[i];
            // Registered (one cycle stale) -- see mc_rd_cmd_cam: the
            // per-entry 16-bit age compare stays inside the CAM behind a
            // flop instead of feeding the arbiter's mask cone directly.
            sch_age_exceed_o[i] = r_valid[i] && r_fdone[i] && !r_sched[i]
                                && r_age_exceed[i];
        end
        sch_head_rel_o = w_sho_found ? w_rel[w_sho_slot] : '0;
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_age_exceed <= '0;
        end else begin
            for (int i = 0; i < NUM_ENTRIES; i++)
                r_age_exceed[i] <= r_valid[i] && (age_thresh_i != 8'd0)
                                && (w_rel[i] >= AGE_WIDTH'({age_thresh_i, 4'h0}));
            if (w_ins_alloc || w_fb_alloc) r_age_exceed[w_free_slot] <= 1'b0;
        end
    )

    // ---- snarf-stream request FIFO (slots to stream, in accept order) ------
    logic            w_sq_wr_valid, w_sq_wr_ready, w_sq_rd_valid, w_sq_rd_ready;
    logic [PTRW-1:0] w_sq_rd_slot;

    assign w_sq_wr_valid = snarf_accept_i && snarf_hit_o;

    gaxi_fifo_sync #(.DATA_WIDTH(PTRW), .DEPTH(NUM_ENTRIES)) u_snarf_q (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_sq_wr_valid),
        .wr_ready   (w_sq_wr_ready),
        .wr_data    (w_sn_slot),
        .rd_ready   (w_sq_rd_ready),
        .count      (),
        .rd_valid   (w_sq_rd_valid),
        .rd_data    (w_sq_rd_slot)
    );

    // ---- commit (scheduled-slot) drain FIFO --------------------------------
    // The arbiter's commit marks a slot scheduled (1 cycle, excluded from
    // sched_lu/oldest immediately => 1 cmd/clock) and enqueues it here. The
    // drain read-engine works through scheduled slots at its own pace, streaming
    // cm_rd to the DFI plane and evicting on last. Decouples marking from drain.
    logic            w_dq_wr_valid, w_dq_wr_ready, w_dq_rd_valid, w_dq_rd_ready;
    logic [PTRW-1:0] w_dq_rd_slot;

    logic [PTRW:0]   r_dq_occ;       // registered drain-queue occupancy (no FIFO-count loop)

    // RATE-MATCHED commit (2026-09-09): a WR may commit only while fewer than
    // WR_DRAIN_AHEAD bursts sit in the drain queue (the head is the burst being
    // fetched, popped at its last beat). The data path then trails its command
    // by a FIXED pipeline latency, never by a queue -- with the old "room in
    // the FIFO" gate the command stream ran up to 16 commands ahead of the
    // data (measured 20 aclk), and no downstream gate can fix that without
    // stalling the in-order command stream. One WR per BL_WORDS cycles is the
    // DQ rate, so this costs no bandwidth. Pairs with the scheduler's fixed
    // command delay (CMD_DELAY) and the DFI write-staged token invariant.
    // Two predicates, one cycle apart. The arbiter DECIDES a write one cycle
    // before it FIRES, so commit_ready_o answers "will a commit decided now be
    // accepted next cycle": occupancy after this cycle's own accept and pop.
    // The accept itself (w_commit_fire) uses the current occupancy -- a fire
    // that the decision-time predicate allowed can only find more room, never
    // less (only pops happen in between). Without the split, two back-to-back
    // writes let the second fire into the cmd FIFO while the CAM refused it:
    // a DRAM WR whose data never drains (the DFI staged gate then holds for
    // ever -- measured 29373-cycle hold, AW/W/AR timeouts).
    logic [PTRW:0] w_dq_occ_next;
    assign w_commit_fire = commit_valid_i && w_dq_wr_ready
                         && (r_dq_occ < (PTRW+1)'(WR_DRAIN_AHEAD));
    assign w_dq_wr_valid = w_commit_fire;
    assign w_dq_pop      = w_dq_rd_valid && w_dq_rd_ready;
    assign w_dq_occ_next = r_dq_occ + (w_commit_fire ? (PTRW+1)'(1) : (PTRW+1)'(0))
                                    - (w_dq_pop      ? (PTRW+1)'(1) : (PTRW+1)'(0));
    assign commit_ready_o = w_dq_wr_ready && (w_dq_occ_next < (PTRW+1)'(WR_DRAIN_AHEAD));
    // The accept condition itself, exported for a core that must not read
    // commit_valid back (mc_bank_pick, recovery Phase 3): registered
    // occupancy and the queue's own ready, NO pop term. The drain pop reaches
    // through the fetch arbitration to BOTH consumer readies (cm_rd_ready_i
    // from the DFI plane, snarf_rd_ready_i from the AXI plane), so a
    // predicate that subtracted it was the worst post-route cone at 100 MHz
    // (AXI-plane order FIFO -> this pop -> the arbiter's winner register,
    // 18 levels, -2.5 ns). Without the pop the predicate is pessimistic by
    // one cycle only when the queue is full and emptying in the same cycle,
    // which the rate-matched stream (one commit per BL_WORDS cycles, one pop
    // per BL_WORDS cycles, occupancy steady at one) never reaches.
    assign commit_ready_now_o = w_dq_wr_ready && (r_dq_occ < (PTRW+1)'(WR_DRAIN_AHEAD));

    gaxi_fifo_sync #(.DATA_WIDTH(PTRW), .DEPTH(NUM_ENTRIES)) u_drain_q (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_dq_wr_valid),
        .wr_ready   (w_dq_wr_ready),
        .wr_data    (commit_slot_i),
        .rd_ready   (w_dq_rd_ready),
        .count      (),
        .rd_valid   (w_dq_rd_valid),
        .rd_data    (w_dq_rd_slot)
    );

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_dq_occ <= '0;
        else                        r_dq_occ <= w_dq_occ_next;
    )

    // Fill target SRAM slot: allocate a free slot on the first beat, else reuse
    // the slot already recorded in the entry's ptr.
    logic [SPTRW-1:0] w_fill_slot;
    assign w_fill_slot  = w_fill_merge ? r_ptr[w_fill_eslot]
                        : (w_fill_first ? w_slot_free : r_ptr[w_fill_eslot]);

    // Engine state: just a burst beat-counter each — NO active/slot FSM. Both
    // readers stream straight off their request-FIFO head (stable until popped),
    // exactly like the fill engine reads its fill FIFO. The head slot IS the
    // "active" slot; "active" == FIFO non-empty; the slot FIFO is popped on the
    // last beat. (declared before the index helpers that reference them)
    // address-side beat pointers -- run one beat AHEAD of the presented beat so
    // each stream sustains 1 beat/cycle over the synchronous-read BRAM.
    logic [BCW-1:0]  r_cm_fbeat;  // commit fetch beat (next beat to issue)
    logic [BCW-1:0]  r_sn_fbeat;  // snarf  fetch beat (next beat to issue)

    // SRAM flat-index helpers (index by the FIFO-head slot's ptr; 32-bit width)
    logic [31:0] w_sn_idx, w_cm_idx, w_fill_idx;
    assign w_sn_idx   = 32'(r_ptr[w_sq_rd_slot]) * 32'(AXI_BEATS_PER_BURST) + 32'(r_sn_fbeat);
    assign w_cm_idx   = 32'(r_ptr[w_dq_rd_slot]) * 32'(AXI_BEATS_PER_BURST) + 32'(r_cm_fbeat);
    assign w_fill_idx = 32'(w_fill_slot)         * 32'(AXI_BEATS_PER_BURST) + 32'(r_fill_beat);

    // ---- 2-deep prefetch skid over the BRAM (snarf XOR commit) --------------
    // The consume side reads the skid head; its carried tag drives last, the B
    // strobe and the eviction. Commit and snarf share the single BRAM read port;
    // only the per-cycle PORT GRANT is exclusive (commit priority + snarf anti-
    // starvation, below) -- the two source FIFOs are independent and can both be
    // non-empty, so aggregate concurrent snarf+commit throughput is 1 beat/cycle
    // (the accepted price of one BRAM read port). One skid suffices; the per-
    // entry is_cm tag routes each beat to the right consumer, and a stalled
    // consumer of one stream can head-of-line-block a beat of the other.
    logic            w_hd_vld, w_hd_iscm, w_hd_blast, w_hd_agg, w_hd_slast;
    logic            w_hd_mgv;
    logic [IW-1:0]   w_hd_mgid;
    logic [SW-1:0]   w_hd_strb;
    logic [SRW-1:0]  w_hd_data;
    logic [IW-1:0]   w_hd_id;
    assign w_hd_vld   = (r_sk_cnt != 2'd0);
    assign w_hd_data  = r_sk_data [r_sk_rd];
    assign w_hd_iscm  = r_sk_iscm [r_sk_rd];
    assign w_hd_blast = r_sk_blast[r_sk_rd];
    assign w_hd_agg   = r_sk_agg  [r_sk_rd];
    assign w_hd_slast = r_sk_slast[r_sk_rd];
    assign w_hd_id    = r_sk_id   [r_sk_rd];
    assign w_hd_mgv   = r_sk_mgv  [r_sk_rd];
    assign w_hd_mgid  = r_sk_mgid [r_sk_rd];
    assign w_hd_strb  = r_sk_strb [r_sk_rd];
    // no snarf stream anywhere (queued, in flight, or at the skid head): a merge
    // must not change data a read ordered before it is about to be forwarded
    assign w_sn_idle  = !w_sq_rd_valid && !(r_if_valid && !r_if_iscm) && !(w_hd_vld && !w_hd_iscm);

    logic w_cm_fire, w_sn_fire, w_pop, w_room;
    // A beat that will push the done queue (the burst-last of the final sub)
    // waits for room there. A merged burst takes two pops of that queue, so a
    // drain of one burst per cycle -- open row, single-beat bursts, every pair
    // merged -- overran the 4-deep queue and the overrun pushes, which are B
    // responses, were lost (board open_page/half_pair write hang, TASK-060).
    // Room only grows between a raise and the fire (pops add it, only this
    // fire takes it), so valid never drops once asserted.
    logic w_dn_would_push, w_dn_wr_ready;
    assign w_dn_would_push  = w_hd_blast && (!w_hd_agg || w_hd_slast);
    assign cm_rd_valid_o    = w_hd_vld &&  w_hd_iscm && (!w_dn_would_push || w_dn_wr_ready);
    assign snarf_rd_valid_o = w_hd_vld && !w_hd_iscm;
    assign cm_rd_data_o     = w_hd_data[DW-1:0];
    assign cm_rd_strb_o     = w_hd_strb;
    assign snarf_rd_data_o  = w_hd_data[DW-1:0];
    assign cm_rd_last_o     = w_hd_blast;
    assign snarf_rd_last_o  = w_hd_blast;
    assign w_cm_fire = cm_rd_valid_o    && cm_rd_ready_i;
    assign w_sn_fire = snarf_rd_valid_o && snarf_rd_ready_i;
    assign w_pop     = w_cm_fire || w_sn_fire;

    // fetch arbitration: commit priority; issue only when a credit is free (or a
    // pop frees one this cycle). Pop the source slot FIFO at FETCH-last so the
    // fetch pointer can advance into the NEXT burst's slot immediately, keeping
    // the read port busy across the burst boundary (the bubble fix).
    logic        w_cm_fetch, w_sn_fetch, w_issue;
    logic [31:0] w_rd_idx;
    assign w_room     = (r_credits != 2'd0) || w_pop;
    assign w_sn_starved = (r_sn_wait >= 5'(SN_STARVE_LIMIT));
    // snarf wins the port when commit is idle OR snarf has waited too long;
    // commit wins otherwise. The two are mutually exclusive by construction.
    assign w_sn_fetch = w_room && w_sq_rd_valid && (!w_dq_rd_valid || w_sn_starved);
    // the drain never reads a slot whose merge fill is still landing (bounded wait;
    // the DFI write-staged gate holds the WR command until its data is staged)
    assign w_cm_fetch = w_room &&  w_dq_rd_valid && !w_sn_fetch && !r_mgfill[w_dq_rd_slot];
    assign w_issue    = w_cm_fetch || w_sn_fetch;
    assign w_rd_idx   = w_cm_fetch ? w_cm_idx : w_sn_idx;
    assign w_dq_rd_ready = w_cm_fetch && (r_cm_fbeat == BCW'(AXI_BEATS_PER_BURST-1));
    assign w_sq_rd_ready = w_sn_fetch && (r_sn_fbeat == BCW'(AXI_BEATS_PER_BURST-1));

    // B consolidation: one B per host burst, strobed on the FINAL sub-command's
    // commit-last (agg && slast). Non-split bursts (agg=0) always strobe. Sourced
    // from the CARRIED tag (the drain FIFO head has already advanced past it).
    // One B per host burst, strobed on the FINAL sub-command's commit-last (agg &&
    // slast); non-split bursts always strobe. A merged entry owes a SECOND B with
    // the merged write's id, so the done rides a small queue and drains one id per
    // cycle: {id} then {mgid}.
    logic           w_dn_push, w_dn_rd_valid, w_dn_mgv;
    logic [IW-1:0]  w_dn_id, w_dn_mgid;
    logic           r_dn_second;
    assign w_dn_push = w_cm_fire && w_dn_would_push;
    gaxi_fifo_sync #(.DATA_WIDTH(1 + 2*IW), .DEPTH(4)) u_done_q (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (w_dn_push),
        .wr_ready   (w_dn_wr_ready),
        .wr_data    ({w_hd_mgv, w_hd_mgid, w_hd_id}),
        .rd_ready   (commit_done_valid_o && (!w_dn_mgv || r_dn_second)),
        .count      (),
        .rd_valid   (w_dn_rd_valid),
        .rd_data    ({w_dn_mgv, w_dn_mgid, w_dn_id})
    );
    assign commit_done_valid_o = w_dn_rd_valid;
    assign commit_done_id_o    = r_dn_second ? w_dn_mgid : w_dn_id;
    assign busy_o = w_old_found || w_sq_rd_valid || w_dq_rd_valid || w_fq_rd_valid
                    || w_hd_vld || r_if_valid || w_dn_rd_valid;

    // ---- sequential --------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_age_ctr   <= '0;
            r_fill_beat <= '0;
            r_cm_fbeat  <= '0;
            r_sn_fbeat  <= '0;
            r_sram_occ  <= '0;
            r_sp_valid  <= 1'b0;
            r_sk_rd     <= 1'b0;
            r_sk_wr     <= 1'b0;
            r_sk_cnt    <= 2'd0;
            r_credits   <= 2'(SKID_DEPTH);
            r_if_valid  <= 1'b0;
            r_sn_wait   <= 5'd0;
            r_dn_second <= 1'b0;
            r_fill_merge <= 1'b0;
            r_fill_eslot <= '0;
            stat_merge_o <= 32'h0;
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                r_valid[i] <= 1'b0;
                r_pv[i]    <= 1'b0;
                r_fdone[i] <= 1'b0;
                r_sched[i] <= 1'b0;
                r_older[i] <= '0;
                r_mgv[i]   <= 1'b0;
                r_mgfill[i]<= 1'b0;
            end
        end else begin
            r_age_ctr <= r_age_ctr + 1'b1;

            // register the snarf probe (pipelines the rd_intake->wr_cam route)
            r_sp_valid <= snarf_probe_valid_i;
            r_sp_bank  <= snarf_probe_bank_i;
            r_sp_row   <= snarf_probe_row_i;
            r_sp_col   <= snarf_probe_col_i;
            r_sp_id    <= snarf_probe_id_i;
            r_sp_len   <= snarf_probe_len_i;

            // insert : allocate + capture key/id/age; fill not yet done
            if (w_ins_alloc || w_fb_alloc) begin
                // a normal insert, or a merge record whose target is gone allocating
                // its own entry at its first data beat (never both in one cycle:
                // ins_ready_o is held off while w_fb_alloc)
                r_valid[w_free_slot] <= 1'b1;
                r_bank [w_free_slot] <= w_fb_alloc ? w_fq_bank : ins_bank_i;
                r_row  [w_free_slot] <= w_fb_alloc ? w_fq_row  : ins_row_i;
                r_col  [w_free_slot] <= w_fb_alloc ? w_fq_col  : ins_col_i;
                r_id   [w_free_slot] <= w_fb_alloc ? w_fq_id   : ins_id_i;
                r_qos  [w_free_slot] <= w_fb_alloc ? w_fq_qos  : ins_qos_i;
                r_age  [w_free_slot] <= r_age_ctr;
                r_fdone[w_free_slot] <= 1'b0;
                r_agg  [w_free_slot] <= w_fb_alloc ? 1'b0 : ins_agg_i;
                r_last [w_free_slot] <= w_fb_alloc ? 1'b1 : ins_last_i;
                r_mgv  [w_free_slot] <= 1'b0;
                r_mgfill[w_free_slot] <= 1'b0;
                // age matrix: the new slot is the YOUNGEST -> older than nobody,
                // and every other slot is older than it.
                for (int j = 0; j < NUM_ENTRIES; j++) begin
                    r_older[w_free_slot][j] <= 1'b0;
                    if (j != int'(w_free_slot)) r_older[j][w_free_slot] <= 1'b1;
                end
            end

            // fill : allocate SRAM slot on first beat, then write burst. Mark the
            // entry fill-COMPLETE on the last beat so it becomes schedulable/
            // snarfable only once every beat is staged in SRAM.
            if (w_wd_fire) begin
                if (w_fill_first) begin
                    r_fill_merge <= w_fill_merge_now;
                    r_fill_eslot <= w_fill_eslot;
                    if (!w_fill_merge_now) begin
                        r_ptr[w_fill_eslot]  <= w_slot_free;
                        r_pv [w_fill_eslot]  <= 1'b1;
                        r_sram_occ[w_slot_free] <= 1'b1;
                    end else begin
                        // merging: the target leaves the schedulable set until the
                        // merged bytes have landed (a commit already decided waits
                        // on r_mgfill at the drain fetch instead)
                        r_fdone [w_fill_eslot] <= 1'b0;
                        r_mgfill[w_fill_eslot] <= 1'b1;
                    end
                end
                r_fill_beat <= wd_last_i ? '0 : (r_fill_beat + 1'b1);
                if (wd_last_i) begin
                    r_fdone[w_fill_eslot] <= 1'b1;
                    if (w_fill_merge) begin
                        r_mgfill[w_fill_eslot] <= 1'b0;
                        r_mgv   [w_fill_eslot] <= 1'b1;
                        r_mgid  [w_fill_eslot] <= w_fq_id;
                        stat_merge_o <= stat_merge_o + 32'h1;
                    end
                end
            end
            // done queue: {id} then {mgid}
            if (commit_done_valid_o)
                r_dn_second <= w_dn_mgv && !r_dn_second;

            // ---- 2-deep prefetch skid pipeline --------------------------------
            // Stage 1 (issue): pick a beat, issue the BRAM read, latch its tag as
            // in-flight. Stage 2 (capture, next cycle): r_rd_q holds the data and
            // r_if_* the tag -> push into the skid FIFO. Credits bound (outstanding
            // + buffered) to SKID_DEPTH so a stalled consumer never loses a beat.
            r_if_valid <= w_issue;
            if (w_issue) begin
                r_if_iscm  <= w_cm_fetch;
                r_if_slot  <= w_cm_fetch ? w_dq_rd_slot : w_sq_rd_slot;
                r_if_blast <= w_cm_fetch ? (r_cm_fbeat == BCW'(AXI_BEATS_PER_BURST-1))
                                         : (r_sn_fbeat == BCW'(AXI_BEATS_PER_BURST-1));
                r_if_agg   <= w_cm_fetch ? r_agg [w_dq_rd_slot] : 1'b0;
                r_if_slast <= w_cm_fetch ? r_last[w_dq_rd_slot] : 1'b0;
                r_if_id    <= w_cm_fetch ? r_id  [w_dq_rd_slot] : r_id[w_sq_rd_slot];
                r_if_mgv   <= w_cm_fetch ? r_mgv [w_dq_rd_slot] : 1'b0;
                r_if_mgid  <= r_mgid[w_dq_rd_slot];
                r_if_strb  <= r_strb[w_rd_idx];
            end

            // advance the fetch beat pointer; wrap at the last beat of the burst
            // (the source FIFO is popped combinationally via w_*_rd_ready there,
            // so the next cycle already reads the next burst's slot).
            if (w_cm_fetch) begin
                if (r_cm_fbeat == BCW'(AXI_BEATS_PER_BURST-1)) r_cm_fbeat <= '0;
                else                                           r_cm_fbeat <= r_cm_fbeat + 1'b1;
            end
            if (w_sn_fetch) begin
                if (r_sn_fbeat == BCW'(AXI_BEATS_PER_BURST-1)) r_sn_fbeat <= '0;
                else                                           r_sn_fbeat <= r_sn_fbeat + 1'b1;
            end

            // push the captured in-flight beat into the skid FIFO tail
            if (r_if_valid) begin
                r_sk_data [r_sk_wr] <= r_rd_q;
                r_sk_iscm [r_sk_wr] <= r_if_iscm;
                r_sk_slot [r_sk_wr] <= r_if_slot;
                r_sk_blast[r_sk_wr] <= r_if_blast;
                r_sk_agg  [r_sk_wr] <= r_if_agg;
                r_sk_slast[r_sk_wr] <= r_if_slast;
                r_sk_id   [r_sk_wr] <= r_if_id;
                r_sk_mgv  [r_sk_wr] <= r_if_mgv;
                r_sk_mgid [r_sk_wr] <= r_if_mgid;
                r_sk_strb [r_sk_wr] <= r_if_strb;
                r_sk_wr             <= r_sk_wr + 1'b1;
            end
            if (w_pop) r_sk_rd <= r_sk_rd + 1'b1;
            r_sk_cnt  <= r_sk_cnt  + (r_if_valid ? 2'd1 : 2'd0) - (w_pop   ? 2'd1 : 2'd0);
            r_credits <= r_credits - (w_issue    ? 2'd1 : 2'd0) + (w_pop   ? 2'd1 : 2'd0);

            // snarf anti-starvation counter: clear on grant, else count cycles a
            // pending snarf is preempted by commit (room available, commit won).
            if (w_sn_fetch)                                   r_sn_wait <= 5'd0;
            else if (w_sq_rd_valid && w_room && !w_sn_starved) r_sn_wait <= r_sn_wait + 5'd1;

            // commit MARK: the arbiter's commit sets scheduled (immediate) +
            // enqueues the slot into the drain FIFO. Excluded from sched_lu/
            // oldest next cycle => arbiter can pick another slot right away.
            if (w_commit_fire)
                r_sched[commit_slot_i] <= 1'b1;

            // commit DRAIN evict at FETCH-last (2026-09-09): the burst's last
            // word is read out of the SRAM this cycle, so the entry and its
            // slot are free from the next edge. The B strobe and its id/agg/
            // last ride the skid tag, so the response needs no entry. Freeing
            // here instead of at consume-last takes the whole command delay +
            // CDC + serializer wait out of the entry lifetime; with the
            // rate-matched commit that lifetime was ~30 cycles, and 8 entries
            // could not cover a burst every 4 -- the W channel stalled (bp 222
            // in the write ceiling). Little's law on the write side.
            if (w_dq_rd_valid && w_dq_rd_ready) begin
                r_valid[w_dq_rd_slot]  <= 1'b0;          // evict entry
                r_pv   [w_dq_rd_slot]  <= 1'b0;
                r_fdone[w_dq_rd_slot]  <= 1'b0;
                r_sched[w_dq_rd_slot]  <= 1'b0;
                r_mgv  [w_dq_rd_slot]  <= 1'b0;
                r_mgfill[w_dq_rd_slot] <= 1'b0;
                r_sram_occ[r_ptr[w_dq_rd_slot]] <= 1'b0;  // free SRAM slot
            end
        end
    )

    // -------------------------------------------------------------------------
    // Data storage: a dedicated, RESET-FREE clocked process so Vivado maps it to
    // Block RAM. RAM contents cannot be async-reset; a memory written inside an
    // async-reset process (the design compiles with +define+USE_ASYNC_RESET)
    // reports "RAM is sensitive to asynchronous reset signal" and dissolves into
    // fabric flip-flops -- defeating the whole point of moving data out of the
    // CAM. One write port + one registered read port = simple dual-port BRAM.
    // Behaviour is identical to keeping these two assignments in the RST block:
    // r_mem is never reset, and the read is registered the same cycle.
    //
    // READ LATENCY IS EXACTLY 1 CYCLE and the read-side pipeline depends on it:
    // the address w_rd_idx is combinational, the output r_rd_q is a single
    // register, so data for the address issued in cycle T lands in r_rd_q in
    // T+1 -- which is when the 1-deep in-flight tag (r_if_*) is paired with it
    // and pushed into the skid. Do NOT register the read address or add an
    // output-register stage (a common Fmax move, also selectable on RAMB) unless
    // you deepen the r_if_* tag pipeline to match: otherwise every captured beat
    // pairs with the WRONG tag (slot/last/id) -> silent data corruption and
    // mis-routed B/eviction, with no elaboration error.
    // -------------------------------------------------------------------------
    always_ff @(posedge aclk) begin
        for (int b = 0; b < SW; b++)
            if (w_wd_fire && w_fill_we[b]) r_mem[w_fill_idx][b*8 +: 8] <= wd_data_i[b*8 +: 8];
        if (w_cm_fetch || w_sn_fetch) r_rd_q <= r_mem[w_rd_idx];
    end
    // strobes: flops, ORed on a merge (a fresh fill replaces)
    always_ff @(posedge aclk) begin
        if (w_wd_fire) r_strb[w_fill_idx] <= w_fill_merge ? (r_strb[w_fill_idx] | wd_strb_i) : wd_strb_i;
    end

endmodule : mc_wr_data_cam
