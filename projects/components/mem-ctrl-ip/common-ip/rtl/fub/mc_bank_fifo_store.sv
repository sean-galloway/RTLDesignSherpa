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
//          per-bank queue is exactly that bit. The only row compares per
//          cycle are the two HEADS' hits against the scheduler's open-row
//          image (one per direction per bank).
//
//          The second record's hit is the stored bit too, not a compare. The
//          pick core reads head2 only under its one-cycle pop shadow, i.e.
//          the cycle after it fired the head as a column command; in that
//          cycle the record it reads was formed while that column was firing,
//          against a row image that showed the head's row open (a column
//          fires only against a live-valid row the record classified as a
//          hit). So "head2's row == the open row" is exactly "head2's row ==
//          head's row", which is the same-as-previous bit of head2's queue
//          position. Whether the column carried auto-precharge does not
//          enter: the image the record was formed against predates it either
//          way. Outside the shadow head2 is not read. The compare form cost
//          a 14-bit 8:1 row mux plus a 14-bit compare per record, sixteen
//          records; the stored form is one bit already there.
//
//          A commit or issue always names the HEAD of its bank queue: the pick
//          core fires the head record, or in the one cycle after a pop (the
//          record's registered latency) the second record, which by then is
//          the head (mc_bank_pick, r_shadow). Each (direction, bank) queue is
//          a gaxi_age_fifo_sync (2026-10-25, owner's choice over the linked
//          list it replaces): the entry is {same-row-as-previous, slot}, the
//          FIFO exposes its head and the two entries behind it (PEEK = 2),
//          which is exactly what the records read -- head, second, and the
//          behind flags from the next position. Beside every entry the FIFO
//          keeps the POOL AGE: all sixteen queues share one rank space, the
//          pushed entry's age is 0 into an empty pool, else one above the
//          largest `youngest` across the queues (or equal to it when a
//          retirement happens in the same cycle), and every queue steps its
//          ages toward zero on each commit or issue. The pick fires at most
//          one command per cycle, so one strobe is one retirement. An
//          entry's age is then at most its rank among the live entries, the
//          oldest entry in the pool sits at age 0 at the head of its queue,
//          and that head's rd_age_thresh is the record's age_exceed: the
//          pick's aged-first request class is "the oldest thing in the
//          pool", from the cycle after the retirement that made it so. The
//          rule and its proof are in the FIFO's header; the CSR
//          SCHED_POLICY.age_thresh is the enable (non-zero) and its
//          magnitude is not read. History: a pool-deep position array
//          (~800 LUT, 2026-10-23), a circular form (416 flops per direction),
//          then the linked list (8 x 3 + 2 x 8 x 3 bits, pumice TASK-054);
//          the FIFO form carries NUM_BANKS x QD entries per direction and
//          is measured against the list on the board. The queues are
//          pool-deep by construction and admission is the pool's, exactly
//          as the entry store's.
//
//          The fill-order FIFO (the slot each W beat belongs to, AW order) is
//          circular for the same reason -- it only ever pops its head.
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
//          Admission hold (2026-10-27): a push lands in a one-entry register
//          per direction and is admitted from it a cycle later. The intake's
//          AW / AR meta FIFOs read their RAM by a pointer, so the bank, the
//          row compare and every per-bank admission check (pool slot, queue
//          occupancy, FIFO ready, mixed cap) were one cone from that pointer
//          into all sixteen bank FIFOs' flags: 12 LUTs and 7.9 ns of wire at
//          100 MHz on the board (granite TASK-003 census, -0.346 ns, 40
//          endpoints). The hold's ready is "empty or draining", registers
//          only; one push per cycle as before; one cycle more from the AXI
//          handshake to the record. The pops decode by comparing the fired
//          slot with each queue's live head (a slot sits in exactly one
//          queue) instead of r_*_bank[slot] -> bank: the slot is the fire
//          cone's latest signal and sat in front of an 8:1 mux.
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
    // Per-bank cap that applies ONLY while the other direction holds entries (0 = off).
    // A bank queue may then not grow past BANK_CAP_MIXED; a direction streaming alone
    // keeps pool-deep queues. Measured (pumice TASK-058): a flat cap of 6 gained 8
    // percent on the concurrent two-threads-per-bank family and cost 4 on the
    // eight-thread streams; this form keeps the streams whole.
    parameter int BANK_CAP_MIXED     = 0,
    // Oldest-first promotion (CSR SCHED_POLICY.age_thresh != 0 -> head record age_exceed =
    // "this head is the oldest entry in the pool" -> the pick's aged-first select). 0 ties
    // the queues' age inputs off so the age column folds to constants; age_exceed is 0 and
    // the CSR field is inert (pumice TASK-059 measured the stamp form out at 490 LUT).
    parameter bit HAS_AGE            = 1'b1,
    // Combining (granite TASK-006, pumice's TASK-060 form on the FIFO store):
    // a write whose {bank,row,col} AND AXI id match a live, uncommitted,
    // un-merged single-burst write entry takes no slot -- its beats land in that entry
    // under their strobes (byte enables, strobes OR'ed) and the entry owes a
    // second B with the merged id; a read whose key and id match a live,
    // unissued read entry takes no slot and no ticket of its own -- the plane
    // allocates it as a SHADOW of that entry's ticket (mc_rd_return_ring)
    // and the one DRAM burst returns twice. Different ids never combine
    // (owner's rule, 2026-11-03): two ids are two requestors. 0 = every access
    // its own entry.
    parameter bit MERGE_EN           = 1'b0,
    parameter bit HEAD2_EN           = 1'b1,// 0 = one head record per bank: head2 outputs are constant 0, and the pick
                                            //     core idles a pair for the cycle after each of its column fires (its
                                            //     pop shadow has no second record to serve). A measured trade, not a
                                            //     recommendation: it costs the one-column-per-cycle single-bank stream.
    parameter int AXI_ID_WIDTH       = 8,
    parameter int AXI_DATA_WIDTH     = 64,
    parameter int NUM_RANKS          = 1,
    parameter int NUM_BANKS          = 8,
    parameter int ROW_WIDTH          = 14,
    parameter int COL_WIDTH          = 10,
    parameter int AXI_BEATS_PER_BURST = 4,
    parameter int RD_RET_DEPTH       = 32,
    parameter int WR_DATA_BUF_WORDS  = 16,  // port compatibility with mc_xddr2_entry_store (unused there too)
    // 1 = a read entering an EMPTY bank queue is that bank's head record in
    // the cycle it is written (from the AR hold), registered at the same edge
    // the FIFO takes it, instead of one cycle later off the FIFO front. One
    // cycle less from AR to the pick for an unloaded bank (granite TASK-003,
    // 2026-10-31). The FIFO entry is valid from that same edge, before the
    // pick can fire the record, so a pop always finds it.
    parameter bit HEAD_BYPASS        = 1'b0,
    // 1 = AR_DIRECT: an AR accepted while the AR hold is EMPTY, that is not a
    // merge and can be placed this cycle (free slot, bank queue room, cap),
    // goes into its bank queue from the push inputs in the push cycle instead
    // of through the hold a cycle later. The hold still takes any AR that
    // cannot be placed at once, and push-ready keeps its hold-only form, so
    // the push handshake never depends on the placement it enables (granite
    // TASK-003, 2026-10-31).
    parameter bit AR_DIRECT          = 1'b0,
    // 1 = POP_REG: a commit / issue pops its bank FIFO one cycle LATE, from a
    // register. Everything the store reads off a queue (head, peeks, the
    // thresh flags, the pop's own slot match) goes through a LOGICAL view
    // that skips the one entry still physically in the FIFO, so the records,
    // the counts and the pops are cycle-for-cycle what the live pop gives.
    // What moves is the timing: the scheduler's fire cone ends at the
    // pop-pending register instead of running on through the FIFO's
    // pointer, count and full / empty logic (granite at 100 MHz, 2026-10-31:
    // 22 of the 29 failing endpoints of the AR_DIRECT build sat behind that
    // pop). The FIFO is one entry deeper and reads one more peek position.
    parameter bit POP_REG            = 1'b0,

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

    // WR done back to mc_axi4_plane (B response trigger), in AW order; ready
    // is the intake's B FIFO room
    output logic                wr_done_valid_o,
    input  logic                wr_done_ready_i,
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
    // the pick's column candidate this cycle as coordinates (registers in
    // the pick; see mc_bank_pick): direction, bank, record 1 or 2. The
    // merge searches skip the entry those coordinates name.
    input  logic                wr_commit_cand_i,
    input  logic                rd_issue_cand_i,
    input  logic [BKW-1:0]      cand_bank_i,
    input  logic                cand_second_i,

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

    output logic                busy_o,

    // ----- combining (MERGE_EN): read-merge decision on the AR being pushed
    // (combinational from ar_push_*; the plane allocates a shadow of
    // ar_merge_ticket_o in the same handshake) and the two free-running
    // counters -----
    output logic                ar_merge_o,
    output logic [RTW-1:0]      ar_merge_ticket_o,
    output logic [31:0]         stat_wr_merge_o,
    output logic [31:0]         stat_rd_merge_o
);

    localparam int BCW  = (AXI_BEATS_PER_BURST > 1) ? $clog2(AXI_BEATS_PER_BURST) : 1;
    localparam int DQ_DEPTH = (NUM_ENTRIES > 1) ? NUM_ENTRIES : 2;
    localparam int QD   = ((BANK_FIFO_DEPTH <= 0) || (BANK_FIFO_DEPTH > NUM_ENTRIES))
                        ? NUM_ENTRIES : BANK_FIFO_DEPTH;
    localparam int QCW  = $clog2(QD + 1);          // per-bank occupancy 0..QD
    // Fill-order FIFO depth: one pending fill per slot, plus one more per slot
    // with MERGE_EN (a merge target owes its own fill AND the merged write's,
    // and both can be pending at once when the W stream lags the AW stream).
    // Sized to NUM_ENTRIES the FIFO overflowed on the board at 32 outstanding
    // half-width writes -- fills landed in the wrong slots (granite TASK-006,
    // 2026-10-29).
    localparam int FO_DEPTH = MERGE_EN ? 2 * NUM_ENTRIES : NUM_ENTRIES;
    localparam int FOPW = (FO_DEPTH > 1) ? $clog2(FO_DEPTH) : 1;   // fill-order position
    localparam int FOW  = $clog2(FO_DEPTH + 1);    // fill-order occupancy 0..FO_DEPTH
    // Pool age: rank among the live entries of BOTH directions, so at most
    // 2 * NUM_ENTRIES - 1; the FIFO saturates at 0, the writer clamps at max.
    localparam int AGEW = $clog2(2 * NUM_ENTRIES);
    localparam int QDW  = PTRW + 1;                // queue entry = {same-row-as-previous, slot}
    localparam int QPK  = POP_REG ? 3 : 2;         // positions behind the head read (+1 for the pending pop)
    localparam int QDP  = QD + (POP_REG ? 1 : 0);  // physical entries: the logical depth plus the pending pop
    localparam int QDF  = (QDP > QPK) ? QDP : QPK + 1; // FIFO depth (PEEK must be below it)

    // ======================================================================
    // Per-(direction, bank) queues: gaxi_age_fifo_sync, declared here, built
    // after the slot logic below. Head and two peek positions per queue.
    // ======================================================================
    // The LOGICAL view (head + two positions behind it) every reader below
    // uses; the FIFO's own ports are the *f_* arrays (see POP_REG).
    logic [NUM_BANKS-1:0] w_wq_wr_ready, w_wq_rd_valid, w_wq_thr;
    logic [QDW-1:0]       w_wq_rd_data [NUM_BANKS];
    logic                 w_wq_pk_vld  [NUM_BANKS][2];
    logic [QDW-1:0]       w_wq_pk_data [NUM_BANKS][2];
    logic                 w_wq_pk_thr  [NUM_BANKS][2];
    logic [NUM_BANKS-1:0] w_rq_wr_ready, w_rq_rd_valid, w_rq_thr;
    logic [QDW-1:0]       w_rq_rd_data [NUM_BANKS];
    logic                 w_rq_pk_vld  [NUM_BANKS][2];
    logic [QDW-1:0]       w_rq_pk_data [NUM_BANKS][2];
    logic                 w_rq_pk_thr  [NUM_BANKS][2];
    logic [NUM_BANKS-1:0] w_wqf_rd_valid, w_wqf_thr, w_rqf_rd_valid, w_rqf_thr;
    logic [QDW-1:0]       w_wqf_rd_data [NUM_BANKS];
    logic [QDW-1:0]       w_rqf_rd_data [NUM_BANKS];
    logic                 w_wqf_pk_vld  [NUM_BANKS][QPK];
    logic [QDW-1:0]       w_wqf_pk_data [NUM_BANKS][QPK];
    logic                 w_wqf_pk_thr  [NUM_BANKS][QPK];
    logic                 w_rqf_pk_vld  [NUM_BANKS][QPK];
    logic [QDW-1:0]       w_rqf_pk_data [NUM_BANKS][QPK];
    logic                 w_rqf_pk_thr  [NUM_BANKS][QPK];
    logic [NUM_BANKS-1:0] w_wq_fpop, w_rq_fpop;   // the FIFOs' rd_ready
    logic                 w_age_dec;
    logic [AGEW-1:0]      w_new_age;

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
    logic [BCW-1:0]       r_wr_bcnt  [NUM_ENTRIES];
    // combining (MERGE_EN): committed (no longer a merge target), a merge
    // attached (owes a second B, released from its own queue entry), its fill still pending
    logic                 r_wr_cmt   [NUM_ENTRIES];
    logic                 r_wr_mgv   [NUM_ENTRIES];
    logic                 r_wr_mgfill[NUM_ENTRIES];
    // a same-id write was admitted after this one (MERGE_EN): the slot is no
    // longer the youngest write of its id, so a merge into it would put the
    // merged B ahead of that younger write's
    logic                 r_wr_yng   [NUM_ENTRIES];

    // Write-beat BRAM and its prefetch skid: identical to mc_xddr2_entry_store,
    // except that the strobes live in flops beside a DATA-only RAM: a merge
    // fill writes only its strobed bytes (byte enables) and ORs its strobes.
    localparam int SRW = DW + SW;
    (* ram_style = "block" *)
    logic [DW-1:0]   r_mem  [NUM_ENTRIES*AXI_BEATS_PER_BURST];
    logic [SW-1:0]   r_strb [NUM_ENTRIES*AXI_BEATS_PER_BURST];
    logic [SRW-1:0]  r_rd_q;
    localparam int SKID_DEPTH = 2;
    logic [SRW-1:0]  r_sk_data  [SKID_DEPTH];
    logic            r_sk_blast [SKID_DEPTH];
    logic            r_sk_slast [SKID_DEPTH];
    logic            r_sk_rd, r_sk_wr;
    logic [1:0]      r_sk_cnt;
    logic [1:0]      r_credits;
    logic            r_if_valid, r_if_blast, r_if_slast;
    logic            r_if_mgv,  r_sk_mgv  [SKID_DEPTH];
    // B release queue, in AW order. Every admitted write -- a slot, or a
    // merge into a slot -- takes one entry at AW admit; the drain's
    // host-burst-last beat marks the entry (and its merge's) done; Bs leave
    // from the head, one per cycle, only while the head is done and the
    // intake takes it. AXI needs same-id Bs in AW order. Releasing EVERY B in
    // AW order gives that with no id compare anywhere and leaves the pick free
    // to commit across banks in any order (granite BUG-001: B used to leave
    // at the drain, i.e. in commit order, and a younger same-id write to a
    // page-hit bank overtook an older one). The queue is bounded by admission
    // and pops only on the intake's ready, so the intake's B FIFO can never
    // overflow (memory-controllers BUG-001). 4 x NUM_ENTRIES covers the live
    // slots, their merges, and the drained entries whose B has not left.
    localparam int BQ_DEPTH = 4 * NUM_ENTRIES;
    localparam int BQPW = $clog2(BQ_DEPTH);
    localparam int BQCW = $clog2(BQ_DEPTH + 1);
    logic [IW-1:0]       r_bq_id [BQ_DEPTH];     // reset-free: written at admit only
    logic [BQ_DEPTH-1:0] r_bq_done;
    logic [BQPW-1:0]     r_bq_rd, r_bq_wr;
    logic [BQCW-1:0]     r_bq_cnt;
    logic                w_bq_full, w_bq_push, w_bq_pop, w_done1;
    logic [BQPW-1:0]     r_wr_pos   [NUM_ENTRIES];   // the slot's own queue entry
    logic [BQPW-1:0]     r_wr_mgpos [NUM_ENTRIES];   // its merged write's entry (r_wr_mgv)
    logic [BQPW-1:0]     r_if_pos,   r_sk_pos   [SKID_DEPTH];
    logic [BQPW-1:0]     r_if_mgpos, r_sk_mgpos [SKID_DEPTH];
    logic [BQPW-1:0]     w_hd_pos, w_hd_mgpos;

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
    // FO_DEPTH entries (see the localparam): a slot appears at most once
    // without MERGE_EN, at most twice with it (own fill, then its merge fill).
    logic [PTRW-1:0] r_fo     [FO_DEPTH];      // circular: head at r_fo_rd, r_fo_cnt entries
    logic            r_fo_mg  [FO_DEPTH];      // this fill merges into its slot (MERGE_EN)
    logic [FOPW-1:0] r_fo_rd;
    logic [FOW-1:0]  r_fo_cnt;
    logic            w_fill_vld;
    logic [PTRW-1:0] w_fill_slot;
    function automatic logic [FOPW-1:0] fopos(input logic [FOPW-1:0] base, input int off);
        int v;
        v = int'(base) + off;
        if (v >= FO_DEPTH) v = v - FO_DEPTH;
        return FOPW'(v);
    endfunction
    assign w_fill_vld  = (r_fo_cnt != '0);
    assign w_fill_slot = r_fo[r_fo_rd];
    logic w_fill_mg;
    assign w_fill_mg   = MERGE_EN && r_fo_mg[r_fo_rd];

    // Per-bank WR queue bookkeeping beside the FIFOs: a registered occupancy
    // (the admission bound and the mixed cap read a flop, not the FIFO's
    // leading `count`, which would close a loop through the push handshake)
    // and the row of the last pushed entry, for the same-row-as-previous bit
    // that rides each queue entry (0 when pushed into an empty queue).
    logic [QCW-1:0]       r_wq_cnt      [NUM_BANKS];
    logic [ROW_WIDTH-1:0] r_wq_tail_row [NUM_BANKS];
    logic                 w_wq_sp_new;

    logic [31:0] w_fill_idx;
    assign w_fill_idx = 32'(w_fill_slot) * 32'(AXI_BEATS_PER_BURST) + 32'(r_wr_bcnt[w_fill_slot]);

    // ---- WR admission hold (header): the AW is taken into a register, and
    //      admitted into the pool and its bank queue from there --------------
    logic                 r_awh_vld;
    logic [BKW-1:0]       r_awh_bank;
    logic [ROW_WIDTH-1:0] r_awh_row;
    logic [COL_WIDTH-1:0] r_awh_col;
    logic [IW-1:0]        r_awh_id;
    logic                 r_awh_last;
    logic [NUM_ENTRIES-1:0] r_awh_am, r_awh_ie;   // registered compares, see below
    logic w_aw_take, w_aw_fire, w_wd_fire, w_fill_done;
    logic w_wr_cap_ok, w_rd_cap_ok;   // conditional per-bank cap (BANK_CAP_MIXED), assigned below the RD slots
    // ---- write merge candidate (MERGE_EN): a live write entry with the held
    //      AW's key AND id (different ids never combine) that is not committed (nor being committed this cycle),
    //      carries no merge yet and is a single-burst write. Fills are in AW
    //      order, so the target's own fill is always ahead of the merge's.
    //      The target must be the YOUNGEST live write of its id (r_wr_yng
    //      clear): the merged B goes out right behind the target's, so only a
    //      same-id write admitted between the two could be overtaken; an
    //      older one is not (a one-id stream's lo/hi pair merges with its
    //      earlier writes still in flight). Bs already queued are ahead of
    //      the target's own, so they cannot be overtaken either (the B
    //      queue, above). The held AW itself
    //      must be a single burst (r_awh_last) so one B closes it. Slots are
    //      unordered, so any match is a valid target (at most one can match:
    //      a second same-key write would have merged into the first).
    //      Registers only, like w_aw_fire.
    // the entry the pick's column candidate names this cycle; computed after
    // the per-entry record flags it reads (head-record register block)
    logic [NUM_ENTRIES-1:0] w_wr_is_cand, w_rd_is_cand;
    logic [NUM_ENTRIES-1:0] w_mg_match;
    logic                   w_mg_found, w_aw_merge;
    logic [PTRW-1:0]        w_mg_slot;
    always_comb begin
        w_mg_found   = 1'b0;
        w_mg_slot    = '0;
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            w_mg_match[i] = MERGE_EN && r_wr_valid[i] && !r_wr_cmt[i] && !r_wr_mgv[i]
                          && r_wr_last[i] && r_awh_am[i] && r_awh_ie[i] && !r_wr_yng[i];
            if (w_mg_match[i]) begin w_mg_found = 1'b1; w_mg_slot = PTRW'(i); end
        end
    end

    // ---- the held AW's comparisons, REGISTERED (100 MHz, TASK-003
    //      2026-10-30). r_awh_am[i]: entry i has the held AW's {bank,row,col};
    //      r_awh_ie[i]: entry i has its id. Computed when the AW is LOADED, against the incoming
    //      push, with forwarding for the entry the departing AW allocates in
    //      that same cycle (it takes r_awh's fields). They stay exact while
    //      the AW holds: only the held AW allocates, so no entry's address or
    //      id changes under it. Same values
    //      as the old per-cycle compares, without the 27-bit address and id
    //      compares in front of the admission's fan-out.
    logic [NUM_ENTRIES-1:0] w_awp_am, w_awp_ie;
    always_comb begin
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            if (w_aw_fire && (w_wr_free_slot == PTRW'(i))) begin
                w_awp_am[i] = (aw_push_bank_i == r_awh_bank) && (aw_push_row_i == r_awh_row)
                           && (aw_push_col_i  == r_awh_col);
                w_awp_ie[i] = (aw_push_id_i == r_awh_id);
            end else begin
                w_awp_am[i] = (aw_push_bank_i == r_wr_bank[i]) && (aw_push_row_i == r_wr_row[i])
                           && (aw_push_col_i  == r_wr_col[i]);
                w_awp_ie[i] = (aw_push_id_i == r_wr_id[i]);
            end
        end
    end
    // The pick's column candidate is excluded from the merge, but NOT by
    // falling through to an allocation: an AW whose match is the candidate
    // waits (neither merges nor allocates) and re-evaluates next cycle, when
    // the target has either committed (no longer a match: allocate) or is no
    // longer the candidate (merge). So w_aw_fire reads registers only and the
    // allocation's fan-out never sees the pick (100 MHz, TASK-003 2026-10-30).
    logic w_mg_ok;
    assign w_mg_ok     = MERGE_EN && r_awh_vld && r_awh_last && w_mg_found;
    assign w_aw_merge  = w_mg_ok && !w_wr_is_cand[w_mg_slot] && !w_bq_full;
    // admit: the held AW enters the pool and its bank queue (registers only);
    // a merge takes no slot and no queue entry
    assign w_aw_fire   = r_awh_vld && !w_mg_ok
                       && w_wr_have_free && (r_wq_cnt[r_awh_bank] != QCW'(QD))
                       && w_wq_wr_ready[r_awh_bank] && w_wr_cap_ok && !w_bq_full;
    assign aw_push_ready_o = !r_awh_vld || w_aw_fire || w_aw_merge;
    assign w_aw_take   = aw_push_valid_i && aw_push_ready_o;
    assign w_wd_fire   = wd_valid_i && wd_ready_o;
    assign w_fill_done = w_wd_fire && (wd_last_i || (r_wr_bcnt[w_fill_slot] == BCW'(AXI_BEATS_PER_BURST - 1)));
    assign wd_ready_o      = w_fill_vld;

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_awh_vld  <= 1'b0;
            r_awh_bank <= '0;
            r_awh_row  <= '0;
            r_awh_col  <= '0;
            r_awh_id   <= '0;
            r_awh_last <= 1'b0;
        end else if (w_aw_take) begin
            r_awh_vld  <= 1'b1;
            r_awh_bank <= aw_push_bank_i;
            r_awh_row  <= aw_push_row_i;
            r_awh_col  <= aw_push_col_i;
            r_awh_id   <= aw_push_id_i;
            r_awh_last <= aw_push_last_i;
        end else if (w_aw_fire || w_aw_merge) begin
            r_awh_vld  <= 1'b0;
        end
    end)
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_awh_am <= '0;
            r_awh_ie <= '0;
        end else if (w_aw_take) begin
            r_awh_am <= w_awp_am;
            r_awh_ie <= w_awp_ie;
        end
    end)

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

    assign w_hd_vld   = (r_sk_cnt != 2'd0);
    assign w_hd_data  = r_sk_data [r_sk_rd];
    assign w_hd_blast = r_sk_blast[r_sk_rd];
    assign w_hd_slast = r_sk_slast[r_sk_rd];

    // The drain never waits for the B side: a done only sets a bit in the
    // release queue, whose entry was taken at admit.
    assign wr_cm_rd_valid_o = w_hd_vld;
    assign wr_cm_rd_data_o  = w_hd_data[DW-1:0];
    assign wr_cm_rd_strb_o  = w_hd_data[SRW-1:DW];
    logic w_hd_mgv;
    assign w_hd_mgv   = r_sk_mgv  [r_sk_rd];
    assign w_hd_pos   = r_sk_pos  [r_sk_rd];
    assign w_hd_mgpos = r_sk_mgpos[r_sk_rd];
    assign wr_cm_rd_last_o  = w_hd_blast;
    assign w_cm_fire        = wr_cm_rd_valid_o && wr_cm_rd_ready_i;

    // Fetch engine: one beat ahead of the presented beat
    logic [BCW-1:0]  r_cm_fbeat;
    logic [31:0]     w_cm_idx;
    assign w_cm_idx = 32'(w_dq_rd_slot) * 32'(AXI_BEATS_PER_BURST) + 32'(r_cm_fbeat);

    logic w_fetch, w_room, w_fetch_last;
    assign w_room       = (r_credits != 2'd0) || w_cm_fire;
    // A commit decided before a merge was seen waits for the merge fill
    // (bounded: the merged W is behind an AW already accepted).
    assign w_fetch      = w_room && w_dq_rd_valid && !(MERGE_EN && r_wr_mgfill[w_dq_rd_slot]);
    assign w_fetch_last = w_fetch && (r_cm_fbeat == BCW'(AXI_BEATS_PER_BURST-1));
    assign w_dq_rd_ready = w_fetch_last;

    // ======================================================================
    // Per-bank WR queue strobes: the commit pops its bank's head (a commit
    // always names the head: see the header), the AW accept pushes the free
    // slot at its bank's tail. The same-as-previous bit of the pushed entry
    // compares the incoming row with the registered tail row; it is
    // meaningful only when something is ahead of it after this cycle's pop.
    // ======================================================================
    // The popped queue is the one whose live HEAD is the committed slot (a
    // slot sits in exactly one queue, and a commit names a head; in the
    // pick's pop-shadow cycle the FIFO already shows the second record's
    // slot at its head). See the header for why this is not r_wr_bank[slot].
    logic [NUM_BANKS-1:0] w_wq_pop, w_wq_push;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            w_wq_pop [b] = w_wr_commit_fire && w_wq_rd_valid[b]
                         && (w_wq_rd_data[b][PTRW-1:0] == wr_commit_slot_i);
            w_wq_push[b] = w_aw_fire && (r_awh_bank == BKW'(b));
        end
    end
    // same-row-as-previous: the held AW's row against its bank's tail row,
    // when the queue holds an entry. Whether this cycle's pop empties the
    // queue does not enter: the bit is read at positions 1 and 2 only (the
    // records below), never at the head, and an entry pushed into a queue
    // emptied under it IS the head. (The pop term put the fire cone on the
    // FIFOs' data inputs, 2026-10-27.)
    assign w_wq_sp_new = (r_wq_cnt[r_awh_bank] != '0) && (r_awh_row == r_wq_tail_row[r_awh_bank]);

    // ======================================================================
    // WR sequential logic
    // ======================================================================
    // -------------------------------------------------------------------------
    // Reset-free write-slot tag storage (memory-controllers MC-005, 2026-11-06).
    // Written once at admit (or merge admit), read only through a slot that
    // r_wr_valid says is live, never reset. Kept out of the async-reset process
    // below so Vivado can infer RAM: Synth 8-4767 dissolved r_wr_bank / r_wr_id /
    // r_wr_last into flops on the 10-27 granite build for the reset alone.
    // Same write conditions as before, in clock-only processes.
    // -------------------------------------------------------------------------
    always_ff @(posedge aclk) begin
        if (w_aw_fire) begin
            r_wr_bank [w_wr_free_slot] <= r_awh_bank;
            r_wr_row  [w_wr_free_slot] <= r_awh_row;
            r_wr_col  [w_wr_free_slot] <= r_awh_col;
            r_wr_id   [w_wr_free_slot] <= r_awh_id;
            r_wr_last [w_wr_free_slot] <= r_awh_last;
            r_wr_pos  [w_wr_free_slot] <= r_bq_wr;
        end
        if (w_aw_merge) r_wr_mgpos[w_mg_slot] <= r_bq_wr;
    end

    always_ff @(posedge aclk) begin
        // the captured in-flight beat lands in the skid FIFO tail (r_sk_mgv is
        // reset and stays in the reset process)
        if (r_if_valid) begin
            r_sk_data [r_sk_wr] <= r_rd_q;
            r_sk_blast[r_sk_wr] <= r_if_blast;
            r_sk_slast[r_sk_wr] <= r_if_slast;
            r_sk_pos  [r_sk_wr] <= r_if_pos;
            r_sk_mgpos[r_sk_wr] <= r_if_mgpos;
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_cm_fbeat  <= '0;
            r_sk_rd     <= 1'b0;
            r_sk_wr     <= 1'b0;
            r_sk_cnt    <= 2'd0;
            r_credits   <= 2'(SKID_DEPTH);
            r_if_valid  <= 1'b0;
            r_fo_cnt    <= '0;
            r_fo_rd     <= '0;
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                r_wr_valid[i] <= 1'b0;
                r_wr_fdone[i] <= 1'b0;
                r_wr_bcnt [i] <= '0;
                r_fo[i]       <= '0;
                r_fo_mg[i]    <= 1'b0;
                r_wr_cmt[i]   <= 1'b0;
                r_wr_mgv[i]   <= 1'b0;
                r_wr_mgfill[i]<= 1'b0;
                r_wr_yng[i]   <= 1'b0;
            end
            r_if_mgv    <= 1'b0;
            r_bq_rd     <= '0;
            r_bq_wr     <= '0;
            r_bq_cnt    <= '0;
            r_bq_done   <= '0;
            for (int k = 0; k < SKID_DEPTH; k++) r_sk_mgv[k] <= 1'b0;
            for (int b = 0; b < NUM_BANKS; b++) begin
                r_wq_cnt[b]      <= '0;
                r_wq_tail_row[b] <= '0;
            end
        end else begin
            // descriptor insert; every live slot of the same id now has a
            // younger write (r_awh_ie is that compare, exact while the AW holds)
            if (w_aw_fire) begin
                for (int i = 0; i < NUM_ENTRIES; i++)
                    if (r_wr_valid[i] && r_awh_ie[i]) r_wr_yng[i] <= 1'b1;
                r_wr_yng  [w_wr_free_slot] <= 1'b0;
                r_wr_valid[w_wr_free_slot] <= 1'b1;
                r_wr_fdone[w_wr_free_slot] <= 1'b0;
                r_wr_bcnt [w_wr_free_slot] <= '0;
                r_wr_cmt  [w_wr_free_slot] <= 1'b0;
                r_wr_mgv  [w_wr_free_slot] <= 1'b0;
                r_wr_mgfill[w_wr_free_slot]<= 1'b0;
            end
            // merge admission: the target entry owes a second B and leaves
            // the schedulable set until the merge fill lands
            if (w_aw_merge) begin
                r_wr_mgv   [w_mg_slot] <= 1'b1;
                r_wr_mgfill[w_mg_slot] <= 1'b1;
                r_wr_fdone [w_mg_slot] <= 1'b0;
            end
            if (w_wr_commit_fire) r_wr_cmt[wr_commit_slot_i] <= 1'b1;

            // fill-order FIFO: circular; pop (head + 1) at fill-done, push at
            // insert behind the current occupancy (a push never sees a full
            // FIFO: an admit needs a free slot and a merge needs an un-merged
            // target, so every slot is in this FIFO at most FO_DEPTH /
            // NUM_ENTRIES times)
            if (w_fill_done) r_fo_rd <= fopos(r_fo_rd, 1);
            if (w_aw_fire || w_aw_merge) begin
                r_fo   [fopos(r_fo_rd, int'(r_fo_cnt))] <= w_aw_merge ? w_mg_slot : w_wr_free_slot;
                r_fo_mg[fopos(r_fo_rd, int'(r_fo_cnt))] <= w_aw_merge;
            end
            r_fo_cnt <= r_fo_cnt - (w_fill_done ? FOW'(1) : FOW'(0)) + ((w_aw_fire || w_aw_merge) ? FOW'(1) : FOW'(0));

            // fill bookkeeping (the beat itself lands in the BRAM below).
            // fdone means EVERY fill the slot owes has landed: a slot's own
            // fill completing while its merge fill is still pending (admitted
            // earlier, or in this very cycle) leaves it not-done; the merge
            // fill, always the later one, sets it. Before this rule the own
            // fill re-entered the slot into the schedulable set and the
            // commit came ahead of the merged beats (the fill-lag test holds
            // a WRITE 114 cycles at the DFI head that way).
            if (w_wd_fire) begin
                if (w_fill_done) begin
                    if (w_fill_mg || !(r_wr_mgfill[w_fill_slot] || (w_aw_merge && (w_mg_slot == w_fill_slot))))
                        r_wr_fdone[w_fill_slot] <= 1'b1;
                    r_wr_bcnt [w_fill_slot] <= '0;
                    if (w_fill_mg) r_wr_mgfill[w_fill_slot] <= 1'b0;
                end else begin
                    r_wr_bcnt[w_fill_slot] <= r_wr_bcnt[w_fill_slot] + 1'b1;
                end
            end

            // per-bank occupancy and tail row (the queue itself is the FIFO)
            for (int b = 0; b < NUM_BANKS; b++) begin
                r_wq_cnt[b] <= QCW'(int'(r_wq_cnt[b]) - (w_wq_pop[b] ? 1 : 0) + (w_wq_push[b] ? 1 : 0));
                if (w_wq_push[b]) r_wq_tail_row[b] <= r_awh_row;
            end

            // fetch engine
            r_if_valid <= w_fetch;
            if (w_fetch) begin
                r_if_blast <= (r_cm_fbeat == BCW'(AXI_BEATS_PER_BURST-1));
                r_if_slast <= r_wr_last[w_dq_rd_slot];
                r_if_pos   <= r_wr_pos[w_dq_rd_slot];
                r_if_mgv   <= MERGE_EN && r_wr_mgv [w_dq_rd_slot];
                r_if_mgpos <= r_wr_mgpos[w_dq_rd_slot];
                if (r_cm_fbeat == BCW'(AXI_BEATS_PER_BURST-1)) r_cm_fbeat <= '0;
                else                                           r_cm_fbeat <= r_cm_fbeat + 1'b1;
            end

            // skid pipeline
            if (r_if_valid) begin
                r_sk_mgv  [r_sk_wr] <= r_if_mgv;
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
                r_wr_cmt  [w_dq_rd_slot] <= 1'b0;
                r_wr_mgv  [w_dq_rd_slot] <= 1'b0;
            end
            // B release queue: an entry per admit (slot or merge), marked done
            // at the drain's host-burst-last beat, popped when the intake
            // takes the head. The pushed entry and the marked ones are always
            // distinct (a marked entry is live, the pushed one is free).
            if (w_bq_push) begin
                r_bq_done[r_bq_wr] <= 1'b0;
                r_bq_wr <= (int'(r_bq_wr) == BQ_DEPTH - 1) ? '0 : r_bq_wr + 1'b1;
            end
            if (w_done1) begin
                r_bq_done[w_hd_pos] <= 1'b1;
                if (w_hd_mgv) r_bq_done[w_hd_mgpos] <= 1'b1;
            end
            if (w_bq_pop) r_bq_rd <= (int'(r_bq_rd) == BQ_DEPTH - 1) ? '0 : r_bq_rd + 1'b1;
            r_bq_cnt <= r_bq_cnt + (w_bq_push ? BQCW'(1) : BQCW'(0)) - (w_bq_pop ? BQCW'(1) : BQCW'(0));
        end
    end)

    // B release queue ids: reset-free (written at admit, read at the head).
    always_ff @(posedge aclk) begin
        if (w_bq_push) r_bq_id[r_bq_wr] <= r_awh_id;
    end

    // Data storage: reset-free so it maps to block RAM; read latency exactly
    // one cycle, paired with the one-deep in-flight tag above.
    always_ff @(posedge aclk) begin
        if (w_wd_fire) begin
            for (int b = 0; b < SW; b++) begin
                if (!w_fill_mg || wd_strb_i[b]) r_mem[w_fill_idx][b*8 +: 8] <= wd_data_i[b*8 +: 8];
            end
        end
        if (w_fetch) r_rd_q[DW-1:0] <= r_mem[w_cm_idx];
    end
    always_ff @(posedge aclk) begin
        if (w_wd_fire) r_strb[w_fill_idx] <= w_fill_mg ? (r_strb[w_fill_idx] | wd_strb_i) : wd_strb_i;
        if (w_fetch)   r_rd_q[SRW-1:DW]   <= r_strb[w_cm_idx];
    end

    // ======================================================================
    // RD slots and per-bank RD FIFOs
    // ======================================================================
    logic                 r_rd_valid  [NUM_ENTRIES];
    logic [BKW-1:0]       r_rd_bank   [NUM_ENTRIES];
    logic [ROW_WIDTH-1:0] r_rd_row    [NUM_ENTRIES];
    logic [COL_WIDTH-1:0] r_rd_col    [NUM_ENTRIES];
    logic [RTW-1:0]       r_rd_ticket [NUM_ENTRIES];
    logic [IW-1:0]        r_rd_id     [NUM_ENTRIES];   // MERGE_EN: only a same-id read combines
    logic [QCW-1:0]       r_rq_cnt    [NUM_BANKS];     // bookkeeping beside the FIFOs, as the WR side
    logic [ROW_WIDTH-1:0] r_rq_tail_row [NUM_BANKS];
    logic                 w_rq_sp_new;

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

    // ---- RD admission hold (header): the AR is taken into a register with
    //      the ring ticket the plane allocates at the handshake, and admitted
    //      into the pool and its bank queue from there ----------------------
    logic                 r_arh_vld;
    logic [BKW-1:0]       r_arh_bank;
    logic [ROW_WIDTH-1:0] r_arh_row;
    logic [COL_WIDTH-1:0] r_arh_col;
    logic [RTW-1:0]       r_arh_ticket;
    logic [IW-1:0]        r_arh_id;
    logic w_ar_take, w_ar_fire, w_ar_fire_hold, w_ar_direct, w_rd_issue_fire, w_ars_ok;
    // the AR being placed: the hold when it is full, else (AR_DIRECT) the push
    logic [BKW-1:0]       w_ars_bank;
    logic [ROW_WIDTH-1:0] w_ars_row;
    logic [COL_WIDTH-1:0] w_ars_col;
    logic [RTW-1:0]       w_ars_ticket;
    logic [IW-1:0]        w_ars_id;
    assign w_ars_bank   = r_arh_vld ? r_arh_bank   : ar_push_bank_i;
    assign w_ars_row    = r_arh_vld ? r_arh_row    : ar_push_row_i;
    assign w_ars_col    = r_arh_vld ? r_arh_col    : ar_push_col_i;
    assign w_ars_ticket = r_arh_vld ? r_arh_ticket : rt_alloc_ticket_i;
    assign w_ars_id     = r_arh_vld ? r_arh_id     : ar_push_id_i;
    assign w_ars_ok       = w_rd_have_free && (r_rq_cnt[w_ars_bank] != QCW'(QD))
                          && w_rq_wr_ready[w_ars_bank] && w_rd_cap_ok;
    assign w_ar_fire_hold = r_arh_vld && w_ars_ok;
    assign w_ar_direct    = AR_DIRECT && !r_arh_vld && w_ar_take && !ar_merge_o && w_ars_ok;
    assign w_ar_fire      = w_ar_fire_hold || w_ar_direct;
    assign rd_cam_ins_ready_o = !r_arh_vld || w_ar_fire_hold;
    assign ar_push_ready_o    = rd_cam_ins_ready_o && rt_alloc_ready_i;
    assign w_ar_take       = ar_push_valid_i && ar_push_ready_o;
    // ---- read merge (MERGE_EN): the AR being pushed matches a live, unissued
    //      read entry (not being issued this cycle) or the held AR, by key
    //      and id (different ids never combine);
    //      the plane allocates it as a shadow of that ticket and this store
    //      takes nothing. Combinational from the push inputs, as the ring's
    //      alloc is in the same handshake.
    logic [NUM_ENTRIES-1:0] w_rdmg_match;
    logic                   w_rdmg_found;
    logic [RTW-1:0]         w_rdmg_ticket;
    always_comb begin
        w_rdmg_found  = 1'b0;
        w_rdmg_ticket = '0;
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            w_rdmg_match[i] = MERGE_EN && r_rd_valid[i]
                            && !w_rd_is_cand[i]
                            && (r_rd_bank[i] == ar_push_bank_i) && (r_rd_row[i] == ar_push_row_i)
                            && (r_rd_col[i]  == ar_push_col_i) && (r_rd_id[i] == ar_push_id_i);
            if (w_rdmg_match[i]) begin w_rdmg_found = 1'b1; w_rdmg_ticket = r_rd_ticket[i]; end
        end
        if (MERGE_EN && r_arh_vld && (r_arh_bank == ar_push_bank_i) && (r_arh_row == ar_push_row_i)
            && (r_arh_col == ar_push_col_i) && (r_arh_id == ar_push_id_i)) begin
            w_rdmg_found  = 1'b1;
            w_rdmg_ticket = r_arh_ticket;
        end
    end
    assign ar_merge_o        = ar_push_valid_i && w_rdmg_found;
    assign ar_merge_ticket_o = w_rdmg_ticket;

    // combining telemetry (free-running)
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            stat_wr_merge_o <= '0;
            stat_rd_merge_o <= '0;
        end else begin
            if (w_aw_merge)               stat_wr_merge_o <= stat_wr_merge_o + 32'd1;
            if (w_ar_take && ar_merge_o)  stat_rd_merge_o <= stat_rd_merge_o + 32'd1;
        end
    end)

    assign w_rd_issue_fire = rd_issue_valid_i && rd_issue_ready_o;
    assign rd_issue_ready_o   = rd_iss_ready_i;
    assign rd_iss_valid_o     = w_rd_issue_fire;
    assign rd_iss_ticket_o    = r_rd_ticket[rd_issue_slot_i];

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            r_arh_vld    <= 1'b0;
            r_arh_bank   <= '0;
            r_arh_row    <= '0;
            r_arh_col    <= '0;
            r_arh_ticket <= '0;
            r_arh_id     <= '0;
        end else if (w_ar_take && !ar_merge_o && !w_ar_direct) begin
            r_arh_vld    <= 1'b1;
            r_arh_bank   <= ar_push_bank_i;
            r_arh_row    <= ar_push_row_i;
            r_arh_col    <= ar_push_col_i;
            r_arh_ticket <= rt_alloc_ticket_i;
            r_arh_id     <= ar_push_id_i;
        end else if (w_ar_fire_hold) begin
            r_arh_vld    <= 1'b0;
        end
    end)

    // pop by the live head (see the WR side), push from the hold
    logic [NUM_BANKS-1:0] w_rq_pop, w_rq_push;
    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            w_rq_pop [b] = w_rd_issue_fire && w_rq_rd_valid[b]
                         && (w_rq_rd_data[b][PTRW-1:0] == rd_issue_slot_i);
            w_rq_push[b] = w_ar_fire && (w_ars_bank == BKW'(b));
        end
    end
    assign w_rq_sp_new = (r_rq_cnt[w_ars_bank] != '0) && (w_ars_row == r_rq_tail_row[w_ars_bank]);

    // Reset-free read-slot tag storage (memory-controllers MC-005, 2026-11-06):
    // written once at AR admit, read only through a slot r_rd_valid says is
    // live, never reset; out of the async-reset process so it can be RAM.
    always_ff @(posedge aclk) begin
        if (w_ar_fire) begin
            r_rd_bank  [w_rd_free_slot] <= w_ars_bank;
            r_rd_row   [w_rd_free_slot] <= w_ars_row;
            r_rd_col   [w_rd_free_slot] <= w_ars_col;
            r_rd_ticket[w_rd_free_slot] <= w_ars_ticket;
            r_rd_id    [w_rd_free_slot] <= w_ars_id;
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            for (int i = 0; i < NUM_ENTRIES; i++) begin
                r_rd_valid[i] <= 1'b0;
            end
            for (int b = 0; b < NUM_BANKS; b++) begin
                r_rq_cnt[b]      <= '0;
                r_rq_tail_row[b] <= '0;
            end
        end else begin
            if (w_ar_fire) begin
                r_rd_valid [w_rd_free_slot] <= 1'b1;
            end
            if (w_rd_issue_fire) r_rd_valid[rd_issue_slot_i] <= 1'b0;
            for (int b = 0; b < NUM_BANKS; b++) begin
                r_rq_cnt[b] <= QCW'(int'(r_rq_cnt[b]) - (w_rq_pop[b] ? 1 : 0) + (w_rq_push[b] ? 1 : 0));
                if (w_rq_push[b]) r_rq_tail_row[b] <= w_ars_row;
            end
        end
    end)

    // the other direction's occupancy, for the conditional cap
    logic w_any_rd, w_any_wr;
    always_comb begin
        w_any_rd = 1'b0; w_any_wr = 1'b0;
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            if (r_rd_valid[i]) w_any_rd = 1'b1;
            if (r_wr_valid[i]) w_any_wr = 1'b1;
        end
    end
    assign w_wr_cap_ok = (BANK_CAP_MIXED == 0) || !w_any_rd || (int'(r_wq_cnt[r_awh_bank]) < BANK_CAP_MIXED);
    assign w_rd_cap_ok = (BANK_CAP_MIXED == 0) || !w_any_wr || (int'(r_rq_cnt[w_ars_bank]) < BANK_CAP_MIXED);

    // ======================================================================
    // Pool age (gaxi_age_fifo_sync's writer rule across all 2 x NUM_BANKS
    // queues): one retirement strobe per commit or issue -- the pick fires
    // one command per cycle, so the two are exclusive -- and the pushed age
    // is 0 into an empty pool, else the pool's largest `youngest` plus one,
    // or that `youngest` itself when a retirement lands at the same edge.
    // An AW and an AR accepted in one cycle both take that age and tie,
    // which the rule allows (age <= rank holds for both). `youngest` is a
    // balanced max tree over the queues' outputs, one array per level
    // (handbook: reduction-tree-one-array-per-level). HAS_AGE = 0 ties the
    // age inputs off; the column folds to constants and age_exceed is 0.
    // ======================================================================
    localparam int NQ  = 2 * NUM_BANKS;
    localparam int NQP = 1 << $clog2(NQ);
    localparam int NQL = $clog2(NQ);
    logic [AGEW-1:0] w_yleaf [NQP];
    logic [AGEW-1:0] w_pool_young;
    logic            w_pool_empty;
    // Per-queue tail age, tracked HERE rather than read off the FIFO's
    // `youngest` (a max tree over its entry array). This store is the pool
    // writer, so it knows every push and every decrement: a queue's newest
    // entry is its tail, it leaves last, and its age is the queue's largest
    // -- the register loads the pushed age (the same-cycle age_dec term is
    // already in it), steps toward zero with age_dec like the entry does,
    // and reads 0 while the queue is empty. Exact under the writer rule,
    // and it takes the FIFO's entry array and tree out of the pool-age
    // path: with HAS_AGE on the board that path (entry age -> queue tree
    // -> 16-queue max -> +1 -> every entry's age register) was 19 LUT
    // levels, -1.5 ns at 75 MHz (2026-10-29). The FIFO's `youngest` output
    // is left unconnected and its tree is pruned.
    logic [AGEW-1:0] r_wq_tail_age [NUM_BANKS];
    logic [AGEW-1:0] r_rq_tail_age [NUM_BANKS];
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            for (int b = 0; b < NUM_BANKS; b++) begin
                r_wq_tail_age[b] <= '0;
                r_rq_tail_age[b] <= '0;
            end
        end else begin
            for (int b = 0; b < NUM_BANKS; b++) begin
                if (w_wq_push[b] && w_wq_wr_ready[b])            r_wq_tail_age[b] <= w_new_age;
                else if (w_age_dec && (r_wq_tail_age[b] != '0)) r_wq_tail_age[b] <= r_wq_tail_age[b] - 1'b1;
                if (w_rq_push[b] && w_rq_wr_ready[b])            r_rq_tail_age[b] <= w_new_age;
                else if (w_age_dec && (r_rq_tail_age[b] != '0)) r_rq_tail_age[b] <= r_rq_tail_age[b] - 1'b1;
            end
        end
    end)
    generate
        for (genvar i = 0; i < NQP; i++) begin : g_yleaf
            if (i < NUM_BANKS) begin : g_wr
                assign w_yleaf[i] = w_wq_rd_valid[i] ? r_wq_tail_age[i] : '0;
            end else if (i < NQ) begin : g_rd
                assign w_yleaf[i] = w_rq_rd_valid[i - NUM_BANKS] ? r_rq_tail_age[i - NUM_BANKS] : '0;
            end else begin : g_pad
                assign w_yleaf[i] = '0;
            end
        end
        for (genvar lvl = 0; lvl < NQL; lvl++) begin : g_ylvl
            localparam int N_OUT = NQP >> (lvl + 1);
            logic [AGEW-1:0] w_max [N_OUT];
            for (genvar k = 0; k < N_OUT; k++) begin : g_node
                logic [AGEW-1:0] w_a, w_b;
                if (lvl == 0) begin : g_from_leaf
                    assign w_a = w_yleaf[2*k];
                    assign w_b = w_yleaf[2*k+1];
                end else begin : g_from_lvl
                    assign w_a = g_ylvl[lvl-1].w_max[2*k];
                    assign w_b = g_ylvl[lvl-1].w_max[2*k+1];
                end
                assign w_max[k] = (w_a > w_b) ? w_a : w_b;
            end
        end
        assign w_pool_young = g_ylvl[NQL-1].w_max[0];   // NQ >= 2, so NQL >= 1
    endgenerate
    assign w_pool_empty = !((|w_wq_rd_valid) || (|w_rq_rd_valid));
    assign w_age_dec    = HAS_AGE && (w_wr_commit_fire || w_rd_issue_fire);
    always_comb begin
        if (!HAS_AGE || w_pool_empty)            w_new_age = '0;
        else if (w_age_dec)                      w_new_age = w_pool_young;
        else if (w_pool_young == {AGEW{1'b1}})   w_new_age = w_pool_young;   // clamp; rank < 2N keeps this unreachable
        else                                     w_new_age = w_pool_young + 1'b1;
    end

    // The queues. With the pool age (HAS_AGE) each is a gaxi_age_fifo_sync: a
    // FIFO controller per queue, an age column, and the head and two peeks
    // read through asynchronous muxes on the entry memory. Without it (the
    // board), mc_bank_queue: the head and the PEEK entries behind it are a
    // shift register of flops, the rest a reset-free LUTRAM touched once per
    // push and once per pop, valids are compares on one registered count --
    // the FPGA shape of ISSUE-001 row 2 (memory-controllers MC-010,
    // 2026-11-08). Same handshakes, same observable timing;
    // formal/mc_common/mc_bank_queue proves the two agree output for output.
    generate if (HAS_AGE) begin : g_q_age
    for (genvar b = 0; b < NUM_BANKS; b++) begin : g_q
        gaxi_age_fifo_sync #(
            .DATA_WIDTH (QDW),
            .AGE_WIDTH  (AGEW),
            .DEPTH      (QDF),
            .PEEK       (QPK)
        ) u_wq (
            .axi_aclk      (aclk),
            .axi_aresetn   (aresetn),
            .age_dec       (w_age_dec),
            .wr_valid      (w_wq_push[b]),
            .wr_ready      (w_wq_wr_ready[b]),
            .wr_data       ({w_wq_sp_new, w_wr_free_slot}),
            .wr_data_age   (w_new_age),
            .rd_ready      (w_wq_fpop[b]),
            .count         (),
            .youngest      (),
            .rd_valid      (w_wqf_rd_valid[b]),
            .rd_data       (w_wqf_rd_data[b]),
            .rd_data_age   (),
            .rd_age_thresh (w_wqf_thr[b]),
            .pk_valid      (w_wqf_pk_vld[b]),
            .pk_data       (w_wqf_pk_data[b]),
            .pk_age_thresh (w_wqf_pk_thr[b])
        );
        gaxi_age_fifo_sync #(
            .DATA_WIDTH (QDW),
            .AGE_WIDTH  (AGEW),
            .DEPTH      (QDF),
            .PEEK       (QPK)
        ) u_rq (
            .axi_aclk      (aclk),
            .axi_aresetn   (aresetn),
            .age_dec       (w_age_dec),
            .wr_valid      (w_rq_push[b]),
            .wr_ready      (w_rq_wr_ready[b]),
            .wr_data       ({w_rq_sp_new, w_rd_free_slot}),
            .wr_data_age   (w_new_age),
            .rd_ready      (w_rq_fpop[b]),
            .count         (),
            .youngest      (),
            .rd_valid      (w_rqf_rd_valid[b]),
            .rd_data       (w_rqf_rd_data[b]),
            .rd_data_age   (),
            .rd_age_thresh (w_rqf_thr[b]),
            .pk_valid      (w_rqf_pk_vld[b]),
            .pk_data       (w_rqf_pk_data[b]),
            .pk_age_thresh (w_rqf_pk_thr[b])
        );
    end
    end else begin : g_q_fifo
    for (genvar b = 0; b < NUM_BANKS; b++) begin : g_q
        mc_bank_queue #(
            .DATA_WIDTH (QDW),
            .DEPTH      (QDF),
            .PEEK       (QPK)
        ) u_wq (
            .axi_aclk      (aclk),
            .axi_aresetn   (aresetn),
            .wr_valid      (w_wq_push[b]),
            .wr_ready      (w_wq_wr_ready[b]),
            .wr_data       ({w_wq_sp_new, w_wr_free_slot}),
            .rd_ready      (w_wq_fpop[b]),
            .count         (),
            .rd_valid      (w_wqf_rd_valid[b]),
            .rd_data       (w_wqf_rd_data[b]),
            .pk_valid      (w_wqf_pk_vld[b]),
            .pk_data       (w_wqf_pk_data[b])
        );
        mc_bank_queue #(
            .DATA_WIDTH (QDW),
            .DEPTH      (QDF),
            .PEEK       (QPK)
        ) u_rq (
            .axi_aclk      (aclk),
            .axi_aresetn   (aresetn),
            .wr_valid      (w_rq_push[b]),
            .wr_ready      (w_rq_wr_ready[b]),
            .wr_data       ({w_rq_sp_new, w_rd_free_slot}),
            .rd_ready      (w_rq_fpop[b]),
            .count         (),
            .rd_valid      (w_rqf_rd_valid[b]),
            .rd_data       (w_rqf_rd_data[b]),
            .pk_valid      (w_rqf_pk_vld[b]),
            .pk_data       (w_rqf_pk_data[b])
        );
        // no age column: no entry ever reaches the pool-age threshold
        assign w_wqf_thr[b] = 1'b0;
        assign w_rqf_thr[b] = 1'b0;
        for (genvar k = 0; k < QPK; k++) begin : g_thr
            assign w_wqf_pk_thr[b][k] = 1'b0;
            assign w_rqf_pk_thr[b][k] = 1'b0;
        end
        wire _unused_age = &{1'b0, w_age_dec, w_new_age};
    end
    end endgenerate
    // Logical view (POP_REG): while a pop is pending the FIFO head is that
    // entry, already gone, so every position reads one further back. Live
    // (POP_REG = 0) the view is the FIFO and the pop goes straight in.
    logic [NUM_BANKS-1:0] r_wq_ppend, r_rq_ppend;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wq_ppend <= '0;
            r_rq_ppend <= '0;
        end else begin
            r_wq_ppend <= POP_REG ? w_wq_pop : '0;
            r_rq_ppend <= POP_REG ? w_rq_pop : '0;
        end
    )
    assign w_wq_fpop = POP_REG ? r_wq_ppend : w_wq_pop;
    assign w_rq_fpop = POP_REG ? r_rq_ppend : w_rq_pop;
    generate if (POP_REG) begin : g_pop_reg
        always_comb begin
            for (int b = 0; b < NUM_BANKS; b++) begin
                if (r_wq_ppend[b]) begin
                    w_wq_rd_valid[b] = w_wqf_pk_vld[b][0];
                    w_wq_rd_data[b]  = w_wqf_pk_data[b][0];
                    w_wq_thr[b]      = w_wqf_pk_thr[b][0];
                    for (int k = 0; k < 2; k++) begin
                        w_wq_pk_vld[b][k]  = w_wqf_pk_vld[b][k+1];
                        w_wq_pk_data[b][k] = w_wqf_pk_data[b][k+1];
                        w_wq_pk_thr[b][k]  = w_wqf_pk_thr[b][k+1];
                    end
                end else begin
                    w_wq_rd_valid[b] = w_wqf_rd_valid[b];
                    w_wq_rd_data[b]  = w_wqf_rd_data[b];
                    w_wq_thr[b]      = w_wqf_thr[b];
                    for (int k = 0; k < 2; k++) begin
                        w_wq_pk_vld[b][k]  = w_wqf_pk_vld[b][k];
                        w_wq_pk_data[b][k] = w_wqf_pk_data[b][k];
                        w_wq_pk_thr[b][k]  = w_wqf_pk_thr[b][k];
                    end
                end
                if (r_rq_ppend[b]) begin
                    w_rq_rd_valid[b] = w_rqf_pk_vld[b][0];
                    w_rq_rd_data[b]  = w_rqf_pk_data[b][0];
                    w_rq_thr[b]      = w_rqf_pk_thr[b][0];
                    for (int k = 0; k < 2; k++) begin
                        w_rq_pk_vld[b][k]  = w_rqf_pk_vld[b][k+1];
                        w_rq_pk_data[b][k] = w_rqf_pk_data[b][k+1];
                        w_rq_pk_thr[b][k]  = w_rqf_pk_thr[b][k+1];
                    end
                end else begin
                    w_rq_rd_valid[b] = w_rqf_rd_valid[b];
                    w_rq_rd_data[b]  = w_rqf_rd_data[b];
                    w_rq_thr[b]      = w_rqf_thr[b];
                    for (int k = 0; k < 2; k++) begin
                        w_rq_pk_vld[b][k]  = w_rqf_pk_vld[b][k];
                        w_rq_pk_data[b][k] = w_rqf_pk_data[b][k];
                        w_rq_pk_thr[b][k]  = w_rqf_pk_thr[b][k];
                    end
                end
            end
        end
    end else begin : g_pop_live
        always_comb begin
            for (int b = 0; b < NUM_BANKS; b++) begin
                w_wq_rd_valid[b] = w_wqf_rd_valid[b];
                w_wq_rd_data[b]  = w_wqf_rd_data[b];
                w_wq_thr[b]      = w_wqf_thr[b];
                for (int k = 0; k < 2; k++) begin
                    w_wq_pk_vld[b][k]  = w_wqf_pk_vld[b][k];
                    w_wq_pk_data[b][k] = w_wqf_pk_data[b][k];
                    w_wq_pk_thr[b][k]  = w_wqf_pk_thr[b][k];
                end
                w_rq_rd_valid[b] = w_rqf_rd_valid[b];
                w_rq_rd_data[b]  = w_rqf_rd_data[b];
                w_rq_thr[b]      = w_rqf_thr[b];
                for (int k = 0; k < 2; k++) begin
                    w_rq_pk_vld[b][k]  = w_rqf_pk_vld[b][k];
                    w_rq_pk_data[b][k] = w_rqf_pk_data[b][k];
                    w_rq_pk_thr[b][k]  = w_rqf_pk_thr[b][k];
                end
            end
        end
    end endgenerate
    // The CSR field is the enable AND the starvation bound. A head with the
    // FIFO's thresh bit is the oldest entry in the pool; it becomes the
    // pick's aged class only after it has been passed over for
    // sched_age_thresh - 1 cycles (so 1 = the moment it is oldest, the
    // 2026-10-25 form; larger values let the hint / rotor / direction
    // choices run until the oldest head has actually waited). Measured
    // without the bound (granite TASK-003 item 5, 2026-10-29): the aged
    // tie-break at 8 streaming threads cost 9 to 12 percent on every
    // stream, because there is always an oldest head and it always won.
    // One saturating counter per queue head, cleared on pop or when the
    // head is no longer oldest.
    logic       w_aged_en;
    logic [7:0] r_wq_wait [NUM_BANKS];
    logic [7:0] r_rq_wait [NUM_BANKS];
    logic [NUM_BANKS-1:0] w_wq_aged, w_rq_aged;
    assign w_aged_en = HAS_AGE && (sched_age_thresh_i != 8'd0);
    `ALWAYS_FF_RST(aclk, aresetn, begin
        if (`RST_ASSERTED(aresetn)) begin
            for (int b = 0; b < NUM_BANKS; b++) begin
                r_wq_wait[b] <= '0;
                r_rq_wait[b] <= '0;
            end
        end else begin
            for (int b = 0; b < NUM_BANKS; b++) begin
                if (w_wq_pop[b] || !w_wq_thr[b])      r_wq_wait[b] <= '0;
                else if (r_wq_wait[b] != 8'hFF)       r_wq_wait[b] <= r_wq_wait[b] + 8'd1;
                if (w_rq_pop[b] || !w_rq_thr[b])      r_rq_wait[b] <= '0;
                else if (r_rq_wait[b] != 8'hFF)       r_rq_wait[b] <= r_rq_wait[b] + 8'd1;
            end
        end
    end)
    generate for (genvar b = 0; b < NUM_BANKS; b++) begin : g_aged
        assign w_wq_aged[b] = w_aged_en && (r_wq_wait[b] >= (sched_age_thresh_i - 8'd1));
        assign w_rq_aged[b] = w_aged_en && (r_rq_wait[b] >= (sched_age_thresh_i - 8'd1));
    end endgenerate

    // ======================================================================
    // Records off the FIFO fronts, registered at the edge. A write record is
    // schedulable only once its data has landed; nothing schedulable can sit
    // behind an unfilled head (fill order == arrival order), so a head that
    // is still filling simply has vld = 0, and the filled entries of a bank
    // are a prefix of its queue: behind_empty is "the next position is not
    // filled". behind_same_row is the stored same-as-previous bit of the next
    // position (filled or pending), the exact close-on-drain term. The FIFO's
    // head is position 0, its peeks are positions 1 and 2; an entry is
    // {same-row-as-previous, slot}.
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
            automatic logic has0, has1, has2, sp1, sp2;
            automatic logic [ROW_WIDTH-1:0] orow;
            orow = bank_open_row_i[b*ROW_WIDTH +: ROW_WIDTH];
            s0 = w_wq_rd_data[b][PTRW-1:0];
            s1 = w_wq_pk_data[b][0][PTRW-1:0];
            s2 = w_wq_pk_data[b][1][PTRW-1:0];
            sp1 = w_wq_pk_data[b][0][PTRW];
            sp2 = w_wq_pk_data[b][1][PTRW];
            has0 = w_wq_rd_valid[b];
            has1 = w_wq_pk_vld[b][0];
            has2 = w_wq_pk_vld[b][1];
            // The head records are registered one cycle behind r_wr_fdone. A
            // merge admitted THIS cycle into a filled entry clears its fdone
            // at the edge, but the record built from this cycle's fdone would
            // still say schedulable for one cycle, and the pick could commit
            // the write with its merged beats still to land: the DFI plane
            // then holds the WRITE for its data while the scheduler's tWR /
            // auto-precharge / ACT timers run from the commit, and the DRAM
            // sees a PRE or ACT too soon after the WRITE it actually got
            // (granite TASK-006, 2026-10-29: 83 percent of a merged open-page
            // pair walk never landed on the board). So the merge target is
            // masked out of the record in the admission cycle itself. Store
            // registers only, ending in the record register: the first form
            // exported a live fill-pending vector into the pick's fire term,
            // a store-to-pick-to-store loop that cost 0.36 ns at 75 MHz and
            // missed 100 MHz by 2.5 ns (2026-10-30). Refusing the merge
            // instead merged nothing (0 of 1024 pairs: the first half's fill
            // is complete before the second half is admitted).
            h = '0;
            h.vld             = has0 && r_wr_fdone[s0] && !(w_aw_merge && (w_mg_slot == s0));
            h.slot            = MC_HEAD_SLOT_W'(s0);
            h.behind_empty    = h.vld && !(has1 && r_wr_fdone[s1]);
            h.behind_same_row = h.vld && has1 && sp1;
            h.age_exceed      = w_wq_aged[b] && w_wq_thr[b];
            h.hit             = bank_row_active_i[b] && (r_wr_row[s0] == orow);
            h2 = '0;
            h2.vld             = has1 && r_wr_fdone[s1] && !(w_aw_merge && (w_mg_slot == s1));
            h2.slot            = MC_HEAD_SLOT_W'(s1);
            h2.behind_empty    = h2.vld && !(has2 && r_wr_fdone[s2]);
            h2.behind_same_row = h2.vld && has2 && sp2;
            h2.age_exceed      = w_wq_aged[b] && w_wq_pk_thr[b][0];
            h2.hit             = has1 && sp1;  // == head.behind_same_row's bit (header)
            if (!HEAD2_EN) h2 = '0;
            w_wr_head [b] = h;
            w_wr_head2[b] = h2;
        end
    end

    always_comb begin
        for (int b = 0; b < NUM_BANKS; b++) begin
            automatic mc_head_rec_t h, h2;
            automatic logic [PTRW-1:0] s0, s1;
            automatic logic has0, has1, has2, sp1, sp2;
            automatic logic [ROW_WIDTH-1:0] orow;
            orow = bank_open_row_i[b*ROW_WIDTH +: ROW_WIDTH];
            s0 = w_rq_rd_data[b][PTRW-1:0];
            s1 = w_rq_pk_data[b][0][PTRW-1:0];
            sp1 = w_rq_pk_data[b][0][PTRW];
            sp2 = w_rq_pk_data[b][1][PTRW];
            has0 = w_rq_rd_valid[b];
            has1 = w_rq_pk_vld[b][0];
            has2 = w_rq_pk_vld[b][1];
            h = '0;
            h.vld             = has0;
            h.slot            = MC_HEAD_SLOT_W'(s0);
            h.behind_empty    = has0 && !has1;
            h.behind_same_row = has0 && has1 && sp1;
            h.age_exceed      = w_rq_aged[b] && w_rq_thr[b];
            h.hit             = bank_row_active_i[b] && (r_rd_row[s0] == orow);
            h2 = '0;
            h2.vld             = has1;
            h2.slot            = MC_HEAD_SLOT_W'(s1);
            h2.behind_empty    = has1 && !has2;
            h2.behind_same_row = has1 && has2 && sp2;
            h2.age_exceed      = w_rq_aged[b] && w_rq_pk_thr[b][0];
            h2.hit             = has1 && sp1;  // == head.behind_same_row's bit (header)
            if (!HEAD2_EN) h2 = '0;
            // HEAD_BYPASS: the AR going into this empty queue now is the head
            if (HEAD_BYPASS && w_ar_fire && (w_ars_bank == BKW'(b)) && !has0) begin
                h = '0;
                h.vld          = 1'b1;
                h.slot         = MC_HEAD_SLOT_W'(w_rd_free_slot);
                h.behind_empty = 1'b1;
                h.hit          = bank_row_active_i[b] && (w_ars_row == orow);
            end
            w_rd_head [b] = h;
            w_rd_head2[b] = h2;
        end
    end

    // Per entry: is it the valid record 1 / record 2 of its bank, registered
    // at the same edge as the records the pick fires on. With the pick's
    // candidate coordinates this names the commit / issue slot exactly
    // (record 1 or 2 of bank B), without the slot itself leaving the store.
    logic [NUM_ENTRIES-1:0] r_wr_h1, r_wr_h2, r_rd_h1, r_rd_h2;
    logic [NUM_ENTRIES-1:0] w_wr_h1, w_wr_h2, w_rd_h1, w_rd_h2;
    always_comb begin
        w_wr_h1 = '0; w_wr_h2 = '0; w_rd_h1 = '0; w_rd_h2 = '0;
        for (int b = 0; b < NUM_BANKS; b++) begin
            if (w_wr_head [b].vld) w_wr_h1[PTRW'(w_wr_head [b].slot)] = 1'b1;
            if (w_wr_head2[b].vld) w_wr_h2[PTRW'(w_wr_head2[b].slot)] = 1'b1;
            if (w_rd_head [b].vld) w_rd_h1[PTRW'(w_rd_head [b].slot)] = 1'b1;
            if (w_rd_head2[b].vld) w_rd_h2[PTRW'(w_rd_head2[b].slot)] = 1'b1;
        end
    end
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            wr_head_o  <= '0;
            wr_head2_o <= '0;
            rd_head_o  <= '0;
            rd_head2_o <= '0;
            r_wr_h1 <= '0; r_wr_h2 <= '0; r_rd_h1 <= '0; r_rd_h2 <= '0;
        end else begin
            wr_head_o  <= w_wr_head;
            wr_head2_o <= w_wr_head2;
            rd_head_o  <= w_rd_head;
            rd_head2_o <= w_rd_head2;
            r_wr_h1 <= w_wr_h1; r_wr_h2 <= w_wr_h2;
            r_rd_h1 <= w_rd_h1; r_rd_h2 <= w_rd_h2;
        end
    )
    // resolve the pick's candidate coordinates against the record flags
    always_comb begin
        for (int i = 0; i < NUM_ENTRIES; i++) begin
            w_wr_is_cand[i] = wr_commit_cand_i && (r_wr_bank[i] == cand_bank_i)
                           && (cand_second_i ? r_wr_h2[i] : r_wr_h1[i]);
            w_rd_is_cand[i] = rd_issue_cand_i  && (r_rd_bank[i] == cand_bank_i)
                           && (cand_second_i ? r_rd_h2[i] : r_rd_h1[i]);
        end
    end

    // ======================================================================
    // Snarf (storage-lite: disabled), B consolidation, busy
    // ======================================================================
    assign snarf_hit_o      = 1'b0;
    assign snarf_rd_valid_o = 1'b0;
    assign snarf_rd_data_o  = '0;
    assign snarf_rd_last_o  = 1'b0;

    assign w_done1         = w_cm_fire && w_hd_blast && w_hd_slast;
    assign w_bq_full       = (r_bq_cnt == BQCW'(BQ_DEPTH));
    // One B per HOST burst: a chopped burst's chunks arrive as separate pushes
    // (agg, last only on the final chunk) and only the last chunk owes a B, so
    // only it takes a queue entry (a non-last chunk's entry would never be
    // marked done and would block the head). A merge target is always a last
    // chunk (w_mg_ok requires it), so a merge always owes one. Fire and merge
    // are mutually exclusive.
    assign w_bq_push       = (w_aw_fire && r_awh_last) || w_aw_merge;
    assign wr_done_valid_o = (r_bq_cnt != '0) && r_bq_done[r_bq_rd];
    assign wr_done_id_o    = r_bq_id[r_bq_rd];
    assign w_bq_pop        = wr_done_valid_o && wr_done_ready_i;

    always_comb begin
        busy_o = w_dq_rd_valid || w_hd_vld || r_if_valid || r_awh_vld || r_arh_vld
              || (r_bq_cnt != '0);
        for (int i = 0; i < NUM_ENTRIES; i++)
            if (r_wr_valid[i] || r_rd_valid[i]) busy_o = 1'b1;
    end

    wire _unused = &{1'b0, snarf_probe_valid_i, snarf_probe_bank_i, snarf_probe_row_i,
                     snarf_probe_col_i, snarf_probe_id_i, snarf_probe_len_i,
                     snarf_accept_i, snarf_rd_ready_i, aw_push_qos_i, aw_push_agg_i,
                     ar_push_qos_i};

endmodule : mc_bank_fifo_store
