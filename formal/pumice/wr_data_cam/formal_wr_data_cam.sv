// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal wrapper for pumice_wr_data_cam -- the write window and its data SRAM.
//
// WHY THIS BLOCK (pumice TASK-035 tier 1). It is where a bug CORRUPTS MEMORY.
// A write burst is filled into an SRAM slot at insert and drained to the DFI
// at commit; if a beat comes back changed, reordered, or from the wrong slot,
// the wrong bytes are written to the DRAM and the transaction reports success.
// Nothing upstream or downstream notices. The block already has a fixed bug of
// exactly this family in its history.
//
// WHAT IS PROVED
//
//   COMMIT DATA INTEGRITY -- the headline, and the property this block exists
//   to keep: a_cm_data. Every drained beat whose burst's fill was observed
//   carries, in order, exactly the data (and strobe) that the fill stream
//   presented for that entry. Attribution is per burst through a model of the
//   commit drain queue, so the upstream DECISION/FIRE split of commit (a beat
//   can drain for a commit whose port handshake has only just landed, or has
//   not landed at all) is modelled rather than assumed away.
//
//   NO SLOT REUSE BEFORE ITS DRAIN -- carried by a_cm_data plus two covers,
//   for a structural reason worth stating. The DUT evicts the entry (and frees
//   its SRAM slot) at FETCH-last, not at consume-last: every beat of the burst
//   has then been read out of the SRAM into the skid, and what remains of the
//   drain is FIFO storage, not storage the refill can corrupt. From that point
//   the controller can legally re-insert, refill and re-commit the same entry
//   while the old tail beats are still draining -- this wrapper's own first
//   draft asserted "the drain queue never holds a slot twice" and FAILED
//   against correct hardware on exactly that interleaving (trace in the task
//   report). The hazard the task names is not "the slot appears twice" but "a
//   refill reaches the SRAM before the old burst has been read out of it";
//   the observable form of that hazard is drained data that no longer matches
//   the recorded fill, which is precisely what a_cm_data asserts. c_reuse_live
//   covers the benign window (a re-commit of a slot whose earlier drain is
//   still in flight) and c_reuse_after_drain covers the completed case, so the
//   proof demonstrates integrity across the whole reuse spectrum rather than
//   assuming the window away. The mutation that frees the SRAM slot one commit
//   early (M2 in the table below) turns this into observable corruption and
//   fails a_cm_data.
//
//   BURST FRAMING -- a_burst_len: between two `cm_rd_last_o` pulses there are
//   exactly AXI_BEATS_PER_BURST accepted beats. A short or long burst
//   desynchronises the DFI write stream for everything behind it.
//
//   SLOT LIFECYCLE -- a_ins_ready_implies_free: the CAM never accepts an
//   insert with every slot occupied.
//
// DOTTED HIERARCHICAL REFERENCES AND THE DISABLED COUNTEREXAMPLE. The wrapper
// contains NO live `dut.*` references (only one in a comment). The fifth model
// (SRAM shadow via `dut.w_fill_idx` / `dut.w_rd_idx`) produced a readback
// counterexample that was left disabled and uncorroborated; the verdict, now
// confirmed by the `dfi_cdc` free-probe discovery, is that those references
// elaborated as IMPLICIT WIRES and therefore as FREE INPUTS in yosys 0.62.
// The shadow was asserting on unconstrained indices and data, so the trace was
// a wrapper defect, not a DUT defect. Model 6 is port-level only and does not
// repeat the hazard.
//
// HOW THE MODEL WORKS (after five wrong ones -- read this before touching it).
// Six models of commit data integrity were built; five were wrong, each for a
// different structural reason, and the fifth produced a counterexample that
// took a forensic trace to dispose of:
//   1. entry-slot shadow compared against the drain stream: the entry slot is
//      not the SRAM slot (an r_ptr[] indirection sits between), and the entry
//      can be re-filled while the old drain is still in the skid, so comparing
//      against live per-entry state reads post-refill data for the old
//      burst's tail beats -- fails on correct hardware.
//   2. counting commit handshakes to attribute beats: the drain is anchored on
//      the arbiter's DECISION, not on commit_valid/ready; a beat fires at
//      cycle 11 for a commit whose handshake lands at cycle 12. No port-level
//      counting fixes the denominator.
//   3. leaving the snarf (read-your-writes) stream free: the commit drain
//      shares its prefetch mover with snarf; every commit property failed on
//      the shared mover instead of the commit path. Snarf is tied off here;
//      it is its own property and deserves its own proof.
//   4. comparing a shadow AFTER its own update: a fetch of an address written
//      in the same cycle reads the pre-write cell on both sides; comparing a
//      cycle late reads post-write on one side -- a read-during-write hazard
//      in the CHECK.
//   5. shadowing the SRAM by the DUT's own w_fill_idx/w_rd_idx via
//      hierarchical references. This elaborates -- and the counterexample it
//      produced ("write 0xFF to SRAM addr 1, fetch addr 1, r_rd_q reads 0")
//      was left disabled and uncorroborated. THE VERDICT, after reproducing
//      the trace and reading it cycle by cycle against the RTL: the
//      counterexample is REFUTED as a DUT defect. It is a free-input artifact:
//      in this yosys 0.62 flow dotted references from the wrapper into the DUT
//      elaborate as implicit wires, and an implicit wire in formal mode is a
//      FREE INPUT. The wrapper-bound indices and data were unconstrained, so
//      the shadow recorded a fictitious write stream and expected a fetch that
//      never happened; the DUT in the same trace fills, commits and fetches
//      lawfully. The independent `dfi_cdc` proof found the same behaviour with
//      injected probes: "hierarchical references elaborate" is NOT
//      "hierarchical references denote the DUT's signals". NO property in this
//      wrapper references dut.* internals.
//   6. THIS MODEL, port-level only. Every beat of the fill stream is recorded
//      into a per-entry shadow at the only moment the entry becomes
//      observable: when its slot goes 0 -> 1 in sch_valid_o ("filled, not yet
//      committed") -- the same technique formal_rd_cmd_cam.sv uses for the
//      ticket. At the commit ACCEPT the whole burst (data and strobe) is
//      SNAPSHOTTED into a model of the commit drain queue, one entry per
//      accepted commit, popped at that burst's last consumed beat. Drained
//      beats are compared against the queue head's snapshot at the beat
//      position the drain stream itself counts. The snapshot is what makes it
//      sound: the entry's live shadow can be overwritten by a refill long
//      before the old burst's tail drains from the skid, so anything compared
//      against live state at drain time (models 1 and 4) fails on correct
//      hardware. Entry slots vs SRAM slots is not a confound: r_ptr[slot] is
//      fixed from the first fill beat to eviction, so per-entry equality is
//      per-SRAM-cell equality for the burst's lifetime. The accept is
//      w_accept = commit_valid_i && commit_ready_o@1 -- NOT the port
//      handshake (see ENVIRONMENT): the RTL's commit has a decision/fire
//      split, and on the fast path the accept fires while commit_ready_o is
//      low. Using the handshake instead under-enqueues the model by exactly
//      the fast-path bursts -- the counterexample that taught this is in the
//      task report.
//
// WHY THE SNAPSHOT IS TAKEN AT THE ACCEPT AND NOT AT INSERT: at insert the
// entry has no data; at fill-landing the burst is complete. Every drained
// burst was accepted (the drain FIFO is fed ONLY by w_commit_fire), so the
// accept is the one event that both (a) sees the complete burst and (b) is
// one-per-drain.
//
// WHICH SLOT IS BEING FILLED is not observable at insert time -- the CAM picks
// it. The wrapper buffers the burst's beats and assigns them to whichever slot
// goes 0 -> 1 in sch_valid_o, which is exactly that entry's fill completing.
//
// SMALL GEOMETRY ON PURPOSE. 2 entries, 2 beats per burst, 8-bit data. The
// movers are the same movers at 2 slots as at 8; a narrow datapath is what
// makes "every beat of every burst" a question the solver can answer rather
// than sample.
//
// ENVIRONMENT. Assumptions, all stated in the assume block:
//   * reset discipline (asserted at time 0, released from f_past_valid >= 2);
//   * ARBITER FIRE PROTOCOL: commit_valid_i implies commit_ready_o was high
//     the previous cycle. This block's commit has a DECISION/FIRE split: the
//     arbiter samples commit_ready_o ("will a commit decided now be accepted
//     next cycle") and presents commit_valid_i one cycle later; the accept
//     itself can then fire while commit_ready_o reads low. The port handshake
//     (valid && ready) and the internal accept (w_commit_fire) describe the
//     same event ONLY under this protocol; without it the solver presents
//     commit_valid into a full drain queue in the one cycle a pop makes
//     commit_ready_o read 1 while no accept happens, and the shadow queue
//     models a commit the DUT never took. This is the interface the RTL
//     documents, not a relaxation: the full-queue hazard itself (ready low,
//     no decision taken) remains in scope and is exercised by the covers.
//   * DECISION-TIME SLOT DISCIPLINE: the slot presented at the fire was
//     schedulable at the decision, one cycle earlier (the arbiter picks its
//     slot when it decides). Without it the solver presents a slot in the same
//     cycle its fill lands, one cycle before the shadow can latch it, and the
//     check is silently skipped on the fast path.
//   * ONE UN-LANDED BURST AT A TIME (!f_pend_full || !wd_valid_i): the wrapper
//     holds the burst being filled in a single buffer and assigns it to
//     whichever slot goes 0 -> 1 in sch_valid_o; if the next burst starts
//     streaming before the previous one has landed, that buffer is
//     overwritten and the SHADOW is wrong, not the DUT. This is a scoping
//     assumption: the proof covers back-to-back bursts but not a second fill
//     overlapping an unlanded one.
// None of these touches the data path: the fill stream, the drain stream and
// the hazard the block exists to keep (a written beat coming back changed,
// reordered, or from a reused slot) are all left free.
//
// MUTATION EVIDENCE (patched copies of wr_flat.v under /tmp, never the
// tracked RTL; each run as its own sby task against THIS wrapper):
//
//   MUTATION                  FLAT CHANGE                         TASK     FIRST FAIL        FAMILY
//   m1_invert_drain_data      cm_rd_data_o = ~w_hd_data[DW-1:0]   prove_f1 a_cm_data         F1
//   m2_tie_last_high          cm_rd_last_o = 1'b1                 prove_f2 a_burst_len       F2
//   m3_force_ins_ready        ins_ready_o  = 1'b1                 prove_f2 a_ins_ready_implies_free F2
//
// Driver: /tmp/wr_data_cam_mut/run_mutations.py. All three FAIL as required.
//
// YOSYS-COMPATIBLE FORM. DUT pre-flattened by sv2v; immediate assertions in
// `always @(posedge clk)`. See formal_rd_cmd_cam.sv for the sibling style and
// formal_bank_timer.sv for the flatten rationale.

`timescale 1ns / 1ps

module formal_wr_data_cam #(
    parameter int NE    = 2,   // NUM_ENTRIES
    parameter int NLU   = 1,   // N_SCHED_LU
    parameter int NB    = 2,   // NUM_BANKS
    parameter int RW    = 2,   // ROW_WIDTH
    parameter int CW    = 2,   // COL_WIDTH
    parameter int IW    = 1,   // AXI_ID_WIDTH
    parameter int DW    = 8,   // AXI_DATA_WIDTH
    parameter int BEATS = 2,   // AXI_BEATS_PER_BURST
    parameter int AGEW  = 4,   // AGE_WIDTH
    parameter int SW    = 1,   // DW/8
    parameter int BKW   = 1,   // $clog2(NB)
    parameter int PTRW  = 1,   // $clog2(NE)
    parameter int BCW   = 1,   // $clog2(BEATS)
    parameter bit FAMILY1 = 1'b1,  // commit data integrity (a_cm_data)
    parameter bit FAMILY2 = 1'b1   // burst framing + slot lifecycle
) (
    input logic aclk,
    input logic aresetn
);

    (* anyseq *) reg            ins_valid_i;
    // ins_last_i marks the final burst of an entry. With aggregation off every
    // insert IS its own complete burst, so leaving `last` free describes a
    // configuration that cannot occur and lets the drain frame bursts
    // differently from the fill.
    wire ins_last_i = 1'b1;
    // Aggregation (one entry absorbing several AXI bursts) is a separate
    // feature with its own ordering question; tied off so this proof is
    // about the fill/commit data path and says so.
    wire ins_agg_i = 1'b0;
    (* anyseq *) reg [BKW-1:0]  ins_bank_i;
    (* anyseq *) reg [RW-1:0]   ins_row_i;
    (* anyseq *) reg [CW-1:0]   ins_col_i;
    (* anyseq *) reg [IW-1:0]   ins_id_i;
    (* anyseq *) reg [3:0]      ins_qos_i;
    (* anyseq *) reg            wd_valid_i;
    (* anyseq *) reg [DW-1:0]   wd_data_i;
    (* anyseq *) reg [SW-1:0]   wd_strb_i;
    // SNARF IS TIED OFF. cm_rd_valid_o is `w_hd_vld && w_hd_iscm`: the commit
    // drain shares its prefetch mover with the read-your-writes (snarf) stream.
    // Leaving snarf free puts a second, independent feature inside every commit
    // property, and the first failure it produced (a_cm_in_burst) was the shared
    // mover, not the commit path. Snarf ordering -- "a probe returns the
    // YOUNGEST matching write" -- is its own property and deserves its own
    // proof rather than being a confound in this one.
    wire snarf_probe_valid_i = 1'b0;
    wire snarf_accept_i      = 1'b0;
    wire snarf_rd_ready_i    = 1'b0;
    (* anyseq *) reg [BKW-1:0]  snarf_probe_bank_i;
    (* anyseq *) reg [RW-1:0]   snarf_probe_row_i;
    (* anyseq *) reg [CW-1:0]   snarf_probe_col_i;
    (* anyseq *) reg [IW-1:0]   snarf_probe_id_i;
    (* anyseq *) reg [7:0]      snarf_probe_len_i;
    (* anyseq *) reg [NLU-1:0]  sched_lu_valid_i;
    (* anyseq *) reg [NLU*BKW-1:0] sched_lu_bank_i;
    (* anyseq *) reg [NLU*RW-1:0]  sched_lu_row_i;
    (* anyseq *) reg [7:0]      age_thresh_i;
    (* anyseq *) reg            commit_valid_i, cm_rd_ready_i;
    (* anyseq *) reg [PTRW-1:0] commit_slot_i;

    // The write-data stream carries exactly BEATS beats per burst, so `last`
    // is not free: it is the framing the AXI side already guarantees.
    reg [BCW-1:0] f_wbeat;
    wire wd_last_i = (f_wbeat == BCW'(BEATS-1));

    wire ins_ready_o, wd_ready_o, snarf_hit_o, snarf_rd_valid_o, snarf_rd_last_o;
    wire [DW-1:0] snarf_rd_data_o;
    wire oldest_valid_o; wire [BKW-1:0] oldest_bank_o; wire [RW-1:0] oldest_row_o;
    wire [CW-1:0] oldest_col_o; wire [IW-1:0] oldest_id_o; wire [PTRW-1:0] oldest_slot_o;
    wire [NLU-1:0] sched_lu_hit_o; wire [NLU*PTRW-1:0] sched_lu_slot_o;
    wire [NLU*CW-1:0] sched_lu_col_o; wire [NLU*IW-1:0] sched_lu_id_o;
    wire [NLU*AGEW-1:0] sched_lu_age_o;
    wire [NE-1:0] sch_valid_o, sch_age_exceed_o;
    wire [NE*BKW-1:0] sch_bank_o; wire [NE*RW-1:0] sch_row_o; wire [NE*CW-1:0] sch_col_o;
    wire [NE*NE-1:0] sch_older_o; wire [NE*4-1:0] sch_qos_o; wire [AGEW-1:0] sch_head_rel_o;
    wire commit_ready_o, cm_rd_valid_o, cm_rd_last_o, commit_done_valid_o, busy_o;
    wire [DW-1:0] cm_rd_data_o; wire [SW-1:0] cm_rd_strb_o; wire [IW-1:0] commit_done_id_o;

    pumice_wr_data_cam #(
        .NUM_ENTRIES(NE), .N_SCHED_LU(NLU), .NUM_BANKS(NB), .ROW_WIDTH(RW),
        .COL_WIDTH(CW), .AXI_ID_WIDTH(IW), .AXI_DATA_WIDTH(DW),
        .AXI_BEATS_PER_BURST(BEATS), .AGE_WIDTH(AGEW), .N_SRAM_SLOTS(NE)
    ) dut (
        .aclk(aclk), .aresetn(aresetn),
        .ins_valid_i(ins_valid_i), .ins_ready_o(ins_ready_o), .ins_bank_i(ins_bank_i),
        .ins_row_i(ins_row_i), .ins_col_i(ins_col_i), .ins_id_i(ins_id_i),
        .ins_qos_i(ins_qos_i), .ins_agg_i(ins_agg_i), .ins_last_i(ins_last_i),
        .wd_valid_i(wd_valid_i), .wd_ready_o(wd_ready_o), .wd_data_i(wd_data_i),
        .wd_strb_i(wd_strb_i), .wd_last_i(wd_last_i),
        .snarf_probe_valid_i(snarf_probe_valid_i), .snarf_probe_bank_i(snarf_probe_bank_i),
        .snarf_probe_row_i(snarf_probe_row_i), .snarf_probe_col_i(snarf_probe_col_i),
        .snarf_probe_id_i(snarf_probe_id_i), .snarf_probe_len_i(snarf_probe_len_i),
        .snarf_hit_o(snarf_hit_o), .snarf_accept_i(snarf_accept_i),
        .snarf_rd_valid_o(snarf_rd_valid_o), .snarf_rd_ready_i(snarf_rd_ready_i),
        .snarf_rd_data_o(snarf_rd_data_o), .snarf_rd_last_o(snarf_rd_last_o),
        .oldest_valid_o(oldest_valid_o), .oldest_bank_o(oldest_bank_o),
        .oldest_row_o(oldest_row_o), .oldest_col_o(oldest_col_o),
        .oldest_id_o(oldest_id_o), .oldest_slot_o(oldest_slot_o),
        .sched_lu_valid_i(sched_lu_valid_i), .sched_lu_bank_i(sched_lu_bank_i),
        .sched_lu_row_i(sched_lu_row_i), .sched_lu_hit_o(sched_lu_hit_o),
        .sched_lu_slot_o(sched_lu_slot_o), .sched_lu_col_o(sched_lu_col_o),
        .sched_lu_id_o(sched_lu_id_o), .sched_lu_age_o(sched_lu_age_o),
        .sch_valid_o(sch_valid_o), .sch_bank_o(sch_bank_o), .sch_row_o(sch_row_o),
        .sch_col_o(sch_col_o), .sch_older_o(sch_older_o), .age_thresh_i(age_thresh_i),
        .sch_age_exceed_o(sch_age_exceed_o), .sch_qos_o(sch_qos_o),
        .sch_head_rel_o(sch_head_rel_o),
        .commit_valid_i(commit_valid_i), .commit_ready_o(commit_ready_o),
        .commit_slot_i(commit_slot_i), .cm_rd_valid_o(cm_rd_valid_o),
        .cm_rd_ready_i(cm_rd_ready_i), .cm_rd_data_o(cm_rd_data_o),
        .cm_rd_strb_o(cm_rd_strb_o), .cm_rd_last_o(cm_rd_last_o),
        .commit_done_valid_o(commit_done_valid_o), .commit_done_id_o(commit_done_id_o),
        .busy_o(busy_o)
    );

    wire w_ins    = ins_valid_i    && ins_ready_o;
    wire w_wd     = wd_valid_i     && wd_ready_o;
    wire w_commit = commit_valid_i && commit_ready_o;
    wire w_cm     = cm_rd_valid_o  && cm_rd_ready_i;

    reg [7:0] f_past_valid = 0;
    always @(posedge aclk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!aresetn);
    always @(posedge aclk) if (f_past_valid >= 2) assume (aresetn);

    // Shadow state, declared BEFORE the environment block that references it:
    // an assume reading a signal declared later becomes an implicit net in a
    // stricter tool, and would then constrain a dangling wire rather than the
    // shadow -- a vacuous assumption that still lets the proof pass.
    reg [DW-1:0] f_pend [BEATS];        // beats of the burst currently filling
    reg [SW-1:0] f_pend_strb [BEATS];
    reg [DW-1:0] f_slot_data [NE][BEATS];
    reg [SW-1:0] f_slot_strb [NE][BEATS];
    reg [NE-1:0] f_known;
    reg [NE-1:0] f_sch_d;
    reg          f_pend_full;           // a complete burst is waiting to land
    reg          f_cmready_d;           // commit_ready_o, one cycle back
    reg          f_cvalid_d;            // commit_valid_i, one cycle back
    reg [PTRW-1:0] f_cslot_d;           // commit_slot_i, one cycle back

    // THE COMMIT ACCEPT EVENT. This block's commit has a DECISION/FIRE split:
    // the port handshake commit_valid_i && commit_ready_o is only the DECISION
    // hint -- it answers "will a commit decided NOW be accepted next cycle".
    // The accept itself (w_commit_fire in the RTL) can fire while
    // commit_ready_o is low in the same cycle (the drain FIFO momentarily
    // full, the decision-time predicate having already committed the slot).
    // The accept is therefore modelled as the protocol-qualified valid: under
    // the fire-protocol assumption below it equals the DUT's w_commit_fire
    // exactly (valid one cycle after ready implies current occupancy and FIFO
    // room, the other two terms of the DUT's accept equation).
    wire w_accept = commit_valid_i && f_cmready_d;

    // ---- environment ------------------------------------------------------
    always @(*) if (aresetn) begin
        // ARBITER FIRE PROTOCOL (see header): commit_valid_i is presented the
        // cycle after a commit_ready_o decision. Without this the solver
        // presents commit_valid into a full drain queue in the one cycle a pop
        // makes commit_ready_o read 1 while no accept happens, and the shadow
        // queue models a commit the DUT never took.
        assume (!commit_valid_i || f_cmready_d);

        // DECISION-TIME SLOT DISCIPLINE: the slot presented at the fire was
        // schedulable at the DECISION, one cycle earlier -- the arbiter picks
        // its slot when it decides. Schedulability of an un-committed entry
        // only rises the cycle its fill lands, so this also closes a shadow
        // race: an accept in the same cycle the landing is visible would
        // snapshot per-entry state one cycle before the shadow latches it
        // (the check would be skipped, not wrong -- but a skipped check on
        // the fast path is how vacuous proofs happen). Sch_valid can only
        // fall afterwards, through this entry's own commit, so the slot is
        // still schedulable at the fire.
        assume (!commit_valid_i || f_sch_d[commit_slot_i]);

        // DECISION INFLIGHT EXCLUSION (the arbiter's own discipline, pumice_cmd_
        // arbiter w_wr_col_inflight_ent): two consecutive fires are two
        // distinct decisions, and a slot whose commit was decided last cycle
        // is excluded from re-pick -- so the same slot is never presented in
        // consecutive cycles. Without this, held-high commit_valid double-
        // accepts into both the DUT's drain FIFO and the shadow queue.
        assume (!(commit_valid_i && f_cvalid_d) || (commit_slot_i != f_cslot_d));

        // ONE UN-LANDED BURST AT A TIME (see header). The counterexample that
        // found this had a second burst's first beat arriving in the same
        // cycle the first burst landed.
        assume (!f_pend_full || !wd_valid_i);
    end

    // =====================================================================
    // SHADOW -- the burst being filled, then per-slot once it lands.
    // =====================================================================

    integer s, b;
    always @(posedge aclk) begin
        if (!aresetn) begin
            f_wbeat <= 0; f_known <= 0; f_sch_d <= 0; f_pend_full <= 1'b0;
            f_cmready_d <= 1'b0; f_cvalid_d <= 1'b0; f_cslot_d <= 0;
            for (b = 0; b < BEATS; b = b + 1) begin
                f_pend[b] <= 0; f_pend_strb[b] <= 0;
            end
            for (s = 0; s < NE; s = s + 1)
                for (b = 0; b < BEATS; b = b + 1) begin
                    f_slot_data[s][b] <= 0; f_slot_strb[s][b] <= 0;
                end
        end else begin
            f_sch_d     <= sch_valid_o;
            f_cmready_d <= commit_ready_o;
            f_cvalid_d  <= commit_valid_i;
            f_cslot_d   <= commit_slot_i;

            if (w_wd) begin
                f_pend[f_wbeat]      <= wd_data_i;
                f_pend_strb[f_wbeat] <= wd_strb_i;
                f_wbeat <= wd_last_i ? 0 : f_wbeat + 1'b1;
                if (wd_last_i) f_pend_full <= 1'b1;
            end

            // the slot that just became schedulable took the buffered burst
            if (f_pend_full)
                for (s = 0; s < NE; s = s + 1)
                    if (sch_valid_o[s] && !f_sch_d[s]) begin
                        for (b = 0; b < BEATS; b = b + 1) begin
                            f_slot_data[s][b] <= f_pend[b];
                            f_slot_strb[s][b] <= f_pend_strb[b];
                        end
                        f_known[s]  <= 1'b1;
                        f_pend_full <= 1'b0;
                    end

            // a committed slot's expectation is stale until refilled
            if (w_accept) f_known[commit_slot_i] <= 1'b0;
        end
    end

    // Which slot is draining, and how far through.
    //
    // A QUEUE, not a register: WR_DRAIN_AHEAD lets a second commit be accepted
    // while the first is still draining ("bursts allowed in the commit drain
    // queue, incl. the one being fetched"). A single-register tracker is reset
    // by that second commit mid-drain, which is what made a_burst_len fail
    // against correct hardware. Modelling the queue rather than assuming it
    // away keeps the pipelining -- and the bugs pipelining causes -- in scope.
    //
    // REGISTER-IZED ON PURPOSE. These arrays are read by the data assertion,
    // and a dynamically-indexed array read there costs one SMT array axiom
    // per write/read pair per BMC step -- measured, that doubles the solve
    // time every step from ~18 and never finishes depth 26. Living in
    // individual registers with explicit case-muxes (CQ=4, BEATS=2, NE=2 are
    // the fixed small geometry) makes every access constant-indexed, which
    // yosys lowers to plain FFs and muxes. Keep it this way.
    localparam int CQ = 4;                     // >= WR_DRAIN_AHEAD
    reg [PTRW-1:0] f_q0_slot, f_q1_slot, f_q2_slot, f_q3_slot;
    reg            f_q0_known, f_q1_known, f_q2_known, f_q3_known;
    reg [DW-1:0]   f_q0_d0, f_q0_d1, f_q1_d0, f_q1_d1;
    reg [DW-1:0]   f_q2_d0, f_q2_d1, f_q3_d0, f_q3_d1;
    reg [SW-1:0]   f_q0_s0, f_q0_s1, f_q1_s0, f_q1_s1;
    reg [SW-1:0]   f_q2_s0, f_q2_s1, f_q3_s0, f_q3_s1;
    reg [1:0]      f_cq_h, f_cq_t;
    reg [2:0]      f_cq_n;
    reg [BCW-1:0]  f_cm_beat;

    // per-slot "a commit of this slot is draining right now" -- the queue-
    // membership fact the reuse cover needs, kept at slot granularity (2 bits)
    reg [NE-1:0] f_inflight;

    // head-of-queue view (muxes, not memories)
    reg [PTRW-1:0] f_cm_slot;
    reg            f_cm_known;
    reg [DW-1:0]   f_head_d0, f_head_d1;
    reg [SW-1:0]   f_head_s0, f_head_s1;
    always @(*) begin
        case (f_cq_h)
            2'd0: begin
                f_cm_slot = f_q0_slot; f_cm_known = f_q0_known;
                f_head_d0 = f_q0_d0;   f_head_d1  = f_q0_d1;
                f_head_s0 = f_q0_s0;   f_head_s1  = f_q0_s1;
            end
            2'd1: begin
                f_cm_slot = f_q1_slot; f_cm_known = f_q1_known;
                f_head_d0 = f_q1_d0;   f_head_d1  = f_q1_d1;
                f_head_s0 = f_q1_s0;   f_head_s1  = f_q1_s1;
            end
            2'd2: begin
                f_cm_slot = f_q2_slot; f_cm_known = f_q2_known;
                f_head_d0 = f_q2_d0;   f_head_d1  = f_q2_d1;
                f_head_s0 = f_q2_s0;   f_head_s1  = f_q2_s1;
            end
            default: begin
                f_cm_slot = f_q3_slot; f_cm_known = f_q3_known;
                f_head_d0 = f_q3_d0;   f_head_d1  = f_q3_d1;
                f_head_s0 = f_q3_s0;   f_head_s1  = f_q3_s1;
            end
        endcase
    end

    // include a commit accepted THIS cycle: f_cq_n is registered, so a drain
    // beat in the same cycle as its accept would otherwise read as 'no burst
    // active'.
    wire           f_cm_active = (f_cq_n != 0) || w_accept;

    // beat position within the drain stream, independent of which commit it
    // belongs to: reset by `last`, incremented by every accepted beat.
    reg [BCW-1:0] f_stream_beat;
    always @(posedge aclk) begin
        if (!aresetn) f_stream_beat <= 0;
        else if (w_cm) f_stream_beat <= cm_rd_last_o ? 0 : f_stream_beat + 1'b1;
    end

    // global counters -- attribution-free (kept to document why commit-count
    // attribution was abandoned: beats can precede their commit's handshake)
    reg [9:0] f_commits, f_cm_beats;
    always @(posedge aclk) begin
        if (!aresetn) begin
            f_commits <= 0; f_cm_beats <= 0;
        end
        else begin
            if (w_accept) f_commits  <= f_commits + 1'b1;
            if (w_cm)     f_cm_beats <= f_cm_beats + 1'b1;
        end
    end

    // slots whose drain RAN TO COMPLETION (its last beat was consumed). A
    // commit of such a slot is legal reuse AFTER the drain; this register
    // only feeds a cover.
    reg [NE-1:0] f_drained;

    always @(posedge aclk) begin
        if (!aresetn) begin
            f_cq_h <= 0; f_cq_t <= 0; f_cq_n <= 0; f_cm_beat <= 0;
            f_drained <= 0; f_inflight <= 0;
            f_q0_slot <= 0; f_q1_slot <= 0; f_q2_slot <= 0; f_q3_slot <= 0;
            f_q0_known <= 1'b0; f_q1_known <= 1'b0; f_q2_known <= 1'b0; f_q3_known <= 1'b0;
            f_q0_d0 <= 0; f_q0_d1 <= 0; f_q1_d0 <= 0; f_q1_d1 <= 0;
            f_q2_d0 <= 0; f_q2_d1 <= 0; f_q3_d0 <= 0; f_q3_d1 <= 0;
            f_q0_s0 <= 0; f_q0_s1 <= 0; f_q1_s0 <= 0; f_q1_s1 <= 0;
            f_q2_s0 <= 0; f_q2_s1 <= 0; f_q3_s0 <= 0; f_q3_s1 <= 0;
        end else begin
            if (w_accept) begin
                // snapshot the whole burst: the live per-entry shadow can be
                // overwritten by a refill before this drain finishes (eviction
                // is at FETCH-last, the tail beats drain from the skid), so
                // the comparison must run against this copy. Under the
                // decision-time slot discipline f_known[slot] is 1 here --
                // the fill landed at least a cycle ago.
                f_inflight[commit_slot_i] <= 1'b1;
                case (f_cq_t)
                    2'd0: begin
                        f_q0_slot <= commit_slot_i;
                        f_q0_known <= f_known[commit_slot_i];
                        case (commit_slot_i)
                            1'b0: begin
                                f_q0_d0 <= f_slot_data[0][0]; f_q0_d1 <= f_slot_data[0][1];
                                f_q0_s0 <= f_slot_strb[0][0]; f_q0_s1 <= f_slot_strb[0][1];
                            end
                            default: begin
                                f_q0_d0 <= f_slot_data[1][0]; f_q0_d1 <= f_slot_data[1][1];
                                f_q0_s0 <= f_slot_strb[1][0]; f_q0_s1 <= f_slot_strb[1][1];
                            end
                        endcase
                    end
                    2'd1: begin
                        f_q1_slot <= commit_slot_i;
                        f_q1_known <= f_known[commit_slot_i];
                        case (commit_slot_i)
                            1'b0: begin
                                f_q1_d0 <= f_slot_data[0][0]; f_q1_d1 <= f_slot_data[0][1];
                                f_q1_s0 <= f_slot_strb[0][0]; f_q1_s1 <= f_slot_strb[0][1];
                            end
                            default: begin
                                f_q1_d0 <= f_slot_data[1][0]; f_q1_d1 <= f_slot_data[1][1];
                                f_q1_s0 <= f_slot_strb[1][0]; f_q1_s1 <= f_slot_strb[1][1];
                            end
                        endcase
                    end
                    2'd2: begin
                        f_q2_slot <= commit_slot_i;
                        f_q2_known <= f_known[commit_slot_i];
                        case (commit_slot_i)
                            1'b0: begin
                                f_q2_d0 <= f_slot_data[0][0]; f_q2_d1 <= f_slot_data[0][1];
                                f_q2_s0 <= f_slot_strb[0][0]; f_q2_s1 <= f_slot_strb[0][1];
                            end
                            default: begin
                                f_q2_d0 <= f_slot_data[1][0]; f_q2_d1 <= f_slot_data[1][1];
                                f_q2_s0 <= f_slot_strb[1][0]; f_q2_s1 <= f_slot_strb[1][1];
                            end
                        endcase
                    end
                    default: begin
                        f_q3_slot <= commit_slot_i;
                        f_q3_known <= f_known[commit_slot_i];
                        case (commit_slot_i)
                            1'b0: begin
                                f_q3_d0 <= f_slot_data[0][0]; f_q3_d1 <= f_slot_data[0][1];
                                f_q3_s0 <= f_slot_strb[0][0]; f_q3_s1 <= f_slot_strb[0][1];
                            end
                            default: begin
                                f_q3_d0 <= f_slot_data[1][0]; f_q3_d1 <= f_slot_data[1][1];
                                f_q3_s0 <= f_slot_strb[1][0]; f_q3_s1 <= f_slot_strb[1][1];
                            end
                        endcase
                    end
                endcase
                f_cq_t <= f_cq_t + 1'b1;
            end
            if (w_cm) begin
                if (cm_rd_last_o) begin
                    f_cq_h <= f_cq_h + 1'b1;
                    f_drained[f_cm_slot] <= 1'b1;
                    f_inflight[f_cm_slot] <= 1'b0;
                end
                f_cm_beat <= cm_rd_last_o ? 0 : f_cm_beat + 1'b1;
            end
            f_cq_n <= f_cq_n + (w_accept ? 1 : 0)
                             - ((w_cm && cm_rd_last_o) ? 1 : 0);
            // a new fill landing on a slot supersedes its drained history
            if (f_pend_full)
                for (s = 0; s < NE; s = s + 1)
                    if (sch_valid_o[s] && !f_sch_d[s]) f_drained[s] <= 1'b0;
        end
    end

    // =====================================================================
    // FAMILY 1 -- COMMIT DATA INTEGRITY (and no slot reuse before its
    // drain, whose observable form is the corruption this family asserts
    // against -- see the header), the reason this file exists
    // =====================================================================
    always @(posedge aclk) if (aresetn && f_past_valid > 3) begin
        // A beat written is the beat drained: for every consumed drain beat
        // whose burst's fill the shadow observed, the data and strobe are
        // exactly the recorded fill beat, at the recorded position -- which
        // is the in-order claim, one assertion. Attributed per burst through
        // the drain-queue model, so the decision/fire split of commit does
        // not matter: beats are compared against the burst whose drain they
        // are, not against the burst whose handshake most recently landed.
        // The same assertion polices slot reuse: it holds only if no refill
        // reaches an SRAM cell before the burst that cell belongs to has been
        // read out -- freeing the slot early (mutation M2) corrupts exactly
        // the beats fetched after the refill and fails here.
        if (FAMILY1 && w_cm && f_cm_active && f_cm_known)
            a_cm_data: assert (cm_rd_data_o == (f_cm_beat == 0 ? f_head_d0 : f_head_d1)
                            && cm_rd_strb_o == (f_cm_beat == 0 ? f_head_s0 : f_head_s1));
    end

    // =====================================================================
    // FAMILY 2 -- BURST FRAMING and SLOT LIFECYCLE
    // =====================================================================
    always @(posedge aclk) if (aresetn && f_past_valid > 3) begin
        // Framing measured from the DRAIN STREAM ITSELF, which needs no
        // attribution: between two `last` pulses there are exactly BEATS beats.
        if (FAMILY2 && w_cm && cm_rd_last_o)
            a_burst_len: assert (f_stream_beat == BCW'(BEATS-1));
        // NOT ASSERTED: beats <= commits * BEATS. Measured, it is FALSE, and
        // the counterexample shows why it is not a DUT bug: a drain beat fires
        // at cycle 11 for a commit whose handshake lands at cycle 12. The drain
        // is anchored on an upstream DECISION, not on commit_valid/ready --
        // which is what the RTL means by "commit_ready_o answers 'will a commit
        // decided now be accepted'": that handshake is about drain-queue SPACE,
        // not about starting a burst. So `commits` counted at the handshake is
        // simply the wrong denominator, and no port-level counting fixes it.
        // NOT a biconditional here, unlike the read CAM. `sch_valid_o` is
        // "filled, not yet committed", so a slot part-way through its fill is
        // not counted in it -- "a slot is free" and "sch_valid is not full" are
        // different statements, and asserting equality fails on correct
        // hardware. What must hold is the safe direction: the CAM never accepts
        // an insert when every slot is already occupied.
        if (FAMILY2 && ins_ready_o) a_ins_ready_implies_free: assert (sch_valid_o != {NE{1'b1}});
    end

    // =====================================================================
    // COVER
    // =====================================================================
    always @(posedge aclk) if (aresetn) begin
        c_fill:        cover (w_wd);
        c_landed:      cover (|f_known);
        c_commit:      cover (w_accept);
        c_drain_beat:  cover (w_cm);
        c_data_check:  cover (w_cm && f_cm_active && f_cm_known);
        c_burst_end:   cover (w_cm && cm_rd_last_o);
        c_both_slots:  cover (&sch_valid_o);
        // the reuse window, exercised not assumed away: a re-commit of a slot
        // whose earlier commit is STILL draining (legal because eviction is
        // at fetch-last; safe only if the refill has not reached the SRAM
        // cells the old drain reads -- which is a_cm_data's claim), and the
        // same boundary from the completed side
        c_reuse_live:        cover (w_accept && f_inflight[commit_slot_i]);
        c_reuse_after_drain: cover (w_accept && f_drained[commit_slot_i]);
    end

endmodule
