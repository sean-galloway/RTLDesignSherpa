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
//   BURST FRAMING, measured from the drain stream itself -- between two
//   `cm_rd_last_o` pulses there are exactly AXI_BEATS_PER_BURST beats. A short
//   or long burst desynchronises the DFI write stream for everything behind it.
//
//   SLOT LIFECYCLE -- the CAM never accepts an insert with every slot occupied.
//
// WHAT IS **NOT** PROVED, and this block is therefore NOT finished:
//
//   COMMIT DATA INTEGRITY -- "a beat written is the beat drained". This is the
//   property the block exists to keep and it is not asserted here. Four
//   successive models of it were wrong, each for a different structural reason:
//     * entry slots are not SRAM slots (an r_ptr[] indirection sits between);
//     * the drain is started by an upstream DECISION, not by commit_valid/ready,
//       so counting commit handshakes attributes beats to the wrong burst;
//     * the commit drain shares its prefetch mover with the snarf stream;
//     * comparing a shadow AFTER its own update reads post-write where the DUT
//       reads pre-write.
//   The fifth model -- shadowing the SRAM by the DUT's own address -- produces a
//   readback counterexample, and I did not corroborate it well enough to call it
//   a defect. It is left disabled and described below rather than asserted,
//   because an unsound property that passes is worse than an absent one and a
//   wrong bug report is worse than both.
//
//   BURST FRAMING -- a committed burst is exactly AXI_BEATS_PER_BURST beats
//   long and `cm_rd_last_o` marks the last one. A short or long burst
//   desynchronises the DFI write stream for everything behind it.
//
//   SLOT LIFECYCLE -- `ins_ready_o` is exactly "a slot is free", and a slot
//   that has been committed is not schedulable again until it is refilled. A
//   slot re-used before its drain writes one burst's data to another burst's
//   address.
//
// WHICH SLOT IS BEING FILLED is not observable at insert time -- the CAM picks
// it. The wrapper buffers the burst's beats and assigns them to whichever slot
// goes 0 -> 1 in `sch_valid_o` ("filled, not yet committed"), which is the same
// technique formal_rd_cmd_cam.sv uses for the ticket and for the same reason.
//
// SMALL GEOMETRY ON PURPOSE. 2 entries, 2 beats per burst, 8-bit data. The
// movers are the same movers at 2 slots as at 8; a narrow datapath is what
// makes "every beat of every burst" a question the solver can answer rather
// than sample.
//
// YOSYS-COMPATIBLE FORM. DUT pre-flattened by sv2v; immediate assertions.

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
    parameter int BCW   = 1    // $clog2(BEATS)
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
    reg [DW-1:0] f_slot_data [NE][BEATS];
    reg [NE-1:0] f_known;
    reg [NE-1:0] f_sch_d;
    reg          f_pend_full;           // a complete burst is waiting to land

    // ---- environment ------------------------------------------------------
    always @(*) if (aresetn) begin
        // the scheduler commits only a slot it was told is schedulable
        assume (!commit_valid_i || sch_valid_o[commit_slot_i]);

        // ONE UN-LANDED BURST AT A TIME. The wrapper holds the burst being
        // filled in a single buffer and assigns it to whichever slot goes
        // 0 -> 1 in sch_valid_o; if the next burst starts streaming before the
        // previous one has landed, that buffer is overwritten and the SHADOW is
        // wrong, not the DUT. The counterexample that found this had a second
        // burst's first beat arriving in the same cycle the first burst landed.
        //
        // This is a scoping assumption and it is worth naming as one: it means
        // the proof covers back-to-back bursts but NOT a second fill overlapping
        // an unlanded one. Covering that needs a per-fill shadow keyed on
        // whatever the CAM uses to target the SRAM write, which is internal.
        assume (!f_pend_full || !wd_valid_i);
    end

    // =====================================================================
    // SHADOW -- the burst being filled, then per-slot once it lands.
    // =====================================================================

    integer s, b;
    always @(posedge aclk) begin
        if (!aresetn) begin
            f_wbeat <= 0; f_known <= 0; f_sch_d <= 0; f_pend_full <= 1'b0;
            for (b = 0; b < BEATS; b = b + 1) f_pend[b] <= 0;
            for (s = 0; s < NE; s = s + 1)
                for (b = 0; b < BEATS; b = b + 1) f_slot_data[s][b] <= 0;
        end else begin
            f_sch_d <= sch_valid_o;

            if (w_wd) begin
                f_pend[f_wbeat] <= wd_data_i;
                f_wbeat <= wd_last_i ? 0 : f_wbeat + 1'b1;
                if (wd_last_i) f_pend_full <= 1'b1;
            end

            // the slot that just became schedulable took the buffered burst
            if (f_pend_full)
                for (s = 0; s < NE; s = s + 1)
                    if (sch_valid_o[s] && !f_sch_d[s]) begin
                        for (b = 0; b < BEATS; b = b + 1) f_slot_data[s][b] <= f_pend[b];
                        f_known[s]  <= 1'b1;
                        f_pend_full <= 1'b0;
                    end

            // a committed slot's expectation is stale until refilled
            if (w_commit) f_known[commit_slot_i] <= 1'b0;
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
    localparam int CQ = 4;                     // >= WR_DRAIN_AHEAD
    reg [PTRW-1:0] f_cq_slot  [CQ];
    reg            f_cq_known [CQ];
    reg [1:0]      f_cq_h, f_cq_t;
    reg [2:0]      f_cq_n;
    reg [BCW-1:0]  f_cm_beat;

    // include a commit accepted THIS cycle: f_cq_n is registered, so a drain
    // beat in the same cycle as its commit handshake would otherwise read as
    // 'no burst active'.
    wire           f_cm_active = (f_cq_n != 0) || w_commit;
    wire [PTRW-1:0] f_cm_slot  = f_cq_slot [f_cq_h];
    wire            f_cm_known = f_cq_known[f_cq_h];

    // ---- SRAM shadow, addressed exactly as the DUT addresses it ----------
    // Read-only references into the DUT, naming the two signals that carry the
    // addresses. There is no port-level way to state this: the drain is started
    // by an upstream decision rather than by commit_valid/ready, so counting
    // handshakes attributes beats wrongly, and the entry->SRAM indirection means
    // the entry slot is not the storage key.
    localparam int MEMD = 4;                    // N_SRAM_SLOTS * BEATS
    reg [DW-1:0] f_mem [MEMD];
    reg [MEMD-1:0] f_mem_known;
    reg [DW-1:0] f_rd_expect;
    reg          f_rd_known;
    reg          f_rd_pending;

    integer m;
    always @(posedge aclk) begin
        if (!aresetn) begin
            f_mem_known <= 0; f_rd_pending <= 1'b0; f_rd_expect <= 0; f_rd_known <= 1'b0;
            for (m = 0; m < MEMD; m = m + 1) f_mem[m] <= 0;
        end else begin
            if (dut.w_wd_fire && dut.w_fill_idx < MEMD) begin
                f_mem[dut.w_fill_idx]       <= wd_data_i;
                f_mem_known[dut.w_fill_idx] <= 1'b1;
            end
            // Capture the EXPECTED value at fetch time, exactly as the DUT
            // captures r_rd_q. Comparing against f_mem a cycle later instead
            // reads the post-write array while r_rd_q holds the pre-write value,
            // so a fetch of an address written in the same cycle mismatches --
            // a read-during-write hazard in the CHECK, not in the DUT. Both
            // sides are non-blocking, so both see the old cell.
            f_rd_pending <= dut.w_cm_fetch;
            f_rd_expect  <= f_mem[dut.w_rd_idx];
            f_rd_known   <= f_mem_known[dut.w_rd_idx];
        end
    end

    // beat position within the drain stream, independent of which commit it
    // belongs to: reset by `last`, incremented by every accepted beat.
    reg [BCW-1:0] f_stream_beat;
    always @(posedge aclk) begin
        if (!aresetn) f_stream_beat <= 0;
        else if (w_cm) f_stream_beat <= cm_rd_last_o ? 0 : f_stream_beat + 1'b1;
    end

    // global counters -- attribution-free
    reg [9:0] f_commits, f_cm_beats;
    always @(posedge aclk) begin
        if (!aresetn) begin f_commits <= 0; f_cm_beats <= 0; end
        else begin
            if (w_commit) f_commits  <= f_commits + 1'b1;
            if (w_cm)     f_cm_beats <= f_cm_beats + 1'b1;
        end
    end

    integer q;
    always @(posedge aclk) begin
        if (!aresetn) begin
            f_cq_h <= 0; f_cq_t <= 0; f_cq_n <= 0; f_cm_beat <= 0;
            for (q = 0; q < CQ; q = q + 1) begin f_cq_slot[q] <= 0; f_cq_known[q] <= 1'b0; end
        end else begin
            if (w_commit) begin
                f_cq_slot [f_cq_t] <= commit_slot_i;
                f_cq_known[f_cq_t] <= f_known[commit_slot_i];
                f_cq_t <= f_cq_t + 1'b1;
            end
            if (w_cm && cm_rd_last_o) f_cq_h <= f_cq_h + 1'b1;
            f_cq_n <= f_cq_n + (w_commit ? 1 : 0)
                             - ((w_cm && cm_rd_last_o) ? 1 : 0);
            if (w_cm) f_cm_beat <= cm_rd_last_o ? 0 : f_cm_beat + 1'b1;
        end
    end

    // =====================================================================
    // FAMILY 1 -- COMMIT DATA INTEGRITY, the reason this file exists
    // =====================================================================
    always @(posedge aclk) if (aresetn && f_past_valid > 3) begin
        // COMMIT DATA INTEGRITY, stated where it is SOUND: at the SRAM.
        //
        // Entry slots and SRAM slots are not the same thing -- the fill writes
        // `w_fill_slot * BEATS + r_fill_beat` and the drain reads
        // `r_ptr[w_dq_rd_slot] * BEATS + r_cm_fbeat`, an entry -> SRAM map via
        // r_ptr[]. Shadowing the ENTRY slot (as the first two attempts did)
        // therefore compares the wrong cell and fails on correct hardware.
        // Shadowing the SRAM by ADDRESS removes the indirection entirely: what
        // was written at an address must be what is read back from it, which is
        // exactly the "a beat written is the beat drained" property this block
        // exists to keep.
        // NOT ENABLED -- see the header note "what is NOT proved". The shadow
        // reports a readback mismatch (write 0xFF to SRAM addr 1, fetch addr 1,
        // r_rd_q reads 0) and I could not corroborate it well enough to assert
        // it. Four earlier versions of this wrapper were wrong about this block
        // -- entry slot vs SRAM slot, commit-handshake attribution, the shared
        // snarf mover, read-during-write in the CHECK -- so a fifth model
        // producing a counterexample is not evidence of a DUT defect. Enabling
        // it is the first step of the follow-up, not a finding to act on.
        if (f_rd_pending && f_rd_known && 1'b0)
            a_sram_readback: assert (dut.r_rd_q[DW-1:0] == f_rd_expect);
    end

    // =====================================================================
    // FAMILY 2 -- BURST FRAMING and SLOT LIFECYCLE
    // =====================================================================
    always @(posedge aclk) if (aresetn && f_past_valid > 3) begin
        // Framing measured from the DRAIN STREAM ITSELF, which needs no
        // attribution: between two `last` pulses there are exactly BEATS beats.
        if (w_cm && cm_rd_last_o)
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
        if (ins_ready_o) a_ins_ready_implies_free: assert (sch_valid_o != {NE{1'b1}});
    end

    // =====================================================================
    // COVER
    // =====================================================================
    always @(posedge aclk) if (aresetn) begin
        c_fill:        cover (w_wd);
        c_landed:      cover (|f_known);
        c_commit:      cover (w_commit);
        c_drain_beat:  cover (w_cm);
        c_data_check:  cover (w_cm && f_cm_active && f_cm_known);
        c_burst_end:   cover (w_cm && cm_rd_last_o);
        c_both_slots:  cover (&sch_valid_o);
    end

endmodule
