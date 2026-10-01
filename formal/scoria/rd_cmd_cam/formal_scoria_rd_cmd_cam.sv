// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
//
// PORTED FROM formal/pumice/rd_cmd_cam, 2026-10-01. scoria's scoria_rd_cmd_cam has a
// port list IDENTICAL to pumice's counterpart (measured, all 8 ported blocks)
// and dv/tests/fub/test_scoria_pumice_logic_parity.py gates the logic
// equivalence, so the properties carry over unchanged -- and this proof was
// mutation-tested against scoria's own RTL before being trusted, because a
// mechanical port that passes everywhere is what a vacuous bind looks like.
//
// References to `pumice BUG-/ISSUE-/TASK-nnn` below are DELIBERATE
// cross-references to where a property was first derived or a bug first found;
// they are not stale text. Claims about pumice FILES have been corrected to
// scoria's where they differ.
//
// Formal wrapper for scoria_rd_cmd_cam -- the read SCHEDULING window.
//
// WHY THIS BLOCK (pumice TASK-035 tier 1). It is the second place in the
// controller where a bug is silent on the wire. An entry carries a TICKET --
// the scoria_rd_return_ring slot the read's data will land in -- from insert
// through to issue. If the wrong ticket comes out, the read completes
// perfectly: right length, right timing, no error anywhere. The data simply
// belongs to a different AXI transaction, and the only witness is a mismatch
// a long way downstream in whoever asked.
//
// WHAT IS PROVED
//
//   TICKET INTEGRITY -- the headline. An arbitrary slot is tracked from the
//   insert that fills it to the issue that frees it, and the ticket forwarded
//   at issue must be the ticket stored at insert. This is the property the
//   block exists to keep, and it is the one sim samples rather than proves.
//
//   SLOT LIFECYCLE -- a slot is never inserted into while occupied, never
//   issued while free, and `ins_ready_o` is exactly "some slot is free". A
//   double-insert silently overwrites a live read; an issue to a free slot
//   forwards a stale ticket.
//
//   THE AGE-ORDER MATRIX -- `sch_older_o` replaces a 16-bit age compare on the
//   arbiter's critical path with 1-bit lookups, so the arbiter's pick is only
//   as good as this matrix. Proved a STRICT ORDER over valid entries:
//   irreflexive, antisymmetric and transitive. None of those failing would
//   fail a test; the arbiter would just pick the wrong read and everything
//   downstream would still be well-formed.
//
//   SCHEDULING VECTOR CONSISTENCY -- `sch_valid_o` agrees with the slot
//   occupancy the rest of the block acts on.
//
// SMALL GEOMETRY ON PURPOSE. 4 entries, 4 banks, 4-bit row/col, 8 ring
// tickets. The lifecycle and the order matrix are the same at 4 entries as at
// 8; what a small window buys is that "every pair of entries" and "every
// triple" are questions the solver can answer exhaustively, which is what the
// transitivity property needs.
//
// YOSYS-COMPATIBLE FORM. DUT pre-flattened by sv2v; immediate assertions in
// `always @(posedge clk)`. See formal_bank_timer.sv.

`timescale 1ns / 1ps

module formal_scoria_rd_cmd_cam #(
    parameter int NE   = 4,    // NUM_ENTRIES
    parameter int NLU  = 2,    // N_SCHED_LU
    parameter int NB   = 4,    // NUM_BANKS
    parameter int RW   = 4,    // ROW_WIDTH
    parameter int CW   = 4,    // COL_WIDTH
    parameter int IW   = 2,    // AXI_ID_WIDTH
    parameter int AGEW = 6,    // AGE_WIDTH
    parameter int RRD  = 8,    // RD_RET_DEPTH
    parameter int BKW  = 2,    // $clog2(NB)
    parameter int PTRW = 2,    // $clog2(NE)
    parameter int TW   = 3     // $clog2(RRD)
) (
    input logic aclk,
    input logic aresetn
);

    (* anyseq *) reg              ins_valid_i;
    (* anyseq *) reg [BKW-1:0]    ins_bank_i;
    (* anyseq *) reg [RW-1:0]     ins_row_i;
    (* anyseq *) reg [CW-1:0]     ins_col_i;
    (* anyseq *) reg [IW-1:0]     ins_id_i;
    (* anyseq *) reg [3:0]        ins_qos_i;
    (* anyseq *) reg [TW-1:0]     ins_ticket_i;
    (* anyseq *) reg [NLU-1:0]            sched_lu_valid_i;
    (* anyseq *) reg [NLU*BKW-1:0]        sched_lu_bank_i;
    (* anyseq *) reg [NLU*RW-1:0]         sched_lu_row_i;
    (* anyseq *) reg [7:0]        age_thresh_i;
    (* anyseq *) reg              issue_valid_i;
    (* anyseq *) reg [PTRW-1:0]   issue_slot_i;
    (* anyseq *) reg              iss_ready_i;

    wire                 ins_ready_o, issue_ready_o, iss_valid_o, busy_o;
    wire [TW-1:0]        iss_ticket_o;
    wire [NLU-1:0]       sched_lu_hit_o;
    wire [NLU*PTRW-1:0]  sched_lu_slot_o;
    wire [NLU*CW-1:0]    sched_lu_col_o;
    wire [NLU*IW-1:0]    sched_lu_id_o;
    wire [NLU*AGEW-1:0]  sched_lu_age_o;
    wire [NE-1:0]        sch_valid_o, sch_age_exceed_o;
    wire [NE*BKW-1:0]    sch_bank_o;
    wire [NE*RW-1:0]     sch_row_o;
    wire [NE*CW-1:0]     sch_col_o;
    wire [NE*NE-1:0]     sch_older_o;
    wire [NE*4-1:0]      sch_qos_o;
    wire [AGEW-1:0]      sch_head_rel_o;
    wire                 oldest_valid_o;
    wire [BKW-1:0]       oldest_bank_o;
    wire [RW-1:0]        oldest_row_o;
    wire [CW-1:0]        oldest_col_o;
    wire [IW-1:0]        oldest_id_o;
    wire [PTRW-1:0]      oldest_slot_o;

    scoria_rd_cmd_cam #(
        .NUM_ENTRIES(NE), .N_SCHED_LU(NLU), .NUM_BANKS(NB), .ROW_WIDTH(RW),
        .COL_WIDTH(CW), .AXI_ID_WIDTH(IW), .AGE_WIDTH(AGEW), .RD_RET_DEPTH(RRD)
    ) dut (
        .aclk(aclk), .aresetn(aresetn),
        .ins_valid_i(ins_valid_i), .ins_ready_o(ins_ready_o),
        .ins_bank_i(ins_bank_i), .ins_row_i(ins_row_i), .ins_col_i(ins_col_i),
        .ins_id_i(ins_id_i), .ins_qos_i(ins_qos_i), .ins_ticket_i(ins_ticket_i),
        .sched_lu_valid_i(sched_lu_valid_i), .sched_lu_bank_i(sched_lu_bank_i),
        .sched_lu_row_i(sched_lu_row_i), .sched_lu_hit_o(sched_lu_hit_o),
        .sched_lu_slot_o(sched_lu_slot_o), .sched_lu_col_o(sched_lu_col_o),
        .sched_lu_id_o(sched_lu_id_o), .sched_lu_age_o(sched_lu_age_o),
        .sch_valid_o(sch_valid_o), .sch_bank_o(sch_bank_o), .sch_row_o(sch_row_o),
        .sch_col_o(sch_col_o), .sch_older_o(sch_older_o),
        .age_thresh_i(age_thresh_i), .sch_age_exceed_o(sch_age_exceed_o),
        .sch_qos_o(sch_qos_o), .sch_head_rel_o(sch_head_rel_o),
        .oldest_valid_o(oldest_valid_o), .oldest_bank_o(oldest_bank_o),
        .oldest_row_o(oldest_row_o), .oldest_col_o(oldest_col_o),
        .oldest_id_o(oldest_id_o), .oldest_slot_o(oldest_slot_o),
        .issue_valid_i(issue_valid_i), .issue_ready_o(issue_ready_o),
        .issue_slot_i(issue_slot_i), .iss_valid_o(iss_valid_o),
        .iss_ready_i(iss_ready_i), .iss_ticket_o(iss_ticket_o),
        .busy_o(busy_o)
    );

    wire w_ins   = ins_valid_i   && ins_ready_o;
    wire w_issue = issue_valid_i && issue_ready_o;

    reg [7:0] f_past_valid = 0;
    always @(posedge aclk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!aresetn);
    always @(posedge aclk) if (f_past_valid >= 2) assume (aresetn);

    // =====================================================================
    // ENVIRONMENT. The scheduler issues only against a slot it was told is
    // schedulable -- `sch_valid_o` is how it knows. Without this the engine
    // issues at a free slot and forwards a stale ticket, which is a statement
    // about the CALLER, not about this block.
    // =====================================================================
    always @(*) if (aresetn) begin
        assume (!issue_valid_i || sch_valid_o[issue_slot_i]);
    end

    // =====================================================================
    // SHADOW: what ticket does each slot hold?
    //
    // The CAM picks the free slot itself, so the wrapper cannot know at insert
    // time WHICH slot was filled. It can see it one cycle later: the slot that
    // went 0 -> 1 in sch_valid_o is the one. So the insert's ticket is held for
    // a cycle and then assigned to whichever slot actually became valid.
    //
    // (The first version of this tracked one anyconst slot and captured the
    // ticket on ANY insert while that slot was free -- so an insert into a
    // DIFFERENT slot poisoned the shadow, and a_ticket_integrity failed against
    // correct hardware. The wrapper was wrong, not the DUT.)
    // =====================================================================
    reg [TW-1:0] f_ticket [NE];      // expected ticket per slot
    reg [NE-1:0] f_known;            // that slot's expected ticket is established
    reg [NE-1:0] f_sch_valid_d;
    reg [TW-1:0] f_pend_ticket;
    reg          f_pend;

    integer s;
    always @(posedge aclk) begin
        if (!aresetn) begin
            f_known <= 0; f_pend <= 1'b0; f_pend_ticket <= 0; f_sch_valid_d <= 0;
            for (s = 0; s < NE; s = s + 1) f_ticket[s] <= 0;
        end else begin
            f_sch_valid_d <= sch_valid_o;
            // assign last cycle's insert to whichever slot just became valid
            if (f_pend)
                for (s = 0; s < NE; s = s + 1)
                    if (sch_valid_o[s] && !f_sch_valid_d[s]) begin
                        f_ticket[s] <= f_pend_ticket;
                        f_known[s]  <= 1'b1;
                    end
            f_pend        <= w_ins;
            f_pend_ticket <= ins_ticket_i;
            // a freed slot's expectation is stale until it is filled again
            if (w_issue) f_known[issue_slot_i] <= 1'b0;
        end
    end

    // =====================================================================
    // FAMILY 1 -- SLOT LIFECYCLE
    // =====================================================================
    integer i, j, k;
    // Loop-computed predicates, asserted ONCE each. A labelled assertion inside
    // a generate/for creates one cell per iteration with the same name, which
    // yosys rejects -- and an unlabelled one gives a failure you cannot name.
    reg ok_irrefl, ok_antisym, ok_trans;
    always @(*) begin
        ok_irrefl = 1'b1; ok_antisym = 1'b1; ok_trans = 1'b1;
        for (i = 0; i < NE; i = i + 1) begin
            if (sch_older_o[i*NE + i]) ok_irrefl = 1'b0;
            for (j = 0; j < NE; j = j + 1) begin
                if (i != j && sch_valid_o[i] && sch_valid_o[j]
                    && (sch_older_o[i*NE + j] == sch_older_o[j*NE + i]))
                    ok_antisym = 1'b0;
                for (k = 0; k < NE; k = k + 1)
                    if (sch_valid_o[i] && sch_valid_o[j] && sch_valid_o[k]
                        && sch_older_o[i*NE + j] && sch_older_o[j*NE + k]
                        && !sch_older_o[i*NE + k])
                        ok_trans = 1'b0;
            end
        end
    end

    always @(posedge aclk) if (aresetn && f_past_valid > 2) begin
        // ins_ready_o is exactly "a slot is free": one early overwrites a live
        // read, one late stalls the intake for no reason.
        a_ins_ready_is_free: assert (ins_ready_o == (sch_valid_o != {NE{1'b1}}));

        // FAMILY 2 -- the age-order matrix is a STRICT ORDER over valid
        // entries. sch_older_o replaces a 16-bit age compare on the arbiter's
        // critical path, so the pick is only as good as this. None of these
        // failing would fail a test: the arbiter would pick the wrong read and
        // everything downstream would still be well formed.
        a_ord_irreflexive:  assert (ok_irrefl);
        a_ord_antisymmetric: assert (ok_antisym);
        a_ord_transitive:   assert (ok_trans);
    end

    // =====================================================================
    // FAMILY 3 -- TICKET INTEGRITY, the reason this file exists
    // =====================================================================
    always @(posedge aclk) if (aresetn && f_past_valid > 3) begin
        if (w_issue && f_known[issue_slot_i] && iss_valid_o)
            a_ticket_integrity: assert (iss_ticket_o == f_ticket[issue_slot_i]);
    end

    // =====================================================================
    // COVER
    // =====================================================================
    always @(posedge aclk) if (aresetn) begin
        c_full:        cover (sch_valid_o == {NE{1'b1}});
        c_insert:      cover (w_ins);
        c_issue:       cover (w_issue);
        c_tracked:     cover (|f_known);
        c_ticket_chk:  cover (w_issue && f_known[issue_slot_i] && iss_valid_o);
        c_two_valid:   cover (sch_valid_o[0] && sch_valid_o[1]);
        c_lu_hit:      cover (|sched_lu_hit_o);
    end

endmodule
