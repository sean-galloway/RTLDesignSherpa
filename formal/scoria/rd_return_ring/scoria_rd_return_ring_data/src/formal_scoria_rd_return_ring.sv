// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
//
// PORTED FROM formal/pumice/rd_return_ring, 2026-10-01. scoria's scoria_rd_return_ring has a
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
// Formal wrapper for scoria_rd_return_ring -- the AR-order read-return buffer.
//
// WHY THIS BLOCK. Its central invariant was recorded on pumice, in
// dv/tbclasses/pumice_telemetry_invariants.py under SIM_ONLY_INVARIANTS, as
// one simulation structurally cannot check. scoria has NO equivalent file --
// checked -- so on this side the statement lives only here:
//
//     "read-return ring occupancy <= RD_RET_DEPTH at all times. Not a counter:
//      it is an instantaneous LEVEL, so it needs the RTL signal. This is the
//      BUG-003 invariant, and the RTL check that caught BUG-003 is exactly the
//      kind the no-assertions ruling forbids."
//
// That is the gap this file closes. An instantaneous level is precisely what a
// formal engine checks and a telemetry counter cannot: the host reads counters
// between bursts, so a level that overshoots and recovers inside a burst is
// invisible to it. Here it is checked in every cycle of every reachable trace.
//
// THE RTL's OWN TWO ASSERTIONS ARE ENVIRONMENT CONTRACTS, NOT DUT CHECKS.
// scoria_rd_return_ring.sv carries two `ifndef SYNTHESIS` assertions:
//
//     assert (!(dfi_ret_valid_i && !w_iq_rd_valid))   // return with no ticket
//     assert (!(issue_valid_i && w_empty))            // issue into an empty ring
//
// Both constrain the block's INPUTS. They were never testing this module; they
// were testing whoever drives it. They appear below as `assume`, which is what
// they always were, and sv2v drops them from the flattened DUT so they cannot
// be double-counted. (They are also assertions living inside RTL, which the
// repo rule forbids -- stating them here is where they belong.)
//
// WHAT IS PROVED. Everything is checked against an INDEPENDENT SHADOW MODEL
// built in this wrapper, not by restating the DUT's own internals. That is
// possible because every input the block's internal issue-FIFO sees is
// port-visible, so the wrapper can reconstruct head, tail, occupancy and the
// issue queue from the interface alone and then disagree with the DUT:
//
//   ACCOUNTING (the BUG-003 family)
//     * occ_o <= DEPTH always, and never wraps through zero
//     * occ_o equals an independently counted alloc-minus-free
//     * alloc_ticket_o equals an independently tracked tail pointer
//     * alloc_ready_o is exactly "not full"
//     * busy_o cannot be low while reads are in flight
//
//   NO FABRICATION
//     * bursts drained <= bursts returned: the ring never emits a burst whose
//       data never arrived (the drain-gating contract)
//     * every drained burst is exactly AXI_BEATS_PER_BURST beats long
//
//   DATA INTEGRITY, end to end through the BRAM
//     * an arbitrary (slot, beat) written by the DFI drains with that same
//       data, in AR order, after an arbitrary scheduler REORDERING between
//       allocation order and issue order
//
// BOUNDED ON PURPOSE. DEPTH=4 (not 32), 8-bit data, 2 beats per burst. The
// accounting is the same accounting at 4 as at 32 -- what changes is only the
// unroll depth needed to fill it -- and a narrow datapath keeps the BRAM's
// address space small enough that data integrity is checkable at all.
//
// YOSYS-COMPATIBLE FORM. DUT pre-flattened by sv2v; immediate assertions in
// `always @(posedge clk)` rather than concurrent SVA. See formal_bank_timer.sv.

`timescale 1ns / 1ps

module formal_scoria_rd_return_ring #(
    parameter int DEPTH = 4,
    parameter int DW    = 8,
    parameter int BEATS = 2,
    parameter int TW    = 2,          // $clog2(DEPTH)
    parameter int BCW   = 1,          // $clog2(BEATS)
    parameter int OCW   = 3,          // $clog2(DEPTH+1)
    // Data integrity is proved as its OWN sby task. It adds an anyconst pair
    // over the BRAM's address space, and carrying that through the accounting
    // proof put step 18 of 28 past ten minutes on its own. Split, each task
    // closes in seconds; together they cover the same ground.
    parameter int F_DATA = 0
) (
    input logic aclk,
    input logic aresetn
);

    // ---- free inputs --------------------------------------------------------
    (* anyseq *) reg            alloc_valid_i;
    (* anyseq *) reg            issue_valid_i;
    (* anyseq *) reg [TW-1:0]   issue_ticket_i;
    (* anyseq *) reg            dfi_ret_valid_i;
    (* anyseq *) reg [DW-1:0]   dfi_ret_data_i;
    (* anyseq *) reg [1:0]      dfi_ret_resp_i;
    (* anyseq *) reg            drain_ready_i;

    wire            alloc_ready_o, issue_ready_o, dfi_ret_ready_o;
    wire [TW-1:0]   alloc_ticket_o;
    wire            drain_valid_o, drain_last_o, busy_o;
    wire [DW-1:0]   drain_data_o;
    wire [1:0]      drain_resp_o;
    wire [OCW-1:0]  occ_o;

    // The DFI drives exactly BEATS beats per burst, so `last` is not free.
    reg [BCW-1:0] f_rbeat;
    wire dfi_ret_last_i = (f_rbeat == BCW'(BEATS-1));

    scoria_rd_return_ring #(
        .DEPTH(DEPTH), .AXI_DATA_WIDTH(DW), .AXI_BEATS_PER_BURST(BEATS)
    ) dut (
        .aclk(aclk), .aresetn(aresetn),
        .alloc_valid_i(alloc_valid_i), .alloc_ready_o(alloc_ready_o),
        .alloc_ticket_o(alloc_ticket_o),
        .issue_valid_i(issue_valid_i), .issue_ready_o(issue_ready_o),
        .issue_ticket_i(issue_ticket_i),
        .dfi_ret_valid_i(dfi_ret_valid_i), .dfi_ret_ready_o(dfi_ret_ready_o),
        .dfi_ret_data_i(dfi_ret_data_i), .dfi_ret_resp_i(dfi_ret_resp_i),
        .dfi_ret_last_i(dfi_ret_last_i),
        .drain_valid_o(drain_valid_o), .drain_ready_i(drain_ready_i),
        .drain_data_o(drain_data_o), .drain_resp_o(drain_resp_o),
        .drain_last_o(drain_last_o),
        .occ_o(occ_o), .busy_o(busy_o)
    );

    wire w_alloc  = alloc_valid_i   && alloc_ready_o;
    wire w_issue  = issue_valid_i   && issue_ready_o;
    wire w_ret    = dfi_ret_valid_i && dfi_ret_ready_o;
    wire w_drain  = drain_valid_o   && drain_ready_i;
    wire w_free   = w_drain && drain_last_o;

    // ---- reset ---------------------------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge aclk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);
    initial assume (!aresetn);
    always @(posedge aclk) if (f_past_valid >= 2) assume (aresetn);

    // =========================================================================
    // SHADOW MODEL -- reconstructed from the interface alone.
    // =========================================================================
    reg [TW-1:0]  f_head, f_tail;      // AR-order ring pointers
    reg [OCW:0]   f_occ;               // ONE BIT WIDER than the DUT's: a DUT
                                       // overflow shows as a disagreement here
                                       // rather than wrapping in both models.
    reg [DEPTH-1:0] f_issued;          // this slot's ticket is in the issue queue

    // The issue queue, modelled: tickets pushed on issue, popped on the last
    // beat of the return that they belong to. Its contents are the ONLY thing
    // that says which slot an arriving return beat lands in.
    reg [TW-1:0]  f_iq [DEPTH];
    reg [TW-1:0]  f_iq_h, f_iq_t;
    reg [OCW:0]   f_iq_n;
    wire [TW-1:0] f_iq_head = f_iq[f_iq_h];

    integer i;
    always @(posedge aclk) begin
        if (!aresetn) begin
            f_head <= 0; f_tail <= 0; f_occ <= 0; f_rbeat <= 0;
            f_issued <= 0;
            f_iq_h <= 0; f_iq_t <= 0; f_iq_n <= 0;
            for (i = 0; i < DEPTH; i = i + 1) f_iq[i] <= 0;
        end else begin
            if (w_alloc) begin
                f_tail             <= f_tail + 1'b1;
                f_issued[f_tail]   <= 1'b0;   // a reallocated slot is un-issued
            end
            if (w_free)  f_head <= f_head + 1'b1;
            f_occ <= f_occ + (w_alloc ? 1 : 0) - (w_free ? 1 : 0);

            if (w_issue) begin
                f_iq[f_iq_t] <= issue_ticket_i;
                f_iq_t       <= f_iq_t + 1'b1;
                f_issued[issue_ticket_i] <= 1'b1;
            end
            if (w_ret && dfi_ret_last_i) f_iq_h <= f_iq_h + 1'b1;
            f_iq_n <= f_iq_n + (w_issue ? 1 : 0)
                             - ((w_ret && dfi_ret_last_i) ? 1 : 0);

            if (w_ret) f_rbeat <= dfi_ret_last_i ? 0 : f_rbeat + 1'b1;
        end
    end

    // "slot t is currently allocated" -- distance from head is inside occupancy
    function automatic allocated(input [TW-1:0] t);
        allocated = ({1'b0, (t - f_head)} < f_occ);
    endfunction

    // =========================================================================
    // ENVIRONMENT ASSUMPTIONS -- the contract the CAM, arbiter and DFI honour.
    // =========================================================================
    always @(*) if (aresetn) begin
        // The RTL's two `ifndef SYNTHESIS` assertions, stated where they belong.
        // A DFI return beat only ever arrives for a ticket that is in flight,
        // because the DFI only returns reads the controller issued.
        assume (!dfi_ret_valid_i || dfi_ret_ready_o);
        // An issue notify only ever names an allocated slot: the CAM entry that
        // issues was given its ticket at admit.
        assume (!issue_valid_i || (occ_o != 0));

        // A ticket is issued exactly once per allocation, and only for a slot
        // that is currently allocated. The scheduler is free to issue them in
        // ANY order -- that reordering is the whole point of the ring -- but it
        // cannot invent a ticket or issue one twice.
        assume (!issue_valid_i || allocated(issue_ticket_i));
        assume (!issue_valid_i || !f_issued[issue_ticket_i]);
        // Never push into a full issue queue: the arbiter's rd_issue_ready gate.
        assume (!issue_valid_i || issue_ready_o);
    end

    // =========================================================================
    // FAMILY 1 -- ACCOUNTING. The BUG-003 family.
    // =========================================================================
    always @(posedge aclk) if (aresetn && f_past_valid > 2) begin
        // THE invariant: occupancy never exceeds the ring's depth. The shadow
        // counter is a bit wider, so an overflow appears as a real excess here
        // rather than silently wrapping in both models at once.
        a_occ_le_depth:  assert (f_occ <= DEPTH);
        a_occ_matches:   assert ({1'b0, occ_o} == f_occ);

        // ...and never wraps the other way. A free with nothing allocated would
        // take the DUT's counter from 0 to DEPTH in one cycle.
        a_no_free_empty: assert (!(w_free && occ_o == 0));

        // The ticket handed out is the tail slot, tracked independently.
        a_ticket_is_tail: assert (alloc_ticket_o == f_tail);

        // Backpressure is exactly fullness -- not one early, not one late.
        a_ready_is_notfull: assert (alloc_ready_o == (occ_o != OCW'(DEPTH)));

        // A controller that reports idle while holding reads would let a soft
        // reset or a geometry reprogram land on top of live traffic.
        if (occ_o != 0) a_busy_when_occupied: assert (busy_o);
    end

    // =========================================================================
    // FAMILY 2 -- NO FABRICATION. The ring cannot emit what never arrived.
    // =========================================================================
    reg [7:0] f_ret_bursts, f_drain_bursts;
    reg [BCW-1:0] f_dbeat;
    always @(posedge aclk) begin
        if (!aresetn) begin
            f_ret_bursts <= 0; f_drain_bursts <= 0; f_dbeat <= 0;
        end else begin
            if (w_ret && dfi_ret_last_i)  f_ret_bursts   <= f_ret_bursts + 1'b1;
            if (w_free)                   f_drain_bursts <= f_drain_bursts + 1'b1;
            if (w_drain) f_dbeat <= drain_last_o ? 0 : f_dbeat + 1'b1;
        end
    end

    always @(posedge aclk) if (aresetn && f_past_valid > 2) begin
        // The drain gate: a burst leaves only after its data has landed. This
        // is the property that would catch a drain fired off a stale ready bit.
        a_no_fabrication: assert (f_drain_bursts <= f_ret_bursts);

        // Every drained burst is exactly BEATS long -- a short or long burst
        // desynchronises the AXI R channel for every read after it.
        if (w_drain && drain_last_o)
            a_burst_length: assert (f_dbeat == BCW'(BEATS-1));
    end

    // =========================================================================
    // FAMILY 3 -- DATA INTEGRITY end to end, across a scheduler reordering.
    // Built only for the `data` task (see F_DATA above).
    // =========================================================================
    // Pick one arbitrary (slot, beat) and follow it: the DFI writes it into the
    // slot at the issue-queue head, it sits in the BRAM, and it must come back
    // out at that slot's turn in AR order -- which, because the scheduler may
    // issue out of order, is NOT the order it arrived in.
    wire w_check;
    generate if (F_DATA != 0) begin : g_data
        (* anyconst *) reg [TW-1:0]  f_slot;
        (* anyconst *) reg [BCW-1:0] f_bidx;

        reg [DW-1:0] f_data;
        reg          f_captured, f_checked;

        wire w_capture = w_ret && !f_captured
                      && (f_iq_head == f_slot) && (f_rbeat == f_bidx);
        // The first drain of that slot after the capture is that same instance:
        // the slot cannot be reallocated until it is freed, and it is freed by
        // being drained.
        assign w_check = w_drain && f_captured && !f_checked
                      && (f_head == f_slot) && (f_dbeat == f_bidx);

        always @(posedge aclk) begin
            if (!aresetn) begin
                f_data <= 0; f_captured <= 1'b0; f_checked <= 1'b0;
            end else begin
                if (w_capture) begin f_data <= dfi_ret_data_i; f_captured <= 1'b1; end
                if (w_check)   f_checked <= 1'b1;
            end
        end

        always @(posedge aclk) if (aresetn && f_past_valid > 2) begin
            if (w_check) a_data_integrity: assert (drain_data_o == f_data);
        end
    end else begin : g_nodata
        assign w_check = 1'b0;
    end endgenerate

    // =========================================================================
    // COVER -- a pass proves nothing if these states are unreachable.
    // =========================================================================
    always @(posedge aclk) if (aresetn) begin
        c_ring_full:     cover (occ_o == OCW'(DEPTH));        // ring fills
        c_drain_burst:   cover (w_drain && drain_last_o);     // a burst leaves
        // reachable only in the F_DATA build; see the note in the .sby
        c_data_checked:  cover (w_check);                     // integrity bites
        // the reordering the block exists for: a ticket issued that is NOT the
        // oldest allocated one
        c_out_of_order:  cover (w_issue && (issue_ticket_i != f_head));
        c_back_to_back:  cover (w_alloc && w_free);           // full-rate steady state
    end

endmodule
