// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_rd_return_ring
// Purpose: AR-order read-return buffer, decoupled from the scheduling CAM.
//          A read is given a TICKET (a ring slot) when it is admitted, in AR
//          order; the CAM entry that schedules it is freed the cycle the column
//          ISSUES, and the ticket alone follows the read through DRAM. Returns
//          arrive in ISSUE order (the DFI path is in order), land in the
//          ticket's slot, and the ring drains from its head in AR order once the
//          head's data is complete. So the number of reads the controller can
//          hold in flight is DEPTH (this ring), not the CAM's entry count: the
//          CAM only has to be as deep as the scheduling window.
//
//          Why: with the CAM holding a read from insert to R-drain, eight
//          entries over a ~27-cycle DRAM round trip bound read bandwidth by
//          Little's law to ~8 x 8 B / 27 cyc = 180 MB/s on the board. Here the
//          CAM entry lives insert -> issue only, and DEPTH bounds the in-flight
//          count (32 = 8 B/cycle sustained across a 27-cycle round trip).
//
//          FSM-free. State is a head/tail pointer pair, a per-slot ready bit +
//          resp, the issue-order ticket FIFO, and the BRAM. No age matrix, no
//          oldest pick: AR order IS the ring order.
//
//          The 2-deep prefetch skid over the synchronous-read BRAM is the one
//          from mc_rd_cmd_cam (same 1-cycle read latency contract; see the
//          note at the BRAM process).
//
//          Read combining (pumice TASK-060): a ticket may be allocated as a
//          SHADOW of an older ticket whose read has not issued (the CAM found
//          the same {bank,row,col}). A shadow is never issued and never
//          filled: it becomes ready when its SOURCE's return completes, and
//          the fetch reads its beats from the source's slot. The source slot
//          is PINNED -- the tail will not re-allocate it -- until every shadow
//          of it has been fetched, which is what keeps the source's data alive
//          past the source's own drain. AR order is unchanged: the shadow is
//          younger than its source, so it drains after it.
//
// Documentation: docs/uarch/PUMICE_AXI4_IFC_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_rd_return_ring #(
    parameter int DEPTH           = 32,     // in-flight reads (power of 2)
    // 1 = a shadow's marking (r_shadow / r_src) lands the cycle AFTER its
    // allocation, from registered {ticket, src}. The merge decision then
    // never fans into the ring's per-slot registers in the push cycle (granite
    // 100 MHz closure, TASK-003 2026-10-30). Safe: a merge source is always
    // still unissued when the merge is decided, so its DFI return is many
    // cycles away, and the source slot is live (not pinnable) until it drains.
    parameter bit MERGE_MARK_REG = 1'b0,
    // 1 = RET_BYPASS: a returning beat that is exactly the next beat the
    // fetch would read (its ticket is the fetch slot, its beat the fetch beat,
    // the slot not a shadow) goes straight into the skid when no BRAM beat is
    // entering it and it has room, drain-valid the next cycle instead of three
    // later (granite TASK-003, 2026-10-31). The BRAM write still happens, so
    // a missed bypass falls back to the fetch unchanged.
    parameter bit RET_BYPASS     = 1'b0,
    parameter int AXI_DATA_WIDTH  = 64,
    parameter int AXI_BEATS_PER_BURST = 4,  // beats per DRAM burst

    parameter int DW  = AXI_DATA_WIDTH,
    parameter int TW  = $clog2(DEPTH),                                        // ticket width
    parameter int BCW = (AXI_BEATS_PER_BURST > 1) ? $clog2(AXI_BEATS_PER_BURST) : 1,
    parameter int OCW = $clog2(DEPTH + 1)
) (
    input  logic                aclk,
    input  logic                aresetn,

    //=========================================================================
    // Allocate (with the CAM insert, AR order): ticket = ring tail
    //=========================================================================
    input  logic                alloc_valid_i,
    output logic                alloc_ready_o,     // ring not full
    output logic [TW-1:0]       alloc_ticket_o,
    // read combining: this allocation is a shadow of alloc_src_i (an older
    // allocated ticket whose read has not issued). Tie 0 without a combiner.
    input  logic                alloc_merge_i,
    input  logic [TW-1:0]       alloc_src_i,

    //=========================================================================
    // Issue notify (from the CAM, when the column issues): ticket -> issue_q
    //=========================================================================
    input  logic                issue_valid_i,
    output logic                issue_ready_o,
    input  logic [TW-1:0]       issue_ticket_i,

    //=========================================================================
    // DFI read return (ISSUE order) -> the issue_q head's slot
    //=========================================================================
    input  logic                dfi_ret_valid_i,
    output logic                dfi_ret_ready_o,
    input  logic [DW-1:0]       dfi_ret_data_i,
    input  logic [1:0]          dfi_ret_resp_i,
    input  logic                dfi_ret_last_i,

    //=========================================================================
    // Drain (AR order = ring order), gated on the head's data being complete
    //=========================================================================
    output logic                drain_valid_o,
    input  logic                drain_ready_i,
    output logic [DW-1:0]       drain_data_o,
    output logic [1:0]          drain_resp_o,
    output logic                drain_last_o,

    output logic [OCW-1:0]      occ_o,             // allocated tickets (observability)
    output logic                busy_o
);

    // ---- ring state --------------------------------------------------------
    logic [TW-1:0]   r_head, r_tail;               // head = oldest allocated
    logic [OCW-1:0]  r_occ;                        // allocated, not yet freed
    logic            r_ready [DEPTH];              // slot data complete
    logic [1:0]      r_resp  [DEPTH];
    logic            r_shadow[DEPTH];              // allocated as a shadow, not yet fully fetched
    logic [TW-1:0]   r_src   [DEPTH];              // slot whose beats this one drains (itself unless a shadow)

    logic w_full, w_empty;
    assign w_full  = (r_occ == OCW'(DEPTH));
    assign w_empty = (r_occ == '0);

    // ---- allocate ----------------------------------------------------------
    // The tail slot is PINNED while an unfetched shadow still points at it:
    // the shadow reads the source's beats at fetch time, after the source has
    // drained and freed, so the slot must not be re-filled until then. No
    // deadlock: the shadow's fetch waits on its source's return (already
    // issued, or issuing from the CAM regardless of this port) and on the R
    // drain, neither of which waits on an allocation.
    logic w_alloc, w_tail_pinned;
    logic          r_mk_vld;                       // MERGE_MARK_REG: a shadow marking pending
    logic [TW-1:0] r_mk_ticket, r_mk_src;
    always_comb begin
        w_tail_pinned = 1'b0;
        for (int i = 0; i < DEPTH; i++)
            if (r_shadow[i] && (r_src[i] == r_tail)) w_tail_pinned = 1'b1;
    end
    assign alloc_ready_o  = !w_full && !w_tail_pinned;
    assign alloc_ticket_o = r_tail;
    assign w_alloc        = alloc_valid_i && alloc_ready_o;

    // ---- issue-order ticket FIFO (tickets awaiting their DFI return) -------
    // Sized DEPTH: a ticket is pushed at most once per allocation, so this can
    // never fill before the ring does; issue_ready_o is a safety net, and the
    // arbiter's rd_issue_ready gate honours it.
    logic          w_iq_wr_ready, w_iq_rd_valid, w_iq_rd_ready;
    logic [TW-1:0] w_iq_rd_ticket;
    assign issue_ready_o = w_iq_wr_ready;

    gaxi_fifo_sync #(.DATA_WIDTH(TW), .DEPTH(DEPTH)) u_issue_q (
        .axi_aclk   (aclk),
        .axi_aresetn(aresetn),
        .wr_valid   (issue_valid_i),
        .wr_ready   (w_iq_wr_ready),
        .wr_data    (issue_ticket_i),
        .rd_ready   (w_iq_rd_ready),
        .count      (),
        .rd_valid   (w_iq_rd_valid),
        .rd_data    (w_iq_rd_ticket)
    );

    // ---- return-fill: beats land in the issue_q head's slot ----------------
    // The slot was allocated at admit, so the fill never waits on storage: a
    // return beat is accepted whenever a ticket is at the issue_q head, which
    // is always the case while a read is in flight.
    logic [BCW-1:0] r_ret_beat;
    logic           w_ret_fire;
    assign dfi_ret_ready_o = w_iq_rd_valid;
    assign w_ret_fire      = dfi_ret_valid_i && dfi_ret_ready_o;
    assign w_iq_rd_ready   = w_ret_fire && dfi_ret_last_i;

    logic [31:0] w_ret_idx;
    assign w_ret_idx = 32'(w_iq_rd_ticket) * 32'(AXI_BEATS_PER_BURST) + 32'(r_ret_beat);

    // ---- drain: ring order, through the BRAM prefetch skid -----------------
    // A FETCH pointer (r_fptr) runs ahead of the head: it walks the allocated
    // slots in ring order and reads each slot's beats as soon as that slot is
    // complete, so the next slot prefetches while the current one's tail
    // drains (no per-slot bubble -- with one beat per slot on the board a
    // fetch-the-head-only scheme would cap the drain at a beat every 3
    // cycles). The HEAD pointer frees a slot when its last beat is CONSUMED.
    // fetch order == drain order == ring order, so the skid's carried
    // last/resp tags belong to the head being consumed.
    (* ram_style = "block" *)
    logic [DW-1:0]  r_mem [DEPTH*AXI_BEATS_PER_BURST];
    logic [DW-1:0]  r_rd_q;
    logic [TW-1:0]  r_fptr;                        // slot being fetched
    logic [BCW-1:0] r_fbeat;                       // next beat of that slot
    logic [OCW-1:0] r_focc;                        // allocated, not yet fully fetched

    localparam int SKID_DEPTH = 2;
    logic [DW-1:0] r_sk_data  [SKID_DEPTH];
    logic          r_sk_blast [SKID_DEPTH];
    logic [1:0]    r_sk_resp  [SKID_DEPTH];
    logic          r_sk_rd, r_sk_wr;
    logic [1:0]    r_sk_cnt;
    logic [1:0]    r_credits;                      // SKID_DEPTH - (in-flight + buffered)

    logic          r_if_valid, r_if_blast;
    logic [1:0]    r_if_resp;

    logic          w_hd_vld, w_hd_blast;
    logic [DW-1:0] w_hd_data;
    logic [1:0]    w_hd_resp;
    assign w_hd_vld   = (r_sk_cnt != 2'd0);
    assign w_hd_data  = r_sk_data [r_sk_rd];
    assign w_hd_blast = r_sk_blast[r_sk_rd];
    assign w_hd_resp  = r_sk_resp [r_sk_rd];

    logic w_dr_fire, w_room, w_fetch, w_fptr_ready;
    assign drain_valid_o = w_hd_vld;
    assign drain_data_o  = w_hd_data;
    assign drain_resp_o  = w_hd_resp;
    assign drain_last_o  = w_hd_blast;
    assign w_dr_fire     = drain_valid_o && drain_ready_i;

    assign w_fptr_ready = (r_focc != '0) && r_ready[r_fptr];
    assign w_room       = (r_credits != 2'd0) || w_dr_fire;
    assign w_fetch      = w_room && w_fptr_ready;

    // RET_BYPASS: the return beat IS the next fetch (exclusive with w_fetch:
    // a fetch needs the slot complete, a bypassed beat's slot is not yet).
    logic w_byp;
    assign w_byp = RET_BYPASS && w_ret_fire && (r_focc != '0) && (w_iq_rd_ticket == r_fptr)
                && (r_ret_beat == r_fbeat) && !r_shadow[r_fptr] && !r_ready[r_fptr]
                && !r_if_valid && w_room;

    // a shadow fetches its SOURCE's beats; any other slot fetches its own
    logic [TW-1:0] w_fsrc;
    assign w_fsrc = r_src[r_fptr];

    logic [31:0] w_dr_idx;
    assign w_dr_idx = 32'(w_fsrc) * 32'(AXI_BEATS_PER_BURST) + 32'(r_fbeat);

    // the head is FREED when its last beat is consumed by the drain
    logic w_free;
    assign w_free = w_dr_fire && w_hd_blast;

    assign occ_o  = r_occ;
    assign busy_o = !w_empty || w_iq_rd_valid || w_hd_vld || r_if_valid;

    // ---- sequential --------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_head <= '0; r_tail <= '0; r_occ <= '0;
            r_mk_vld <= 1'b0; r_mk_ticket <= '0; r_mk_src <= '0;
            r_ret_beat <= '0; r_fptr <= '0; r_fbeat <= '0; r_focc <= '0;
            r_sk_rd <= 1'b0; r_sk_wr <= 1'b0; r_sk_cnt <= 2'd0;
            r_credits <= 2'(SKID_DEPTH);
            r_if_valid <= 1'b0; r_if_blast <= 1'b0; r_if_resp <= 2'b00;
            for (int i = 0; i < DEPTH; i++) begin
                r_ready [i] <= 1'b0;
                r_resp  [i] <= 2'b00;
                r_shadow[i] <= 1'b0;
                r_src   [i] <= TW'(i);
            end
        end else begin
            // return-fill: mark the slot complete on the last beat, and every
            // shadow of it with it (a shadow is allocated before its source
            // issues, so it is registered long before this return)
            if (w_ret_fire) begin
                if (dfi_ret_last_i) begin
                    r_ready[w_iq_rd_ticket] <= 1'b1;
                    r_resp [w_iq_rd_ticket] <= dfi_ret_resp_i;
                    r_ret_beat <= '0;
                    for (int i = 0; i < DEPTH; i++)
                        if (r_shadow[i] && (r_src[i] == w_iq_rd_ticket)) r_ready[i] <= 1'b1;
                end else begin
                    r_ret_beat <= r_ret_beat + 1'b1;
                end
            end

            // allocate: claim the tail slot (its stale ready bit is cleared).
            // After the return-fill so the clear wins on the slot being
            // claimed; a freed slot is never a shadow (cleared at fetch).
            if (w_alloc) begin
                r_ready [r_tail] <= 1'b0;
                r_shadow[r_tail] <= MERGE_MARK_REG ? 1'b0 : alloc_merge_i;
                r_src   [r_tail] <= (!MERGE_MARK_REG && alloc_merge_i) ? alloc_src_i : r_tail;
                r_tail           <= r_tail + 1'b1;
            end
            // MERGE_MARK_REG: last cycle's merged allocation becomes a shadow
            // now; a return of its source in this very cycle readies it too.
            if (MERGE_MARK_REG && r_mk_vld) begin
                r_shadow[r_mk_ticket] <= 1'b1;
                r_src   [r_mk_ticket] <= r_mk_src;
                if (w_ret_fire && dfi_ret_last_i && (w_iq_rd_ticket == r_mk_src))
                    r_ready[r_mk_ticket] <= 1'b1;
            end
            r_mk_vld    <= MERGE_MARK_REG && w_alloc && alloc_merge_i;
            r_mk_ticket <= r_tail;
            r_mk_src    <= alloc_src_i;

            // fetch stage 1: issue the BRAM read of the fetch slot's next beat
            r_if_valid <= w_fetch;
            if (w_fetch || w_byp) begin
                r_if_blast <= (r_fbeat == BCW'(AXI_BEATS_PER_BURST - 1));
                r_if_resp  <= r_resp[w_fsrc];
                if (r_fbeat == BCW'(AXI_BEATS_PER_BURST - 1)) begin
                    r_fbeat <= '0;
                    r_fptr  <= r_fptr + 1'b1;      // slot fully fetched: next slot
                    r_shadow[r_fptr] <= 1'b0;      // a shadow releases its source's pin
                end else begin
                    r_fbeat <= r_fbeat + 1'b1;
                end
            end
            r_focc <= r_focc + (w_alloc ? OCW'(1) : OCW'(0))
                             - (((w_fetch || w_byp) && (r_fbeat == BCW'(AXI_BEATS_PER_BURST - 1))) ? OCW'(1) : OCW'(0));

            // fetch stage 2: the captured beat enters the skid tail
            // (RET_BYPASS: or the bypassed return beat, never in the same cycle)
            if (r_if_valid) begin
                r_sk_data [r_sk_wr] <= r_rd_q;
                r_sk_blast[r_sk_wr] <= r_if_blast;
                r_sk_resp [r_sk_wr] <= r_if_resp;
                r_sk_wr             <= r_sk_wr + 1'b1;
            end else if (w_byp) begin
                r_sk_data [r_sk_wr] <= dfi_ret_data_i;
                r_sk_blast[r_sk_wr] <= (r_fbeat == BCW'(AXI_BEATS_PER_BURST - 1));
                r_sk_resp [r_sk_wr] <= dfi_ret_resp_i;
                r_sk_wr             <= r_sk_wr + 1'b1;
            end
            if (w_dr_fire) r_sk_rd <= r_sk_rd + 1'b1;
            r_sk_cnt  <= r_sk_cnt  + ((r_if_valid || w_byp) ? 2'd1 : 2'd0) - (w_dr_fire ? 2'd1 : 2'd0);
            r_credits <= r_credits - ((w_fetch || w_byp) ? 2'd1 : 2'd0) + (w_dr_fire ? 2'd1 : 2'd0);

            // free the head when its last beat is consumed
            if (w_free) r_head <= r_head + 1'b1;

            r_occ <= r_occ + (w_alloc ? OCW'(1) : OCW'(0)) - (w_free ? OCW'(1) : OCW'(0));
        end
    )

    // -------------------------------------------------------------------------
    // Data storage: reset-free clocked process so Vivado maps it to Block RAM.
    // READ LATENCY IS EXACTLY 1 CYCLE and the fetch pipeline depends on it
    // (r_if_* pairs with r_rd_q the cycle after w_fetch). See mc_rd_cmd_cam
    // for the full note.
    // -------------------------------------------------------------------------
    always_ff @(posedge aclk) begin
        if (w_ret_fire) r_mem[w_ret_idx] <= dfi_ret_data_i;
        if (w_fetch)    r_rd_q           <= r_mem[w_dr_idx];
    end

`ifndef SYNTHESIS
    // A return beat with no ticket at the issue_q head means a read reached
    // the DFI that the ring never saw issued -- a lost ticket, and every later
    // read would fill the wrong slot. Also: a ticket must never be issued for
    // a slot that is not allocated.
    always @(posedge aclk)
        if (aresetn) begin
            assert (!(dfi_ret_valid_i && !w_iq_rd_valid))
              else $error("RD_RING @%0t: DFI return beat with NO ticket in flight", $time);
            assert (!(issue_valid_i && w_empty))
              else $error("RD_RING @%0t: issue of ticket %0d with the ring EMPTY", $time, issue_ticket_i);
            // a shadow's source must be an allocated, unreturned, non-shadow
            // slot: anything else never makes the shadow ready
            assert (!(w_alloc && alloc_merge_i
                      && (r_shadow[alloc_src_i] || r_ready[alloc_src_i]
                          || (OCW'(TW'(alloc_src_i - r_head)) >= r_occ))))
              else $error("RD_RING @%0t: shadow of ticket %0d which is not a live source", $time, alloc_src_i);
        end
`endif

endmodule : mc_rd_return_ring
