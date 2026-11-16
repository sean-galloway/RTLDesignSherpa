// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_prime_fill
// Purpose:
//   Multi-outstanding AXI4 read-master fill engine for jet-prime (TASK-001
//   step 2).  Replaces the shared single-outstanding l1_fill in the jet
//   coherence core: every MSHR entry owns one AXI4 read ID (ARID = entry
//   index; the single CLEAN_UNIQUE upgrade owns the slot after the last
//   entry), so several line fetches are in flight on the memory port at
//   once and their R bursts return in whatever order the memory side
//   chooses.  The engine demuxes R by ID back to the launching entry and
//   presents each beat with the entry's claimed {set, way} so the plane's
//   data-array W-port mux needs no in-flight record of its own.
//
// Documentation: projects/components/cache-ip/jet-prime-mesi-l1/docs/delta/01_fill_engine.md
// Subsystem: jet-prime (TASK-001 step 2, 2026-11-15)
//
// Author: sean galloway
// Created: 2026-11-15

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: jet_prime_fill
//==============================================================================
// Description:
//   Launch side (jet_prime_control's start-held-until-accept contract):
//     fill_accept_o = fill_start_i & AR register free & inflight room &
//                     the launch's slot is free.
//     The AR register is free when it is empty or drains this cycle
//     (fub_axi_arready), so launches can be accepted back to back at one
//     per cycle while the transport takes ARs.  FILL_INFLIGHT caps the
//     number of accepted-not-done fills: at 1 the engine is the old
//     single-outstanding l1_fill (the pair rig keeps it there until the
//     fabric is rebuilt in step 3); at MSHR_COUNT+1 every entry and the
//     upgrade can be in flight together.  The plane gates fill_start_i
//     with the capture contract (no launch while a victim capture streams
//     or opens -- the entry's own beats must not land before its victim
//     is captured); the engine itself has no view of the data array.
//
//   AR side: one registered AR at a time (arvalid held until arready, the
//     AXI rule).  ARID = slot (zero-extended), ARLEN = FILL_BEATS-1 for a
//     data fill and 0 for the no-data CLEAN_UNIQUE, ARSIZE = the bus,
//     INCR, the l1_pkg cacheable ARCACHE.
//
//   R side: every accepted R beat enters a DEPTH-4 staging queue
//     ({slot, data, PassDirty, last}; fub_axi_rready is the queue's
//     wr_ready, DECISION D-6: rready never drops on consumer-side stalls,
//     only at a genuinely full queue).  The queue's read side is presented
//     unconditionally: the beat consumer (data-array W port) is
//     always-ready for fill beats (the MAS fill > commit > hit rule), so
//     the queue drains one beat per cycle and a slow burst never blocks
//     another slot's beats for more than the queue depth.  Beats of
//     different IDs may interleave (AXI4 permits it); each slot keeps its
//     own beat counter, so the beat number presented is always the slot's
//     own position in its burst.
//
//   Completion: fill_done_o pulses in the cycle the slot's LAST beat is
//     presented (the same alignment as l1_fill's F_DONE: one cycle after
//     the RLAST acceptance into the queue), carrying the slot's entry
//     index, class and the PassDirty accumulated across its burst.  A
//     CLEAN_UNIQUE completes on its single RLAST beat with no beat
//     presented.  jet_prime_control queues completions in done order
//     (its done queue replaced the launch-order completion queue).
//
//   Storage: SLOTS x {valid, set, way, beat counter, pd, ru}, one AR
//   register, the staging queue, an in-flight counter.  No FSM: the AR
//   register and the per-slot counters are the whole state.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / WAYS / LINE_BYTES / BUS_WIDTH:
//     geometry per l1_pkg defaults (shared with the arrays)
//   MSHR_COUNT:
//     J1 geometry; SLOTS = MSHR_COUNT + 1 (the upgrade's no-data slot)
//   FILL_INFLIGHT:
//     maximum accepted-not-done fills, 1..SLOTS (default SLOTS)
//   AXI_ID_WIDTH / AXI_USER_WIDTH:
//     fub_axi id/user widths; 2**AXI_ID_WIDTH must cover SLOTS
//
//------------------------------------------------------------------------------
// Notes:
//   - RRESP[1:0] is accepted but not acted on (the rig memory is always
//     OKAY, as l1_fill); RRESP[2] (PassDirty) accumulates per slot.
//   - The staging queue carries the slot from RID's low bits; an RID
//     outside SLOTS is a transport fault (simulation-checked).
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: jet_prime_coh_core
//   - Launches from: jet_prime_control (fill_* seam)
//   - Transport: axi4_master_rd_monlite via l1_axi4_plane / l1_ace_plane
//   - Queue: gaxi_fifo_sync (house)
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/jet-prime-mesi-l1/dv/tests/test_jet_prime_fill.py
//   Plan: dv/testplans/jet_prime_fill_testplan.yaml
//   Run: pytest projects/components/cache-ip/jet-prime-mesi-l1/dv/tests/test_jet_prime_fill.py -v
//
//==============================================================================

module jet_prime_fill
    import jet_prime_pkg::*;
    import l1_pkg::*;
#(
    parameter int ADDR_WIDTH     = AMBER_ADDR_WIDTH,
    parameter int SETS           = AMBER_SETS,
    parameter int WAYS           = AMBER_WAYS,
    parameter int LINE_BYTES     = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH      = AMBER_BUS_WIDTH,
    parameter int MSHR_COUNT     = jet_prime_pkg::MSHR_COUNT,
    parameter int FILL_INFLIGHT  = MSHR_COUNT + 1,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    localparam int SET_W      = $clog2(SETS),
    localparam int WAY_W      = $clog2(WAYS),
    localparam int STRB_W     = BUS_WIDTH / 8,
    localparam int FILL_BEATS = LINE_BYTES / STRB_W,
    localparam int BEAT_W     = $clog2(FILL_BEATS),
    localparam int MW         = $clog2(MSHR_COUNT),
    localparam int SLOTS      = MSHR_COUNT + 1,
    localparam int SLOT_W     = $clog2(SLOTS),
    localparam int IW         = AXI_ID_WIDTH,
    localparam int UW         = AXI_USER_WIDTH
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // launch seam (jet_prime_control; start held until accept)
    input  logic                        fill_start_i,
    input  logic [ADDR_WIDTH-1:0]       fill_addr_i,
    input  logic [1:0]                  fill_cls_i,      // jet_prime_fill_class_t
    input  logic [MW-1:0]               fill_idx_i,      // MSHR entry (ignored for CU)
    input  logic [SET_W-1:0]            fill_set_i,      // claimed set/way the beats land in
    input  logic [WAY_W-1:0]            fill_way_i,
    output logic                        fill_accept_o,

    // beat stream (consumer always-ready)
    output logic                        fill_beat_valid_o,
    output logic [MW-1:0]               fill_beat_idx_o,
    output logic [BEAT_W-1:0]           fill_beat_num_o,
    output logic [SET_W-1:0]            fill_beat_set_o,
    output logic [WAY_W-1:0]            fill_beat_way_o,
    output logic [BUS_WIDTH-1:0]        fill_beat_data_o,

    // completion (with the last beat; CU with its single no-data beat)
    output logic                        fill_done_o,
    output logic [MW-1:0]               fill_done_idx_o,
    output logic [1:0]                  fill_done_cls_o,
    output logic                        fill_done_pd_o,

    // any launch accepted and not yet done, or an AR awaiting the transport
    output logic                        fill_busy_o,

    // fub_axi upstream side of axi4_master_rd (DECISION D3)
    output logic [IW-1:0]               fub_axi_arid,
    output logic [ADDR_WIDTH-1:0]       fub_axi_araddr,
    output logic [7:0]                  fub_axi_arlen,
    output logic [2:0]                  fub_axi_arsize,
    output logic [1:0]                  fub_axi_arburst,
    output logic                        fub_axi_arlock,
    output logic [3:0]                  fub_axi_arcache,
    output logic [2:0]                  fub_axi_arprot,
    output logic [3:0]                  fub_axi_arqos,
    output logic [3:0]                  fub_axi_arregion,
    output logic [UW-1:0]               fub_axi_aruser,
    output logic                        fub_axi_arvalid,
    input  logic                        fub_axi_arready,
    input  logic [IW-1:0]               fub_axi_rid,
    input  logic [BUS_WIDTH-1:0]        fub_axi_rdata,
    input  logic [3:0]                  fub_axi_rresp,
    input  logic                        fub_axi_rlast,
    input  logic [UW-1:0]               fub_axi_ruser,
    input  logic                        fub_axi_rvalid,
    output logic                        fub_axi_rready
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("jet_prime_fill: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("jet_prime_fill: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0 || FILL_BEATS < 2)
            $error("jet_prime_fill: LINE_BYTES / BUS_WIDTH*8 must be a power of two >= 2");
        if ((BUS_WIDTH % 8) != 0)
            $error("jet_prime_fill: BUS_WIDTH must be a multiple of 8");
        if (MSHR_COUNT < 2 || MSHR_COUNT > 16)
            $error("jet_prime_fill: MSHR_COUNT must be 2..16");
        if (FILL_INFLIGHT < 1 || FILL_INFLIGHT > SLOTS)
            $error("jet_prime_fill: FILL_INFLIGHT must be 1..MSHR_COUNT+1");
        if ((1 << IW) < SLOTS)
            $error("jet_prime_fill: AXI_ID_WIDTH must cover MSHR_COUNT+1 read IDs");
    end

    localparam logic [SLOT_W-1:0] CU_SLOT = SLOT_W'(SLOTS - 1);

    // ------------------------------------------------------------------
    // Per-slot flight records
    // ------------------------------------------------------------------
    logic [SLOTS-1:0]        r_slot_vld;
    logic [SET_W-1:0]        r_slot_set  [SLOTS];
    logic [WAY_W-1:0]        r_slot_way  [SLOTS];
    logic [BEAT_W-1:0]       r_slot_cnt  [SLOTS];
    logic [SLOTS-1:0]        r_slot_pd;
    logic [SLOTS-1:0]        r_slot_ru;
    logic [SLOT_W:0]         r_inflight;

    // the AR register (one AR awaiting the transport)
    logic                    r_ar_vld;
    logic [ADDR_WIDTH-1:0]   r_ar_addr;
    logic [SLOT_W-1:0]       r_ar_slot;
    logic                    r_ar_nodata;

    // ------------------------------------------------------------------
    // Launch accept
    // ------------------------------------------------------------------
    logic                    w_launch_cu;
    logic [SLOT_W-1:0]       w_launch_slot;
    logic                    w_ar_free;
    logic                    w_ar_fire;

    assign w_launch_cu   = (fill_cls_i == JET_CLS_CU);
    assign w_launch_slot = w_launch_cu ? CU_SLOT : SLOT_W'(fill_idx_i);
    assign w_ar_fire     = fub_axi_arvalid & fub_axi_arready;
    assign w_ar_free     = ~r_ar_vld | w_ar_fire;

    assign fill_accept_o = fill_start_i & w_ar_free
                           & (r_inflight < (SLOT_W+1)'(FILL_INFLIGHT))
                           & ~r_slot_vld[w_launch_slot];

    // ------------------------------------------------------------------
    // R-beat staging queue (DECISION D-6): {slot, data, pd, last}
    // ------------------------------------------------------------------
    localparam int STG_W = SLOT_W + BUS_WIDTH + 2;

    logic                    stg_wr_ready;
    logic                    stg_rd_valid;
    logic [STG_W-1:0]        stg_rd_data;
    logic [SLOT_W-1:0]       w_rid_slot;
    logic [SLOT_W-1:0]       w_pop_slot;
    logic [BUS_WIDTH-1:0]    w_pop_data;
    logic                    w_pop_pd;
    logic                    w_pop_last;
    logic                    w_pop_cu;

    assign w_rid_slot = fub_axi_rid[SLOT_W-1:0];

    gaxi_fifo_sync #(
        .DATA_WIDTH (STG_W),
        .DEPTH      (4)
    ) u_stage (
        .axi_aclk    (clk),
        .axi_aresetn (rst_n),
        .wr_valid    (fub_axi_rvalid),
        .wr_ready    (stg_wr_ready),
        .wr_data     ({w_rid_slot, fub_axi_rdata, fub_axi_rresp[2], fub_axi_rlast}),
        .rd_ready    (1'b1),           // the beat consumer is always-ready
        .count       (),
        .rd_valid    (stg_rd_valid),
        .rd_data     (stg_rd_data)
    );

    assign fub_axi_rready = stg_wr_ready;

    assign {w_pop_slot, w_pop_data, w_pop_pd, w_pop_last} = stg_rd_data;
    assign w_pop_cu = (w_pop_slot == CU_SLOT);

    // ------------------------------------------------------------------
    // Beat presentation + completion (combinational on the queue head)
    // ------------------------------------------------------------------
    assign fill_beat_valid_o = stg_rd_valid & ~w_pop_cu;
    assign fill_beat_idx_o   = MW'(w_pop_slot);
    assign fill_beat_num_o   = r_slot_cnt[w_pop_slot];
    assign fill_beat_set_o   = r_slot_set[w_pop_slot];
    assign fill_beat_way_o   = r_slot_way[w_pop_slot];
    assign fill_beat_data_o  = w_pop_data;

    assign fill_done_o       = stg_rd_valid & w_pop_last;
    assign fill_done_idx_o   = MW'(w_pop_slot);
    assign fill_done_cls_o   = w_pop_cu            ? JET_CLS_CU
                               : r_slot_ru[w_pop_slot] ? JET_CLS_RU
                               :                     JET_CLS_RNSD;
    assign fill_done_pd_o    = r_slot_pd[w_pop_slot] | w_pop_pd;

    assign fill_busy_o       = r_ar_vld | (r_inflight != '0);

    // RRESP[1:0]/[3] and RUSER are accepted, not acted on (the memory side
    // is always OKAY; errors are a rig-integration concern, as l1_fill)
    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_r_fields;
    assign unused_r_fields = &{1'b0, fub_axi_rresp[3], fub_axi_rresp[1:0], fub_axi_ruser};
    /* verilator lint_on UNUSEDSIGNAL */

    // ------------------------------------------------------------------
    // AR channel
    // ------------------------------------------------------------------
    assign fub_axi_arid     = IW'(r_ar_slot);
    assign fub_axi_araddr   = r_ar_addr;
    assign fub_axi_arlen    = r_ar_nodata ? 8'h0 : 8'(FILL_BEATS - 1);
    assign fub_axi_arsize   = 3'($clog2(STRB_W));
    assign fub_axi_arburst  = 2'b01;             // INCR
    assign fub_axi_arlock   = 1'b0;
    assign fub_axi_arcache  = AMBER_ACE_AX_CACHE;
    assign fub_axi_arprot   = 3'b0;
    assign fub_axi_arqos    = 4'b0;
    assign fub_axi_arregion = 4'b0;
    assign fub_axi_aruser   = '0;
    assign fub_axi_arvalid  = r_ar_vld;

    // ------------------------------------------------------------------
    // Sequential state
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_slot_vld  <= '0;
            r_slot_pd   <= '0;
            r_slot_ru   <= '0;
            r_inflight  <= '0;
            r_ar_vld    <= 1'b0;
            r_ar_addr   <= '0;
            r_ar_slot   <= '0;
            r_ar_nodata <= 1'b0;
            for (int s = 0; s < SLOTS; s++) begin
                r_slot_set[s] <= '0;
                r_slot_way[s] <= '0;
                r_slot_cnt[s] <= '0;
            end
        end else begin
            // the AR register: loaded by an accept (which may coincide with
            // the previous AR's handshake), emptied by the handshake
            if (fill_accept_o) begin
                r_ar_vld    <= 1'b1;
                r_ar_addr   <= fill_addr_i;
                r_ar_slot   <= w_launch_slot;
                r_ar_nodata <= w_launch_cu;
            end else if (w_ar_fire) begin
                r_ar_vld <= 1'b0;
            end
            // slot open at the accept
            if (fill_accept_o) begin
                r_slot_vld[w_launch_slot] <= 1'b1;
                r_slot_set[w_launch_slot] <= fill_set_i;
                r_slot_way[w_launch_slot] <= fill_way_i;
                r_slot_cnt[w_launch_slot] <= '0;
                r_slot_pd[w_launch_slot]  <= 1'b0;
                r_slot_ru[w_launch_slot]  <= (fill_cls_i == JET_CLS_RU);
            end
            // beat bookkeeping + slot close at the last beat (an accept and
            // a done never target the same slot: a slot is relaunched only
            // after its entry retires)
            if (stg_rd_valid) begin
                r_slot_cnt[w_pop_slot] <= r_slot_cnt[w_pop_slot] + 1'b1;
                r_slot_pd[w_pop_slot]  <= r_slot_pd[w_pop_slot] | w_pop_pd;
                if (w_pop_last) begin
                    r_slot_vld[w_pop_slot] <= 1'b0;
                end
            end
            case ({fill_accept_o, fill_done_o})
                2'b10:   r_inflight <= r_inflight + 1'b1;
                2'b01:   r_inflight <= r_inflight - 1'b1;
                default: ;  // 00: no event; 11: net hold
            endcase
        end
    )

    // ------------------------------------------------------------------
    // Simulation-only contract checks
    // ------------------------------------------------------------------
    // pragma translate_off
    // Every R beat belongs to a slot in flight.
    assert property (@(posedge clk) disable iff (!rst_n)
        ((fub_axi_rvalid & fub_axi_rready)
         |-> ((fub_axi_rid < IW'(SLOTS)) & r_slot_vld[w_rid_slot])))
        else $error("jet_prime_fill: R beat for a slot not in flight (rid=%0d)", fub_axi_rid);

    // A no-data CLEAN_UNIQUE answers with exactly one beat.
    assert property (@(posedge clk) disable iff (!rst_n)
        ((fub_axi_rvalid & fub_axi_rready & (w_rid_slot == CU_SLOT))
         |-> fub_axi_rlast))
        else $error("jet_prime_fill: multi-beat response on the no-data upgrade slot");

    // A data fill's last beat is its FILL_BEATS-th.
    assert property (@(posedge clk) disable iff (!rst_n)
        ((fill_done_o & ~w_pop_cu)
         |-> (r_slot_cnt[w_pop_slot] == BEAT_W'(FILL_BEATS - 1))))
        else $error("jet_prime_fill: RLAST before the line's last beat");

    // The in-flight count never exceeds the cap.
    assert property (@(posedge clk) disable iff (!rst_n)
        (r_inflight <= (SLOT_W+1)'(FILL_INFLIGHT)))
        else $error("jet_prime_fill: in-flight count over FILL_INFLIGHT");

    // A launch never targets a slot already in flight.
    assert property (@(posedge clk) disable iff (!rst_n)
        (fill_start_i |-> ~r_slot_vld[w_launch_slot]))
        else $error("jet_prime_fill: launch for a slot already in flight");
    // pragma translate_on

endmodule : jet_prime_fill
