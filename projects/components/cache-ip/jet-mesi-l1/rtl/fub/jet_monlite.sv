// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_monlite
// Purpose:
//   Drop-and-count MonBus observer for the jet MESI L1 J7 metrics (MAS
//   ch04).  Taps the jet control/MSHR/WB event signals and emits one
//   128-bit house-format MonBus packet per J7 event class.  The observer
//   drives nothing in the measured path -- a packet the monbus will not
//   take is dropped and counted, never backpressured.
//
// Documentation: projects/components/cache-ip/jet-mesi-l1/docs/jet_mas/ch04_monbus_observation/01_event_map.md
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-29

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: jet_monlite
//==============================================================================
// Description:
//   Event classes (MAS ch04 jet extension):
//     MSHR_ALLOC    one-cycle pulse when jet_mshr grants an alloc
//     MSHR_MERGE    one-cycle pulse when jet_mshr appends a merge
//     MSHR_RETIRE   one-cycle pulse when jet_mshr retires an entry
//     MSHR_OCCUPANCY gauge sample on every occupancy change
//     WB_OCCUPANCY  gauge sample on every WB occupancy change
//     STALL_TAG_FULL tag-full stall release (duration measured)
//
//   Payload packing (right-aligned fields):
//     MSHR_ALLOC    [15:0] set | [17:16] fill class | [23:18] occupancy-after
//     MSHR_MERGE    [MW-1:0] entry index | [MW+7:MW] merge depth |
//                   [39:24] entry age (cycles since alloc)
//     MSHR_RETIRE   [MW-1:0] entry index | [23:16] occupancy-before |
//                   [39:24] fill latency (alloc cycle -> retire cycle)
//     MSHR_OCCUPANCY [7:0] occupancy count
//     WB_OCCUPANCY  [7:0] occupancy count
//     STALL_TAG_FULL [7:0] stall class code (5) | [15:8] stall duration
//
//   Drop-and-count: same STREAM monitor-lite idiom as l1_monlite -- an
//   8-bit saturating counter accumulates drops; when non-zero and the
//   queue has drained with no live candidate, the count is re-emitted as
//   PktTypeError/AMBER_EV_DROPPED.  Up to two candidates may fire per
//   cycle; a one-entry deferral register serializes the second write into
//   the next cycle, preserving stream order.
//
//   USE_MONITOR=0 ties the observer off (house gen_no_monitor idiom): the
//   "absent" half of the present-vs-absent measurement-integrity pin.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   MSHR_COUNT / SETS / WAYS:
//     Description: geometry, forwarded from jet_top
//     Type: int
//   AGENT_ID / UNIT_ID:
//     Description: designer-allocated house monitor ids
//     Type: logic
//   DROP_CODE:
//     Description: event_code of the drop-report packet (shared amber
//       constant; l1_monlite uses the same value)
//     Type: logic [7:0]
//   USE_MONITOR:
//     Description: 0 = tie monbus outputs off, count held at zero
//     Type: bit
//   OUT_DEPTH:
//     Description: monbus output queue depth, a power of two >= 2
//     Type: int
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: jet_top (MonBus arbiter client 3)
//   - Queue: gaxi_fifo_sync (house shared storage primitive)
//   - Package: ocelus_common_pkg, jet_pkg, l1_pkg
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/jet-mesi-l1/dv/tests/test_jet_monlite.py
//   Run: pytest projects/components/cache-ip/jet-mesi-l1/dv/tests/test_jet_monlite.py -v
//
//==============================================================================

module jet_monlite
    import jet_pkg::*;
    import l1_pkg::*;
    import ocelus_common_pkg::*;
#(
    parameter int MSHR_COUNT  = jet_pkg::MSHR_COUNT,
    parameter int SETS        = AMBER_SETS,
    parameter int WAYS        = AMBER_WAYS,
    parameter logic [15:0] AGENT_ID   = 16'h00A2,
    parameter logic [7:0]  UNIT_ID    = 8'h01,
    parameter logic [7:0]  DROP_CODE  = 8'(AMBER_EV_DROPPED),
    parameter bit          USE_MONITOR = 1'b1,
    parameter int          OUT_DEPTH   = 4,
    localparam int SET_W      = $clog2(SETS),
    localparam int WAY_W      = $clog2(WAYS),
    localparam int MW         = $clog2(MSHR_COUNT),
    localparam int OCC_W      = MW + 1
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // ---- MSHR event taps ----
    input  logic                        mshr_alloc_i,
    input  logic [SET_W-1:0]            mshr_alloc_set_i,
    input  logic [1:0]                  mshr_alloc_cls_i,
    input  logic [MW-1:0]               mshr_alloc_idx_i,
    input  logic                        mshr_merge_i,
    input  logic [MW-1:0]               mshr_merge_idx_i,
    input  logic [MW:0]                 mshr_merge_depth_i,
    input  logic                        mshr_retire_i,
    input  logic [MW-1:0]               mshr_retire_idx_i,
    input  logic [OCC_W-1:0]            mshr_occupancy_i,

    // ---- WB event taps ----
    input  logic [$clog2(jet_pkg::VICTIM_DEPTH + 1)-1:0] wb_occupancy_i,

    // ---- control stall taps ----
    input  logic                        ctrl_stall_i,
    input  logic [2:0]                  ctrl_stall_reason_i,

    // ---- side-band timestamp ----
    input  monbus_timestamp_t           i_mon_time,

    // ---- monitor bus ----
    output logic                        monbus_valid,
    input  logic                        monbus_ready,
    output monitor_packet_t             monbus_packet,
    output monbus_timestamp_t           monbus_timestamp,

    // ---- status ----
    output logic [7:0]                  dropped_count
);

    // ------------------------------------------------------------------
    // Elaboration-time checks
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("jet_monlite: SETS must be a power of two");
        if ((OUT_DEPTH & (OUT_DEPTH - 1)) != 0 || OUT_DEPTH < 2)
            $error("jet_monlite: OUT_DEPTH must be a power of two >= 2");
    end

    // ------------------------------------------------------------------
    // Per-entry alloc-cycle tracking (for retire latency + merge age)
    // ------------------------------------------------------------------
    monbus_timestamp_t r_alloc_cyc [MSHR_COUNT];

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int e = 0; e < MSHR_COUNT; e++) begin
                r_alloc_cyc[e] <= '0;
            end
        end else begin
            if (mshr_alloc_i) begin
                r_alloc_cyc[mshr_alloc_idx_i] <= i_mon_time;
            end
        end
    )

    // ------------------------------------------------------------------
    // Stall tracking: measure contiguous stall duration, emit on release.
    // Only the tag-full class (STALL_TAG_FULL) is instrumented for J7.
    // ------------------------------------------------------------------
    localparam logic [2:0] STALL_TAG_FULL = 3'd5;

    logic        r_stall_active;
    logic [7:0]  r_stall_dur;
    logic [2:0]  r_stall_class;
    wire         w_tag_full_now = ctrl_stall_i
                                  & (ctrl_stall_reason_i == STALL_TAG_FULL);
    wire         w_stall_start  = w_tag_full_now & ~r_stall_active;
    wire         w_stall_release= ~w_tag_full_now & r_stall_active
                                  & (r_stall_class == STALL_TAG_FULL);
    wire         w_stall_class_change = w_tag_full_now & r_stall_active
                                        & (r_stall_class != STALL_TAG_FULL);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_stall_active <= 1'b0;
            r_stall_dur    <= 8'd0;
            r_stall_class  <= STALL_TAG_FULL;
        end else begin
            if (w_stall_release || w_stall_class_change) begin
                // emit on release (or on class change: close the old one)
                r_stall_active <= w_stall_class_change;
                r_stall_dur    <= 8'd0;
                r_stall_class  <= ctrl_stall_reason_i;
            end else if (w_tag_full_now) begin
                r_stall_active <= 1'b1;
                r_stall_class  <= STALL_TAG_FULL;
                if (r_stall_dur < 8'hFF) begin
                    r_stall_dur <= r_stall_dur + 1'b1;
                end
            end else begin
                r_stall_active <= 1'b0;
                r_stall_dur    <= 8'd0;
            end
        end
    )

    // ------------------------------------------------------------------
    // Occupancy gauge change detection
    // ------------------------------------------------------------------
    logic [OCC_W-1:0] r_mshr_occ_q;
    logic [$clog2(jet_pkg::VICTIM_DEPTH + 1)-1:0] r_wb_occ_q;
    wire              w_mshr_occ_fire = (mshr_occupancy_i != r_mshr_occ_q);
    wire              w_wb_occ_fire   = (wb_occupancy_i != r_wb_occ_q);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_mshr_occ_q <= '0;
            r_wb_occ_q   <= '0;
        end else begin
            r_mshr_occ_q <= mshr_occupancy_i;
            r_wb_occ_q   <= wb_occupancy_i;
        end
    )

    // ------------------------------------------------------------------
    // Candidate events: {ptype, code, data}, priority-ordered.  At most
    // three could fire (alloc+merge+retire are independent inputs), but
    // the queue engine below takes the top two and drops the rest.
    // Priority: RETIRE > MERGE > ALLOC > STALL > MSHR_OCC > WB_OCC.
    // ------------------------------------------------------------------
    localparam int N_CAND = 6;
    // priority index: 0 RETIRE, 1 MERGE, 2 ALLOC, 3 STALL, 4 MSHR_OCC, 5 WB_OCC

    logic [3:0]  c_ptype   [N_CAND];
    logic [7:0]  c_code    [N_CAND];
    logic [63:0] c_data    [N_CAND];
    logic        c_fire    [N_CAND];

    // Occupancy sampled at the event edge is the PRE-UPDATE value.  An alloc
    // increments occupancy, so occupancy-after = mshr_occupancy_i + 1.
    wire [63:0] w_alloc_data =
        64'(mshr_alloc_set_i)
        | (64'(mshr_alloc_cls_i) << 16)
        | (64'(mshr_occupancy_i + OCC_W'(1)) << 18);

    wire [63:0] w_merge_data =
        64'(mshr_merge_idx_i)
        | (64'(mshr_merge_depth_i) << MW)
        | ((mshr_merge_i ? (i_mon_time - r_alloc_cyc[mshr_merge_idx_i]) : 64'd0)
           << (MW + 8));

    // Occupancy sampled at the event edge is the PRE-UPDATE value.  A retire
    // decrements occupancy, so occupancy-before = mshr_occupancy_i.
    wire [63:0] w_retire_data =
        64'(mshr_retire_idx_i)
        | (64'(mshr_occupancy_i) << 16)
        | ((mshr_retire_i ? (i_mon_time - r_alloc_cyc[mshr_retire_idx_i]) : 64'd0)
           << 24);

    wire [63:0] w_stall_data =
        64'(STALL_TAG_FULL)
        | (64'(r_stall_dur) << 8);

    wire [63:0] w_mshr_occ_data = 64'(mshr_occupancy_i);
    wire [63:0] w_wb_occ_data   = 64'(wb_occupancy_i);

    always_comb begin
        for (int i = 0; i < N_CAND; i++) begin
            c_ptype[i] = PktTypePerf;
            c_code[i]  = 8'h00;
            c_data[i]  = '0;
            c_fire[i]  = 1'b0;
        end
        // 0: RETIRE
        c_code[0] = 8'(JET_EV_MSHR_RETIRE);
        c_data[0] = w_retire_data;
        c_fire[0] = mshr_retire_i;
        // 1: MERGE
        c_code[1] = 8'(JET_EV_MSHR_MERGE);
        c_data[1] = w_merge_data;
        c_fire[1] = mshr_merge_i;
        // 2: ALLOC
        c_code[2] = 8'(JET_EV_MSHR_ALLOC);
        c_data[2] = w_alloc_data;
        c_fire[2] = mshr_alloc_i;
        // 3: STALL release
        c_code[3] = 8'(JET_EV_STALL_TAG_FULL);
        c_data[3] = w_stall_data;
        c_fire[3] = w_stall_release;
        // 4: MSHR occupancy gauge
        c_code[4] = 8'(JET_EV_MSHR_OCCUPANCY);
        c_data[4] = w_mshr_occ_data;
        c_fire[4] = w_mshr_occ_fire;
        // 5: WB occupancy gauge
        c_code[5] = 8'(JET_EV_WB_OCCUPANCY);
        c_data[5] = w_wb_occ_data;
        c_fire[5] = w_wb_occ_fire;
    end

    wire [3:0] w_fire_n = 4'(
          4'(c_fire[0]) + 4'(c_fire[1]) + 4'(c_fire[2])
        + 4'(c_fire[3]) + 4'(c_fire[4]) + 4'(c_fire[5]));

    // ------------------------------------------------------------------
    // Output queue (gaxi_fifo_sync, same idiom as l1_monlite)
    // ------------------------------------------------------------------
    localparam int QW  = MONBUS_PKT_WIDTH + MONBUS_TS_WIDTH;
    localparam int OQW = (OUT_DEPTH > 1) ? $clog2(OUT_DEPTH) : 1;

    logic                       r_pend_q;
    monitor_packet_t            r_pend_pkt;
    monbus_timestamp_t          r_pend_ts;

    logic [QW-1:0]              fifo_wdata;
    logic                       fifo_wr_valid, fifo_wr_ready;
    logic [QW-1:0]              fifo_rdata;
    logic                       fifo_rd_valid, fifo_rd_ready;
    logic [$clog2(OUT_DEPTH):0] fifo_count;

    gaxi_fifo_sync #(
        .DATA_WIDTH (QW),
        .DEPTH      (OUT_DEPTH)
    ) u_out_q (
        .axi_aclk    (clk),
        .axi_aresetn (rst_n),
        .wr_valid    (fifo_wr_valid),
        .wr_ready    (fifo_wr_ready),
        .wr_data     (fifo_wdata),
        .rd_ready    (fifo_rd_ready),
        .count       (fifo_count),
        .rd_valid    (fifo_rd_valid),
        .rd_data     (fifo_rdata)
    );

    // first/second priority candidates (high-priority-first)
    logic [$clog2(N_CAND)-1:0] w_p1_idx, w_p2_idx;
    logic        w_fire1, w_fire2;

    always_comb begin
        w_p1_idx = '0;
        w_fire1  = 1'b0;
        w_p2_idx = '0;
        w_fire2  = 1'b0;
        // walk high-priority-first (index 0 is highest); p1 = first hit,
        // p2 = second hit
        for (int i = 0; i < N_CAND; i++) begin
            if (c_fire[i]) begin
                if (!w_fire1) begin
                    w_p1_idx = $clog2(N_CAND)'(i);
                    w_fire1  = 1'b1;
                end else if (!w_fire2) begin
                    w_p2_idx = $clog2(N_CAND)'(i);
                    w_fire2  = 1'b1;
                end
            end
        end
    end

    // ------------------------------------------------------------------
    // Drop accounting (identical STREAM idiom to l1_monlite)
    // ------------------------------------------------------------------
    logic [OQW:0] r_eff_q;
    wire [OQW:0] w_eff_cnt  = r_eff_q;
    wire         w_q_empty  = (w_eff_cnt == '0);
    wire         w_room1    = (w_eff_cnt + (OQW+1)'(r_pend_q))
                              <= (OQW+1)'(OUT_DEPTH - 1);
    wire         w_room2    = (w_eff_cnt <= (OQW+1)'(OUT_DEPTH - 2));

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_eff_q <= '0;
        end else begin
            r_eff_q <= r_eff_q + (OQW+1)'(fifo_wr_valid)
                       - (OQW+1)'(fifo_rd_valid && fifo_rd_ready);
        end
    )

    wire        w_take1    = w_fire1 && w_room1;
    wire        w_take2    = w_fire2 && w_room2 && !r_pend_q;
    wire [3:0]  w_lost     = w_fire_n - 4'(w_take1) - 4'(w_take2);
    logic [7:0] r_dropped;

    wire w_drop_rpt = (r_dropped != 8'd0)
                      && (w_lost == 4'd0) && !w_fire1 && w_q_empty
                      && !`RST_ASSERTED(rst_n);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_dropped <= 8'd0;
        end else begin
            if (w_drop_rpt) begin
                r_dropped <= 8'd0;
            end else if (r_dropped >= 8'hFE) begin
                r_dropped <= (w_lost != 4'd0) ? 8'hFF : r_dropped;
            end else begin
                r_dropped <= r_dropped + 8'(w_lost);
            end
        end
    )

    // ------------------------------------------------------------------
    // Queue push path
    // ------------------------------------------------------------------
    monitor_packet_t   w_slot1_pkt, w_slot2_pkt;
    monbus_timestamp_t w_slot1_ts;

    assign w_slot1_pkt = w_fire1
        ? create_monitor_packet(c_ptype[w_p1_idx], PROTOCOL_CORE,
                                c_code[w_p1_idx], 9'd0, UNIT_ID, AGENT_ID,
                                c_data[w_p1_idx])
        : create_monitor_packet(PktTypeError, PROTOCOL_CORE,
                                DROP_CODE, 9'd0, UNIT_ID,
                                AGENT_ID, 64'(r_dropped));
    assign w_slot1_ts = i_mon_time;
    assign w_slot2_pkt = create_monitor_packet(c_ptype[w_p2_idx],
                                               PROTOCOL_CORE,
                                               c_code[w_p2_idx], 9'd0,
                                               UNIT_ID, AGENT_ID,
                                               c_data[w_p2_idx]);

    assign fifo_wr_valid = r_pend_q || w_take1 || w_drop_rpt;
    assign fifo_wdata    = r_pend_q ? {r_pend_ts, r_pend_pkt}
                                    : (w_take1 ? {w_slot1_ts, w_slot1_pkt}
                                               : {i_mon_time, w_slot1_pkt});

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pend_q   <= 1'b0;
            r_pend_pkt <= '0;
            r_pend_ts  <= '0;
        end else begin
            if (w_take2) begin
                r_pend_q   <= 1'b1;
                r_pend_pkt <= w_slot2_pkt;
                r_pend_ts  <= i_mon_time;
            end else if (r_pend_q && w_take1) begin
                r_pend_q   <= 1'b1;
                r_pend_pkt <= w_slot1_pkt;
                r_pend_ts  <= w_slot1_ts;
            end else begin
                r_pend_q <= 1'b0;
            end
        end
    )

    // ------------------------------------------------------------------
    // MonBus outputs
    // ------------------------------------------------------------------
    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_taps;
    assign unused_taps = &{1'b0, mshr_alloc_i, mshr_alloc_set_i,
                           mshr_alloc_cls_i, mshr_alloc_idx_i, mshr_merge_i,
                           mshr_merge_idx_i, mshr_merge_depth_i,
                           mshr_retire_i, mshr_retire_idx_i,
                           ctrl_stall_i, ctrl_stall_reason_i,
                           i_mon_time, clk};
    logic unused_fifo;
    assign unused_fifo = &{1'b0, fifo_wr_ready, fifo_count};
    /* verilator lint_on UNUSEDSIGNAL */

    if (USE_MONITOR) begin : gen_monitor
        assign monbus_valid     = fifo_rd_valid;
        assign monbus_packet    = fifo_rdata[MONBUS_PKT_WIDTH-1:0];
        assign monbus_timestamp = fifo_rdata[QW-1:MONBUS_PKT_WIDTH];
        assign fifo_rd_ready    = monbus_ready;
        assign dropped_count    = r_dropped;
    end else begin : gen_no_monitor
        assign monbus_valid     = 1'b0;
        assign monbus_packet    = '0;
        assign monbus_timestamp = '0;
        assign fifo_rd_ready    = 1'b0;
        assign dropped_count    = 8'd0;
    end

endmodule : jet_monlite
