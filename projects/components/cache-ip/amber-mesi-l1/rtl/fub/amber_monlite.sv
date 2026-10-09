// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_monlite
// Purpose:
//   Drop-and-count MonBus observer for the amber MESI L1 (DECISION D8,
//   MAS ch04): taps the amber_core control-plane signals and emits one
//   128-bit house-format MonBus packet per Table 4.1.1 event class. The
//   observer drives nothing in the observed path -- a packet the monbus
//   will not take is dropped and counted, never backpressured.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch04_monbus_observation/01_event_map.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-08

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: amber_monlite
//==============================================================================
// Description:
//   Event strobes (MAS ch04 Table 4.1.1 emit points):
//     HIT        entry into CTRL_HIT_RD / CTRL_HIT_WR (state-edge detect)
//     MISS       one cycle deferred from CTRL_MISS_VICTIM entry, so the
//                victim way (registered by control at the entry) is exact
//     SNOOP      tap_snoop_fire (the AC handshake accepted: snoop_req &&
//                snoop_ready at the grant cycle; tap_snoop_hit /
//                tap_snoop_resp are combinationally valid there)
//     EVICT      tap_victim_load (dirty victim staged to amber_victim);
//                way/dirty were latched with the MISS packet
//     TRANSITION tap_tag_wr_en outside CTRL_INIT (the INIT walk writes I
//                over I -- a reset artifact, not a coherence transition);
//                cause encodes the emitting state (1=HIT_WR promotion,
//                2=FILL_WRITE install/upgrade, 4=SNOOP, 7=other)
//     FILL_START CTRL_MISS_FILL entry;  FILL_END CTRL_FILL_WRITE entry
//     DRAIN_START CTRL_MISS_DRAIN entry; DRAIN_END tap_drain_done
//                (the drain line address is captured at DRAIN_START)
//
//   Every miss replays through HIT_RD/HIT_WR, so every CPU transaction
//   ends with a HIT event; an upgrade commits its S->M tag write in
//   FILL_WRITE (TRANSITION) and replays as a hit at M.
//
//   Packet format: the house monitor_common_pkg 128-bit layout built with
//   create_monitor_packet -- PktTypePerf for event classes, PROTOCOL_CORE,
//   designer-allocated AGENT_ID / UNIT_ID, channel/reserved zero. The
//   64-bit event_data packing (right-aligned fields):
//     HIT        [15:0] set | [19:16] way | [22:20] state_before |
//                [25:23] state_after | [26] we
//     MISS       [15:0] set | [19:16] way | [21:20] miss_class | [22] we
//     SNOOP      [2:0] snoop_type | [3] hit | [8:4] response_class (CRRESP)
//     EVICT      [15:0] set | [19:16] way | [20] dirty | [52:21] line_addr
//     TRANSITION [15:0] set | [19:16] way | [22:20] old_state |
//                [25:23] new_state | [29:26] cause
//     FILL_/DRAIN_ start/end  zero-extended line_addr
//     DROPPED    [7:0] dropped_count
//
//   Output queue: the house gaxi_fifo_sync (D11 shared storage primitive)
//     holds OUT_DEPTH {timestamp, packet} words. Up to two candidates
//     fire per cycle -- a TRANSITION co-firing with the HIT_WR promotion
//     or the FILL_END it accompanies, the only pairs by construction --
//     and the single FIFO write port defers slot 2 through a one-entry
//     register into the next cycle; take decisions run on the effective
//     occupancy (FIFO count + deferral) so the w_take1/w_take2 drop
//     accounting is identical to a two-slot queue and the deferral is
//     invisible at the pins (the deferred entry always sits behind the
//     entries ahead of it, whose drain hides the one-cycle transport).
//     Priority EVICT > SNOOP > HIT_RD > HIT_WR > MISS > FILL_START >
//     DRAIN_START > FILL_END > DRAIN_END > TRANSITION; candidates that
//     find no room are dropped and counted, never stalled (Review Focus
//     5).
//
//   Drop-and-count (MAS ch04/02, the STREAM monitor-lite idiom): an 8-bit
//   saturating counter accumulates the drops; when it is non-zero, no
//   candidate fires this cycle and the queue has drained, the count is
//   re-emitted as PktTypeError/DROP_CODE and the counter clears. A
//   report is pushed into a DRAINED queue only -- it must never take the
//   slot a live event needs while the bus is congested.
//
//   Timestamp: the 64-bit side-band is captured INTO the queue entry at
//   push (MAS ch03/05: sampled at emission, held stable while mon_valid
//   is high); the consumer samples it at the handshake.
//
//   USE_MONITOR=0 ties the observer off (house gen_no_monitor idiom): the
//   "absent" half of the present-vs-absent measurement-integrity pin.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / LINE_BYTES / BUS_WIDTH:
//     Description: geometry per amber_pkg defaults (field widths only)
//     Type: int
//   AGENT_ID / UNIT_ID:
//     Description: designer-allocated house monitor ids (monitor_common_pkg
//       allocation rules; amber = 16'h00A0, monlite unit = 8'h01)
//     Type: logic
//   DROP_CODE:
//     Description: event_code of the drop-report packet (the only amber
//       constant in the otherwise amber-free counting engine; a lift to
//       utility-ip/misc overrides this — T8 review Minor #3)
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
//   - Instantiated by: amber_core (test harness: dv/tb/amber_monlite_th.sv)
//   - Queue: gaxi_fifo_sync u_out_q (house shared storage primitive, D11)
//   - Package: monitor_common_pkg (packet layout), amber_pkg (event codes,
//     ctrl_state_t, cache_state_t)
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_monlite.py
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_monlite.py -v
//
//==============================================================================

module amber_monlite
    import amber_pkg::*;
    import monitor_common_pkg::*;
#(
    parameter int ADDR_WIDTH  = AMBER_ADDR_WIDTH,
    parameter int SETS        = AMBER_SETS,
    parameter int WAYS        = AMBER_WAYS,
    parameter int LINE_BYTES  = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH   = AMBER_BUS_WIDTH,
    parameter logic [15:0] AGENT_ID     = 16'h00A0,
    parameter logic [7:0]  UNIT_ID      = 8'h01,
    parameter logic [7:0]  DROP_CODE    = 8'(AMBER_EV_DROPPED),
    parameter bit          USE_MONITOR  = 1'b1,
    parameter int          OUT_DEPTH    = 4,
    localparam int SET_INDEX_WIDTH   = $clog2(SETS),
    localparam int LINE_OFFSET_WIDTH = $clog2(LINE_BYTES),
    localparam int TAG_WIDTH         = ADDR_WIDTH - SET_INDEX_WIDTH
                                       - LINE_OFFSET_WIDTH,
    localparam int LINE_ADDR_WIDTH   = TAG_WIDTH + SET_INDEX_WIDTH,
    localparam int WAY_INDEX_WIDTH   = (WAYS > 1) ? $clog2(WAYS) : 1,
    localparam int STRB_W            = BUS_WIDTH / 8,
    localparam int FILL_BEATS        = LINE_BYTES / STRB_W
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // ---- observation taps (amber_core wiring; the harness taps the
    //      closure's pins plus read-only control internals) ----
    input  logic [3:0]                  tap_ctrl_state,

    // hit context: valid in the HIT_RD / HIT_WR entry cycle
    input  logic [SET_INDEX_WIDTH-1:0]  tap_hit_set,
    input  logic [WAY_INDEX_WIDTH-1:0]  tap_hit_way,
    input  logic [2:0]                  tap_hit_state_before,
    input  logic                        tap_req_we,

    // miss context: set valid from accept through the transaction; the
    // victim way/state arrive registered -- sampled at the deferred cycle
    input  logic [SET_INDEX_WIDTH-1:0]  tap_miss_set,
    input  logic [1:0]                  tap_miss_class,

    // snoop context: valid at the AC grant cycle (tap_snoop_fire)
    input  logic                        tap_snoop_fire,
    input  logic [2:0]                  tap_snoop_type,
    input  logic                        tap_snoop_hit,
    input  logic [AMBER_CRRESP_WIDTH-1:0] tap_snoop_resp,

    // eviction context: tap_victim_addr is the staged full line address
    input  logic                        tap_victim_load,
    input  logic [ADDR_WIDTH-1:0]       tap_victim_addr,
    input  logic [WAY_INDEX_WIDTH-1:0]  tap_victim_way,
    input  logic [2:0]                  tap_victim_state,

    // tag-array state write (transition); old state resolved per cause
    input  logic                        tap_tag_wr_en,
    input  logic [SET_INDEX_WIDTH-1:0]  tap_tag_wr_set,
    input  logic [WAY_INDEX_WIDTH-1:0]  tap_tag_wr_way,
    input  logic [2:0]                  tap_tag_wr_new_state,
    input  logic [2:0]                  tap_state_old,

    // fill / drain line addresses (full addresses, line-aligned)
    input  logic [ADDR_WIDTH-1:0]       tap_fill_addr,
    input  logic                        tap_drain_done,

    // side-band timestamp
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
            $error("amber_monlite: SETS must be a power of two");
        if ((OUT_DEPTH & (OUT_DEPTH - 1)) != 0 || OUT_DEPTH < 2)
            $error("amber_monlite: OUT_DEPTH must be a power of two >= 2");
    end

    // ------------------------------------------------------------------
    // State-edge strobes (one-cycle pulses at the emit points)
    // ------------------------------------------------------------------
    logic [3:0] state_q;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            state_q <= AMBER_CTRL_INIT;   // INIT: no spurious entry strobe
        end else begin
            state_q <= tap_ctrl_state;
        end
    )

    wire in_hit_rd = (tap_ctrl_state == AMBER_CTRL_HIT_RD);
    wire in_hit_wr = (tap_ctrl_state == AMBER_CTRL_HIT_WR);
    wire in_miss_victim = (tap_ctrl_state == AMBER_CTRL_MISS_VICTIM);
    wire in_miss_fill = (tap_ctrl_state == AMBER_CTRL_MISS_FILL);
    wire in_miss_drain = (tap_ctrl_state == AMBER_CTRL_MISS_DRAIN);
    wire in_fill_write = (tap_ctrl_state == AMBER_CTRL_FILL_WRITE);

    wire w_hit_rd_fire  = in_hit_rd  && (state_q != AMBER_CTRL_HIT_RD);
    wire w_hit_wr_fire  = in_hit_wr  && (state_q != AMBER_CTRL_HIT_WR);
    wire w_miss_victim_entry = in_miss_victim
                               && (state_q != AMBER_CTRL_MISS_VICTIM);
    wire w_fill_start_fire = in_miss_fill
                             && (state_q != AMBER_CTRL_MISS_FILL);
    wire w_drain_start_fire = in_miss_drain
                              && (state_q != AMBER_CTRL_MISS_DRAIN);
    wire w_fill_end_fire = in_fill_write
                           && (state_q != AMBER_CTRL_FILL_WRITE);

    // MISS packet deferred one cycle so the victim way/state registered
    // by control at the MISS_VICTIM entry are exact at the tap
    logic r_miss_pend_q;
    wire  w_miss_fire = r_miss_pend_q;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_miss_pend_q <= 1'b0;
        end else begin
            r_miss_pend_q <= w_miss_victim_entry;
        end
    )

    // line addresses captured for the paired end events (the start events
    // sample the taps combinationally at their own fire cycle)
    logic [LINE_ADDR_WIDTH-1:0] r_drain_line_q;
    logic [LINE_ADDR_WIDTH-1:0] r_fill_line_q;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_drain_line_q <= '0;
            r_fill_line_q  <= '0;
        end else begin
            if (w_drain_start_fire) begin
                r_drain_line_q <= LINE_ADDR_WIDTH'(
                    tap_victim_addr >> LINE_OFFSET_WIDTH);
            end
            if (w_fill_start_fire) begin
                r_fill_line_q <= LINE_ADDR_WIDTH'(
                    tap_fill_addr >> LINE_OFFSET_WIDTH);
            end
        end
    )

    // TRANSITION strobe: every tag-array state write outside the INIT walk
    wire w_trans_fire = tap_tag_wr_en
                        && (tap_ctrl_state != AMBER_CTRL_INIT);

    logic [3:0] w_trans_cause;
    always_comb begin
        unique case (tap_ctrl_state)
            AMBER_CTRL_HIT_WR:     w_trans_cause = 4'd1;
            AMBER_CTRL_FILL_WRITE: w_trans_cause = 4'd2;
            AMBER_CTRL_SNOOP:      w_trans_cause = 4'd4;
            default:               w_trans_cause = 4'd7;
        endcase
    end

    // ------------------------------------------------------------------
    // Candidate events: {ptype, code, data}, priority-ordered. At most two
    // fire per cycle (TRANSITION with the HIT_WR promotion or the FILL_END
    // it accompanies; verified exhaustively by the directed matrix).
    // ------------------------------------------------------------------
    logic [3:0]  c_ptype   [10];
    logic [7:0]  c_code    [10];
    logic [63:0] c_data    [10];
    logic        c_fire    [10];

    localparam int N_CAND = 10;
    // priority index: 0 EVICT, 1 SNOOP, 2 HIT_RD, 3 HIT_WR, 4 MISS,
    //                 5 FILL_START, 6 DRAIN_START, 7 FILL_END,
    //                 8 DRAIN_END, 9 TRANSITION

    wire [2:0] w_hit_state_after = tap_req_we ? AMBER_STATE_M
                                                : tap_hit_state_before;
    wire [63:0] w_hit_data =
        64'(tap_hit_set)
        | (64'(tap_hit_way) << 16)
        | (64'(tap_hit_state_before) << 20)
        | (64'(w_hit_state_after) << 23)
        | (64'(tap_req_we) << 26);

    wire [SET_INDEX_WIDTH-1:0] w_victim_set =
        SET_INDEX_WIDTH'(tap_victim_addr >> LINE_OFFSET_WIDTH);

    wire [63:0] w_miss_data =
        64'(tap_miss_set)
        | (64'(tap_victim_way) << 16)
        | (64'(tap_miss_class) << 20)
        | (64'(tap_req_we) << 22);

    wire [63:0] w_snoop_data =
        64'(tap_snoop_type)
        | (64'(tap_snoop_hit) << 3)
        | (64'(tap_snoop_resp) << 4);

    wire [63:0] w_evict_data =
        64'(w_victim_set)
        | (64'(tap_victim_way) << 16)
        | (64'(tap_victim_state == AMBER_STATE_M) << 20)
        | (64'(tap_victim_addr >> LINE_OFFSET_WIDTH) << 21);

    wire [63:0] w_trans_data =
        64'(tap_tag_wr_set)
        | (64'(tap_tag_wr_way) << 16)
        | (64'(tap_state_old) << 20)
        | (64'(tap_tag_wr_new_state) << 23)
        | (64'(w_trans_cause) << 26);

    always_comb begin
        for (int i = 0; i < N_CAND; i++) begin
            c_ptype[i] = PktTypePerf;
            c_code[i]  = 8'h00;
            c_data[i]  = '0;
            c_fire[i]  = 1'b0;
        end
        // 0: EVICT
        c_code[0]  = 8'(AMBER_EV_EVICT);
        c_data[0]  = w_evict_data;
        c_fire[0]  = tap_victim_load;
        // 1: SNOOP
        c_code[1]  = 8'(AMBER_EV_SNOOP);
        c_data[1]  = w_snoop_data;
        c_fire[1]  = tap_snoop_fire;
        // 2/3: HIT_RD / HIT_WR
        c_code[2]  = 8'(AMBER_EV_HIT);
        c_data[2]  = w_hit_data;
        c_fire[2]  = w_hit_rd_fire;
        c_code[3]  = 8'(AMBER_EV_HIT);
        c_data[3]  = w_hit_data;
        c_fire[3]  = w_hit_wr_fire;
        // 4: MISS
        c_code[4]  = 8'(AMBER_EV_MISS);
        c_data[4]  = w_miss_data;
        c_fire[4]  = w_miss_fire;
        // 5/6/7/8: fill / drain start+end (starts sample the taps at their
        // own fire cycle; ends use the address captured at the start)
        c_code[5]  = 8'(AMBER_EV_FILL_START);
        c_data[5]  = 64'(LINE_ADDR_WIDTH'(tap_fill_addr >> LINE_OFFSET_WIDTH));
        c_fire[5]  = w_fill_start_fire;
        c_code[6]  = 8'(AMBER_EV_DRAIN_START);
        c_data[6]  = 64'(LINE_ADDR_WIDTH'(tap_victim_addr
                                          >> LINE_OFFSET_WIDTH));
        c_fire[6]  = w_drain_start_fire;
        c_code[7]  = 8'(AMBER_EV_FILL_END);
        c_data[7]  = 64'(r_fill_line_q);
        c_fire[7]  = w_fill_end_fire;
        c_code[8]  = 8'(AMBER_EV_DRAIN_END);
        c_data[8]  = 64'(r_drain_line_q);
        c_fire[8]  = tap_drain_done;
        // 9: TRANSITION
        c_code[9]  = 8'(AMBER_EV_TRANSITION);
        c_data[9]  = w_trans_data;
        c_fire[9]  = w_trans_fire;
    end

    wire [3:0] w_fire_n = 4'(
          4'(c_fire[0]) + 4'(c_fire[1]) + 4'(c_fire[2]) + 4'(c_fire[3])
        + 4'(c_fire[4]) + 4'(c_fire[5]) + 4'(c_fire[6]) + 4'(c_fire[7])
        + 4'(c_fire[8]) + 4'(c_fire[9]));

    // ------------------------------------------------------------------
    // Output queue: the house gaxi_fifo_sync (DECISION D11 shared storage
    // primitive, same idiom as the amber_cpu_frontend D-6 staging FIFO)
    // holds {timestamp, packet} words. The candidate logic may fire twice
    // in a cycle (the TRANSITION co-fire with HIT_WR / FILL_WRITE, the
    // only co-fire pairs by construction); the FIFO has one write port,
    // so slot 2 rides a one-entry deferral register and enters the FIFO
    // the next cycle. The deferral is invisible at the pins: take
    // decisions run on the EFFECTIVE occupancy (FIFO count + deferral),
    // which keeps the w_take1/w_take2 drop accounting identical to a
    // two-slot queue, and the deferred entry always sits behind the
    // entries ahead of it, whose drain hides the one-cycle transport
    // (a co-fire pair is always followed by a fire-free cycle: FILL_WRITE
    // -> REPLAY, HIT_WR -> IDLE, and no grant lands in either).
    // House memory idiom: the FIFO storage carries no reset; only the
    // deferral register and the drop counter are resettable flops.
    // ------------------------------------------------------------------
    localparam int QW  = MONBUS_PKT_WIDTH + MONBUS_TS_WIDTH;
    localparam int OQW = (OUT_DEPTH > 1) ? $clog2(OUT_DEPTH) : 1;

    logic                       r_pend_q;   // deferral register valid
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

    // first/second priority candidates
    logic [3:0]  w_p1_idx, w_p2_idx;
    logic        w_fire1, w_fire2;

    always_comb begin
        w_p1_idx = 4'd0;
        w_fire1  = 1'b0;
        w_p2_idx = 4'd0;
        w_fire2  = 1'b0;
        // walk low-priority-first so the last fired (highest priority)
        // lands in slot 1 and the runner-up in slot 2
        for (int i = N_CAND - 1; i >= 0; i--) begin
            if (c_fire[i]) begin
                w_p2_idx = w_p1_idx;
                w_fire2  = w_fire1;
                w_p1_idx = 4'(i);
                w_fire1  = 1'b1;
            end
        end
    end

    // ------------------------------------------------------------------
    // Drop accounting and the pending drop report (STREAM monitor-lite
    // idiom: the count goes out into a DRAINED queue only). Effective
    // occupancy (FIFO + deferral) is tracked as a small registered
    // counter -- the house fifo's own count output reflects next-pointer
    // state and would close a combinational loop through the takes.
    // Every fifo_wr_valid beat is accepted (room is budgeted before
    // asserting it), so counting beats is exact.
    // ------------------------------------------------------------------
    logic [OQW:0] r_eff_q;
    wire [OQW:0] w_eff_cnt  = r_eff_q;
    wire         w_q_empty  = (w_eff_cnt == '0);
    wire         w_room1    = (w_eff_cnt <= (OQW+1)'(OUT_DEPTH - 1));
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
            // saturating 8-bit (MAS ch04/02): 256 consecutive drops pin at
            // 0xFF and the overflow is visible in the report
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
    // Queue push path. The single FIFO write port serves, in order: the
    // deferral register (slot 2 of last cycle's co-fire pair), then slot
    // 1 of this cycle, then the drop report -- the three are mutually
    // exclusive except deferral + slot 1, where slot 1 chains into the
    // deferral register (stream order preserved: the deferred entry is
    // always the older). Every wr_valid beat is guaranteed wr_ready (the
    // deferral had its room budgeted by w_room2; the report fires only
    // into an empty queue; slot 1 checks w_room1), so the FIFO never
    // silently drops a beat.
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
            // slot 2 of a co-fire pair defers; a slot 1 arriving while
            // the deferral drains chains behind it (unreachable today --
            // a grant never lands in REPLAY/IDLE-adjacent cycles -- but
            // counted-correct either way)
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
    assign unused_taps = &{1'b0, tap_ctrl_state, tap_hit_set, tap_hit_way,
                           tap_hit_state_before, tap_req_we, tap_miss_set,
                           tap_miss_class, tap_snoop_fire, tap_snoop_type,
                           tap_snoop_hit, tap_snoop_resp, tap_victim_load,
                           tap_victim_addr, tap_victim_way, tap_victim_state,
                           tap_tag_wr_en, tap_tag_wr_set, tap_tag_wr_way,
                           tap_tag_wr_new_state, tap_state_old,
                           tap_fill_addr, tap_drain_done, i_mon_time, clk};
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

endmodule : amber_monlite
