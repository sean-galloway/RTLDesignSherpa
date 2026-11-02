// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: mc_monlite
// Purpose: Drop-and-count Ocelus observer for the memory controllers'
//          internal events: taps errors and debug state the controller
//          already has and emits one 128-bit house-format PROTOCOL_CORE
//          packet per event. Drives nothing in the observed path.
//
// Documentation: projects/components/mem-ctrl-ip/common-ip/docs/common_mas/ch11_ocelus_plane/01_mc_ocelus_plane.md
// Subsystem: mem-ctrl-ip common-ip
//
// Author: sean galloway
// Created: 2026-11-01
//==============================================================================
// Description:
//   Events (event_code = mc_event_e, also the event's bit in cfg_ev_en):
//
//     code  name            packet  fires on                       payload (event_data)
//     0x00  CAL_ERR         Error   cal_err_i rising               0
//     0x01  ZQ_OVERDUE      Error   zq_overdue_i rising            0
//     0x02  REF_BACKLOG     Error   ref_pending_i reaching          [3:0] pending
//                                   REF_BACKLOG_MAX (rising)
//     0x03  AW_RAGGED       Error   aw_ragged_i                    0
//     0x04  RD_BEAT_LOST    Error   rd_beat_lost_i                 0
//     0x05  RET_ORPHAN      Error   ret_orphan_i                   0
//     0x06  DROPPED         Error   events were lost (below)       [15:0] count lost
//     0x08  INIT_DONE       Debug   init_done_i rising             [4:0] init state
//     0x09  INIT_STATE      Debug   init_state_i changed           [4:0] new state
//     0x0A  DIR_FLIP        Debug   dir_flip_i                     [7:0] batch that ended,
//                                                                  [8] new dir (1 = write),
//                                                                  [10:9] cause (0 old-direction
//                                                                  fire, 1 drained, 2 batch cap)
//     0x0B  REFRESH         Debug   a REF / REFpb accepted         [4:0] dram_op_e
//     0x0C  ZQ              Debug   a ZQCS / ZQCL accepted         [4:0] dram_op_e
//     0x0D  PAGE_TO_PRE     Debug   a page-timeout PRE accepted    0
//     0x0E  STORE_FULL      Debug   the store began refusing a     [0] write side, [1] read side
//                                   push (rising)
//     0x0F  RING_FULL       Debug   the read-return ring went      0
//                                   full (rising)
//
//   Every event has a pending bit. An event sets its bit (and latches its
//   payload); each cycle the lowest-numbered pending event -- errors first
//   -- goes into the output queue if it has room. The packet's timestamp
//   is i_mon_time at that cycle, at most a few cycles after the event when
//   the queue is draining. An event that fires again while its bit is
//   still set is lost and counted; so is everything while the queue is
//   full and the bit is held. The count goes out as a DROPPED packet once
//   nothing else is pending, and clears. The controller is never stalled.
//
//   cfg_enable = 0 clears every pending bit and stops new ones; cfg_ev_en
//   masks events one by one. Edge detectors keep running either way, so
//   turning the monitor on does not report a level that was already up.
//
// Parameters:
//   - UNIT_ID / AGENT_ID: the packet's identity (designer-allocated)
//   - OUT_DEPTH: output queue depth, {timestamp, packet} words, >= 2
//   - REF_BACKLOG_MAX: the refresh controller's saturation level
//     (mc_xddr2_refresh_ctrl MAX_PENDING)
//
// Notes:
//   - All taps are aclk-domain; the DFI-side loss pulse arrives already
//     synchronized by mc_dfi_2p1_plane.
//   - Same queue idiom as l1_monlite: gaxi_fifo_sync, storage unreset.
//
// Test:
//   projects/components/mem-ctrl-ip/common-ip/dv/tests/fub/test_mc_monlite.py
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module mc_monlite
    import mc_common_pkg::*;
    import ocelus_common_pkg::*;
#(
    parameter logic [7:0]  UNIT_ID         = 8'h20,
    parameter logic [15:0] AGENT_ID        = 16'h0012,
    parameter int          OUT_DEPTH       = 4,
    parameter logic [3:0]  REF_BACKLOG_MAX = 4'd8
) (
    input  logic              aclk,
    input  logic              aresetn,

    // ---- configuration ----
    input  logic              cfg_enable,
    input  logic [15:0]       cfg_ev_en,         // bit [event_code]

    // ---- taps (aclk domain) ----
    input  logic              cal_err_i,         // level
    input  logic              zq_overdue_i,      // level
    input  logic [3:0]        ref_pending_i,     // refresh backlog
    input  logic              aw_ragged_i,       // pulse
    input  logic              rd_beat_lost_i,    // pulse
    input  logic              ret_orphan_i,      // pulse
    input  logic              init_done_i,       // level
    input  logic [4:0]        init_state_i,
    input  logic              dir_flip_i,        // pulse
    input  logic              dir_i,
    input  logic [1:0]        dir_cause_i,
    input  logic [7:0]        dir_batch_i,
    input  logic              cmd_accept_i,      // a command left the scheduler
    input  dram_op_e          cmd_accept_op_i,
    input  logic              accept_to_pre_i,   // ... and it is a page-timeout PRE
    input  logic              store_wr_full_i,   // level: a write push is refused
    input  logic              store_rd_full_i,   // level: a read push is refused
    input  logic              ring_full_i,       // level

    // ---- side-band timestamp ----
    input  monbus_timestamp_t i_mon_time,

    // ---- monitor bus ----
    output logic              monbus_valid,
    input  logic              monbus_ready,
    output monitor_packet_t   monbus_packet,
    output monbus_timestamp_t monbus_timestamp,

    // ---- status ----
    output logic [15:0]       error_count,       // error packets queued (wraps)
    output logic [15:0]       dropped_count      // events lost since the last DROPPED packet
);

    localparam int NEV = 16;
    localparam int EV_DROPPED = int'(MC_EV_DROPPED);

    // ------------------------------------------------------------------
    // Edge detectors (always running)
    // ------------------------------------------------------------------
    logic       r_cal_err, r_zq_overdue, r_ref_max, r_init_done;
    logic       r_store_full, r_ring_full;
    logic [4:0] r_init_state;

    logic w_ref_max, w_store_full;
    assign w_ref_max    = (ref_pending_i >= REF_BACKLOG_MAX);
    assign w_store_full = store_wr_full_i || store_rd_full_i;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_cal_err    <= 1'b0;
            r_zq_overdue <= 1'b0;
            r_ref_max    <= 1'b0;
            r_init_done  <= 1'b0;
            r_init_state <= '0;
            r_store_full <= 1'b0;
            r_ring_full  <= 1'b0;
        end else begin
            r_cal_err    <= cal_err_i;
            r_zq_overdue <= zq_overdue_i;
            r_ref_max    <= w_ref_max;
            r_init_done  <= init_done_i;
            r_init_state <= init_state_i;
            r_store_full <= w_store_full;
            r_ring_full  <= ring_full_i;
        end
    )

    // ------------------------------------------------------------------
    // This cycle's events, bit = event code
    // ------------------------------------------------------------------
    logic [NEV-1:0] w_hit, w_ev;
    always_comb begin
        w_hit = '0;
        w_hit[4'(MC_EV_CAL_ERR)]      = cal_err_i && !r_cal_err;
        w_hit[4'(MC_EV_ZQ_OVERDUE)]   = zq_overdue_i && !r_zq_overdue;
        w_hit[4'(MC_EV_REF_BACKLOG)]  = w_ref_max && !r_ref_max;
        w_hit[4'(MC_EV_AW_RAGGED)]    = aw_ragged_i;
        w_hit[4'(MC_EV_RD_BEAT_LOST)] = rd_beat_lost_i;
        w_hit[4'(MC_EV_RET_ORPHAN)]   = ret_orphan_i;
        w_hit[4'(MC_EV_INIT_DONE)]    = init_done_i && !r_init_done;
        w_hit[4'(MC_EV_INIT_STATE)]   = (init_state_i != r_init_state);
        w_hit[4'(MC_EV_DIR_FLIP)]     = dir_flip_i;
        w_hit[4'(MC_EV_REFRESH)]      = cmd_accept_i && is_refresh_op(cmd_accept_op_i);
        w_hit[4'(MC_EV_ZQ)]           = cmd_accept_i && is_zq_op(cmd_accept_op_i);
        w_hit[4'(MC_EV_PAGE_TO_PRE)]  = accept_to_pre_i;
        w_hit[4'(MC_EV_STORE_FULL)]   = w_store_full && !r_store_full;
        w_hit[4'(MC_EV_RING_FULL)]    = ring_full_i && !r_ring_full;
    end
    // DROPPED is not an edge: it is raised from the drop counter below
    assign w_ev = w_hit & cfg_ev_en & {NEV{cfg_enable}};

    // ------------------------------------------------------------------
    // Output queue: {timestamp, packet} words (house gaxi_fifo_sync)
    // ------------------------------------------------------------------
    localparam int QW = MONBUS_PKT_WIDTH + MONBUS_TS_WIDTH;

    logic          fifo_wr_valid, fifo_wr_ready;
    logic [QW-1:0] fifo_wdata;
    logic          fifo_rd_valid;
    logic [QW-1:0] fifo_rdata;
    logic [$clog2(OUT_DEPTH):0] fifo_count;

    gaxi_fifo_sync #(
        .DATA_WIDTH (QW),
        .DEPTH      (OUT_DEPTH)
    ) u_out_q (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (fifo_wr_valid),
        .wr_ready    (fifo_wr_ready),
        .wr_data     (fifo_wdata),
        .rd_ready    (monbus_ready),
        .count       (fifo_count),
        .rd_valid    (fifo_rd_valid),
        .rd_data     (fifo_rdata)
    );

    assign monbus_valid     = fifo_rd_valid;
    assign monbus_packet    = fifo_rdata[MONBUS_PKT_WIDTH-1:0];
    assign monbus_timestamp = fifo_rdata[QW-1:MONBUS_PKT_WIDTH];

    // ------------------------------------------------------------------
    // Pending bits, payloads, and the one take per cycle
    // ------------------------------------------------------------------
    logic [NEV-1:0] r_pend;
    logic [3:0]     r_pl_ref;
    logic [4:0]     r_pl_init;
    logic [10:0]    r_pl_dir;
    logic [4:0]     r_pl_refop, r_pl_zqop;
    logic [1:0]     r_pl_full;
    logic [15:0]    r_dropped;

    // lowest-numbered pending event (errors before debug)
    logic           w_take_any;
    logic [3:0]     w_take_idx;
    logic [NEV-1:0] w_take;
    always_comb begin
        w_take_any = 1'b0;
        w_take_idx = '0;
        for (int i = NEV - 1; i >= 0; i--)
            if (r_pend[i]) begin
                w_take_any = 1'b1;
                w_take_idx = 4'(i);
            end
    end

    // DROPPED goes out only when nothing else waits
    logic w_drop_rpt;
    assign w_drop_rpt = !w_take_any && (r_dropped != 16'd0)
                        && cfg_enable && cfg_ev_en[EV_DROPPED];

    assign fifo_wr_valid = w_take_any || w_drop_rpt;
    assign w_take = (w_take_any && fifo_wr_ready) ? (NEV'(1) << w_take_idx) : '0;

    // events this cycle that find their bit still held are lost
    logic [NEV-1:0] w_lost_vec;
    logic [4:0]     w_lost;
    always_comb begin
        w_lost_vec = w_ev & r_pend & ~w_take;
        w_lost     = '0;
        for (int i = 0; i < NEV; i++) w_lost = w_lost + 5'(w_lost_vec[i]);
    end
    // a new event is captured when its bit is free (or freeing this cycle)
    logic [NEV-1:0] w_cap;
    assign w_cap = w_ev & (~r_pend | w_take);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_pend     <= '0;
            r_pl_ref   <= '0;
            r_pl_init  <= '0;
            r_pl_dir   <= '0;
            r_pl_refop <= '0;
            r_pl_zqop  <= '0;
            r_pl_full  <= '0;
            r_dropped  <= '0;
        end else begin
            r_pend <= cfg_enable ? ((r_pend & ~w_take) | w_ev) : '0;
            if (w_cap[4'(MC_EV_REF_BACKLOG)]) r_pl_ref   <= ref_pending_i;
            if (w_cap[4'(MC_EV_INIT_DONE)] || w_cap[4'(MC_EV_INIT_STATE)])
                                          r_pl_init  <= init_state_i;
            if (w_cap[4'(MC_EV_DIR_FLIP)])    r_pl_dir   <= {dir_cause_i, dir_i, dir_batch_i};
            if (w_cap[4'(MC_EV_REFRESH)])     r_pl_refop <= 5'(cmd_accept_op_i);
            if (w_cap[4'(MC_EV_ZQ)])          r_pl_zqop  <= 5'(cmd_accept_op_i);
            if (w_cap[4'(MC_EV_STORE_FULL)])  r_pl_full  <= {store_rd_full_i, store_wr_full_i};
            // drop counter: saturating; a DROPPED packet taken clears it
            // to whatever was lost in that same cycle
            if (w_drop_rpt && fifo_wr_ready)
                r_dropped <= 16'(w_lost);
            else if (r_dropped > (16'hFFFF - 16'(w_lost)))
                r_dropped <= 16'hFFFF;
            else
                r_dropped <= r_dropped + 16'(w_lost);
        end
    )

    // ------------------------------------------------------------------
    // Packet for the taken event
    // ------------------------------------------------------------------
    logic [7:0]  w_code;
    logic [3:0]  w_ptype;
    logic [63:0] w_data;
    always_comb begin
        w_code  = w_drop_rpt ? 8'(MC_EV_DROPPED) : {4'h0, w_take_idx};
        w_ptype = (w_code < 8'h08) ? PktTypeError : PktTypeDebug;
        w_data  = '0;
        if (w_drop_rpt) w_data[15:0] = r_dropped;
        else case (w_take_idx)
            4'(MC_EV_REF_BACKLOG): w_data[3:0]  = r_pl_ref;
            4'(MC_EV_INIT_DONE),
            4'(MC_EV_INIT_STATE):  w_data[4:0]  = r_pl_init;
            4'(MC_EV_DIR_FLIP):    w_data[10:0] = r_pl_dir;
            4'(MC_EV_REFRESH):     w_data[4:0]  = r_pl_refop;
            4'(MC_EV_ZQ):          w_data[4:0]  = r_pl_zqop;
            4'(MC_EV_STORE_FULL):  w_data[1:0]  = r_pl_full;
            default:               w_data       = '0;
        endcase
    end

    assign fifo_wdata = {i_mon_time,
                         create_monitor_packet(w_ptype, PROTOCOL_CORE, w_code,
                                               9'd0, UNIT_ID, AGENT_ID, w_data)};

    // ------------------------------------------------------------------
    // Status
    // ------------------------------------------------------------------
    logic [15:0] r_err_cnt;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))                              r_err_cnt <= '0;
        else if (fifo_wr_valid && fifo_wr_ready && (w_ptype == PktTypeError))
                                                                 r_err_cnt <= r_err_cnt + 16'd1;
    )
    assign error_count   = r_err_cnt;
    assign dropped_count = r_dropped;

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_ok;
    assign unused_ok = &{1'b0, fifo_count, w_cap};   // w_cap: only the payload-carrying bits are read
    /* verilator lint_on UNUSEDSIGNAL */

endmodule : mc_monlite
