// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: onyx_monlite
// Purpose:
//   Drop-and-count MonBus observer for onyx (D9).  Taps onyx_ccu's event
//   pulses and emits one 128-bit house-format MonBus packet per event
//   class.  The observer drives nothing in the measured path: a packet the
//   monbus will not take is dropped and counted, never backpressured.
//   The idiom is jet_prime_monlite's (and l1_monlite's before it).
//
// Documentation: projects/components/cache-ip/onyx-ace-ccu/docs/onyx_has/ch04_interfaces/04_observation_monbus.md
// Subsystem: onyx (cache-ip)
//
// Author: sean galloway
// Created: 2026-11-21
//==============================================================================
// Module: onyx_monlite
//==============================================================================
// Description:
//   Event classes (onyx_pkg):
//     TXN_START    a grant: [PORT_W-1:0] port | [7:5] class | [15:8] slot
//     GATHER_DONE  a slot's last CR: [7:0] slot | [8] DataTransfer |
//                  [9] PassDirty | [31:16] gather latency (grant -> last CR)
//     MEM_READ     a memory AR taken: [7:0] slot
//     READ_WASTED  a DataTransfer verdict for a slot whose read was issued
//                  or presented (its beats will be dropped): no payload
//     ABSORB       an absorption's BRESP: [7:0] slot
//     WRITEBACK    a cache write-back AW taken: [PORT_W-1:0] port
//     LOCK_WAIT    a port's candidate waited behind a held line, emitted
//                  on release: [PORT_W-1:0] port | [23:8] duration (cycles,
//                  saturating)
//
//   The elision measurement (D6): GATHER_DONE with DataTransfer counts the
//   lines a peer supplied; MEM_READ counts the memory reads issued; a
//   supplied line with no READ_WASTED is a read the manager did not have to
//   make.  DEFER_AR=1 should show READ_WASTED at zero.
//
//   Why holders and not the caches' two-intake engine: onyx's events
//   cluster -- a grant, a gather and a memory AR routinely land in one
//   cycle -- and the first pair-rig run with a two-intake, four-deep queue
//   lost 9 of 66 TXN_START packets and 3 of 69 MEM_READ ones; a 16-deep
//   queue lost exactly the same, so it was the intake, not the depth.  The
//   counts this observer exists for (D6's reads issued and wasted) must be
//   exact, and the pair-rig TB holds them to its own model's.  The AC
//   handshake count (a SNOOP_OUT class in the first cut) was dropped as
//   redundant: it is TXN_START times the peer count.
//
//   Drop-and-count: an 8-bit saturating counter accumulates drops; when
//   non-zero and nothing is waiting, the count is re-emitted as
//   PktTypeError / AMBER_EV_DROPPED.  Each class has a two-deep holder
//   (see below); only a class firing into a full holder loses an event.
//   Stream order is per class; classes interleave round-robin.
//
//   USE_MONITOR=0 ties the observer off (house gen_no_monitor idiom).
//
//   Masks, in the ocelus layers (the MonBus is a low-bandwidth event
//   channel; every per-transaction class here floods it under sustained
//   traffic, so the integrator picks what to transmit):
//     cfg_mon_enable            the observer as a whole (1 = on)
//     cfg_perf_enable           the event classes, all PktTypePerf (1 = on)
//     cfg_error_enable          the drop report, PktTypeError (1 = on)
//     cfg_pkt_mask[type]        bit set drops that packet type (bit 4 Perf,
//                               bit 0 Error), the cfg_*_pkt_mask convention
//     cfg_perf_mask[code[3:0]]  bit set drops that event class: bit 0
//                               TXN_START (0x20), 2 GATHER_DONE, 3 MEM_READ,
//                               4 READ_WASTED, 5 ABSORB, 6 WRITEBACK, 7
//                               LOCK_WAIT -- the group core's
//                               cfg_core_perf_mask indexes the same codes
//     cfg_error_mask[code[3:0]] bit set drops that Error code (bit 9 = the
//                               drop report, AMBER_EV_DROPPED 0x09)
//     cfg_port_mask[p]          bit set drops the events attributed to port
//                               p: TXN_START by the requesting port,
//                               GATHER_DONE and READ_WASTED by the answering
//                               port, LOCK_WAIT by the waiting port (MEM_READ,
//                               ABSORB and WRITEBACK carry no port in v1)
//   A masked event is dropped at the source: it enters no holder, counts
//   as nothing lost, and the drop report says only what the channel lost.
//   A masked drop report leaves the count accumulating in dropped_count.
//
//------------------------------------------------------------------------------
// Parameters:
//   N_PORTS / SLOTS: onyx_ccu's; AGENT_ID / UNIT_ID: the house monitor ids
//   (onyx_pkg defaults); DROP_CODE: the shared amber drop code; OUT_DEPTH:
//   output queue depth, a power of two >= 2.
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: onyx_top (and the onyx pair-rig harness beside onyx_ccu)
//   - Queue: gaxi_fifo_sync
//
//==============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"

module onyx_monlite
    import onyx_pkg::*;
    import l1_pkg::*;
    import ocelus_common_pkg::*;
#(
    parameter int          N_PORTS     = 2,
    parameter int          SLOTS       = 18,
    parameter logic [15:0] AGENT_ID    = ONYX_AGENT_ID,
    parameter logic [7:0]  UNIT_ID     = ONYX_UNIT_ID,
    parameter logic [7:0]  DROP_CODE   = 8'(AMBER_EV_DROPPED),
    parameter bit          USE_MONITOR = 1'b1,
    parameter int          OUT_DEPTH   = 16,
    localparam int SLOT_W = (SLOTS > 1) ? $clog2(SLOTS) : 1,
    localparam int PORT_W = (N_PORTS > 1) ? $clog2(N_PORTS) : 1
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // ---- onyx_ccu event taps ----
    input  logic                        evt_grant_i,
    input  logic [PORT_W-1:0]           evt_grant_port_i,
    input  logic [SLOT_W-1:0]           evt_grant_slot_i,
    input  logic [2:0]                  evt_grant_cls_i,
    input  logic [N_PORTS-1:0]          evt_ac_i,
    input  logic [N_PORTS-1:0]          evt_gather_i,          // per answering port
    input  logic [SLOT_W-1:0]           evt_gather_slot_i [N_PORTS],
    input  logic [N_PORTS-1:0]          evt_gather_dt_i,
    input  logic [N_PORTS-1:0]          evt_gather_pd_i,
    input  logic                        evt_mem_ar_i,
    input  logic [SLOT_W-1:0]           evt_mem_ar_slot_i,
    input  logic [N_PORTS-1:0]          evt_read_wasted_i,     // per answering port
    input  logic                        evt_absorb_i,
    input  logic [SLOT_W-1:0]           evt_absorb_slot_i,
    input  logic                        evt_wb_i,
    input  logic [PORT_W-1:0]           evt_wb_port_i,
    input  logic [N_PORTS-1:0]          evt_lock_wait_i,

    // ---- configuration: the ocelus layers (enables 1 = on; masks bit set = drop) ----
    input  logic                        cfg_mon_enable,
    input  logic                        cfg_perf_enable,
    input  logic                        cfg_error_enable,
    input  logic [15:0]                 cfg_pkt_mask,
    input  logic [15:0]                 cfg_perf_mask,
    input  logic [15:0]                 cfg_error_mask,
    input  logic [N_PORTS-1:0]          cfg_port_mask,

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

    initial begin
        if ((OUT_DEPTH & (OUT_DEPTH - 1)) != 0 || OUT_DEPTH < 2)
            $error("onyx_monlite: OUT_DEPTH must be a power of two >= 2");
    end

    // ------------------------------------------------------------------
    // Per-slot grant cycle (for the gather latency)
    // ------------------------------------------------------------------
    monbus_timestamp_t r_grant_cyc [SLOTS];
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int s = 0; s < SLOTS; s++) r_grant_cyc[s] <= '0;
        end else begin
            if (evt_grant_i) r_grant_cyc[evt_grant_slot_i] <= i_mon_time;
        end
    )

    // ------------------------------------------------------------------
    // Lock-wait episodes per port: duration measured, emitted on release
    // (one port per cycle is emitted; a second release the same cycle
    // waits one cycle in its own register -- the hold shifts the count,
    // not the fact)
    // ------------------------------------------------------------------
    logic [N_PORTS-1:0] r_lw_active;
    logic [15:0]        r_lw_dur [N_PORTS];
    logic [N_PORTS-1:0] r_lw_pend;          // a release waiting to be emitted
    logic [15:0]        r_lw_pend_dur [N_PORTS];
    logic [N_PORTS-1:0] w_lw_release;
    logic               w_lw_fire;
    logic [PORT_W-1:0]  w_lw_port;
    logic [15:0]        w_lw_dur_out;
    always_comb begin
        w_lw_release = r_lw_active & ~evt_lock_wait_i;
        w_lw_fire    = 1'b0;
        w_lw_port    = '0;
        w_lw_dur_out = '0;
        for (int d = N_PORTS - 1; d >= 0; d--) begin
            if (r_lw_pend[d] || w_lw_release[d]) begin
                w_lw_fire    = 1'b1;
                w_lw_port    = PORT_W'(d);
                w_lw_dur_out = r_lw_pend[d] ? r_lw_pend_dur[d] : r_lw_dur[d];
            end
        end
    end
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_lw_active <= '0;
            r_lw_pend   <= '0;
            for (int d = 0; d < N_PORTS; d++) begin
                r_lw_dur[d]      <= '0;
                r_lw_pend_dur[d] <= '0;
            end
        end else begin
            for (int d = 0; d < N_PORTS; d++) begin
                if (evt_lock_wait_i[d]) begin
                    r_lw_active[d] <= 1'b1;
                    if (!r_lw_active[d]) r_lw_dur[d] <= 16'd1;
                    else if (r_lw_dur[d] != 16'hFFFF) r_lw_dur[d] <= r_lw_dur[d] + 16'd1;
                end else begin
                    r_lw_active[d] <= 1'b0;
                end
                // a release not emitted this cycle (another port's was) parks
                if (w_lw_release[d] && !(w_lw_fire && (w_lw_port == PORT_W'(d)))) begin
                    r_lw_pend[d]     <= 1'b1;
                    r_lw_pend_dur[d] <= r_lw_dur[d];
                end else if (w_lw_fire && (w_lw_port == PORT_W'(d))) begin
                    r_lw_pend[d]     <= 1'b0;
                end
            end
        end
    )

    // ------------------------------------------------------------------
    // Event classes and their payloads this cycle
    // ------------------------------------------------------------------
    // A class fires at most once a cycle, so the per-port events (a gather
    // completed by port p's CR, a read wasted by it) are a class per port:
    // GATHER x N, READ_WASTED x N, then MEM_READ, TXN_START, ABSORB,
    // WRITEBACK, LOCK_WAIT.
    localparam int N_CL = 2 * N_PORTS + 5;
    localparam int CL_MEM = 2 * N_PORTS, CL_TXN = CL_MEM + 1, CL_ABS = CL_MEM + 2,
                   CL_WB = CL_MEM + 3, CL_LW = CL_MEM + 4;
    logic [7:0]  c_code [N_CL];
    logic [63:0] c_data [N_CL];
    logic        c_raw  [N_CL];      // the event this cycle
    logic        c_port_masked [N_CL];
    logic        c_fire [N_CL];      // the event, admitted by the masks

    // the layers: the observer, the Perf type, the type mask, then per
    // class the event mask and the port mask
    wire w_perf_on = cfg_mon_enable && cfg_perf_enable && !cfg_pkt_mask[PktTypePerf];
    wire w_err_on  = cfg_mon_enable && cfg_error_enable && !cfg_pkt_mask[PktTypeError]
                     && !cfg_error_mask[DROP_CODE[3:0]];

    wire [63:0] w_grant_data = 64'(evt_grant_port_i) | (64'(evt_grant_cls_i) << 5) | (64'(evt_grant_slot_i) << 8);
    wire [63:0] w_lw_data    = 64'(w_lw_port) | (64'(w_lw_dur_out) << 8);

    always_comb begin
        for (int p = 0; p < N_PORTS; p++) begin
            // GATHER_DONE: [7:0] slot | [8] DT | [9] PD | [15:12] answering port | [31:16] grant-to-gather cycles
            c_code[p] = 8'(ONYX_EV_GATHER_DONE);
            c_data[p] = 64'(evt_gather_slot_i[p]) | (64'(evt_gather_dt_i[p]) << 8) | (64'(evt_gather_pd_i[p]) << 9)
                      | (64'(p) << 12)
                      | (64'(16'(i_mon_time - r_grant_cyc[evt_gather_slot_i[p]])) << 16);
            c_raw[p]  = evt_gather_i[p];
            c_port_masked[p] = cfg_port_mask[p];
            c_code[N_PORTS + p] = 8'(ONYX_EV_READ_WASTED);
            c_data[N_PORTS + p] = 64'(p) << 12;
            c_raw[N_PORTS + p]  = evt_read_wasted_i[p];
            c_port_masked[N_PORTS + p] = cfg_port_mask[p];
        end
        c_code[CL_MEM] = 8'(ONYX_EV_MEM_READ);  c_data[CL_MEM] = 64'(evt_mem_ar_slot_i); c_raw[CL_MEM] = evt_mem_ar_i;
        c_code[CL_TXN] = 8'(ONYX_EV_TXN_START); c_data[CL_TXN] = w_grant_data;           c_raw[CL_TXN] = evt_grant_i;
        c_code[CL_ABS] = 8'(ONYX_EV_ABSORB);    c_data[CL_ABS] = 64'(evt_absorb_slot_i); c_raw[CL_ABS] = evt_absorb_i;
        c_code[CL_WB]  = 8'(ONYX_EV_WRITEBACK); c_data[CL_WB]  = 64'(evt_wb_port_i);     c_raw[CL_WB]  = evt_wb_i;
        c_code[CL_LW]  = 8'(ONYX_EV_LOCK_WAIT); c_data[CL_LW]  = w_lw_data;              c_raw[CL_LW]  = w_lw_fire;
        c_port_masked[CL_MEM] = 1'b0;
        c_port_masked[CL_TXN] = cfg_port_mask[evt_grant_port_i];
        c_port_masked[CL_ABS] = 1'b0;
        c_port_masked[CL_WB]  = 1'b0;
        c_port_masked[CL_LW]  = cfg_port_mask[w_lw_port];
        for (int c = 0; c < N_CL; c++)
            c_fire[c] = c_raw[c] && w_perf_on && !cfg_perf_mask[c_code[c][3:0]] && !c_port_masked[c];
    end

    // ------------------------------------------------------------------
    // Per-class holders, two deep: a class fires at most once a cycle, and
    // the MonBus takes one packet a cycle, so the holders absorb the
    // cycles where several classes fire together (a grant, a gather and a
    // memory AR land in one cycle routinely).  A class whose two entries
    // are both waiting when it fires again loses that event, counted.  The
    // drain picks one non-empty class a cycle, round-robin from the class
    // after the last pick, so no class waits behind a busier one for long.
    // ------------------------------------------------------------------
    localparam int CL_W = $clog2(N_CL);
    logic [1:0]  h_cnt [N_CL];
    logic [63:0] h_d0  [N_CL];
    logic [63:0] h_d1  [N_CL];
    logic [CL_W-1:0] r_pick_rr;

    logic            w_pick_vld;
    logic [CL_W-1:0] w_pick;
    always_comb begin
        w_pick_vld = 1'b0;
        w_pick     = '0;
        for (int k = N_CL - 1; k >= 0; k--) begin
            automatic int c = (32'(r_pick_rr) + k) % N_CL;
            if (h_cnt[c] != 2'd0) begin
                w_pick_vld = 1'b1;
                w_pick     = CL_W'(c);
            end
        end
    end

    logic w_take;
    logic [3:0] w_lost;
    always_comb begin
        w_lost = '0;
        for (int c = 0; c < N_CL; c++)
            if (c_fire[c] && (h_cnt[c] == 2'd2) && !(w_take && (w_pick == CL_W'(c))))
                w_lost = w_lost + 4'd1;
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_pick_rr <= '0;
            for (int c = 0; c < N_CL; c++) begin
                h_cnt[c] <= '0;
                h_d0[c]  <= '0;
                h_d1[c]  <= '0;
            end
        end else begin
            for (int c = 0; c < N_CL; c++) begin
                automatic logic pop  = w_take && (w_pick == CL_W'(c));
                automatic logic push = c_fire[c] && ((h_cnt[c] != 2'd2) || pop);
                if (pop) begin
                    h_d0[c] <= h_d1[c];
                end
                if (push) begin
                    // land at the first free entry after this cycle's pop
                    if ((h_cnt[c] - 2'(pop)) == 2'd0) h_d0[c] <= c_data[c];
                    else                              h_d1[c] <= c_data[c];
                end
                h_cnt[c] <= h_cnt[c] + 2'(push) - 2'(pop);
            end
            if (w_take) r_pick_rr <= CL_W'((32'(w_pick) + 1) % N_CL);
        end
    )

    // ------------------------------------------------------------------
    // Output queue (gaxi_fifo_sync, the l1_monlite idiom): one write a
    // cycle, the picked holder's head or the drop report
    // ------------------------------------------------------------------
    localparam int QW  = MONBUS_PKT_WIDTH + MONBUS_TS_WIDTH;
    localparam int OQW = (OUT_DEPTH > 1) ? $clog2(OUT_DEPTH) : 1;

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

    logic [OQW:0] r_eff_q;
    wire          w_q_empty = (r_eff_q == '0);
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) r_eff_q <= '0;
        else r_eff_q <= r_eff_q + (OQW+1)'(fifo_wr_valid) - (OQW+1)'(fifo_rd_valid && fifo_rd_ready);
    )

    // the picked head goes out when the queue takes it (its own wr_ready,
    // not a shadow count: a write the queue refuses would vanish uncounted
    // -- the first run lost one packet that way, reporting 10 of 11);
    // otherwise it waits in its holder, and only a full holder loses
    assign w_take = w_pick_vld && fifo_wr_ready;

    logic [7:0] r_dropped;
    wire w_drop_rpt = w_err_on && (r_dropped != 8'd0) && (w_lost == 4'd0) && !w_pick_vld && w_q_empty
                      && fifo_wr_ready && !`RST_ASSERTED(rst_n);
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) r_dropped <= 8'd0;
        else if (w_drop_rpt) r_dropped <= 8'd0;
        else if (r_dropped >= 8'hFE) r_dropped <= (w_lost != 4'd0) ? 8'hFF : r_dropped;
        else r_dropped <= r_dropped + 8'(w_lost);
    )

    monitor_packet_t w_out_pkt;
    assign w_out_pkt = w_pick_vld
        ? create_monitor_packet(PktTypePerf, PROTOCOL_CORE, c_code[w_pick], 9'd0, UNIT_ID, AGENT_ID, h_d0[w_pick])
        : create_monitor_packet(PktTypeError, PROTOCOL_CORE, DROP_CODE, 9'd0, UNIT_ID, AGENT_ID, 64'(r_dropped));
    assign fifo_wr_valid = w_take || w_drop_rpt;
    assign fifo_wdata    = {i_mon_time, w_out_pkt};

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_fifo;
    assign unused_fifo = &{1'b0, fifo_count, evt_ac_i};
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

endmodule : onyx_monlite
