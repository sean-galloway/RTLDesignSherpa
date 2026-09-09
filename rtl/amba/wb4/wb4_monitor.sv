// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_monitor
// Purpose: Wishbone B4 transaction monitor on the cmd/rsp queue contract,
//          reporting errors, timeouts, latency and completions as monitor
//          bus packets (protocol = PROTOCOL_WB).
//
// Documentation: docs/markdown/rtl-amba/wb4/wb4_monitor.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-09
//
//==============================================================================
// Description:
//   Watches the cmd_*/rsp_* queues of a wb4_master or wb4_slave (the
//   timing-convenient proxy for the Wishbone wires, the same place
//   apb4_monitor attaches) and emits one 128-bit monitor packet per event:
//   a completion (ACK/RTY) or error (ERR) per transfer, timeouts on a stuck
//   request or a stuck oldest termination, a latency-threshold crossing per
//   transfer, optional queue debug events, and address-range violations
//   through the shared apb_monitor_addr_check.
//
//   Transfers are tracked in an IN-ORDER queue of MAX_TRANSACTIONS entries,
//   not a slot table: Wishbone terminates in issue order, so the response
//   always pairs with the oldest open request. A slot table that picks "the
//   first active slot" mis-pairs the moment a freed slot is reused while an
//   older one is still open, which pipelined traffic does all the time.
//
// Features:
//   - Same cfg_* / monbus / status port set as apb4_monitor (family-uniform)
//   - USE_MONITOR=0 removes the body and ties the outputs
//   - N_ADDR_RANGES>0 instantiates the shared address-range checker tagged
//     PROTOCOL_WB; its packets take second priority behind the event FIFO
//   - Lossy-but-honest: a tracking overflow or a dropped packet (FIFO full)
//     is reported (WB_ERR_TRACK_LOST) or counted, never wedges the queue
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   USE_MONITOR, N_ADDR_RANGES, ADDR_WIDTH, DATA_WIDTH, UNIT_ID, AGENT_ID,
//   MAX_TRANSACTIONS (queue depth, power of two recommended),
//   MONITOR_FIFO_DEPTH (event FIFO)
//
//------------------------------------------------------------------------------
// Behavior:
//------------------------------------------------------------------------------
//   cmd handshake -> push {we, adr, sel, timestamp} at tail (or TRACK_LOST)
//   rsp handshake -> pop head; status ACK -> completion (READ/WRITE),
//                    RTY -> completion RTY, ERR -> error (if cfg_slverr_enable)
//                    latency = now - head.timestamp; > threshold -> perf
//   cmd_valid && !cmd_ready for cfg_cmd_timeout_cnt -> WB_TIMEOUT_CMD (once per stall)
//   head open for cfg_rsp_timeout_cnt                -> WB_TIMEOUT_RSP (once per entry)
//   rsp with empty queue && cfg_protocol_enable      -> WB_ERR_ORPHAN_RSP
//   FIFO write priority: error > timeout > perf > debug > completion
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - apb4_monitor.sv (the family template), apb_monitor_addr_check.sv,
//     wb4_master.sv / wb4_slave.sv (what it watches), monitor_wb4_pkg.sv
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: val/amba/test_wb4_monitor.py
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module wb4_monitor
    import monitor_common_pkg::*;   // PROTOCOL_WB, PktType*, packet builder
    import monitor_wb4_pkg::*;      // WB_ERR_*, WB_TIMEOUT_*, WB_COMPL_*, WB_PERF_*, WB_DEBUG_*
    import wb4_pkg::*;              // WB4_RSP_* status encoding
#(
    parameter bit USE_MONITOR         = 1'b1,
    parameter int N_ADDR_RANGES       = 0,
    parameter int ADDR_WIDTH          = 32,
    parameter int DATA_WIDTH          = 32,
    parameter logic [7:0]  UNIT_ID    = 8'h01,
    parameter logic [15:0] AGENT_ID   = 16'h000B,
    parameter int MAX_TRANSACTIONS    = 8,      // in-order tracking queue depth
    parameter int MONITOR_FIFO_DEPTH  = 8,
    // Short params
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = DW/8,
    parameter int STW = WB4_STATUS_WIDTH
)
(
    input  logic                     aclk,
    input  logic                     aresetn,

    // Command queue being watched
    input  logic                     cmd_valid,
    input  logic                     cmd_ready,
    input  logic                     cmd_we,
    input  logic [AW-1:0]            cmd_adr,
    input  logic [DW-1:0]            cmd_dat,
    input  logic [SW-1:0]            cmd_sel,

    // Response queue being watched
    input  logic                     rsp_valid,
    input  logic                     rsp_ready,
    input  logic [STW-1:0]           rsp_status,
    input  logic [DW-1:0]            rsp_dat,

    // Configuration - Error Detection
    input  logic                     cfg_error_enable,        // Enable error event packets
    input  logic                     cfg_timeout_enable,      // Enable timeout event packets
    input  logic                     cfg_protocol_enable,     // Enable orphan-response detection
    input  logic                     cfg_slverr_enable,       // Report ERR terminations as errors

    // Configuration - Performance Monitoring
    input  logic                     cfg_perf_enable,
    input  logic                     cfg_latency_enable,
    input  logic                     cfg_throughput_enable,   // Kept for family uniformity (no packet today)

    // Configuration - Debug
    input  logic                     cfg_debug_enable,
    input  logic                     cfg_trans_debug_enable,
    input  logic [3:0]               cfg_debug_level,

    // Configuration - Thresholds and Timeouts
    input  logic [15:0]              cfg_cmd_timeout_cnt,
    input  logic [15:0]              cfg_rsp_timeout_cnt,
    input  logic [31:0]              cfg_latency_threshold,
    input  logic [15:0]              cfg_throughput_threshold,

    // Address-range checker configuration (active when N_ADDR_RANGES > 0)
    input  logic                                                              cfg_addr_check_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0]                cfg_addr_range_enable,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0]        cfg_addr_range_low,
    input  logic [(N_ADDR_RANGES > 0 ? N_ADDR_RANGES : 1)-1:0][AW-1:0]        cfg_addr_range_high,

    // Free-running monitor-time broadcast
    input  monitor_common_pkg::monbus_timestamp_t   i_mon_time,

    // Monitor bus
    output logic                                    monbus_valid,
    input  logic                                    monbus_ready,
    output monitor_common_pkg::monitor_packet_t     monbus_packet,
    output monitor_common_pkg::monbus_timestamp_t   monbus_timestamp,

    // Status
    output logic [7:0]               active_count,
    output logic [15:0]              error_count,
    output logic [31:0]              transaction_count
);

    if (USE_MONITOR) begin : gen_monitor

    // ------------------------------------------------------------------------
    // In-order tracking queue
    // ------------------------------------------------------------------------
    localparam int QW = $clog2(MAX_TRANSACTIONS);          // index width
    localparam int CW = $clog2(MAX_TRANSACTIONS + 1);      // occupancy width

    typedef struct packed {
        logic          we;
        logic [AW-1:0] adr;
        logic [3:0]    sel4;           // low 4 select bits, for aux_data
        logic [31:0]   t_issue;
        logic          rsp_timed_out;  // WB_TIMEOUT_RSP already reported
    } track_t;

    track_t          r_q [MAX_TRANSACTIONS];
    logic [QW-1:0]   r_head, r_tail;
    logic [CW-1:0]   r_count;
    logic            w_q_empty, w_q_full;
    track_t          w_head;

    logic [31:0]     r_timestamp;
    logic [15:0]     r_error_count;
    logic [31:0]     r_transaction_count;

    logic w_cmd_handshake, w_rsp_handshake;
    logic w_push, w_pop, w_track_lost, w_orphan;

    // Timeout state (used by the tracking block below to mark the head)
    logic [15:0] r_cmd_stall_timer;
    logic        r_cmd_timeout_reported;
    logic        w_cmd_timeout_fire, w_rsp_timeout_fire;
    logic [31:0] w_head_age;

    assign w_cmd_handshake = cmd_valid && cmd_ready;
    assign w_rsp_handshake = rsp_valid && rsp_ready;
    assign w_q_empty       = (r_count == '0);
    assign w_q_full        = (32'(r_count) >= MAX_TRANSACTIONS);
    assign w_head          = r_q[r_head];
    assign w_push          = w_cmd_handshake && !w_q_full;
    assign w_track_lost    = w_cmd_handshake &&  w_q_full;
    assign w_pop           = w_rsp_handshake && !w_q_empty;
    assign w_orphan        = w_rsp_handshake &&  w_q_empty;

    assign active_count      = 8'(r_count);
    assign error_count       = r_error_count;
    assign transaction_count = r_transaction_count;

    // Completion-time figures for the head entry
    logic [31:0] w_latency;
    logic        w_is_err, w_is_rty, w_is_ack;
    assign w_latency = r_timestamp - w_head.t_issue;
    assign w_is_err  = (rsp_status == WB4_RSP_ERR);
    assign w_is_rty  = (rsp_status == WB4_RSP_RTY);
    assign w_is_ack  = !w_is_err && !w_is_rty;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_timestamp         <= '0;
            r_head              <= '0;
            r_tail              <= '0;
            r_count             <= '0;
            r_error_count       <= '0;
            r_transaction_count <= '0;
            for (int i = 0; i < MAX_TRANSACTIONS; i++) r_q[i] <= '0;
        end else begin
            r_timestamp <= r_timestamp + 1'b1;
            if (w_push) begin
                r_q[r_tail].we            <= cmd_we;
                r_q[r_tail].adr           <= cmd_adr;
                r_q[r_tail].sel4          <= 4'(cmd_sel);
                r_q[r_tail].t_issue       <= r_timestamp;
                r_q[r_tail].rsp_timed_out <= 1'b0;
                r_tail <= (32'(r_tail) == MAX_TRANSACTIONS - 1) ? '0 : r_tail + 1'b1;
            end
            if (w_pop) begin
                r_head <= (32'(r_head) == MAX_TRANSACTIONS - 1) ? '0 : r_head + 1'b1;
                r_transaction_count <= r_transaction_count + 1'b1;
            end
            r_count <= r_count + CW'(w_push) - CW'(w_pop);
            if (w_rsp_timeout_fire && !w_q_empty)
                r_q[r_head].rsp_timed_out <= 1'b1;
            if ((w_rsp_handshake && w_is_err && cfg_slverr_enable) || w_orphan || w_track_lost)
                r_error_count <= r_error_count + 1'b1;
        end
    )

    // ------------------------------------------------------------------------
    // Timeouts. cmd: a request offered and not taken; rsp: the oldest open
    // request unterminated. Each fires ONCE (per stall / per entry).
    // ------------------------------------------------------------------------
    assign w_head_age = r_timestamp - w_head.t_issue;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_cmd_stall_timer      <= '0;
            r_cmd_timeout_reported <= 1'b0;
        end else begin
            if (cmd_valid && !cmd_ready) begin
                if (r_cmd_stall_timer != 16'hFFFF) r_cmd_stall_timer <= r_cmd_stall_timer + 1'b1;
                if (w_cmd_timeout_fire) r_cmd_timeout_reported <= 1'b1;
            end else begin
                r_cmd_stall_timer      <= '0;
                r_cmd_timeout_reported <= 1'b0;
            end
        end
    )

    assign w_cmd_timeout_fire = cfg_timeout_enable && cmd_valid && !cmd_ready &&
                                !r_cmd_timeout_reported && (cfg_cmd_timeout_cnt != '0) &&
                                (r_cmd_stall_timer >= cfg_cmd_timeout_cnt);
    assign w_rsp_timeout_fire = cfg_timeout_enable && !w_q_empty && !w_head.rsp_timed_out &&
                                (cfg_rsp_timeout_cnt != '0) &&
                                (w_head_age >= 32'(cfg_rsp_timeout_cnt));

    // ------------------------------------------------------------------------
    // Debug: queue activity edges
    // ------------------------------------------------------------------------
    logic r_q_active_q;
    logic w_q_active_edge, w_q_idle_edge;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_q_active_q <= 1'b0;
        else                        r_q_active_q <= !w_q_empty;
    )
    assign w_q_active_edge = !w_q_empty &&  !r_q_active_q;
    assign w_q_idle_edge   =  w_q_empty &&   r_q_active_q;

    // ------------------------------------------------------------------------
    // Event selection (one FIFO write per clock; error > timeout > perf > debug > completion)
    // ------------------------------------------------------------------------
    typedef struct packed {
        logic [3:0]  packet_type;
        logic [7:0]  event_code;
        logic [31:0] event_data;
        logic [7:0]  aux_data;
    } monitor_entry_t;

    logic           w_fifo_wr_valid, w_fifo_wr_ready, w_fifo_rd_valid, w_fifo_rd_ready;
    monitor_entry_t w_fifo_wr_data,  w_fifo_rd_data;
    logic [7:0]     w_aux_head, w_aux_cmd;
    logic [31:0]    w_adr_head, w_adr_cmd;

    assign w_aux_head = {3'h0, w_head.sel4, w_head.we};
    assign w_aux_cmd  = {3'h0, 4'(cmd_sel), cmd_we};
    assign w_adr_head = 32'(w_head.adr);
    assign w_adr_cmd  = 32'(cmd_adr);

    always_comb begin
        w_fifo_wr_valid = 1'b0;
        w_fifo_wr_data  = '0;
        if (cfg_error_enable && w_rsp_handshake && w_is_err && cfg_slverr_enable && !w_q_empty) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data  = '{PktTypeError, WB_ERR_ERR, w_adr_head, w_aux_head};
        end else if (cfg_error_enable && cfg_protocol_enable && w_orphan) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data  = '{PktTypeError, WB_ERR_ORPHAN_RSP, 32'(rsp_dat), {6'h0, rsp_status}};
        end else if (cfg_error_enable && w_track_lost) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data  = '{PktTypeError, WB_ERR_TRACK_LOST, w_adr_cmd, w_aux_cmd};
        end else if (w_cmd_timeout_fire) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data  = '{PktTypeTimeout, WB_TIMEOUT_CMD, w_adr_cmd, r_cmd_stall_timer[7:0]};
        end else if (w_rsp_timeout_fire) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data  = '{PktTypeTimeout, WB_TIMEOUT_RSP, w_adr_head, w_head_age[7:0]};
        end else if (cfg_perf_enable && cfg_latency_enable && w_pop && (w_latency > cfg_latency_threshold)) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data  = '{PktTypePerf, w_head.we ? WB_PERF_WRITE_LATENCY : WB_PERF_READ_LATENCY,
                                w_latency, w_aux_head};
        end else if (cfg_debug_enable && cfg_trans_debug_enable && (w_q_active_edge || w_q_idle_edge)) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data  = '{PktTypeDebug, w_q_active_edge ? WB_DEBUG_QUEUE_ACTIVE : WB_DEBUG_QUEUE_IDLE,
                                {24'h0, 8'(r_count)}, 8'h0};
        end else if (w_pop && (w_is_ack || w_is_rty)) begin
            w_fifo_wr_valid = 1'b1;
            w_fifo_wr_data  = '{PktTypeCompletion,
                                w_is_rty ? WB_COMPL_RTY : (w_head.we ? WB_COMPL_WRITE : WB_COMPL_READ),
                                w_adr_head, w_aux_head};
        end
    end

    // REGISTERED=0 (mux read): rd_data is valid IN the clock of the
    // rd_valid/rd_ready handshake, which is when the packet is built below.
    // Flop mode (REGISTERED=1) presents rd_data one clock AFTER the handshake
    // (the BFM's 'fifo_flop' contract); read combinationally it re-presents
    // the popped entry for a clock on back-to-back reads, so a burst of
    // events would duplicate one packet and lose the next. Seen 2026-09-09
    // on this module's first test (TASK-086 covers the siblings).
    gaxi_fifo_sync #(
        .REGISTERED      (0),
        .DATA_WIDTH      ($bits(monitor_entry_t)),
        .DEPTH           (MONITOR_FIFO_DEPTH),
        .ALMOST_WR_MARGIN(1),
        .ALMOST_RD_MARGIN(1)
    ) monitor_fifo (
        .axi_aclk      (aclk),
        .axi_aresetn   (aresetn),
        .wr_valid      (w_fifo_wr_valid),
        .wr_ready      (w_fifo_wr_ready),
        .wr_data       (w_fifo_wr_data),
        .rd_ready      (w_fifo_rd_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count         (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid      (w_fifo_rd_valid),
        .rd_data       (w_fifo_rd_data)
    );

    // A full FIFO drops the event (lossy-but-honest, as the family does);
    // tracking is unaffected because the queue does not wait for the packet.
    /* verilator lint_off UNUSEDSIGNAL */
    logic w_fifo_drop;
    assign w_fifo_drop = w_fifo_wr_valid && !w_fifo_wr_ready;
    /* verilator lint_on UNUSEDSIGNAL */

    // ------------------------------------------------------------------------
    // Packet construction, address checker merge, output skid
    // ------------------------------------------------------------------------
    logic                                    w_monbus_pkt_valid, w_monbus_pkt_ready;
    monitor_common_pkg::monitor_packet_t     w_monbus_pkt_data, w_fifo_pkt_data;
    monitor_common_pkg::monbus_timestamp_t   w_monbus_pkt_ts;

    assign w_fifo_pkt_data = monitor_common_pkg::create_monitor_packet(
        w_fifo_rd_data.packet_type,
        monitor_common_pkg::PROTOCOL_WB,
        w_fifo_rd_data.event_code,
        9'h0,
        UNIT_ID,
        AGENT_ID,
        {24'h0, w_fifo_rd_data.aux_data, w_fifo_rd_data.event_data}
    );

    logic                                    w_addr_pkt_valid, w_addr_pkt_ready;
    monitor_common_pkg::monitor_packet_t     w_addr_pkt_data;
    monitor_common_pkg::monbus_timestamp_t   w_addr_pkt_timestamp;

    if (N_ADDR_RANGES > 0) begin : gen_addr_check
        apb_monitor_addr_check #(
            .N_ADDR_RANGES (N_ADDR_RANGES),
            .ADDR_WIDTH    (ADDR_WIDTH),
            .UNIT_ID       (UNIT_ID),
            .AGENT_ID      (AGENT_ID),
            .PROTOCOL      (monitor_common_pkg::PROTOCOL_WB)
        ) addr_check (
            .clk                   (aclk),
            .aresetn               (aresetn),
            .i_mon_time            (i_mon_time),
            .cmd_paddr             (cmd_adr),
            .cmd_pwrite            (cmd_we),
            .cmd_valid             (cmd_valid),
            .cmd_ready             (cmd_ready),
            .cfg_addr_check_enable (cfg_addr_check_enable),
            .cfg_addr_range_enable (cfg_addr_range_enable),
            .cfg_addr_range_low    (cfg_addr_range_low),
            .cfg_addr_range_high   (cfg_addr_range_high),
            .addr_pkt_valid        (w_addr_pkt_valid),
            .addr_pkt_ready        (w_addr_pkt_ready),
            .addr_pkt_data         (w_addr_pkt_data),
            .addr_pkt_timestamp    (w_addr_pkt_timestamp)
        );
    end else begin : gen_no_addr_check
        assign w_addr_pkt_valid     = 1'b0;
        assign w_addr_pkt_data      = '0;
        assign w_addr_pkt_timestamp = '0;
        /* verilator lint_off UNUSEDSIGNAL */
        logic w_unused_addr;
        assign w_unused_addr = ^{cfg_addr_check_enable, cfg_addr_range_enable,
                                 cfg_addr_range_low, cfg_addr_range_high, w_addr_pkt_ready};
        /* verilator lint_on UNUSEDSIGNAL */
    end

    always_comb begin
        if (w_fifo_rd_valid) begin
            w_monbus_pkt_valid = 1'b1;
            w_monbus_pkt_data  = w_fifo_pkt_data;
            w_monbus_pkt_ts    = i_mon_time;
        end else if (w_addr_pkt_valid) begin
            w_monbus_pkt_valid = 1'b1;
            w_monbus_pkt_data  = w_addr_pkt_data;
            w_monbus_pkt_ts    = w_addr_pkt_timestamp;
        end else begin
            w_monbus_pkt_valid = 1'b0;
            w_monbus_pkt_data  = '0;
            w_monbus_pkt_ts    = '0;
        end
    end
    assign w_fifo_rd_ready  = w_monbus_pkt_ready && w_fifo_rd_valid;
    assign w_addr_pkt_ready = w_monbus_pkt_ready && !w_fifo_rd_valid;

    localparam int MONBUS_TOTAL_W =
        monitor_common_pkg::MONBUS_PKT_WIDTH + monitor_common_pkg::MONBUS_TS_WIDTH;
    logic [MONBUS_TOTAL_W-1:0] w_skid_wr_data, w_skid_rd_data;
    assign w_skid_wr_data = {w_monbus_pkt_data, w_monbus_pkt_ts};

    gaxi_skid_buffer #(
        .DATA_WIDTH    (MONBUS_TOTAL_W),
        .DEPTH         (2)
    ) monbus_skid_buffer (
        .axi_aclk      (aclk),
        .axi_aresetn   (aresetn),
        .wr_valid      (w_monbus_pkt_valid),
        .wr_ready      (w_monbus_pkt_ready),
        .wr_data       (w_skid_wr_data),
        .rd_valid      (monbus_valid),
        .rd_ready      (monbus_ready),
        .rd_data       (w_skid_rd_data),
        /* verilator lint_off PINCONNECTEMPTY */
        .count         (),
        .rd_count      ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    assign monbus_packet    = w_skid_rd_data[MONBUS_TOTAL_W-1 -: monitor_common_pkg::MONBUS_PKT_WIDTH];
    assign monbus_timestamp = w_skid_rd_data[monitor_common_pkg::MONBUS_TS_WIDTH-1 : 0];

    // Ports kept for family uniformity that this monitor does not act on yet.
    /* verilator lint_off UNUSEDSIGNAL */
    logic w_unused;
    assign w_unused = ^{cfg_throughput_enable, cfg_debug_level, cfg_throughput_threshold, cmd_dat, rsp_dat[DW-1:1]};
    /* verilator lint_on UNUSEDSIGNAL */

`ifdef FORMAL
    logic f_past_valid;
    initial f_past_valid = 1'b0;
    always_ff @(posedge aclk) f_past_valid <= 1'b1;
    always_ff @(posedge aclk) if (f_past_valid && aresetn && $past(aresetn)) begin
        // Occupancy never exceeds the queue and tracks push/pop exactly.
        assert (32'(r_count) <= MAX_TRANSACTIONS);
        // A pop only when something is open; an orphan only when nothing is.
        assert (!w_pop || !w_q_empty);
        assert (!w_orphan || w_q_empty);
    end
`endif

    end else begin : gen_no_monitor
        assign monbus_valid      = 1'b0;
        assign monbus_packet     = '0;
        assign monbus_timestamp  = '0;
        assign active_count      = 8'h0;
        assign error_count       = 16'h0;
        assign transaction_count = 32'h0;
    end

endmodule : wb4_monitor
