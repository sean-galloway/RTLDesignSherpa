// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_monlite_th
// Purpose:
//   Test harness for amber_monlite (Task 8, MAS ch04): the amber_frontend_th
//   closure (REAL amber_cpu_frontend + REAL amber_control + landed arrays)
//   plus amber_monlite tapped per the MAS ch04 emit points. The observer
//   drives nothing in the closure -- its only outputs are the monbus
//   handshake pins. Taps that correspond to harness-visible wires come from
//   the closure top; payload taps of control-internal registers use
//   read-only hierarchical references (simulation-only, harness-local --
//   amber_core owns the real wiring in integration).
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch04_monbus_observation/01_event_map.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-08

`timescale 1ns / 1ps

//==============================================================================
// Module: amber_monlite_th
//==============================================================================
// Description:
//   amber_frontend_th u_core carries the whole closure; amber_monlite
//   u_monlite observes it. USE_MONITOR=0 ties the observer off (the
//   present-vs-absent "absent" configuration, house gen_no_monitor idiom).
//
//   Tap wiring:
//     - state / strobes / fill / drain / victim / tag-write taps come from
//       the closure's own pins (ctrl_state, victim_load, victim_addr,
//       fill_start/fill_addr, drain_start/drain_done, tag_wr_*, snoop
//       handshake, repl_victim_way) -- the same signals amber_core will
//       wire at integration.
//     - payload taps of control-internal registers (the latched request
//       context, hit resolution, snoop resolution) are read hierarchically
//       from u_core.u_control -- read-only, never driven.
//
//------------------------------------------------------------------------------
// Parameters: closure geometry + USE_MONITOR.
//------------------------------------------------------------------------------
//
// Notes:
//   - No resets or registers here beyond the DUTs: pure wiring + taps.
//   - mon_time is the 64-bit side-band timestamp the TB drives (a cycle
//     counter); the packet stream is scored against it.
//
//==============================================================================

module amber_monlite_th
    import amber_pkg::*;
#(
    parameter int ADDR_WIDTH  = AMBER_ADDR_WIDTH,
    parameter int SETS        = AMBER_SETS,
    parameter int WAYS        = AMBER_WAYS,
    parameter int LINE_BYTES  = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH   = AMBER_BUS_WIDTH,
    parameter bit USE_MONITOR = 1'b1,
    localparam int SET_INDEX_WIDTH   = $clog2(SETS),
    localparam int LINE_OFFSET_WIDTH = $clog2(LINE_BYTES),
    localparam int TAG_WIDTH         = ADDR_WIDTH - SET_INDEX_WIDTH - LINE_OFFSET_WIDTH,
    localparam int TAG_STATE_WIDTH   = TAG_WIDTH + 3,
    localparam int STRB_W            = BUS_WIDTH / 8,
    localparam int FILL_BEATS        = LINE_BYTES / STRB_W,
    localparam int BEAT_INDEX_WIDTH  = $clog2(FILL_BEATS),
    localparam int WAY_INDEX_WIDTH   = $clog2(WAYS),
    localparam int MEM_ADDR_WIDTH    = SET_INDEX_WIDTH + BEAT_INDEX_WIDTH,
    localparam int CPU_REQ_W         = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH,
    localparam int CPU_RSP_W         = BUS_WIDTH
)(
    input  logic clk,
    input  logic rst_n,

    // CPU GAXI request channel (write stream): packed {addr, we, be, wdata}
    input  logic                      cpu_req_wr_valid,
    output logic                      cpu_req_wr_ready,
    input  logic [CPU_REQ_W-1:0]      cpu_req_wr_data,

    // CPU GAXI response channel (read stream): packed {rdata}
    output logic                      cpu_rsp_rd_valid,
    input  logic                      cpu_rsp_rd_ready,
    output logic [CPU_RSP_W-1:0]      cpu_rsp_rd_data,

    // fill / drain / victim stub handshakes
    input  logic                      fill_done,
    input  logic                      drain_done,
    output logic                      fill_start,
    output logic [ADDR_WIDTH-1:0]     fill_addr,
    output logic [2:0]                fill_req_class,
    output logic                      drain_start,
    output logic                      victim_load,
    output logic [ADDR_WIDTH-1:0]     victim_addr,
    output logic [LINE_BYTES*8-1:0]   victim_data,

    // fill-beat datapath (TB stub writes received beats into the data array)
    input  logic                       fillbeat_wr_en,
    input  logic [MEM_ADDR_WIDTH-1:0]  fillbeat_wr_addr,
    input  logic [WAY_INDEX_WIDTH-1:0] fillbeat_wr_way,
    input  logic [BUS_WIDTH-1:0]       fillbeat_wr_data,
    input  logic [STRB_W-1:0]          fillbeat_wr_be,
    input  logic                       fill_beat_valid,
    input  logic [BEAT_INDEX_WIDTH-1:0] fill_beat_idx,

    // snoop responder core-facing handshake
    input  logic                      snoop_req,
    input  logic [2:0]                snoop_type,
    input  logic [ADDR_WIDTH-1:0]     snoop_addr,
    input  logic                      cd_ready_in,
    output logic                      snoop_ready,
    output logic [AMBER_CRRESP_WIDTH-1:0] ctrl_crresp,
    output logic                      ctrl_cdvalid,
    output logic                      ctrl_cdlast,
    output logic [BUS_WIDTH-1:0]      ctrl_cddata,

    // init-walk status + FSM observability
    output logic                      init_busy,
    output logic [SET_INDEX_WIDTH-1:0] init_set,
    output logic [3:0]                ctrl_state,

    // frontend <-> control handshake observation taps
    output logic                      fe_req_valid,
    output logic                      ctrl_req_ready,
    output logic                      ctrl_rsp_valid,
    output logic [BUS_WIDTH-1:0]      ctrl_rsp_data,

    // scoreboard observation taps (array write ports + repl interface)
    output logic                      tag_wr_en,
    output logic [WAYS-1:0]           tag_wr_way_onehot,
    output logic [SET_INDEX_WIDTH-1:0] tag_wr_set,
    output logic [TAG_STATE_WIDTH-1:0] tag_wr_tag_state,
    output logic                      ctrl_data_wr_en,
    output logic                      data_wr_en,
    output logic [WAYS-1:0]           data_wr_way_onehot,
    output logic [MEM_ADDR_WIDTH-1:0] data_wr_addr,
    output logic [BUS_WIDTH-1:0]      data_wr_wdata,
    output logic [STRB_W-1:0]         data_wr_be,
    output logic                      repl_req,
    output logic                      repl_hit,
    output logic                      repl_update,
    output logic [WAY_INDEX_WIDTH-1:0] repl_hit_way,
    output logic [WAY_INDEX_WIDTH-1:0] repl_victim_way,

    // tag-array port B: TB backdoor read
    input  logic [SET_INDEX_WIDTH-1:0] tag_b_set,
    output logic [WAYS-1:0][TAG_STATE_WIDTH-1:0] tag_b_tag_state,

    // MonBus observation stream
    input  logic [63:0]               mon_time,
    output logic                      monbus_valid,
    input  logic                      monbus_ready,
    output logic [127:0]              monbus_packet,
    output logic [63:0]               monbus_timestamp,
    output logic [7:0]                monbus_dropped
);

    // ------------------------------------------------------------------
    // The closure under observation
    // ------------------------------------------------------------------
    amber_frontend_th #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_core (
        .clk               (clk),
        .rst_n             (rst_n),
        .cpu_req_wr_valid  (cpu_req_wr_valid),
        .cpu_req_wr_ready  (cpu_req_wr_ready),
        .cpu_req_wr_data   (cpu_req_wr_data),
        .cpu_rsp_rd_valid  (cpu_rsp_rd_valid),
        .cpu_rsp_rd_ready  (cpu_rsp_rd_ready),
        .cpu_rsp_rd_data   (cpu_rsp_rd_data),
        .fill_done         (fill_done),
        .drain_done        (drain_done),
        .fill_start        (fill_start),
        .fill_addr         (fill_addr),
        .fill_req_class    (fill_req_class),
        .drain_start       (drain_start),
        .victim_load       (victim_load),
        .victim_addr       (victim_addr),
        .victim_data       (victim_data),
        .fillbeat_wr_en    (fillbeat_wr_en),
        .fillbeat_wr_addr  (fillbeat_wr_addr),
        .fillbeat_wr_way   (fillbeat_wr_way),
        .fillbeat_wr_data  (fillbeat_wr_data),
        .fillbeat_wr_be    (fillbeat_wr_be),
        .fill_beat_valid   (fill_beat_valid),
        .fill_beat_idx     (fill_beat_idx),
        .snoop_req         (snoop_req),
        .snoop_type        (snoop_type),
        .snoop_addr        (snoop_addr),
        .cd_ready_in       (cd_ready_in),
        .snoop_ready       (snoop_ready),
        .ctrl_crresp       (ctrl_crresp),
        .ctrl_cdvalid      (ctrl_cdvalid),
        .ctrl_cdlast       (ctrl_cdlast),
        .ctrl_cddata       (ctrl_cddata),
        .init_busy         (init_busy),
        .init_set          (init_set),
        .ctrl_state        (ctrl_state),
        .fe_req_valid      (fe_req_valid),
        .ctrl_req_ready    (ctrl_req_ready),
        .ctrl_rsp_valid    (ctrl_rsp_valid),
        .ctrl_rsp_data     (ctrl_rsp_data),
        .tag_wr_en         (tag_wr_en),
        .tag_wr_way_onehot (tag_wr_way_onehot),
        .tag_wr_set        (tag_wr_set),
        .tag_wr_tag_state  (tag_wr_tag_state),
        .ctrl_data_wr_en   (ctrl_data_wr_en),
        .data_wr_en        (data_wr_en),
        .data_wr_way_onehot(data_wr_way_onehot),
        .data_wr_addr      (data_wr_addr),
        .data_wr_wdata     (data_wr_wdata),
        .data_wr_be        (data_wr_be),
        .repl_req          (repl_req),
        .repl_hit          (repl_hit),
        .repl_update       (repl_update),
        .repl_hit_way      (repl_hit_way),
        .repl_victim_way   (repl_victim_way),
        .tag_b_set         (tag_b_set),
        .tag_b_tag_state   (tag_b_tag_state)
    );

    // ------------------------------------------------------------------
    // Observer taps
    // ------------------------------------------------------------------
    // tag-write one-hot -> way index (single-bit one-hot on every non-INIT
    // write; INIT writes are all-ones and suppressed inside the observer)
    logic [WAY_INDEX_WIDTH-1:0] tap_tag_wr_way;

    always_comb begin
        tap_tag_wr_way = '0;
        for (int w = 0; w < WAYS; w++) begin
            if (tag_wr_way_onehot[w]) begin
                tap_tag_wr_way = WAY_INDEX_WIDTH'(w);
            end
        end
    end

    // old-state resolution per write cause: FILL_WRITE installs over an
    // Invalid line unless it is an upgrade commit (upgr_q), which rewrites
    // the hit way S->M; HIT_WR promotes the hit state; SNOOP rewrites the
    // resolved reference state
    logic [2:0] tap_state_old;

    always_comb begin
        unique case (ctrl_state)
            AMBER_CTRL_SNOOP:      tap_state_old = u_core.u_control.sn_hit_state_q;
            AMBER_CTRL_HIT_WR:     tap_state_old = u_core.u_control.hit_state_q;
            AMBER_CTRL_FILL_WRITE: tap_state_old = u_core.u_control.upgr_q
                                                   ? u_core.u_control.hit_state_q
                                                   : AMBER_STATE_I;
            default:               tap_state_old = AMBER_STATE_I;
        endcase
    end

    amber_monlite #(
        .ADDR_WIDTH  (ADDR_WIDTH),
        .SETS        (SETS),
        .WAYS        (WAYS),
        .LINE_BYTES  (LINE_BYTES),
        .BUS_WIDTH   (BUS_WIDTH),
        .USE_MONITOR (USE_MONITOR)
    ) u_monlite (
        .clk                 (clk),
        .rst_n               (rst_n),
        .tap_ctrl_state      (ctrl_state),
        .tap_hit_set         (u_core.u_control.req_set),
        .tap_hit_way         (u_core.u_control.hit_way_q),
        .tap_hit_state_before(u_core.u_control.hit_state_q),
        .tap_req_we          (u_core.u_control.req_we_q),
        .tap_miss_set        (u_core.u_control.req_set),
        .tap_miss_class      (2'(AMBER_MISS_UNKNOWN)),
        .tap_snoop_fire      (snoop_req && snoop_ready),
        .tap_snoop_type      (snoop_type),
        .tap_snoop_hit       (u_core.u_control.sn_hit_any),
        .tap_snoop_resp      (ctrl_crresp),
        .tap_victim_load     (victim_load),
        .tap_victim_addr     (victim_addr),
        .tap_victim_way      (u_core.u_control.victim_way_q),
        .tap_victim_state    (u_core.u_control.mv_victim_state),
        .tap_tag_wr_en       (tag_wr_en),
        .tap_tag_wr_set      (tag_wr_set),
        .tap_tag_wr_way      (tap_tag_wr_way),
        .tap_tag_wr_new_state(tag_wr_tag_state[2:0]),
        .tap_state_old       (tap_state_old),
        .tap_fill_addr       (fill_addr),
        .tap_drain_done      (drain_done),
        .i_mon_time          (mon_time),
        .monbus_valid        (monbus_valid),
        .monbus_ready        (monbus_ready),
        .monbus_packet       (monbus_packet),
        .monbus_timestamp    (monbus_timestamp),
        .dropped_count       (monbus_dropped)
    );

endmodule : amber_monlite_th
