// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_lookup_macro_test
// Purpose:
//   Macro composition suite 1 (Task 9.5): the LOOKUP DATAPLANE interaction
//   group -- amber_control + amber_tag_array + amber_data_array + amber_repl
//   -- pinned in isolation between the unit suites and amber_core. The group
//   carries no fill/drain/victim/snoop FUBs, so those partner handshakes stay
//   timing stubs at the boundary (D-12) exactly like the control bring-up
//   harness; the composition (arrays + repl closing control's dataplane) is
//   the real one. Pure wiring + the same two landed muxes: the data-array
//   write port (control's CPU merge wins over the fill stub's received
//   beats) and the tag-array port-B lookup (control owns port B only while
//   it services a snoop; otherwise the TB keeps its init-walk readback
//   backdoor).
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch01_overview/01_architecture.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-08

`timescale 1ns / 1ps

//==============================================================================
// Module: amber_lookup_macro_test
//==============================================================================
// Description:
//   Test-only wrapper (approved `_test` suffix) for the lookup dataplane
//   macro cell. amber_core (landed, Task 9) is the shipping integrator; this
//   wrapper exists so the control<->array<->repl interactions (hit/miss
//   decode, multi-way compare, write-hit promotion, victim-way selection,
//   init-walk interaction) run as a named regression composition with a real
//   DUT top instead of harness-side composition.
//
//   Structurally this mirrors dv/tb/amber_control_th.sv -- that harness
//   already closes exactly this group for the control unit suite; the macro
//   suite pins the same wiring as a stable, documented cell on the bring-up
//   ladder (unit -> macro -> amber_core) and carries the lookup-focused
//   scenario list (see dv/testplans/amber_lookup_macro_testplan.yaml). The
//   fill/drain/victim/snoop pins remain boundary stubs driven by the TB with
//   timing-only semantics (D-12); the data-array write mux and the port-B
//   mux are the landed idioms, unchanged.
//
//   Hierarchical taps: none beyond the landed port taps -- every observable
//   the scoreboard needs is exported on the port list (the scoreboard never
//   LHS-assigns into the DUT hierarchy; read-only hierarchical references
//   stay a TB-side concern where a scenario needs leaf internals, the same
//   sanctioned pattern as the landed suites).
//
//------------------------------------------------------------------------------
// Parameters: same geometry contract as the arrays (amber_pkg defaults).
//------------------------------------------------------------------------------
//
// Notes:
//   - No resets or registers here: this is pure wiring.
//   - Line/bus geometry stays at the pkg defaults (64 B / 64-bit); the
//     macro grid varies SETS/WAYS (tiny 16/2 + default 128/4).
//
//==============================================================================

module amber_lookup_macro_test
    import amber_pkg::*;
#(
    parameter int ADDR_WIDTH = AMBER_ADDR_WIDTH,
    parameter int SETS       = AMBER_SETS,
    parameter int WAYS       = AMBER_WAYS,
    parameter int LINE_BYTES = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH  = AMBER_BUS_WIDTH,
    localparam int SET_INDEX_WIDTH   = $clog2(SETS),
    localparam int LINE_OFFSET_WIDTH = $clog2(LINE_BYTES),
    localparam int TAG_WIDTH         = ADDR_WIDTH - SET_INDEX_WIDTH - LINE_OFFSET_WIDTH,
    localparam int TAG_STATE_WIDTH   = TAG_WIDTH + 3,
    localparam int STRB_W            = BUS_WIDTH / 8,
    localparam int FILL_BEATS        = LINE_BYTES / STRB_W,
    localparam int BEAT_INDEX_WIDTH  = $clog2(FILL_BEATS),
    localparam int WAY_INDEX_WIDTH   = $clog2(WAYS),
    localparam int MEM_ADDR_WIDTH    = SET_INDEX_WIDTH + BEAT_INDEX_WIDTH
)(
    input  logic clk,
    input  logic rst_n,

    // frontend stub <-> control request/response
    input  logic                      req_valid,
    input  logic [ADDR_WIDTH-1:0]     req_addr,
    input  logic                      req_we,
    input  logic [STRB_W-1:0]         req_be,
    input  logic [BUS_WIDTH-1:0]      req_wdata,
    output logic                      ctrl_req_ready,
    output logic                      ctrl_rsp_valid,
    output logic [BUS_WIDTH-1:0]      ctrl_rsp_data,

    // fill / drain / victim stub handshakes (TB models partner timing, D-12)
    input  logic                      fill_done,
    input  logic                      drain_done,
    output logic                      fill_start,
    output logic [ADDR_WIDTH-1:0]     fill_addr,
    output logic [2:0]                fill_req_class,
    output logic                      drain_start,
    output logic                      victim_load,
    output logic [ADDR_WIDTH-1:0]     victim_addr,
    output logic [LINE_BYTES*8-1:0]   victim_data,

    // fill-beat datapath: the stub writes received beats into the data
    // array and strobes the beat index to control (pf_data_valid update,
    // MAS ch02/06)
    input  logic                       fillbeat_wr_en,
    input  logic [MEM_ADDR_WIDTH-1:0]  fillbeat_wr_addr,
    input  logic [WAY_INDEX_WIDTH-1:0] fillbeat_wr_way,
    input  logic [BUS_WIDTH-1:0]       fillbeat_wr_data,
    input  logic [STRB_W-1:0]          fillbeat_wr_be,
    input  logic                       fill_beat_valid,
    input  logic [BEAT_INDEX_WIDTH-1:0] fill_beat_idx,

    // snoop responder core-facing handshake (stubbed at this boundary;
    // unused by the lookup scenarios -- control's port-B ownership mux is
    // still the landed one)
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

    // tag-array port B: TB backdoor read, muxed against control's snoop
    // lookup (control wins while ctrl_tag_b_req is high)
    input  logic [SET_INDEX_WIDTH-1:0] tag_b_set,
    output logic [WAYS-1:0][TAG_STATE_WIDTH-1:0] tag_b_tag_state
);

    // ------------------------------------------------------------------
    // DUT <-> array/repl wiring
    // ------------------------------------------------------------------
    logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_a_set;
    logic [WAYS-1:0][TAG_STATE_WIDTH-1:0]  ctrl_tag_a_tag_state;
    logic                                  ctrl_tag_b_req;
    logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_b_set;
    logic [WAYS-1:0][TAG_STATE_WIDTH-1:0]  ctrl_tag_b_tag_state;
    logic [MEM_ADDR_WIDTH-1:0]             ctrl_data_a_addr;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_data_a_way;
    logic [BUS_WIDTH-1:0]                  ctrl_data_a_rdata;
    logic [WAYS-1:0]                       ctrl_data_a_wr_way_onehot;
    logic [MEM_ADDR_WIDTH-1:0]             ctrl_data_a_wr_addr;
    logic [BUS_WIDTH-1:0]                  ctrl_data_a_wr_wdata;
    logic [STRB_W-1:0]                     ctrl_data_a_wr_be;
    logic [MEM_ADDR_WIDTH-1:0]             ctrl_data_b_addr;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_data_b_way;
    logic [BUS_WIDTH-1:0]                  ctrl_data_b_rdata;
    logic [SET_INDEX_WIDTH-1:0]            ctrl_repl_set;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_repl_way;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_repl_hit_way;

    amber_control #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_control (
        .clk                     (clk),
        .rst_n                   (rst_n),
        .req_valid               (req_valid),
        .req_addr                (req_addr),
        .req_we                  (req_we),
        .req_be                  (req_be),
        .req_wdata               (req_wdata),
        .ctrl_req_ready          (ctrl_req_ready),
        .ctrl_rsp_valid          (ctrl_rsp_valid),
        .ctrl_rsp_data           (ctrl_rsp_data),
        .ctrl_tag_a_set          (ctrl_tag_a_set),
        .ctrl_tag_a_tag_state    (ctrl_tag_a_tag_state),
        .ctrl_tag_a_wr_en        (tag_wr_en),
        .ctrl_tag_a_wr_way_onehot(tag_wr_way_onehot),
        .ctrl_tag_a_wr_set       (tag_wr_set),
        .ctrl_tag_a_wr_tag_state (tag_wr_tag_state),
        .ctrl_data_a_addr        (ctrl_data_a_addr),
        .ctrl_data_a_way         (ctrl_data_a_way),
        .ctrl_data_a_rdata       (ctrl_data_a_rdata),
        .ctrl_data_a_wr_en       (ctrl_data_wr_en),
        .ctrl_data_a_wr_way_onehot(ctrl_data_a_wr_way_onehot),
        .ctrl_data_a_wr_addr     (ctrl_data_a_wr_addr),
        .ctrl_data_a_wr_wdata    (ctrl_data_a_wr_wdata),
        .ctrl_data_a_wr_be       (ctrl_data_a_wr_be),
        .ctrl_tag_b_req          (ctrl_tag_b_req),
        .ctrl_tag_b_set          (ctrl_tag_b_set),
        .ctrl_tag_b_tag_state    (ctrl_tag_b_tag_state),
        .ctrl_data_b_addr        (ctrl_data_b_addr),
        .ctrl_data_b_way         (ctrl_data_b_way),
        .ctrl_data_b_rdata       (ctrl_data_b_rdata),
        .ctrl_repl_req           (repl_req),
        .ctrl_repl_set           (ctrl_repl_set),
        .ctrl_repl_way           (ctrl_repl_way),
        .ctrl_repl_hit           (repl_hit),
        .ctrl_repl_update        (repl_update),
        .ctrl_repl_hit_way       (ctrl_repl_hit_way),
        .ctrl_victim_load        (victim_load),
        .ctrl_victim_addr_in     (victim_addr),
        .ctrl_victim_data_in     (victim_data),
        .ctrl_fill_start         (fill_start),
        .ctrl_fill_addr          (fill_addr),
        .ctrl_req_class          (fill_req_class),
        .ctrl_fill_done          (fill_done),
        .ctrl_fill_beat_valid    (fill_beat_valid),
        .ctrl_fill_beat_idx      (fill_beat_idx),
        .ctrl_drain_start        (drain_start),
        .ctrl_drain_done         (drain_done),
        .ctrl_snoop_req          (snoop_req),
        .ctrl_snoop_ready        (snoop_ready),
        .ctrl_snoop_type         (snoop_type),
        .ctrl_snoop_addr         (snoop_addr),
        .ctrl_crresp             (ctrl_crresp),
        .ctrl_cddata             (ctrl_cddata),
        .ctrl_cdlast             (ctrl_cdlast),
        .ctrl_cdvalid            (ctrl_cdvalid),
        .ctrl_cdready            (cd_ready_in),
        .ctrl_init_busy          (init_busy),
        .ctrl_init_set           (init_set),
        .ctrl_state              (ctrl_state)
    );

    // Tag-array port-B mux: control owns the port only while servicing a
    // snoop (grant cycle + CTRL_SNOOP); the TB backdoor owns it otherwise.
    logic [SET_INDEX_WIDTH-1:0] tag_b_set_muxed;

    assign tag_b_set_muxed = ctrl_tag_b_req ? ctrl_tag_b_set : tag_b_set;

    amber_tag_array #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES)
    ) u_tag (
        .clk           (clk),
        .a_set         (ctrl_tag_a_set),
        .a_tag_state   (ctrl_tag_a_tag_state),
        .b_set         (tag_b_set_muxed),
        .b_tag_state   (ctrl_tag_b_tag_state),
        .wr_en         (tag_wr_en),
        .wr_way_onehot (tag_wr_way_onehot),
        .wr_set        (tag_wr_set),
        .wr_tag_state  (tag_wr_tag_state)
    );

    // the TB backdoor observes the same port-B data the DUT sees
    assign tag_b_tag_state = ctrl_tag_b_tag_state;

    // Data-array write-port mux: control (CPU merge) wins over fill beats.
    logic [WAYS-1:0] fillbeat_wr_way_onehot;

    always_comb begin
        for (int w = 0; w < WAYS; w++) begin
            fillbeat_wr_way_onehot[w] =
                (fillbeat_wr_way == WAY_INDEX_WIDTH'(w));
        end
    end

    always_comb begin
        if (ctrl_data_wr_en) begin
            data_wr_en         = 1'b1;
            data_wr_way_onehot = ctrl_data_a_wr_way_onehot;
            data_wr_addr       = ctrl_data_a_wr_addr;
            data_wr_wdata      = ctrl_data_a_wr_wdata;
            data_wr_be         = ctrl_data_a_wr_be;
        end else begin
            data_wr_en         = fillbeat_wr_en;
            data_wr_way_onehot = fillbeat_wr_way_onehot;
            data_wr_addr       = fillbeat_wr_addr;
            data_wr_wdata      = fillbeat_wr_data;
            data_wr_be         = fillbeat_wr_be;
        end
    end

    amber_data_array #(
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_data (
        .clk           (clk),
        .a_addr        (ctrl_data_a_addr),
        .a_way         (ctrl_data_a_way),
        .a_rdata       (ctrl_data_a_rdata),
        .b_addr        (ctrl_data_b_addr),
        .b_way         (ctrl_data_b_way),
        .b_rdata       (ctrl_data_b_rdata),
        .wr_en         (data_wr_en),
        .wr_way_onehot (data_wr_way_onehot),
        .wr_addr       (data_wr_addr),
        .wr_wdata      (data_wr_wdata),
        .wr_be         (data_wr_be)
    );

    amber_repl #(
        .SETS  (SETS),
        .WAYS  (WAYS)
    ) u_repl (
        .clk             (clk),
        .rst_n           (rst_n),
        .repl_req        (repl_req),
        .repl_set        (ctrl_repl_set),
        .repl_victim_way (repl_victim_way),
        .repl_hit        (repl_hit),
        .repl_update     (repl_update),
        .repl_hit_way    (ctrl_repl_hit_way)
    );

    // repl_victim_way feeds the DUT as ctrl_repl_way (wire-join here; the
    // tap above is the scoreboard's observation point).
    assign ctrl_repl_way = repl_victim_way;

    // the repl policy-update way is both the control output and the repl
    // engine's update input -- one wire, observed at the top
    assign repl_hit_way = ctrl_repl_hit_way;

endmodule : amber_lookup_macro_test
