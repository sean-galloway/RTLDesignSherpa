// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_coh_macro_test
// Purpose:
//   Macro composition suite 4 (Task 9.5): the COHERENCE/SNOOP LOOP
//   interaction group -- amber_control + amber_snoop_resp (with the
//   pending_fill_bypass / victim leaves in the loop) -- the promoted
//   Task 7 ad-hoc composition (amber_snoop_resp_th + real_control_loop)
//   as a named macro regression cell. REAL amber_control (FSM + snoop
//   service) + the landed tag/data/repl arrays + REAL amber_snoop_resp
//   (house axi4ace_snoop_slave transport + SR FSM), fill/drain partner
//   timing stubbed (D-12). The ctrl_* snoop handshake is INTERNAL to
//   this wrapper (snoop_resp <-> control); the TB observes it through
//   taps and drives snoops at the ACE boundary only.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/07_amber_snoop_resp.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-08

`timescale 1ns / 1ps

//==============================================================================
// Module: amber_coh_macro_test
//==============================================================================
// Description:
//   Test-only wrapper (approved `_test` suffix) for the coherence macro
//   cell: the Task 7 closed-loop wiring carried verbatim -- same
//   composition, same taps, same three landed muxes (data-array write
//   port: control's CPU merge wins over the fill stub's received beats;
//   tag-array port-B lookup: control owns port B only while it services
//   a snoop, otherwise the TB keeps its init-walk readback backdoor;
//   tag-array write port: TB backdoor wins over control, asserted only
//   when the FSM is quiescent -- a TB discipline). The suite pins the
//   cross-block scenarios the group owns: PassDirty forwarding,
//   snoop-vs-gather interleave, CR-after-CDLAST, zero-gap AC, plus the
//   two Task-7 found-and-fixed amber_control pins that travel with the
//   promotion (HIT_WR E->M promotion one-hot, sn_stale_gnt
//   set-narrowing -- see dv/testplans/amber_coh_macro_testplan.yaml).
//
//   Binding contract (landed RTL, binding over MAS ch02 spelling):
//   snoop_resp holds ctrl_snoop_req until ctrl_snoop_ready; ctrl_crresp
//   is valid at the grant cycle and latched by the adapter; CD beats
//   flow on ctrl_cdvalid && ctrl_cdready with ctrl_cdlast on the final
//   beat; CR is presented by the adapter only after CDLAST (IHI0022 +
//   onyx-D4).
//
//   amber_core (landed, Task 9) is the shipping integrator; this wrapper
//   keeps the group's cross-block interaction suite runnable in
//   isolation on the bring-up ladder (unit -> macro -> amber_core) and
//   hands its pinned scenarios to the Task 11 pair rig.
//
//------------------------------------------------------------------------------
// Parameters: snoop-responder geometry (ADDR/DATA_WIDTH/LINE_BYTES) plus
//   the control/array geometry (SETS/WAYS); the macro grid varies
//   SETS/WAYS (tiny 16/2 + default 128/4) with the bus/line at the pkg
//   defaults (64-bit / 64 B).
//------------------------------------------------------------------------------
//
// Notes:
//   - The TB tag-write backdoor exists for line-state seeding only (the
//     CPU path never installs E; the Table 3.0 E rows are unreachable
//     without it). The TB asserts it only when the control FSM is
//     observably IDLE and no snoop is in flight, so the mux never sees
//     a real collision.
//   - Everything here is combinationally wired -- the only registers
//     belong to the DUTs.
//
//==============================================================================

module amber_coh_macro_test
    import amber_pkg::*;
#(
    parameter int ADDR_WIDTH = AMBER_ADDR_WIDTH,
    parameter int DATA_WIDTH = AMBER_BUS_WIDTH,
    parameter int LINE_BYTES = AMBER_LINE_BYTES,
    parameter int SETS       = AMBER_SETS,
    parameter int WAYS       = AMBER_WAYS,
    localparam int SET_INDEX_WIDTH   = $clog2(SETS),
    localparam int LINE_OFFSET_WIDTH = $clog2(LINE_BYTES),
    localparam int TAG_WIDTH         = ADDR_WIDTH - SET_INDEX_WIDTH - LINE_OFFSET_WIDTH,
    localparam int TAG_STATE_WIDTH   = TAG_WIDTH + 3,
    localparam int STRB_W            = DATA_WIDTH / 8,
    localparam int FILL_BEATS        = LINE_BYTES / STRB_W,
    localparam int BEAT_INDEX_WIDTH  = $clog2(FILL_BEATS),
    localparam int WAY_INDEX_WIDTH   = $clog2(WAYS),
    localparam int MEM_ADDR_WIDTH    = SET_INDEX_WIDTH + BEAT_INDEX_WIDTH
)(
    input  logic clk,
    input  logic rst_n,

    // ------------------------------------------------------------------
    // ACE snoop pins (AXI4ACESnoopMaster BFM attaches here)
    // ------------------------------------------------------------------
    input  logic [ADDR_WIDTH-1:0]   m_axi_acaddr,
    input  logic [3:0]              m_axi_acsnoop,
    input  logic [2:0]              m_axi_acprot,
    input  logic                    m_axi_acvalid,
    output logic                    m_axi_acready,
    output logic [4:0]              m_axi_crresp,
    output logic                    m_axi_crvalid,
    input  logic                    m_axi_crready,
    output logic [DATA_WIDTH-1:0]   m_axi_cddata,
    output logic                    m_axi_cdlast,
    output logic                    m_axi_cdvalid,
    input  logic                    m_axi_cdready,

    // ------------------------------------------------------------------
    // frontend stub <-> control request/response
    // ------------------------------------------------------------------
    input  logic                      req_valid,
    input  logic [ADDR_WIDTH-1:0]     req_addr,
    input  logic                      req_we,
    input  logic [STRB_W-1:0]         req_be,
    input  logic [DATA_WIDTH-1:0]     req_wdata,
    output logic                      ctrl_req_ready,
    output logic                      ctrl_rsp_valid,
    output logic [DATA_WIDTH-1:0]     ctrl_rsp_data,

    // ------------------------------------------------------------------
    // fill / drain / victim stub handshakes (TB models partner timing, D-12)
    // ------------------------------------------------------------------
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
    // array and strobes the beat index to control (pf_data_valid update)
    input  logic                       fillbeat_wr_en,
    input  logic [MEM_ADDR_WIDTH-1:0]  fillbeat_wr_addr,
    input  logic [WAY_INDEX_WIDTH-1:0] fillbeat_wr_way,
    input  logic [DATA_WIDTH-1:0]      fillbeat_wr_data,
    input  logic [STRB_W-1:0]          fillbeat_wr_be,
    input  logic                       fill_beat_valid,
    input  logic [BEAT_INDEX_WIDTH-1:0] fill_beat_idx,

    // ------------------------------------------------------------------
    // TB tag-write backdoor (line-state seeding; TB asserts only when
    // quiescent -- see header Notes)
    // ------------------------------------------------------------------
    input  logic                       tb_tag_wr_en,
    input  logic [WAYS-1:0]            tb_tag_wr_way_onehot,
    input  logic [SET_INDEX_WIDTH-1:0] tb_tag_wr_set,
    input  logic [TAG_STATE_WIDTH-1:0] tb_tag_wr_tag_state,

    // init-walk status + FSM observability
    output logic                      init_busy,
    output logic [SET_INDEX_WIDTH-1:0] init_set,
    output logic [3:0]                ctrl_state,

    // snoop-responder handshake taps (observation only; the real handshake
    // is internal to this harness)
    output logic                      snoop_req,
    output logic                      snoop_ready,
    output logic [4:0]                ctrl_crresp,
    output logic [DATA_WIDTH-1:0]     ctrl_cddata,
    output logic                      ctrl_cdlast,
    output logic                      ctrl_cdvalid,
    output logic                      ctrl_cdready,

    // scoreboard observation taps (array write ports + repl interface)
    output logic                      tag_wr_en,
    output logic [WAYS-1:0]           tag_wr_way_onehot,
    output logic [SET_INDEX_WIDTH-1:0] tag_wr_set,
    output logic [TAG_STATE_WIDTH-1:0] tag_wr_tag_state,
    output logic                      ctrl_data_wr_en,
    output logic                      data_wr_en,
    output logic [WAYS-1:0]           data_wr_way_onehot,
    output logic [MEM_ADDR_WIDTH-1:0] data_wr_addr,
    output logic [DATA_WIDTH-1:0]     data_wr_wdata,
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
    logic                                  ctrl_tag_a_wr_en;
    logic [WAYS-1:0]                       ctrl_tag_a_wr_way_onehot;
    logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_a_wr_set;
    logic [TAG_STATE_WIDTH-1:0]            ctrl_tag_a_wr_tag_state;
    logic                                  ctrl_tag_b_req;
    logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_b_set;
    logic [WAYS-1:0][TAG_STATE_WIDTH-1:0]  ctrl_tag_b_tag_state;
    logic [MEM_ADDR_WIDTH-1:0]             ctrl_data_a_addr;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_data_a_way;
    logic [DATA_WIDTH-1:0]                 ctrl_data_a_rdata;
    logic [WAYS-1:0]                       ctrl_data_a_wr_way_onehot;
    logic [MEM_ADDR_WIDTH-1:0]             ctrl_data_a_wr_addr;
    logic [DATA_WIDTH-1:0]                 ctrl_data_a_wr_wdata;
    logic [STRB_W-1:0]                     ctrl_data_a_wr_be;
    logic [MEM_ADDR_WIDTH-1:0]             ctrl_data_b_addr;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_data_b_way;
    logic [DATA_WIDTH-1:0]                 ctrl_data_b_rdata;
    logic [SET_INDEX_WIDTH-1:0]            ctrl_repl_set;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_repl_way;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_repl_hit_way;

    // snoop responder <-> control handshake (internal; tapped at the top)
    logic                                  snoop_req_int;
    logic                                  snoop_ready_int;
    logic [4:0]                            ctrl_crresp_int;
    logic [DATA_WIDTH-1:0]                 ctrl_cddata_int;
    logic                                  ctrl_cdlast_int;
    logic                                  ctrl_cdvalid_int;

    // ------------------------------------------------------------------
    // The snoop-responder <-> control handshake: internal wires, observed
    // at the top through the taps declared in the port list.
    // ------------------------------------------------------------------
    logic [2:0]                w_snoop_type;
    logic [ADDR_WIDTH-1:0]     w_snoop_addr;

    assign snoop_req   = snoop_req_int;
    assign snoop_ready = snoop_ready_int;
    assign ctrl_crresp = ctrl_crresp_int;
    assign ctrl_cddata = ctrl_cddata_int;
    assign ctrl_cdlast = ctrl_cdlast_int;
    assign ctrl_cdvalid = ctrl_cdvalid_int;

    amber_control #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (DATA_WIDTH)
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
        .ctrl_tag_a_wr_en        (ctrl_tag_a_wr_en),
        .ctrl_tag_a_wr_way_onehot(ctrl_tag_a_wr_way_onehot),
        .ctrl_tag_a_wr_set       (ctrl_tag_a_wr_set),
        .ctrl_tag_a_wr_tag_state (ctrl_tag_a_wr_tag_state),
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
        .ctrl_snoop_req          (snoop_req_int),
        .ctrl_snoop_ready        (snoop_ready_int),
        .ctrl_snoop_type         (w_snoop_type),
        .ctrl_snoop_addr         (w_snoop_addr),
        .ctrl_crresp             (ctrl_crresp_int),
        .ctrl_cddata             (ctrl_cddata_int),
        .ctrl_cdlast             (ctrl_cdlast_int),
        .ctrl_cdvalid            (ctrl_cdvalid_int),
        .ctrl_cdready            (ctrl_cdready),
        .ctrl_init_busy          (init_busy),
        .ctrl_init_set           (init_set),
        .ctrl_state              (ctrl_state)
    );

    // ------------------------------------------------------------------
    // The ACE snoop responder: transport + SR FSM + ACSNOOP translation.
    // Its core-facing handshake is wired straight to amber_control; the
    // taps above observe the same wires.
    // ------------------------------------------------------------------
    amber_snoop_resp #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .LINE_BYTES (LINE_BYTES)
    ) u_snoop_resp (
        .aclk           (clk),
        .aresetn        (rst_n),
        .m_axi_acaddr   (m_axi_acaddr),
        .m_axi_acsnoop  (m_axi_acsnoop),
        .m_axi_acprot   (m_axi_acprot),
        .m_axi_acvalid  (m_axi_acvalid),
        .m_axi_acready  (m_axi_acready),
        .m_axi_crresp   (m_axi_crresp),
        .m_axi_crvalid  (m_axi_crvalid),
        .m_axi_crready  (m_axi_crready),
        .m_axi_cddata   (m_axi_cddata),
        .m_axi_cdlast   (m_axi_cdlast),
        .m_axi_cdvalid  (m_axi_cdvalid),
        .m_axi_cdready  (m_axi_cdready),
        .ctrl_snoop_req (snoop_req_int),
        .ctrl_snoop_addr(w_snoop_addr),
        .ctrl_snoop_type(w_snoop_type),
        .ctrl_snoop_ready(snoop_ready_int),
        .ctrl_crresp    (ctrl_crresp_int),
        .ctrl_cddata    (ctrl_cddata_int),
        .ctrl_cdlast    (ctrl_cdlast_int),
        .ctrl_cdvalid   (ctrl_cdvalid_int),
        .ctrl_cdready   (ctrl_cdready)
    );

    // ------------------------------------------------------------------
    // Tag-array write-port mux: control's own writes vs the TB backdoor.
    // The TB backdoor wins by construction (asserted only when control is
    // quiescent); the scoreboard observes the muxed port plus both enables
    // so every write is attributable.
    // ------------------------------------------------------------------
    assign tag_wr_en         = ctrl_tag_a_wr_en | tb_tag_wr_en;
    assign tag_wr_way_onehot = tb_tag_wr_en ? tb_tag_wr_way_onehot
                                            : ctrl_tag_a_wr_way_onehot;
    assign tag_wr_set        = tb_tag_wr_en ? tb_tag_wr_set
                                            : ctrl_tag_a_wr_set;
    assign tag_wr_tag_state  = tb_tag_wr_en ? tb_tag_wr_tag_state
                                            : ctrl_tag_a_wr_tag_state;

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

    // ------------------------------------------------------------------
    // Data-array write-port mux: control (CPU merge) wins over fill beats.
    // ------------------------------------------------------------------
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
        .BUS_WIDTH  (DATA_WIDTH)
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

endmodule : amber_coh_macro_test
