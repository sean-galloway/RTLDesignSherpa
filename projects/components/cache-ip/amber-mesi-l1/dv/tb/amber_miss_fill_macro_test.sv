// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_miss_fill_macro_test
// Purpose:
//   Macro composition suite 2 (Task 9.5): the MISS/FILL PATH interaction
//   group -- amber_control (with the pending_fill_bypass leaf) + the REAL
//   amber_fill engine -- pinned in isolation. The fill engine closes with
//   its house axi4_master_rd transport (DECISION D3, the fill/drain unit
//   rig's closure) and the wrapper exposes the transport's m_axi AR/R
//   memory side at the top for the cocotb TB's AXI4 slave responder.
//   Drain/victim/snoop stay boundary stubs (D-12): the drain handshake is
//   a TB timing model, snoops enter on the control-facing pins exactly
//   like the control suite.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/06_fill_drain.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-08

`timescale 1ns / 1ps

//==============================================================================
// Module: amber_miss_fill_macro_test
//==============================================================================
// Description:
//   Test-only wrapper (approved `_test` suffix) for the miss/fill macro
//   cell. amber_core (landed, Task 9) is the shipping integrator; this
//   wrapper puts the REAL fill orchestration in the loop while the rest
//   of the partner set stays stubbed, so the cross-block pins this group
//   owns run against the engine instead of a timing model:
//
//     * fill orchestration through the real AR/R protocol (the stub could
//       not observe AR channel shape: arlen/arsize/arburst/araddr);
//     * beat gathering through the R staging FIFO into the data array
//       (wrapper-internal write mux, the landed core idiom);
//     * upgrade no-fetch -- CLEAN_UNIQUE must never raise ARVALID;
//     * killed-fill re-fetch -- a snoop-killed pending line re-issues AR
//       for real (the stub re-asserted fill_start; the engine must
//       re-orchestrate the burst);
//     * mid-fill snoop service against beats arriving on the real R
//       channel (the pending-fill bypass reads the array as beats land).
//
//   Data-array write-port arbitration (control's CPU merge wins over fill
//   beats, deterministic priority, never simultaneous by construction) is
//   the landed core idiom verbatim: fill beats install into the victim way
//   at {fill set, beat idx}, with the install way tapped READ-ONLY from
//   u_control.victim_way_q -- the same sanctioned hierarchical reference
//   amber_core documents (the wrapper never LHS-assigns DUT internals).
//
//   Pure wiring + the landed muxes; the only registers belong to the
//   DUTs. The scoreboard observes the muxed array write ports, the repl
//   interface, the fill handshake taps and the m_axi pins at the top.
//
//------------------------------------------------------------------------------
// Parameters: same geometry contract as the other amber blocks.
//------------------------------------------------------------------------------
//
// Notes:
//   - Single clock / active-low reset (clk / rst_n).
//   - Line/bus geometry stays at the pkg defaults (64 B / 64-bit,
//     FILL_BEATS=8); the macro grid varies SETS/WAYS (tiny 16/2 +
//     default 128/4).
//
//==============================================================================

module amber_miss_fill_macro_test
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

    // snoop responder core-facing handshake (stubbed at this boundary;
    // the TB drives the amber_snoop_resp core-facing contract per D-12)
    input  logic                      snoop_req,
    input  logic [2:0]                snoop_type,
    input  logic [ADDR_WIDTH-1:0]     snoop_addr,
    input  logic                      cd_ready_in,
    output logic                      snoop_ready,
    output logic [AMBER_CRRESP_WIDTH-1:0] ctrl_crresp,
    output logic                      ctrl_cdvalid,
    output logic                      ctrl_cdlast,
    output logic [BUS_WIDTH-1:0]      ctrl_cddata,

    // drain / victim stub handshakes (TB models partner timing, D-12)
    input  logic                      drain_done,
    output logic                      drain_start,
    output logic                      victim_load,
    output logic [ADDR_WIDTH-1:0]     victim_addr,
    output logic [LINE_BYTES*8-1:0]   victim_data,

    // m_axi memory side (the TB's AXI4 read responder closes here; AR/R
    // belong to the internal axi4_master_rd transport)
    output logic [7:0]                m_axi_arid,
    output logic [ADDR_WIDTH-1:0]     m_axi_araddr,
    output logic [7:0]                m_axi_arlen,
    output logic [2:0]                m_axi_arsize,
    output logic [1:0]                m_axi_arburst,
    output logic                      m_axi_arlock,
    output logic [3:0]                m_axi_arcache,
    output logic [2:0]                m_axi_arprot,
    output logic [3:0]                m_axi_arqos,
    output logic [3:0]                m_axi_arregion,
    output logic [0:0]                m_axi_aruser,
    output logic                      m_axi_arvalid,
    input  logic                      m_axi_arready,
    input  logic [7:0]                m_axi_rid,
    input  logic [BUS_WIDTH-1:0]      m_axi_rdata,
    input  logic [1:0]                m_axi_rresp,
    input  logic                      m_axi_rlast,
    input  logic [0:0]                m_axi_ruser,
    input  logic                      m_axi_rvalid,
    output logic                      m_axi_rready,

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

    // fill handshake taps (fill_start is control's launch strobe; done /
    // beats come back from the REAL engine)
    output logic                      fill_start,
    output logic [ADDR_WIDTH-1:0]     fill_addr,
    output logic [2:0]                fill_req_class,
    output logic                      fill_done,
    output logic                      fill_beat_valid,
    output logic [BEAT_INDEX_WIDTH-1:0] fill_beat_idx,

    // tag-array port B: TB backdoor read, muxed against control's snoop
    // lookup (control wins while ctrl_tag_b_req is high)
    input  logic [SET_INDEX_WIDTH-1:0] tag_b_set,
    output logic [WAYS-1:0][TAG_STATE_WIDTH-1:0] tag_b_tag_state
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the FUBs)
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("amber_miss_fill_macro_test: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("amber_miss_fill_macro_test: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
            $error("amber_miss_fill_macro_test: LINE_BYTES / BUS_WIDTH*8 must be a power of two");
        if (WAYS < 2)
            $error("amber_miss_fill_macro_test: WAYS must be >= 2");
    end

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

    // fill datapath: engine -> control (pf beat accounting) and engine ->
    // data array (beat payload, muxed against control's CPU merge)
    logic [BUS_WIDTH-1:0]                  fill_beat_data;

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

    // ------------------------------------------------------------------
    // The REAL fill path: amber_fill -> axi4_master_rd -> m_axi AR/R.
    // ------------------------------------------------------------------
    logic [7:0]          fill_arid;
    logic [ADDR_WIDTH-1:0] fill_araddr;
    logic [7:0]          fill_arlen;
    logic [2:0]          fill_arsize;
    logic [1:0]          fill_arburst;
    logic                fill_arlock;
    logic [3:0]          fill_arcache;
    logic [2:0]          fill_arprot;
    logic [3:0]          fill_arqos;
    logic [3:0]          fill_arregion;
    logic [0:0]          fill_aruser;
    logic                fill_arvalid;
    logic                fill_arready;
    logic [7:0]          fill_rid;
    logic [BUS_WIDTH-1:0] fill_rdata;
    logic [1:0]          fill_rresp;
    logic                fill_rlast;
    logic [0:0]          fill_ruser;
    logic                fill_rvalid;
    logic                fill_rready;

    amber_fill #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_fill (
        .clk               (clk),
        .rst_n             (rst_n),
        .fill_start        (fill_start),
        .fill_addr         (fill_addr),
        .fill_req_class    (fill_req_class),
        .fill_done         (fill_done),
        .fill_beat_valid   (fill_beat_valid),
        .fill_beat_data    (fill_beat_data),
        .fill_beat_idx     (fill_beat_idx),
        .fill_last         (),
        .fub_axi_arid      (fill_arid),
        .fub_axi_araddr    (fill_araddr),
        .fub_axi_arlen     (fill_arlen),
        .fub_axi_arsize    (fill_arsize),
        .fub_axi_arburst   (fill_arburst),
        .fub_axi_arlock    (fill_arlock),
        .fub_axi_arcache   (fill_arcache),
        .fub_axi_arprot    (fill_arprot),
        .fub_axi_arqos     (fill_arqos),
        .fub_axi_arregion  (fill_arregion),
        .fub_axi_aruser    (fill_aruser),
        .fub_axi_arvalid   (fill_arvalid),
        .fub_axi_arready   (fill_arready),
        .fub_axi_rid       (fill_rid),
        .fub_axi_rdata     (fill_rdata),
        .fub_axi_rresp     (fill_rresp),
        .fub_axi_rlast     (fill_rlast),
        .fub_axi_ruser     (fill_ruser),
        .fub_axi_rvalid    (fill_rvalid),
        .fub_axi_rready    (fill_rready)
    );

    axi4_master_rd #(
        .AXI_ID_WIDTH   (8),
        .AXI_ADDR_WIDTH (ADDR_WIDTH),
        .AXI_DATA_WIDTH (BUS_WIDTH),
        .AXI_USER_WIDTH (1)
    ) u_axi_rd (
        .aclk              (clk),
        .aresetn           (rst_n),
        .fub_axi_arid      (fill_arid),
        .fub_axi_araddr    (fill_araddr),
        .fub_axi_arlen     (fill_arlen),
        .fub_axi_arsize    (fill_arsize),
        .fub_axi_arburst   (fill_arburst),
        .fub_axi_arlock    (fill_arlock),
        .fub_axi_arcache   (fill_arcache),
        .fub_axi_arprot    (fill_arprot),
        .fub_axi_arqos     (fill_arqos),
        .fub_axi_arregion  (fill_arregion),
        .fub_axi_aruser    (fill_aruser),
        .fub_axi_arvalid   (fill_arvalid),
        .fub_axi_arready   (fill_arready),
        .fub_axi_rid       (fill_rid),
        .fub_axi_rdata     (fill_rdata),
        .fub_axi_rresp     (fill_rresp),
        .fub_axi_rlast     (fill_rlast),
        .fub_axi_ruser     (fill_ruser),
        .fub_axi_rvalid    (fill_rvalid),
        .fub_axi_rready    (fill_rready),
        .m_axi_arid        (m_axi_arid),
        .m_axi_araddr      (m_axi_araddr),
        .m_axi_arlen       (m_axi_arlen),
        .m_axi_arsize      (m_axi_arsize),
        .m_axi_arburst     (m_axi_arburst),
        .m_axi_arlock      (m_axi_arlock),
        .m_axi_arcache     (m_axi_arcache),
        .m_axi_arprot      (m_axi_arprot),
        .m_axi_arqos       (m_axi_arqos),
        .m_axi_arregion    (m_axi_arregion),
        .m_axi_aruser      (m_axi_aruser),
        .m_axi_arvalid     (m_axi_arvalid),
        .m_axi_arready     (m_axi_arready),
        .m_axi_rid         (m_axi_rid),
        .m_axi_rdata       (m_axi_rdata),
        .m_axi_rresp       (m_axi_rresp),
        .m_axi_rlast       (m_axi_rlast),
        .m_axi_ruser       (m_axi_ruser),
        .m_axi_rvalid      (m_axi_rvalid),
        .m_axi_rready      (m_axi_rready),
        .busy              ()
    );

    // ------------------------------------------------------------------
    // Tag-array port-B mux: control owns the port only while servicing a
    // snoop (grant cycle + CTRL_SNOOP); the TB backdoor owns it otherwise.
    // ------------------------------------------------------------------
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
    // The fill beats install into the victim way at {fill set, beat idx};
    // the install way exists only inside the control context, tapped
    // READ-ONLY from u_control.victim_way_q (the landed amber_core idiom;
    // repl_victim_way is NOT a substitute -- the RANDOM policy advances at
    // the MISS_VICTIM request and is unstable across the boundary).
    // ------------------------------------------------------------------
    logic [WAYS-1:0] fill_wr_way_onehot;

    always_comb begin
        for (int w = 0; w < WAYS; w++) begin
            fill_wr_way_onehot[w] =
                (u_control.victim_way_q == WAY_INDEX_WIDTH'(w));
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
            data_wr_en         = fill_beat_valid;
            data_wr_way_onehot = fill_wr_way_onehot;
            data_wr_addr       = {ctrl_tag_a_set, fill_beat_idx};
            data_wr_wdata      = fill_beat_data;
            data_wr_be         = {STRB_W{1'b1}};
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

endmodule : amber_miss_fill_macro_test
