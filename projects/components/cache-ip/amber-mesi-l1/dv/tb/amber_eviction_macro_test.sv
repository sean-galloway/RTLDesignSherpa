// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_eviction_macro_test
// Purpose:
//   Macro composition suite 3 (Task 9.5): the EVICTION/WRITEBACK
//   interaction group -- amber_control (with the victim depth-1 leaf) +
//   the REAL amber_drain engine -- pinned in isolation. The drain engine
//   closes with its house axi4_master_wr transport (DECISION D3, the
//   fill/drain unit rig's closure) and the wrapper exposes the
//   transport's m_axi AW/W/B memory side at the top for the cocotb TB's
//   AXI4 slave responder. Fill stays a timing stub at the boundary
//   (D-12): the TB models the fill partner exactly like the control
//   suite; snoops enter on the control-facing pins.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/05_amber_victim.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-08

`timescale 1ns / 1ps

//==============================================================================
// Module: amber_eviction_macro_test
//==============================================================================
// Description:
//   Test-only wrapper (approved `_test` suffix) for the eviction/writeback
//   macro cell. amber_core (landed, Task 9) is the shipping integrator;
//   this wrapper puts the REAL drain path in the loop while the fill
//   partner stays stubbed, so the cross-block pins this group owns run
//   against the engine instead of a fixed-latency model:
//
//     * dirty-victim gather: control's staged payload (victim_load /
//       victim_addr / victim_data) feeds the REAL drain burst -- the W
//       channel carries the staged bytes, not a model of them;
//     * drain ordering with real B-response latency: drain_done cannot
//       fire until the B channel returns (the stub could assert done at
//       any fixed latency);
//     * victim-buffer pressure: the depth-1 leaf (inside amber_control)
//       holds the line for the whole real drain window; the mid-drain
//       snoop bypass reads the staged buffer while the engine is still
//       waiting on B;
//     * writeback payload integrity into the TB MemoryModel through the
//       real W channel.
//
//   Data-array write-port arbitration (control's CPU merge wins over the
//   fill stub's received beats, deterministic priority, never simultaneous
//   by construction) is the landed harness idiom, unchanged. The victim
//   payload crosses the wrapper boundary on wires the way amber_core wires
//   them; the wrapper never LHS-assigns DUT internals (the leaf internals
//   the scoreboard wants are read-only hierarchical taps, the sanctioned
//   pattern, used TB-side only).
//
//   Pure wiring + the landed muxes; the only registers belong to the
//   DUTs. The scoreboard observes the muxed array write ports, the repl
//   interface, the drain handshake taps and the m_axi pins at the top.
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

module amber_eviction_macro_test
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

    // fill stub handshakes (TB models partner timing, D-12)
    input  logic                      fill_done,
    input  logic                      fill_beat_valid,
    input  logic [BEAT_INDEX_WIDTH-1:0] fill_beat_idx,
    output logic                      fill_start,
    output logic [ADDR_WIDTH-1:0]     fill_addr,
    output logic [2:0]                fill_req_class,

    // fill-beat datapath: the stub writes received beats into the data
    // array and strobes the beat index to control (pf_data_valid update,
    // MAS ch02/06)
    input  logic                       fillbeat_wr_en,
    input  logic [MEM_ADDR_WIDTH-1:0]  fillbeat_wr_addr,
    input  logic [WAY_INDEX_WIDTH-1:0] fillbeat_wr_way,
    input  logic [BUS_WIDTH-1:0]       fillbeat_wr_data,
    input  logic [STRB_W-1:0]          fillbeat_wr_be,

    // m_axi memory side (the TB's AXI4 write responder closes here;
    // AW/W/B belong to the internal axi4_master_wr transport)
    output logic [7:0]                m_axi_awid,
    output logic [ADDR_WIDTH-1:0]     m_axi_awaddr,
    output logic [7:0]                m_axi_awlen,
    output logic [2:0]                m_axi_awsize,
    output logic [1:0]                m_axi_awburst,
    output logic                      m_axi_awlock,
    output logic [3:0]                m_axi_awcache,
    output logic [2:0]                m_axi_awprot,
    output logic [3:0]                m_axi_awqos,
    output logic [3:0]                m_axi_awregion,
    output logic [0:0]                m_axi_awuser,
    output logic                      m_axi_awvalid,
    input  logic                      m_axi_awready,
    output logic [BUS_WIDTH-1:0]      m_axi_wdata,
    output logic [STRB_W-1:0]         m_axi_wstrb,
    output logic                      m_axi_wlast,
    output logic [0:0]                m_axi_wuser,
    output logic                      m_axi_wvalid,
    input  logic                      m_axi_wready,
    input  logic [7:0]                m_axi_bid,
    input  logic [1:0]                m_axi_bresp,
    input  logic [0:0]                m_axi_buser,
    input  logic                      m_axi_bvalid,
    output logic                      m_axi_bready,

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

    // drain handshake taps (drain_start + the staged victim payload are
    // control's launch strobes; done comes back from the REAL engine)
    output logic                      drain_start,
    output logic                      drain_done,
    output logic                      victim_load,
    output logic [ADDR_WIDTH-1:0]     victim_addr,
    output logic [LINE_BYTES*8-1:0]   victim_data,

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
            $error("amber_eviction_macro_test: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("amber_eviction_macro_test: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
            $error("amber_eviction_macro_test: LINE_BYTES / BUS_WIDTH*8 must be a power of two");
        if (WAYS < 2)
            $error("amber_eviction_macro_test: WAYS must be >= 2");
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
    // The REAL drain path: control's staged victim payload -> amber_drain
    // -> axi4_master_wr -> m_axi AW/W/B.
    // ------------------------------------------------------------------
    logic [7:0]            drain_awid;
    logic [ADDR_WIDTH-1:0] drain_awaddr;
    logic [7:0]            drain_awlen;
    logic [2:0]            drain_awsize;
    logic [1:0]            drain_awburst;
    logic                  drain_awlock;
    logic [3:0]            drain_awcache;
    logic [2:0]            drain_awprot;
    logic [3:0]            drain_awqos;
    logic [3:0]            drain_awregion;
    logic [0:0]            drain_awuser;
    logic                  drain_awvalid;
    logic                  drain_awready;
    logic [BUS_WIDTH-1:0]  drain_wdata;
    logic [STRB_W-1:0]     drain_wstrb;
    logic                  drain_wlast;
    logic [0:0]            drain_wuser;
    logic                  drain_wvalid;
    logic                  drain_wready;
    logic [7:0]            drain_bid;
    logic [1:0]            drain_bresp;
    logic [0:0]            drain_buser;
    logic                  drain_bvalid;
    logic                  drain_bready;

    amber_drain #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_drain (
        .clk              (clk),
        .rst_n            (rst_n),
        .drain_start      (drain_start),
        .victim_addr      (victim_addr),
        .victim_data      (victim_data),
        .drain_done       (drain_done),
        .fub_axi_awid     (drain_awid),
        .fub_axi_awaddr   (drain_awaddr),
        .fub_axi_awlen    (drain_awlen),
        .fub_axi_awsize   (drain_awsize),
        .fub_axi_awburst  (drain_awburst),
        .fub_axi_awlock   (drain_awlock),
        .fub_axi_awcache  (drain_awcache),
        .fub_axi_awprot   (drain_awprot),
        .fub_axi_awqos    (drain_awqos),
        .fub_axi_awregion (drain_awregion),
        .fub_axi_awuser   (drain_awuser),
        .fub_axi_awvalid  (drain_awvalid),
        .fub_axi_awready  (drain_awready),
        .fub_axi_wdata    (drain_wdata),
        .fub_axi_wstrb    (drain_wstrb),
        .fub_axi_wlast    (drain_wlast),
        .fub_axi_wuser    (drain_wuser),
        .fub_axi_wvalid   (drain_wvalid),
        .fub_axi_wready   (drain_wready),
        .fub_axi_bid      (drain_bid),
        .fub_axi_bresp    (drain_bresp),
        .fub_axi_buser    (drain_buser),
        .fub_axi_bvalid   (drain_bvalid),
        .fub_axi_bready   (drain_bready)
    );

    axi4_master_wr #(
        .AXI_ID_WIDTH   (8),
        .AXI_ADDR_WIDTH (ADDR_WIDTH),
        .AXI_DATA_WIDTH (BUS_WIDTH),
        .AXI_USER_WIDTH (1)
    ) u_axi_wr (
        .aclk              (clk),
        .aresetn           (rst_n),
        .fub_axi_awid      (drain_awid),
        .fub_axi_awaddr    (drain_awaddr),
        .fub_axi_awlen     (drain_awlen),
        .fub_axi_awsize    (drain_awsize),
        .fub_axi_awburst   (drain_awburst),
        .fub_axi_awlock    (drain_awlock),
        .fub_axi_awcache   (drain_awcache),
        .fub_axi_awprot    (drain_awprot),
        .fub_axi_awqos     (drain_awqos),
        .fub_axi_awregion  (drain_awregion),
        .fub_axi_awuser    (drain_awuser),
        .fub_axi_awvalid   (drain_awvalid),
        .fub_axi_awready   (drain_awready),
        .fub_axi_wdata     (drain_wdata),
        .fub_axi_wstrb     (drain_wstrb),
        .fub_axi_wlast     (drain_wlast),
        .fub_axi_wuser     (drain_wuser),
        .fub_axi_wvalid    (drain_wvalid),
        .fub_axi_wready    (drain_wready),
        .fub_axi_bid       (drain_bid),
        .fub_axi_bresp     (drain_bresp),
        .fub_axi_buser     (drain_buser),
        .fub_axi_bvalid    (drain_bvalid),
        .fub_axi_bready    (drain_bready),
        .m_axi_awid        (m_axi_awid),
        .m_axi_awaddr      (m_axi_awaddr),
        .m_axi_awlen       (m_axi_awlen),
        .m_axi_awsize      (m_axi_awsize),
        .m_axi_awburst     (m_axi_awburst),
        .m_axi_awlock      (m_axi_awlock),
        .m_axi_awcache     (m_axi_awcache),
        .m_axi_awprot      (m_axi_awprot),
        .m_axi_awqos       (m_axi_awqos),
        .m_axi_awregion    (m_axi_awregion),
        .m_axi_awuser      (m_axi_awuser),
        .m_axi_awvalid     (m_axi_awvalid),
        .m_axi_awready     (m_axi_awready),
        .m_axi_wdata       (m_axi_wdata),
        .m_axi_wstrb       (m_axi_wstrb),
        .m_axi_wlast       (m_axi_wlast),
        .m_axi_wuser       (m_axi_wuser),
        .m_axi_wvalid      (m_axi_wvalid),
        .m_axi_wready      (m_axi_wready),
        .m_axi_bid         (m_axi_bid),
        .m_axi_bresp       (m_axi_bresp),
        .m_axi_buser       (m_axi_buser),
        .m_axi_bvalid      (m_axi_bvalid),
        .m_axi_bready      (m_axi_bready),
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
    // Data-array write-port mux: control (CPU merge) wins over the fill
    // stub's beats -- the landed harness idiom.
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

endmodule : amber_eviction_macro_test
