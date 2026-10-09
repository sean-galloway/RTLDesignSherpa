// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_pair_fabric
// Purpose:
//   The minimal 2-master snoopy manager the plain-AXI4 amber pair rig needs
//   (onyx proper waits per amber D10 / onyx v0.2). ONE coherence
//   transaction at a time: the two caches are blocking and single-
//   outstanding each, so system-wide serialization is sufficient -- and
//   required for coherence, because a granted peer snoop must observe the
//   winner's COMMITTED line state, which only grant-after-completion
//   ordering guarantees. Fair round-robin between the two caches at the
//   grant point and at the shared-memory write port.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch01_overview/01_architecture.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-09

`timescale 1ns / 1ps

//==============================================================================
// Module: amber_pair_fabric
//==============================================================================
// Description:
//   Per direction, the fabric takes the cache's D-8 coherence sideband
//   (coh_req_valid/addr/type: one pulse per fill launch -- READ_SHARED /
//   READ_UNIQUE on a miss, CLEAN_UNIQUE on an upgrade -- and per dirty
//   write-back launch, WRITE_BACK) and:
//
//     fill / upgrade : drive AC to the PEER -> gather CR/CD (the amber
//                      responder presents CR only after the final CD beat,
//                      onyx-D4) -> DataTransfer: the CD line is buffered
//                      (depth-1 per direction) and the requester's R beats
//                      are sourced from the buffer (the memory AR is
//                      suppressed); no DataTransfer: the AR passes through
//                      to the shared sdpram_slave_axi4_axi4 memory.
//     write-back     : pure write-port pass-through (AW/W/B), arbitrated
//                      onto the single memory write port.
//
//   Snoop map (IHI0022 ACSNOOP[3:0]): READ_SHARED -> SNOOP_READ_SHARED
//   (4'h1), READ_UNIQUE -> SNOOP_READ_UNIQUE (4'h7), CLEAN_UNIQUE ->
//   SNOOP_MAKE_INVALID (4'hC).
//
//   Kill rule: while a coherence transaction is in flight the peer's own
//   same-line fill request stays pending (its AR is held). A data-expecting
//   snoop against that pending fill would deadlock -- the peer's
//   pending-fill bypass gates CD beats on fill data the fabric is holding.
//   So when the peer has an UNGRANTED same-line request at AC issue, the
//   snoop is MakeInvalid instead (IHI0022 forbids DataTransfer on
//   MakeInvalid): the pending fill is invalidated (the peer's blocking
//   pipeline replays it through the fabric) and no data is needed. Against
//   an INSTALLED line MakeInvalid would silently discard dirty data, so the
//   rule is exact: it fires only on the ungranted-pending case, where the
//   peer provably holds nothing installed to lose.
//
//   Safe-peer wait: acvalid is held until the peer's FSM is snoop-safe
//   (peer_state input = the peer amber_top's ctrl_state): not in INIT, the
//   miss states, FILL_WRITE or REPLAY. Without this, a snoop accepted in
//   the shadow of the peer's fill commit could be serviced against the
//   pre-commit pending-fill bypass (raw, pre-merge beats) or race the
//   commit's tag write -- a 1-2 cycle margin is not a design. The wait
//   cannot deadlock: a peer with an ungranted request parks in MISS_FILL
//   with its AR held, which is exactly the kill-rule case (MakeInvalid
//   needs no fill data); a peer mid-miss reaches its fill launch (the
//   sideband pulse) in bounded time, after which the pending term releases
//   the wait.
//
//   Point of coherence: a PassDirty response means the peer owned the only
//   correct copy; the forwarded line is also written to the shared memory
//   (AWID 8'hA0|dir) once the buffer holds it. While an absorption is
//   pending, pass-through ARs and write-back AWs to the same line hold
//   (per-direction pending-absorption address registers) -- the memory
//   image of such a line is stale until the absorption lands. A write-back
//   matching a pending absorption orders behind it (the write-back carries
//   strictly newer bytes).
//
//   Fairness / liveness: round-robin at the coherence grant and at the
//   memory write port; one memory read in flight at a time (both caches
//   issue ID 0, so the R channel is demuxed by ownership, never
//   interleaved); one write burst in flight at a time (B routed by owner).
//
//------------------------------------------------------------------------------
// Parameters: geometry per amber_pkg (the fabric moves lines; SETS/WAYS are
//   package context only).
//------------------------------------------------------------------------------
//
// Notes:
//   - Single clock / active-low reset (clk / rst_n).
//   - The peer_state inputs are the peer caches' ctrl_state observability
//     outputs (amber_top ctrl_state) -- bring-up-fabric visibility, not a
//     production onyx interface.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: the Task 11 pair rig (amber_pair_rig_tb)
//   - Consumes: two amber_top memory sides + D-8 sidebands + ACE responders
//   - Package: amber_pkg (ACE request classes)
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_pair_rig.py
//   Plan: dv/testplans/amber_pair_rig_testplan.yaml
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_pair_rig.py -v
//
//==============================================================================

module amber_pair_fabric
    import amber_pkg::*;
#(
    parameter int ADDR_WIDTH     = AMBER_ADDR_WIDTH,
    parameter int SETS           = AMBER_SETS,
    parameter int WAYS           = AMBER_WAYS,
    parameter int LINE_BYTES     = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH      = AMBER_BUS_WIDTH,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    localparam int STRB_W           = BUS_WIDTH / 8,
    localparam int FILL_BEATS       = LINE_BYTES / STRB_W,
    localparam int BEAT_INDEX_WIDTH = $clog2(FILL_BEATS),
    localparam int IW               = AXI_ID_WIDTH,
    localparam int UW               = AXI_USER_WIDTH
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // ------------------------------------------------------------------
    // Cache 0 / cache 1 AXI4 master-facing ports (the amber_top m_axi_*
    // monlite-wrapped masters)
    // ------------------------------------------------------------------
    input  logic [IW-1:0]               c0_arid,
    input  logic [ADDR_WIDTH-1:0]       c0_araddr,
    input  logic [7:0]                  c0_arlen,
    input  logic [2:0]                  c0_arsize,
    input  logic [1:0]                  c0_arburst,
    input  logic                        c0_arlock,
    input  logic [3:0]                  c0_arcache,
    input  logic [2:0]                  c0_arprot,
    input  logic [3:0]                  c0_arqos,
    input  logic [3:0]                  c0_arregion,
    input  logic [UW-1:0]               c0_aruser,
    input  logic                        c0_arvalid,
    output logic                        c0_arready,
    output logic [IW-1:0]               c0_rid,
    output logic [BUS_WIDTH-1:0]        c0_rdata,
    output logic [1:0]                  c0_rresp,
    output logic                        c0_rlast,
    output logic [UW-1:0]               c0_ruser,
    output logic                        c0_rvalid,
    input  logic                        c0_rready,

    input  logic [IW-1:0]               c0_awid,
    input  logic [ADDR_WIDTH-1:0]       c0_awaddr,
    input  logic [7:0]                  c0_awlen,
    input  logic [2:0]                  c0_awsize,
    input  logic [1:0]                  c0_awburst,
    input  logic                        c0_awlock,
    input  logic [3:0]                  c0_awcache,
    input  logic [2:0]                  c0_awprot,
    input  logic [3:0]                  c0_awqos,
    input  logic [3:0]                  c0_awregion,
    input  logic [UW-1:0]               c0_awuser,
    input  logic                        c0_awvalid,
    output logic                        c0_awready,
    input  logic [BUS_WIDTH-1:0]        c0_wdata,
    input  logic [STRB_W-1:0]           c0_wstrb,
    input  logic                        c0_wlast,
    input  logic [UW-1:0]               c0_wuser,
    input  logic                        c0_wvalid,
    output logic                        c0_wready,
    output logic [IW-1:0]               c0_bid,
    output logic [1:0]                  c0_bresp,
    output logic [UW-1:0]               c0_buser,
    output logic                        c0_bvalid,
    input  logic                        c0_bready,

    input  logic [IW-1:0]               c1_arid,
    input  logic [ADDR_WIDTH-1:0]       c1_araddr,
    input  logic [7:0]                  c1_arlen,
    input  logic [2:0]                  c1_arsize,
    input  logic [1:0]                  c1_arburst,
    input  logic                        c1_arlock,
    input  logic [3:0]                  c1_arcache,
    input  logic [2:0]                  c1_arprot,
    input  logic [3:0]                  c1_arqos,
    input  logic [3:0]                  c1_arregion,
    input  logic [UW-1:0]               c1_aruser,
    input  logic                        c1_arvalid,
    output logic                        c1_arready,
    output logic [IW-1:0]               c1_rid,
    output logic [BUS_WIDTH-1:0]        c1_rdata,
    output logic [1:0]                  c1_rresp,
    output logic                        c1_rlast,
    output logic [UW-1:0]               c1_ruser,
    output logic                        c1_rvalid,
    input  logic                        c1_rready,

    input  logic [IW-1:0]               c1_awid,
    input  logic [ADDR_WIDTH-1:0]       c1_awaddr,
    input  logic [7:0]                  c1_awlen,
    input  logic [2:0]                  c1_awsize,
    input  logic [1:0]                  c1_awburst,
    input  logic                        c1_awlock,
    input  logic [3:0]                  c1_awcache,
    input  logic [2:0]                  c1_awprot,
    input  logic [3:0]                  c1_awqos,
    input  logic [3:0]                  c1_awregion,
    input  logic [UW-1:0]               c1_awuser,
    input  logic                        c1_awvalid,
    output logic                        c1_awready,
    input  logic [BUS_WIDTH-1:0]        c1_wdata,
    input  logic [STRB_W-1:0]           c1_wstrb,
    input  logic                        c1_wlast,
    input  logic [UW-1:0]               c1_wuser,
    input  logic                        c1_wvalid,
    output logic                        c1_wready,
    output logic [IW-1:0]               c1_bid,
    output logic [1:0]                  c1_bresp,
    output logic [UW-1:0]               c1_buser,
    output logic                        c1_bvalid,
    input  logic                        c1_bready,

    // ------------------------------------------------------------------
    // ACE snoop-master side per cache (fabric drives AC into the cache's
    // responder; CR/CD return from it)
    // ------------------------------------------------------------------
    output logic [ADDR_WIDTH-1:0]       s0_acaddr,
    output logic [3:0]                  s0_acsnoop,
    output logic [2:0]                  s0_acprot,
    output logic                        s0_acvalid,
    input  logic                        s0_acready,
    input  logic [AMBER_CRRESP_WIDTH-1:0] s0_crresp,
    input  logic                        s0_crvalid,
    output logic                        s0_crready,
    input  logic [BUS_WIDTH-1:0]        s0_cddata,
    input  logic                        s0_cdlast,
    input  logic                        s0_cdvalid,
    output logic                        s0_cdready,

    output logic [ADDR_WIDTH-1:0]       s1_acaddr,
    output logic [3:0]                  s1_acsnoop,
    output logic [2:0]                  s1_acprot,
    output logic                        s1_acvalid,
    input  logic                        s1_acready,
    input  logic [AMBER_CRRESP_WIDTH-1:0] s1_crresp,
    input  logic                        s1_crvalid,
    output logic                        s1_crready,
    input  logic [BUS_WIDTH-1:0]        s1_cddata,
    input  logic                        s1_cdlast,
    input  logic                        s1_cdvalid,
    output logic                        s1_cdready,

    // ------------------------------------------------------------------
    // D-8 coherence sideband inputs (one pulse per fill / upgrade / WB)
    // ------------------------------------------------------------------
    input  logic                        c0_coh_req_valid,
    input  logic [ADDR_WIDTH-1:0]       c0_coh_req_addr,
    input  logic [2:0]                  c0_coh_req_type,
    input  logic                        c1_coh_req_valid,
    input  logic [ADDR_WIDTH-1:0]       c1_coh_req_addr,
    input  logic [2:0]                  c1_coh_req_type,

    // ------------------------------------------------------------------
    // Peer FSM visibility (the caches' ctrl_state; the safe-peer wait)
    // ------------------------------------------------------------------
    input  logic [3:0]                  peer0_state,
    input  logic [3:0]                  peer1_state,

    // ------------------------------------------------------------------
    // Shared-memory AXI4 master side (to sdpram_slave_axi4_axi4)
    // ------------------------------------------------------------------
    output logic [IW-1:0]               mem_arid,
    output logic [ADDR_WIDTH-1:0]       mem_araddr,
    output logic [7:0]                  mem_arlen,
    output logic [2:0]                  mem_arsize,
    output logic [1:0]                  mem_arburst,
    output logic                        mem_arlock,
    output logic [3:0]                  mem_arcache,
    output logic [2:0]                  mem_arprot,
    output logic [3:0]                  mem_arqos,
    output logic [3:0]                  mem_arregion,
    output logic [UW-1:0]               mem_aruser,
    output logic                        mem_arvalid,
    input  logic                        mem_arready,
    input  logic [IW-1:0]               mem_rid,
    input  logic [BUS_WIDTH-1:0]        mem_rdata,
    input  logic [1:0]                  mem_rresp,
    input  logic                        mem_rlast,
    input  logic [UW-1:0]               mem_ruser,
    input  logic                        mem_rvalid,
    output logic                        mem_rready,

    output logic [IW-1:0]               mem_awid,
    output logic [ADDR_WIDTH-1:0]       mem_awaddr,
    output logic [7:0]                  mem_awlen,
    output logic [2:0]                  mem_awsize,
    output logic [1:0]                  mem_awburst,
    output logic                        mem_awlock,
    output logic [3:0]                  mem_awcache,
    output logic [2:0]                  mem_awprot,
    output logic [3:0]                  mem_awqos,
    output logic [3:0]                  mem_awregion,
    output logic [UW-1:0]               mem_awuser,
    output logic                        mem_awvalid,
    input  logic                        mem_awready,
    output logic [BUS_WIDTH-1:0]        mem_wdata,
    output logic [STRB_W-1:0]           mem_wstrb,
    output logic                        mem_wlast,
    output logic [UW-1:0]               mem_wuser,
    output logic                        mem_wvalid,
    input  logic                        mem_wready,
    input  logic [IW-1:0]               mem_bid,
    input  logic [1:0]                  mem_bresp,
    input  logic [UW-1:0]               mem_buser,
    input  logic                        mem_bvalid,
    output logic                        mem_bready,

    // ------------------------------------------------------------------
    // Debug / observability taps (unused in the datapath)
    // ------------------------------------------------------------------
    output logic [3:0]                  dbg_state,
    output logic                        dbg_grant_dir,
    output logic [1:0]                  dbg_pend_vld,
    output logic [1:0]                  dbg_buf_vld,
    output logic [1:0]                  dbg_abs_pend,
    output logic                        dbg_kill,
    output logic [3:0]                  dbg_acsnoop,
    output logic [ADDR_WIDTH-1:0]       dbg_grant_addr
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the FUBs)
    // ------------------------------------------------------------------
    initial begin
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("amber_pair_fabric: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0 || FILL_BEATS < 2)
            $error("amber_pair_fabric: LINE_BYTES / BUS_WIDTH*8 must be a power of two >= 2");
        if ((BUS_WIDTH % 8) != 0)
            $error("amber_pair_fabric: BUS_WIDTH must be a multiple of 8");
    end

    // ------------------------------------------------------------------
    // Encodings
    // ------------------------------------------------------------------
    localparam logic [3:0] ACSNOOP_READ_SHARED  = 4'h1;   // IHI0022
    localparam logic [3:0] ACSNOOP_READ_UNIQUE  = 4'h7;
    localparam logic [3:0] ACSNOOP_MAKE_INVALID = 4'hC;

    localparam logic [3:0] ST_IDLE        = 4'h0;
    localparam logic [3:0] ST_LOOKUP      = 4'h2;
    localparam logic [3:0] ST_HIT_RD      = 4'h3;
    localparam logic [3:0] ST_HIT_WR      = 4'h4;
    localparam logic [3:0] ST_INIT        = 4'h1;   // amber_pkg ctrl_state_t
    localparam logic [3:0] ST_MISS_VICTIM = 4'h5;
    localparam logic [3:0] ST_MISS_DRAIN  = 4'h6;
    localparam logic [3:0] ST_MISS_FILL   = 4'h7;
    localparam logic [3:0] ST_FILL_WRITE  = 4'h8;
    localparam logic [3:0] ST_REPLAY      = 4'h9;

    function automatic logic [3:0] map_snoop(input logic [2:0] req_type);
        case (req_type)
            AMBER_ACE_READ_SHARED:  return ACSNOOP_READ_SHARED;
            AMBER_ACE_READ_UNIQUE:  return ACSNOOP_READ_UNIQUE;
            default:                return ACSNOOP_MAKE_INVALID;
        endcase
    endfunction

    // ------------------------------------------------------------------
    // Request sideband pulse latches: the pending registers ARE the
    // per-direction request queue (one outstanding per blocking cache).
    // WRITE_BACK pulses are not coherence requests.
    // ------------------------------------------------------------------
    // Per-direction pending-request FIFO. An upgrade completes at the
    // cache without waiting for the fabric (the D-8 sideband is an
    // observation output), so a cache can raise its NEXT request while
    // its previous one is still queued here -- the queue must hold more
    // than one entry per direction or requests would be silently
    // overwritten (found by the randomized dual-CPU soak).
    localparam int PEND_DEPTH = 4;
    logic [2:0]              pend_cnt_q [2];
    logic [ADDR_WIDTH-1:0]   pend_line_q [2][PEND_DEPTH];
    logic [2:0]              pend_type_q [2][PEND_DEPTH];
    logic [1:0]              pend_ovf_q;   // overflow: debug only (TB-checked)
    // per-direction drain guard: the just-completed transaction's line,
    // for the cycles between the fabric's F_DONE and the peer's fill
    // commit -- a data-expecting snoop on that line would hit the
    // pending-fill bypass (pf-gated CD on a fabric-held AR) and deadlock,
    // so the kill rule and the safe-peer wait must see it
    logic [1:0]              drain_vld_q;
    logic [ADDR_WIDTH-1:0]   drain_line_q [2];

    wire [1:0] coh_pulse_vld;
    assign coh_pulse_vld[0] = c0_coh_req_valid
        && (c0_coh_req_type != 3'(AMBER_ACE_WRITE_BACK));
    assign coh_pulse_vld[1] = c1_coh_req_valid
        && (c1_coh_req_type != 3'(AMBER_ACE_WRITE_BACK));

    // ------------------------------------------------------------------
    // Grant selection: fair round-robin over pending, buffer-free requests
    // ------------------------------------------------------------------
    logic                       rr_q;             // grant round-robin
    logic [1:0]                 buf_vld_q;

    logic      g_take [2];
    logic      g_dir;
    // Upgrade-priority scheduling: an upgrade completes at the cache
    // without waiting for this fabric (the D-8 sideband is an observation
    // output), so upgrades arrive faster than fills and the per-direction
    // queue would grow unboundedly if fills could hog the serial grant.
    // A CLEAN_UNIQUE head is granted first (round-robin between two);
    // fills drain in the idle slots -- upgrades occupy the fabric ~5
    // cycles of every ~10-cycle arrival period, leaving ample fill slots.
    logic g_up [2];
    always_comb begin
        for (int i = 0; i < 2; i++) begin
            g_take[i] = (pend_cnt_q[i] != 3'd0) && !buf_vld_q[i];
            g_up[i]   = g_take[i]
                && (pend_type_q[i][0] == 3'(AMBER_ACE_CLEAN_UNIQUE));
        end
        if (g_up[1'(rr_q)])
            g_dir = rr_q;
        else if (g_up[1'(1 - rr_q)])
            g_dir = 1 - rr_q;
        else if (g_take[1'(rr_q)])
            g_dir = rr_q;
        else if (g_take[1'(1 - rr_q)])
            g_dir = 1 - rr_q;
        else
            g_dir = rr_q;
    end
    wire g_valid = g_take[0] || g_take[1];
    wire g_peer  = 1 - g_dir;

    // kill rule (evaluated at AC-ISSUE time, not at grant): the peer
    // holds a same-line request it cannot serve data for -- either an
    // ungranted request (fill in flight, AR held by this fabric) or a
    // just-completed transaction still landing beats at the cache
    // (pf-gated bypass either way). Evaluating combinationally at issue
    // closes the skew where the peer's fill launched in the cycle before
    // the grant -- a same-cycle pulse is visible here, so the snoop
    // converts to MakeInvalid exactly when it must. g_kill below is the
    // grant-time PREDICTION (debug tap); the issue-time value selects the
    // actual ACSNOOP and the AC valid gating.
    wire g_kill = (pend_cnt_q[1'(g_peer)] != 3'd0)
        && (pend_line_q[1'(g_peer)][0] == pend_line_q[1'(g_dir)][0]);

    // ------------------------------------------------------------------
    // Coherence FSM: one transaction at a time
    // ------------------------------------------------------------------
    localparam logic [3:0] F_IDLE      = 4'd0;
    localparam logic [3:0] F_AC        = 4'd1;
    localparam logic [3:0] F_RESP      = 4'd2;
    localparam logic [3:0] F_REPLAY_AR = 4'd3;
    localparam logic [3:0] F_REPLAY_R  = 4'd4;
    localparam logic [3:0] F_PASS_AR   = 4'd5;
    localparam logic [3:0] F_PASS_R    = 4'd6;
    localparam logic [3:0] F_DONE      = 4'd7;

    logic [3:0]                  state_q;
    logic                       grant_q;          // requester cache (0/1)
    logic [ADDR_WIDTH-1:0]      grant_addr_q;     // line-aligned request line
    logic [2:0]                 grant_type_q;     // amber_ace_req_t class
    logic                       kill_q;           // MakeInvalid (kill rule)
    logic [3:0]                 acsnoop_q;
    logic [LINE_BYTES*8-1:0]    line_buf_q [2];
    logic [1:0]                 abs_pend_vld_q;
    logic [ADDR_WIDTH-1:0]      abs_pend_addr_q [2];
    logic [1:0]                 abs_req_q;        // absorb engine kick

    logic [BEAT_INDEX_WIDTH-1:0] beat_q;
    logic [IW-1:0]              replay_rid_q;
    logic [AMBER_CRRESP_WIDTH-1:0] crresp_q;
    logic                       r_owner_q;
    logic [7:0]                 beat_count_q;

    // ------------------------------------------------------------------
    // Write port: write-back pass-through + PassDirty absorption, one
    // burst in flight system-wide, fair round-robin
    // ------------------------------------------------------------------
    localparam logic [2:0] W_IDLE = 3'd0;
    localparam logic [2:0] W_AW   = 3'd1;
    localparam logic [2:0] W_W    = 3'd2;
    localparam logic [2:0] W_B    = 3'd3;

    logic [2:0]                 wstate_q;
    logic [1:0]                 w_owner_q;
    logic                       w_is_abs_q;
    logic [1:0]                 w_rr_q;
    logic [BEAT_INDEX_WIDTH-1:0] w_beat_q;

    // ------------------------------------------------------------------
    // Cache-side channel aggregation
    // ------------------------------------------------------------------
    logic [1:0] c_arvalid, c_arready, c_rready;
    logic [IW-1:0]       c_arid [2];
    logic [ADDR_WIDTH-1:0] c_araddr [2];
    logic [7:0]          c_arlen [2];
    logic [2:0]          c_arsize [2];
    logic [1:0]          c_arburst [2];
    logic                  c_arlock [2];
    logic [3:0]            c_arcache [2];
    logic [2:0]            c_arprot [2];
    logic [3:0]            c_arqos [2];
    logic [3:0]            c_arregion [2];
    logic [UW-1:0]         c_aruser [2];

    assign c_arvalid = {c1_arvalid, c0_arvalid};
    assign c_rready  = {c1_rready, c0_rready};
    assign c_arid[0] = c0_arid;       assign c_arid[1] = c1_arid;
    assign c_araddr[0] = c0_araddr;   assign c_araddr[1] = c1_araddr;
    assign c_arlen[0] = c0_arlen;     assign c_arlen[1] = c1_arlen;
    assign c_arsize[0] = c0_arsize;   assign c_arsize[1] = c1_arsize;
    assign c_arburst[0] = c0_arburst; assign c_arburst[1] = c1_arburst;
    assign c_arlock[0] = c0_arlock;   assign c_arlock[1] = c1_arlock;
    assign c_arcache[0] = c0_arcache; assign c_arcache[1] = c1_arcache;
    assign c_arprot[0] = c0_arprot;   assign c_arprot[1] = c1_arprot;
    assign c_arqos[0] = c0_arqos;     assign c_arqos[1] = c1_arqos;
    assign c_arregion[0] = c0_arregion; assign c_arregion[1] = c1_arregion;
    assign c_aruser[0] = c0_aruser;   assign c_aruser[1] = c1_aruser;

    logic [1:0] c_awvalid, c_awready, c_wvalid, c_wready, c_bready;
    logic [IW-1:0]       c_awid [2];
    logic [ADDR_WIDTH-1:0] c_awaddr [2];
    logic [7:0]          c_awlen [2];
    logic [2:0]          c_awsize [2];
    logic [1:0]          c_awburst [2];
    logic                  c_awlock [2];
    logic [3:0]            c_awcache [2];
    logic [2:0]            c_awprot [2];
    logic [3:0]            c_awqos [2];
    logic [3:0]            c_awregion [2];
    logic [UW-1:0]         c_awuser [2];
    logic [BUS_WIDTH-1:0]  c_wdata [2];
    logic [STRB_W-1:0]     c_wstrb [2];
    logic                  c_wlast [2];
    logic [UW-1:0]         c_wuser [2];

    assign c_awvalid = {c1_awvalid, c0_awvalid};
    assign c_wvalid  = {c1_wvalid, c0_wvalid};
    assign c_bready  = {c1_bready, c0_bready};
    assign c_awid[0] = c0_awid;       assign c_awid[1] = c1_awid;
    assign c_awaddr[0] = c0_awaddr;   assign c_awaddr[1] = c1_awaddr;
    assign c_awlen[0] = c0_awlen;     assign c_awlen[1] = c1_awlen;
    assign c_awsize[0] = c0_awsize;   assign c_awsize[1] = c1_awsize;
    assign c_awburst[0] = c0_awburst; assign c_awburst[1] = c1_awburst;
    assign c_awlock[0] = c0_awlock;   assign c_awlock[1] = c1_awlock;
    assign c_awcache[0] = c0_awcache; assign c_awcache[1] = c1_awcache;
    assign c_awprot[0] = c0_awprot;   assign c_awprot[1] = c1_awprot;
    assign c_awqos[0] = c0_awqos;     assign c_awqos[1] = c1_awqos;
    assign c_awregion[0] = c0_awregion; assign c_awregion[1] = c1_awregion;
    assign c_awuser[0] = c0_awuser;   assign c_awuser[1] = c1_awuser;
    assign c_wdata[0] = c0_wdata;     assign c_wdata[1] = c1_wdata;
    assign c_wstrb[0] = c0_wstrb;     assign c_wstrb[1] = c1_wstrb;
    assign c_wlast[0] = c0_wlast;     assign c_wlast[1] = c1_wlast;
    assign c_wuser[0] = c0_wuser;     assign c_wuser[1] = c1_wuser;

    // ------------------------------------------------------------------
    // Pending-absorption address match: a read or write must not touch a
    // line whose absorption has not landed
    // ------------------------------------------------------------------
    function automatic logic abs_match(input logic [ADDR_WIDTH-1:0] addr);
        return (abs_pend_vld_q[0] && (abs_pend_addr_q[0] == addr))
            || (abs_pend_vld_q[1] && (abs_pend_addr_q[1] == addr));
    endfunction

    // ------------------------------------------------------------------
    // Safe-peer wait: the AC may only be presented when the peer's FSM
    // cannot arm a same-line bypass under a data-expecting snoop (not in
    // INIT / miss states / FILL_WRITE / REPLAY), or when the peer has an
    // ungranted request (the kill-rule case: its fill is fabric-held and
    // the kill snoop needs no data).
    // ------------------------------------------------------------------
    logic [3:0] peer_state_now;
    logic       peer_pend_now;
    always_comb begin
        if (grant_q == 1'b0) begin
            peer_state_now = peer1_state;   // snooping cache 1
            peer_pend_now  = (pend_cnt_q[1] != 3'd0) || coh_pulse_vld[1];
        end else begin
            peer_state_now = peer0_state;   // snooping cache 0
            peer_pend_now  = (pend_cnt_q[0] != 3'd0) || coh_pulse_vld[0];
        end
    end

    function automatic logic peer_unsafe(input logic [3:0] st);
        return (st == ST_INIT) || (st == ST_MISS_VICTIM)
            || (st == ST_MISS_DRAIN) || (st == ST_MISS_FILL)
            || (st == ST_FILL_WRITE) || (st == ST_REPLAY);
    endfunction

    // the peer-pending bypass lets the AC fire while the peer parks in
    // MISS_FILL with a fabric-held AR -- but NOT during the drain window
    // on this very line (that fill's beats are flowing; a data-expecting
    // snoop must wait for the commit)
    wire peer_drain_grant = drain_vld_q[1'(1 - grant_q)]
        && (drain_line_q[1'(1 - grant_q)] == grant_addr_q);
    wire peer_safe_data = !peer_unsafe(peer_state_now)
        || (peer_pend_now && !peer_drain_grant);
    // issue-time kill: same rule against the CURRENT queue/drain state,
    // including a same-cycle sideband pulse (the fabric sees it live;
    // the registered queue lags it by a cycle)
    wire [1:0] issue_pulse = coh_pulse_vld;
    wire issue_peer_pulse_same
        = issue_pulse[1'(1 - grant_q)]
          && ((1 - grant_q) == 1'b0 ? c0_coh_req_addr : c1_coh_req_addr)
             == grant_addr_q;
    // NB: the DRAIN window is deliberately NOT a kill condition. A kill
    // is only sound while the peer's fill cannot commit (its AR held by
    // this fabric); during the drain the fill completes independently,
    // and an AC issued here can sit in the peer's skid past the commit --
    // a MakeInvalid serviced against a COMMITTED line would discard
    // installed dirty data. Drain-same-line instead waits (peer_safe).
    wire issue_kill
        = ((pend_cnt_q[1'(1 - grant_q)] != 3'd0)
           && (pend_line_q[1'(1 - grant_q)][0] == grant_addr_q))
          || issue_peer_pulse_same;
    wire [3:0] issue_acsnoop = issue_kill ? ACSNOOP_MAKE_INVALID
                              : map_snoop(grant_type_q);
    // a MakeInvalid snoop carries no data dependency: it is servable in
    // any peer state (it kills a pending fill instead of gathering data),
    // so it issues without the safe-peer wait -- this keeps the upgrade
    // drain rate at or above the cache's upgrade arrival rate
    // a kill issues without the data-side safe wait only when the peer
    // is not mid-commit on this very line (the drain window must wait:
    // the fill completes independently, and a kill serviced after the
    // commit would discard installed dirty data)
    wire peer_safe = (issue_kill && !peer_drain_grant) || peer_safe_data;

    // ------------------------------------------------------------------
    // Snoop channel muxing
    // ------------------------------------------------------------------
    logic [1:0] acready, crvalid, cdvalid, cdlast;
    logic [1:0][AMBER_CRRESP_WIDTH-1:0] crresp_w;
    logic [1:0][BUS_WIDTH-1:0] cddata_w;

    assign acready  = {s1_acready, s0_acready};
    assign crvalid  = {s1_crvalid, s0_crvalid};
    assign cdvalid  = {s1_cdvalid, s0_cdvalid};
    assign cdlast   = {s1_cdlast, s0_cdlast};
    assign crresp_w = {s1_crresp, s0_crresp};
    assign cddata_w = {s1_cddata, s0_cddata};

    wire snoop_ac_accept = acready[1'(1 - grant_q)] && (state_q == F_AC)
                           && peer_safe;
    wire snoop_cd_beat   = cdvalid[1'(1 - grant_q)] && (state_q == F_RESP);
    wire snoop_cd_last   = cdlast[1'(1 - grant_q)];
    wire snoop_cr_accept = crvalid[1'(1 - grant_q)] && (state_q == F_RESP);

    assign s0_acaddr  = grant_addr_q;
    assign s1_acaddr  = grant_addr_q;
    assign s0_acsnoop = issue_acsnoop;
    assign s1_acsnoop = issue_acsnoop;
    assign s0_acprot  = 3'b000;
    assign s1_acprot  = 3'b000;
    assign s0_acvalid = (state_q == F_AC) && (grant_q == 1'b1) && peer_safe;
    assign s1_acvalid = (state_q == F_AC) && (grant_q == 1'b0) && peer_safe;
    assign s0_crready = (state_q == F_RESP);
    assign s1_crready = (state_q == F_RESP);
    assign s0_cdready = (state_q == F_RESP);
    assign s1_cdready = (state_q == F_RESP);

    // ------------------------------------------------------------------
    // Cache AR / memory AR / cache R muxing
    // ------------------------------------------------------------------
    assign c_arready[0] = ((state_q == F_REPLAY_AR) && (grant_q == 1'b0))
                       || ((state_q == F_PASS_AR) && (grant_q == 1'b0)
                           && !abs_match(c0_araddr));
    assign c_arready[1] = ((state_q == F_REPLAY_AR) && (grant_q == 1'b1))
                       || ((state_q == F_PASS_AR) && (grant_q == 1'b1)
                           && !abs_match(c1_araddr));
    assign c0_arready = c_arready[0];
    assign c1_arready = c_arready[1];

    assign mem_arid     = c_arid[1'(grant_q)];
    assign mem_araddr   = c_araddr[1'(grant_q)];
    assign mem_arlen    = c_arlen[1'(grant_q)];
    assign mem_arsize   = c_arsize[1'(grant_q)];
    assign mem_arburst  = c_arburst[1'(grant_q)];
    assign mem_arlock   = c_arlock[1'(grant_q)];
    assign mem_arcache  = c_arcache[1'(grant_q)];
    assign mem_arprot   = c_arprot[1'(grant_q)];
    assign mem_arqos    = c_arqos[1'(grant_q)];
    assign mem_arregion = c_arregion[1'(grant_q)];
    assign mem_aruser   = c_aruser[1'(grant_q)];
    assign mem_arvalid  = (state_q == F_PASS_AR) && c_arvalid[1'(grant_q)]
                          && !abs_match(c_araddr[1'(grant_q)]);

    logic [IW-1:0]       r_rid;
    logic [BUS_WIDTH-1:0] r_rdata;
    logic [1:0]          r_rresp;
    logic                r_rlast;
    logic [UW-1:0]       r_ruser;
    logic                r_rvalid;

    always_comb begin
        if (state_q == F_REPLAY_R) begin
            r_rid    = replay_rid_q;
            r_rdata  = line_buf_q[1'(grant_q)][32'(beat_q) * BUS_WIDTH
                                           +: BUS_WIDTH];
            r_rresp  = 2'b00;
            r_rlast  = (beat_q == BEAT_INDEX_WIDTH'(FILL_BEATS - 1));
            r_ruser  = '0;
            r_rvalid = 1'b1;
        end else if (state_q == F_PASS_R) begin
            r_rid    = mem_rid;
            r_rdata  = mem_rdata;
            r_rresp  = mem_rresp;
            r_rlast  = mem_rlast;
            r_ruser  = mem_ruser;
            r_rvalid = mem_rvalid;
        end else begin
            r_rid    = '0;
            r_rdata  = '0;
            r_rresp  = '0;
            r_rlast  = 1'b0;
            r_ruser  = '0;
            r_rvalid = 1'b0;
        end
    end

    assign c0_rid    = r_rid;
    assign c1_rid    = r_rid;
    assign c0_rdata  = r_rdata;
    assign c1_rdata  = r_rdata;
    assign c0_rresp  = r_rresp;
    assign c1_rresp  = r_rresp;
    assign c0_rlast  = r_rlast;
    assign c1_rlast  = r_rlast;
    assign c0_ruser  = r_ruser;
    assign c1_ruser  = r_ruser;
    assign c0_rvalid = r_rvalid && (grant_q == 1'b0);
    assign c1_rvalid = r_rvalid && (grant_q == 1'b1);
    assign mem_rready = (state_q == F_PASS_R) && c_rready[1'(r_owner_q)];

    // ------------------------------------------------------------------
    // Write port arbitration: {cache0 wb, cache1 wb, absorb0, absorb1},
    // fair round-robin; a write-back to a line with a pending absorption
    // holds (the absorption is older and must land first)
    // ------------------------------------------------------------------
    logic [1:0] wb_blocked;
    assign wb_blocked[0] = c0_awvalid && abs_match(c0_awaddr);
    assign wb_blocked[1] = c1_awvalid && abs_match(c1_awaddr);

    logic [3:0] w_cand;
    assign w_cand = {abs_req_q[1], abs_req_q[0],
                     (c1_awvalid && !wb_blocked[1]),
                     (c0_awvalid && !wb_blocked[0])};

    logic [1:0] w_sel;
    always_comb begin
        w_sel = w_rr_q;
        for (int k = 0; k < 4; k++) begin
            if (w_cand[(32'(w_rr_q) + k) % 4])
                w_sel = 2'((32'(w_rr_q) + k) % 4);
        end
    end
    wire        w_valid   = |w_cand;
    wire        w_is_abs  = (w_sel >= 2'd2);
    wire [1:0]  w_dir     = w_is_abs ? (w_sel - 2'd2) : w_sel;

    // registered owner for the burst in flight
    wire        cur_is_abs = (wstate_q == W_IDLE) ? w_is_abs : w_is_abs_q;
    wire [1:0]  cur_dir    = (wstate_q == W_IDLE) ? w_dir : w_owner_q;

    assign mem_awid     = cur_is_abs ? IW'(8'hA0 | 8'(cur_dir))
                                     : c_awid[1'(cur_dir)];
    assign mem_awaddr   = cur_is_abs ? abs_pend_addr_q[1'(cur_dir)]
                                     : c_awaddr[1'(cur_dir)];
    assign mem_awlen    = cur_is_abs ? 8'(FILL_BEATS - 1) : c_awlen[1'(cur_dir)];
    assign mem_awsize   = cur_is_abs ? 3'($clog2(STRB_W)) : c_awsize[1'(cur_dir)];
    assign mem_awburst  = cur_is_abs ? 2'b01 : c_awburst[1'(cur_dir)];
    assign mem_awlock   = cur_is_abs ? 1'b0 : c_awlock[1'(cur_dir)];
    assign mem_awcache  = cur_is_abs ? 4'b0000 : c_awcache[1'(cur_dir)];
    assign mem_awprot   = cur_is_abs ? 3'b000 : c_awprot[1'(cur_dir)];
    assign mem_awqos    = cur_is_abs ? 4'b0000 : c_awqos[1'(cur_dir)];
    assign mem_awregion = cur_is_abs ? 4'b0000 : c_awregion[1'(cur_dir)];
    assign mem_awuser   = cur_is_abs ? '0 : c_awuser[1'(cur_dir)];
    assign mem_awvalid  = (wstate_q == W_AW);

    logic [BUS_WIDTH-1:0] w_data;
    logic [STRB_W-1:0]    w_strb;
    logic                 w_last;
    assign w_data = cur_is_abs
        ? line_buf_q[1'(cur_dir)][32'(w_beat_q) * BUS_WIDTH +: BUS_WIDTH]
        : c_wdata[1'(cur_dir)];
    assign w_strb = cur_is_abs ? {STRB_W{1'b1}} : c_wstrb[1'(cur_dir)];
    assign w_last = cur_is_abs
        ? (w_beat_q == BEAT_INDEX_WIDTH'(FILL_BEATS - 1))
        : c_wlast[1'(cur_dir)];
    assign mem_wdata = w_data;
    assign mem_wstrb = w_strb;
    assign mem_wlast = w_last;
    assign mem_wuser = '0;
    assign mem_wvalid = (wstate_q == W_W);

    assign c0_awready = (wstate_q == W_AW) && !cur_is_abs
                        && (cur_dir == 2'd0) && mem_awready;
    assign c1_awready = (wstate_q == W_AW) && !cur_is_abs
                        && (cur_dir == 2'd1) && mem_awready;
    assign c0_wready  = (wstate_q == W_W) && !cur_is_abs && (cur_dir == 2'd0)
                        && mem_wready;
    assign c1_wready  = (wstate_q == W_W) && !cur_is_abs && (cur_dir == 2'd1)
                        && mem_wready;

    assign c0_bvalid = (wstate_q == W_B) && !cur_is_abs && (cur_dir == 2'd0)
                       && mem_bvalid;
    assign c1_bvalid = (wstate_q == W_B) && !cur_is_abs && (cur_dir == 2'd1)
                       && mem_bvalid;
    assign c0_bid    = mem_bid;
    assign c1_bid    = mem_bid;
    assign c0_bresp  = mem_bresp;
    assign c1_bresp  = mem_bresp;
    assign c0_buser  = mem_buser;
    assign c1_buser  = mem_buser;
    assign mem_bready = (wstate_q == W_B)
                        && (cur_is_abs || c_bready[1'(cur_dir)]);

    // ------------------------------------------------------------------
    // Coherence FSM (owns: pend/buf/abs bookkeeping, snoop and AR/R flow)
    // ------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state_q            <= F_IDLE;
            grant_q            <= 1'b0;
            grant_addr_q       <= '0;
            grant_type_q       <= '0;
            kill_q             <= 1'b0;
            acsnoop_q          <= '0;
            rr_q               <= 1'b0;
            pend_cnt_q[0]      <= '0;
            pend_cnt_q[1]      <= '0;
            pend_ovf_q         <= '0;
            drain_vld_q        <= '0;
            drain_line_q[0]    <= '0;
            drain_line_q[1]    <= '0;
            buf_vld_q          <= '0;
            line_buf_q[0]      <= '0;
            line_buf_q[1]      <= '0;
            abs_pend_vld_q     <= '0;
            abs_pend_addr_q[0] <= '0;
            abs_pend_addr_q[1] <= '0;
            abs_req_q          <= '0;
            beat_q             <= '0;
            replay_rid_q       <= '0;
            crresp_q           <= '0;
            r_owner_q          <= 1'b0;
            beat_count_q       <= '0;
        end else begin
            // request pulse push / grant pop (per-direction FIFO)
            for (int i = 0; i < 2; i++) begin
                automatic logic push = coh_pulse_vld[i];
                automatic logic pop  = g_valid && ((g_dir == 1'b0) ? (i == 0) : (i == 1))
                                       && (state_q == F_IDLE);
                if (push && pop) begin
                    // grant the head (shift down); the new request takes
                    // the last valid slot (full: the freed tail)
                    for (int k = 0; k < PEND_DEPTH - 1; k++) begin
                        pend_line_q[i][k] <= pend_line_q[i][k+1];
                        pend_type_q[i][k] <= pend_type_q[i][k+1];
                    end
                    if (pend_cnt_q[i] == 3'(PEND_DEPTH)) begin
                        pend_line_q[i][PEND_DEPTH-1]
                            <= (i == 0) ? c0_coh_req_addr : c1_coh_req_addr;
                        pend_type_q[i][PEND_DEPTH-1]
                            <= (i == 0) ? c0_coh_req_type : c1_coh_req_type;
                    end else begin
                        pend_line_q[i][PEND_DEPTH-1] <= '0;
                        pend_type_q[i][PEND_DEPTH-1] <= '0;
                        pend_line_q[i][2'(pend_cnt_q[i]) - 2'd1]
                            <= (i == 0) ? c0_coh_req_addr : c1_coh_req_addr;
                        pend_type_q[i][2'(pend_cnt_q[i]) - 2'd1]
                            <= (i == 0) ? c0_coh_req_type : c1_coh_req_type;
                    end
                end else if (push) begin
                    if (pend_cnt_q[i] < 3'(PEND_DEPTH)) begin
                        pend_line_q[i][2'(pend_cnt_q[i])]
                            <= (i == 0) ? c0_coh_req_addr : c1_coh_req_addr;
                        pend_type_q[i][2'(pend_cnt_q[i])]
                            <= (i == 0) ? c0_coh_req_type : c1_coh_req_type;
                        pend_cnt_q[i] <= pend_cnt_q[i] + 3'd1;
                    end else begin
                        pend_ovf_q[i] <= 1'b1;   // debug; TB asserts never
                    end
                end else if (pop) begin
                    for (int k = 0; k < PEND_DEPTH - 1; k++) begin
                        pend_line_q[i][k] <= pend_line_q[i][k+1];
                        pend_type_q[i][k] <= pend_type_q[i][k+1];
                    end
                    pend_line_q[i][PEND_DEPTH-1] <= '0;
                    pend_type_q[i][PEND_DEPTH-1] <= '0;
                    pend_cnt_q[i] <= pend_cnt_q[i] - 3'd1;
                end
            end

            // absorption completion (observed from the write FSM)
            if ((wstate_q == W_B) && w_is_abs_q && mem_bvalid) begin
                abs_pend_vld_q[1'(w_owner_q)] <= 1'b0;
            end

            // drain guard: arm at transaction completion, drop once the
            // peer's FSM settles in a STABLE snoop-safe state. SNOOP is
            // deliberately not a clearing state -- it can be a detour from
            // an uncommitted fill (the pf bypass still armed), and clearing
            // there let a data-expecting AC in against the armed bypass.
            if (state_q == F_DONE) begin
                drain_vld_q[grant_q]  <= 1'b1;
                drain_line_q[grant_q] <= grant_addr_q;
            end else begin
                if (drain_vld_q[0]
                    && ((peer0_state == ST_IDLE) || (peer0_state == ST_LOOKUP)
                        || (peer0_state == ST_HIT_RD)
                        || (peer0_state == ST_HIT_WR)))
                    drain_vld_q[0] <= 1'b0;
                if (drain_vld_q[1]
                    && ((peer1_state == ST_IDLE) || (peer1_state == ST_LOOKUP)
                        || (peer1_state == ST_HIT_RD)
                        || (peer1_state == ST_HIT_WR)))
                    drain_vld_q[1] <= 1'b0;
            end

            // buffer free: at transaction end when no absorption trails,
            // or when a trailing absorption completes
            if ((state_q == F_DONE) && buf_vld_q[grant_q]
                && !abs_pend_vld_q[1'(grant_q)]) begin
                buf_vld_q[grant_q] <= 1'b0;
            end else if ((wstate_q == W_B) && w_is_abs_q && mem_bvalid
                         && buf_vld_q[1'(w_owner_q)]
                         && state_q != F_REPLAY_R
                         && !(state_q == F_REPLAY_AR
                              && 2'(grant_q) == w_owner_q)) begin
                buf_vld_q[1'(w_owner_q)] <= 1'b0;
            end

            unique case (state_q)
                F_IDLE: begin
                    if (g_valid) begin
                        grant_q      <= g_dir;
                        grant_addr_q <= pend_line_q[1'(g_dir)][0];
                        grant_type_q <= pend_type_q[1'(g_dir)][0];
                        kill_q       <= g_kill;
                        acsnoop_q    <= g_kill ? ACSNOOP_MAKE_INVALID
                                     : map_snoop(pend_type_q[1'(g_dir)][0]);
                        rr_q         <= 1 - rr_q;
                        beat_count_q <= '0;
                        state_q      <= F_AC;
                    end
                end

                F_AC: begin
                    if (snoop_ac_accept) begin
                        state_q      <= F_RESP;
                        beat_count_q <= '0;
                    end
                end

                F_RESP: begin
                    if (snoop_cd_beat) begin
                        line_buf_q[1'(grant_q)][32'(beat_count_q) * BUS_WIDTH
                                             +: BUS_WIDTH]
                            <= cddata_w[1'(1 - grant_q)];
                        beat_count_q <= beat_count_q + 8'd1;
                        if (snoop_cd_last) begin
                            buf_vld_q[grant_q] <= 1'b1;
                        end
                    end
                    if (snoop_cr_accept) begin
                        crresp_q <= crresp_w[1'(1 - grant_q)];
                        if (crresp_w[1'(1 - grant_q)][AMBER_CRRESP_DT]) begin
                            if (crresp_w[1'(1 - grant_q)][AMBER_CRRESP_PD]) begin
                                abs_req_q[1'(grant_q)]       <= 1'b1;
                                abs_pend_vld_q[1'(grant_q)]  <= 1'b1;
                                abs_pend_addr_q[1'(grant_q)] <= grant_addr_q;
                            end
                            if (grant_type_q
                                == 3'(AMBER_ACE_CLEAN_UNIQUE)) begin
                                // upgrades carry no data and raise no AR:
                                // the CR completes the transaction (a DT
                                // here would be a protocol error; finish
                                // anyway rather than wait a phantom AR)
                                state_q <= F_DONE;
                            end else begin
                                state_q <= F_REPLAY_AR;
                            end
                        end else begin
                            if (grant_type_q
                                == 3'(AMBER_ACE_CLEAN_UNIQUE)) begin
                                state_q <= F_DONE;
                            end else begin
                                state_q <= F_PASS_AR;
                            end
                        end
                    end
                end

                F_REPLAY_AR: begin
                    // swallow the requester's AR (arready driven high);
                    // the R beats replay from the buffer
                    if (c_arvalid[1'(grant_q)]) begin
                        replay_rid_q <= c_arid[1'(grant_q)];
                        beat_q       <= '0;
                        state_q      <= F_REPLAY_R;
                    end
                end

                F_REPLAY_R: begin
                    if (c_rready[1'(grant_q)]) begin
                        if (beat_q == BEAT_INDEX_WIDTH'(FILL_BEATS - 1)) begin
                            state_q <= F_DONE;
                        end else begin
                            beat_q <= beat_q + BEAT_INDEX_WIDTH'(1);
                        end
                    end
                end

                F_PASS_AR: begin
                    // forward the AR once no absorption to this line is
                    // pending (the memory image must be authoritative)
                    if (mem_arvalid && mem_arready) begin
                        r_owner_q <= grant_q;
                        state_q   <= F_PASS_R;
                    end
                end

                F_PASS_R: begin
                    if (mem_rvalid && c_rready[1'(r_owner_q)] && mem_rlast) begin
                        state_q <= F_DONE;
                    end
                end

                F_DONE: begin
                    // the granted request was consumed at the grant; a
                    // follow-on pulse during this transaction stays pending
                    // (the pending latch is re-armed by its own pulse)
                    state_q <= F_IDLE;
                end

                default: state_q <= F_IDLE;
            endcase

            // absorption request consumed by the write port
            if ((wstate_q == W_AW) && w_is_abs_q && mem_awready) begin
                abs_req_q[1'(w_owner_q)] <= 1'b0;
            end
        end
    end

    // ------------------------------------------------------------------
    // Write FSM (owns only its own sequencing registers)
    // ------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            wstate_q   <= W_IDLE;
            w_owner_q  <= '0;
            w_is_abs_q <= 1'b0;
            w_rr_q     <= '0;
            w_beat_q   <= '0;
        end else begin
            unique case (wstate_q)
                W_IDLE: begin
                    if (w_valid) begin
                        w_owner_q  <= w_dir;
                        w_is_abs_q <= w_is_abs;
                        w_rr_q     <= 2'((32'(w_sel) + 1) % 4);
                        w_beat_q   <= '0;
                        wstate_q   <= W_AW;
                    end
                end
                W_AW: begin
                    if (mem_awready) begin
                        wstate_q <= W_W;
                    end
                end
                W_W: begin
                    if (mem_wready) begin
                        if (w_last) begin
                            wstate_q <= W_B;
                        end else begin
                            w_beat_q <= w_beat_q + BEAT_INDEX_WIDTH'(1);
                        end
                    end
                end
                W_B: begin
                    if (mem_bvalid) begin
                        wstate_q <= W_IDLE;
                    end
                end
                default: wstate_q <= W_IDLE;
            endcase
        end
    end

    // ------------------------------------------------------------------
    // Debug taps
    // ------------------------------------------------------------------
    assign dbg_state      = state_q;
    assign dbg_grant_dir  = grant_q;
    assign dbg_pend_vld   = {(pend_cnt_q[1] != 3'd0),
                             (pend_cnt_q[0] != 3'd0)};
    assign dbg_buf_vld    = buf_vld_q;
    assign dbg_abs_pend   = abs_pend_vld_q;
    assign dbg_kill       = issue_kill;
    assign dbg_acsnoop    = issue_acsnoop;
    assign dbg_grant_addr = grant_addr_q;

endmodule : amber_pair_fabric
