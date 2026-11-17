// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_prime_pair_fabric
// Purpose:
//   The 2-master snoopy manager of the plain-AXI4 jet-prime pair rig,
//   rebuilt as a pipelined fabric (jet-prime TASK-001 step 3). jet's
//   fabric ran ONE coherence transaction at a time: grant, snoop the
//   peer, then (and only then) the memory read, then the next grant.
//   This fabric serializes PER LINE instead: a transaction table holds
//   every request in flight, a request waits only behind an in-flight
//   transaction on its own line (grant-after-completion survives for
//   same-line conflicts only), the memory read is issued alongside the
//   snoop and its data dropped when the peer supplies the line, and
//   several memory reads are outstanding at once (one AXI read ID per
//   table slot). Fair round-robin between the two caches at the grant
//   and at the shared-memory write port.
//
// Documentation: projects/components/cache-ip/jet-prime-mesi-l1/docs/delta/02_pair_fabric.md
// Subsystem: jet-prime (forked from jet at 2be919254, 2026-11-12 -- jet-prime TASK-001;
//            rebuilt pipelined in step 3, 2026-11-16)
//
// Author: sean galloway
// Created: 2026-10-29

`timescale 1ns / 1ps
`include "reset_defs.svh"

//==============================================================================
// Module: jet_prime_pair_fabric
//==============================================================================
// Description:
//   Per direction, the fabric takes the cache's D-8 coherence sideband
//   (coh_req_valid/addr/type: one pulse per fill launch --
//   READ_NOT_SHARED_DIRTY / READ_UNIQUE on a miss, CLEAN_UNIQUE on an
//   upgrade -- and per dirty write-back launch, WRITE_BACK) and the
//   cache's retire sideband (coh_done_valid/id: the MSHR entry retired, or
//   MSHR_COUNT for the upgrade), and:
//
//     fill / upgrade : allocate a table slot when no slot holds the line;
//                      take the requester's AR (the request becomes
//                      post-AR at the cache only now); drive AC to the
//                      PEER; once the AC is accepted, issue the memory AR
//                      (data fills only; a CleanUnique has no data).  The
//                      CR verdict routes the data: no DataTransfer -> the
//                      memory R beats pass through to the requester;
//                      DataTransfer -> the CD line is buffered in the slot
//                      and replayed to the requester, the memory beats
//                      are consumed and dropped (or the AR suppressed if
//                      the verdict is in before it was presented); PassDirty ->
//                      the buffered line is also written to the shared
//                      memory (the point of coherence).  The slot is
//                      freed when the requester has every beat, the
//                      memory read (if any) is drained, the absorption
//                      (if any) has its BRESP, and the requester's retire
//                      pulse for the entry has been seen.
//     write-back     : pure write-port pass-through (AW/W/B), arbitrated
//                      onto the single memory write port with the
//                      absorptions.
//
//   Snoop map (IHI0022 ACSNOOP[3:0]): READ_SHARED /
//   READ_NOT_SHARED_DIRTY -> SNOOP_READ_SHARED (4'h1), READ_UNIQUE ->
//   SNOOP_READ_UNIQUE (4'h7), CLEAN_UNIQUE -> SNOOP_MAKE_INVALID (4'hC).
//
//   Per-line serialization, pulse to retire.  A request whose line is
//   held by a valid slot (either direction) waits ungranted; its AR stays
//   at the cache, so the entry is pre-AR, and jet_prime_control's pre-AR
//   rule answers any snoop to it at the Invalid row with no effect -- the
//   loser's own grant re-resolves against the winner's committed line.
//   The lock is held until the winner's RETIRE (the coh_done sideband),
//   not its last beat: between the last R beat and the retire the
//   winner's entry is post-AR with beats landing, and a snoop there would
//   be answered from the pending-fill bypass with the post-fill state and
//   no data (PF_GUARD) -- an answer that orders the snoop AFTER a fill
//   that must stay ordered before it.  The responder's own sn_safe hold
//   (any done-unretired fill) covers most of that window; the retire
//   sideband closes it exactly, and the amber-era kill rule, drain guard
//   and peer-state wait go with it.
//
//   The AR alongside the snoop.  The memory read starts as soon as the
//   peer has ACCEPTED the AC (not when the CR is back), so with an idle
//   peer the CR arrives a cycle or two before the first memory beat and
//   nothing stalls; a beat arriving before its verdict holds the memory R
//   channel (rready low) for the bounded remainder of the snoop
//   service.  Issuing at AC-accept rather than at grant keeps that stall
//   bounded by the responder, not by the peer's commit backlog.  The one
//   hazard the earlier order (snoop, then AR) prevented for free is a
//   write-back landing in memory between the memory read and the snoop:
//   a WB AW to a line therefore holds while a slot on that line has no
//   CR yet (and, as before, while an absorption to it is pending).
//
//   Point of coherence: a PassDirty response means the peer owned the only
//   correct copy; the forwarded line is also written to the shared memory
//   (AWID 8'hA0|dir) from the slot buffer.  While the absorption is
//   pending the slot keeps the line locked, so no read or write-back to
//   that line reaches memory before it lands.
//
//   Liveness: every wait resolves on an agent that does not wait on this
//   fabric -- the CR (the responder grants whenever its own commits have
//   retired; commits need only landed beats), the requester's rready and
//   retire (local), the memory, and the write port's round-robin.  The
//   requester's AR register is held behind a same-line conflict for the
//   winner's lifetime (bounded), which also holds that cache's later
//   launches -- the cost of keeping the loser pre-AR.
//
//------------------------------------------------------------------------------
// Parameters:
//   FAB_SLOTS      -- transaction table depth (shared by both caches); also
//                     the memory read IDs in use (0 .. FAB_SLOTS-1).  Sized
//                     at 2 * (MSHR_COUNT + 1) nothing ever waits for a slot.
//   SNOOP_INFLIGHT -- ACs accepted by one peer and not yet answered (the
//                     responder serves one at a time; its transport skids
//                     the next).  1 = one snoop per peer at a time.
//   Geometry per l1_pkg (the fabric moves lines; SETS/WAYS are package
//   context only).
//------------------------------------------------------------------------------
//
// Notes:
//   - Single clock / active-low reset (clk / rst_n).
//   - The slot line buffers are one array per peer indexed {slot, beat}:
//     one write port each (that peer's CD beat), two read ports (replay,
//     absorption) -- distributed RAM, payload-only (no reset).
//   - The memory read ID is the slot index; the requester sees its own
//     ARID back (kept in the slot).  Beats of different slots may
//     interleave on a cache's R channel (AXI4 permits it per ID; the
//     jet_prime_fill engine demuxes by ID).
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: the pair rig (jet_prime_pair_rig_tb) and the Genesys2
//     reference harness at REF_CACHE_SEL=3
//   - Consumes: two jet_prime_top memory sides + D-8 sidebands + ACE responders
//   - Package: l1_pkg (ACE request classes)
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/jet-prime-mesi-l1/dv/tests/test_jet_prime_pair_rig.py
//   Plan: dv/testplans/jet_prime_pair_rig_testplan.yaml
//   Run: pytest projects/components/cache-ip/jet-prime-mesi-l1/dv/tests/test_jet_prime_pair_rig.py -v
//
//==============================================================================

module jet_prime_pair_fabric
    import l1_pkg::*;
#(
    parameter int ADDR_WIDTH     = AMBER_ADDR_WIDTH,
    parameter int SETS           = AMBER_SETS,
    parameter int WAYS           = AMBER_WAYS,
    parameter int LINE_BYTES     = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH      = AMBER_BUS_WIDTH,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    parameter int FAB_SLOTS      = 16,
    parameter int SNOOP_INFLIGHT = 2,
    localparam int STRB_W           = BUS_WIDTH / 8,
    localparam int FILL_BEATS       = LINE_BYTES / STRB_W,
    localparam int BEAT_INDEX_WIDTH = $clog2(FILL_BEATS),
    localparam int IW               = AXI_ID_WIDTH,
    localparam int UW               = AXI_USER_WIDTH,
    localparam int SLOT_W           = (FAB_SLOTS > 1) ? $clog2(FAB_SLOTS) : 1,
    localparam int OFFSET_W         = $clog2(LINE_BYTES),
    localparam int LINE_W           = ADDR_WIDTH - OFFSET_W
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // ------------------------------------------------------------------
    // Cache 0 / cache 1 AXI4 master-facing ports (the jet_prime_top m_axi_*
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
    // and the retire sideband (one pulse per retired entry / completed
    // upgrade; the id is the entry's read ID, MSHR_COUNT for the upgrade)
    // ------------------------------------------------------------------
    input  logic                        c0_coh_req_valid,
    input  logic [ADDR_WIDTH-1:0]       c0_coh_req_addr,
    input  logic [2:0]                  c0_coh_req_type,
    input  logic                        c1_coh_req_valid,
    input  logic [ADDR_WIDTH-1:0]       c1_coh_req_addr,
    input  logic [2:0]                  c1_coh_req_type,
    input  logic                        c0_coh_done_valid,
    input  logic [IW-1:0]               c0_coh_done_id,
    input  logic                        c1_coh_done_valid,
    input  logic [IW-1:0]               c1_coh_done_id,

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
    output logic                        dbg_busy,         // any slot valid
    output logic [FAB_SLOTS-1:0]        dbg_slot_vld,
    output logic [1:0]                  dbg_pend_vld,
    output logic                        dbg_abs_pend,     // an absorption not yet landed
    output logic                        dbg_grant,        // a grant this cycle
    output logic                        dbg_grant_dir,
    output logic [ADDR_WIDTH-1:0]       dbg_grant_addr,
    output logic [SLOT_W-1:0]           dbg_grant_slot
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the FUBs)
    // ------------------------------------------------------------------
    initial begin
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("jet_prime_pair_fabric: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0 || FILL_BEATS < 2)
            $error("jet_prime_pair_fabric: LINE_BYTES / BUS_WIDTH*8 must be a power of two >= 2");
        if ((BUS_WIDTH % 8) != 0)
            $error("jet_prime_pair_fabric: BUS_WIDTH must be a multiple of 8");
        if (FAB_SLOTS < 2 || (1 << SLOT_W) < FAB_SLOTS)
            $error("jet_prime_pair_fabric: FAB_SLOTS must be >= 2");
        if ((1 << IW) < FAB_SLOTS)
            $error("jet_prime_pair_fabric: 2**AXI_ID_WIDTH must cover FAB_SLOTS (the memory read IDs)");
        if (SNOOP_INFLIGHT < 1)
            $error("jet_prime_pair_fabric: SNOOP_INFLIGHT must be >= 1");
    end

    // ------------------------------------------------------------------
    // Encodings
    // ------------------------------------------------------------------
    localparam logic [3:0] ACSNOOP_READ_SHARED  = 4'h1;   // IHI0022
    localparam logic [3:0] ACSNOOP_READ_UNIQUE  = 4'h7;
    localparam logic [3:0] ACSNOOP_MAKE_INVALID = 4'hC;
    // ReadNotSharedDirty is issued on the upstream AR channel, but the
    // fabric still probes the peer with a READ_SHARED snoop (the two
    // request classes differ only in upstream ARSNOOP; peer resolution
    // and PassDirty handling are identical for this 2-cache fabric).

    function automatic logic [3:0] map_snoop(input logic [2:0] req_type);
        case (req_type)
            AMBER_ACE_READ_SHARED,
            AMBER_ACE_READ_NOT_SHARED_DIRTY: return ACSNOOP_READ_SHARED;
            AMBER_ACE_READ_UNIQUE:           return ACSNOOP_READ_UNIQUE;
            default:                         return ACSNOOP_MAKE_INVALID;
        endcase
    endfunction

    function automatic logic is_nodata(input logic [2:0] req_type);
        return (req_type == 3'(AMBER_ACE_CLEAN_UNIQUE))
            || (req_type == 3'(AMBER_ACE_MAKE_UNIQUE));
    endfunction

    /* verilator lint_off UNUSEDSIGNAL */
    function automatic logic [LINE_W-1:0] line_of(input logic [ADDR_WIDTH-1:0] addr);
        return addr[ADDR_WIDTH-1 -: LINE_W];   // the offset bits are not the line
    endfunction
    /* verilator lint_on UNUSEDSIGNAL */

    localparam int SNQ_W   = SLOT_W + 1;                 // snoop queue count
    localparam int SNI_W   = $clog2(SNOOP_INFLIGHT + 1); // issued count
    localparam int SNI_IW  = (SNOOP_INFLIGHT > 1) ? $clog2(SNOOP_INFLIGHT) : 1; // issued index
    localparam int PEND_DEPTH = 4;
    localparam int BUF_AW  = SLOT_W + BEAT_INDEX_WIDTH;  // {slot, beat}

    // ------------------------------------------------------------------
    // Cache-side channel aggregation
    // ------------------------------------------------------------------
    logic [1:0] c_arvalid, c_arready, c_rready;
    logic [IW-1:0]         c_arid [2];
    logic [ADDR_WIDTH-1:0] c_araddr [2];
    logic [7:0]            c_arlen [2];
    logic [3:0]            c_arcache [2];
    logic [2:0]            c_arprot [2];
    logic [UW-1:0]         c_aruser [2];

    assign c_arvalid = {c1_arvalid, c0_arvalid};
    assign c_rready  = {c1_rready, c0_rready};
    assign c_arid[0] = c0_arid;         assign c_arid[1] = c1_arid;
    assign c_araddr[0] = c0_araddr;     assign c_araddr[1] = c1_araddr;
    assign c_arlen[0] = c0_arlen;       assign c_arlen[1] = c1_arlen;
    assign c_arcache[0] = c0_arcache;   assign c_arcache[1] = c1_arcache;
    assign c_arprot[0] = c0_arprot;     assign c_arprot[1] = c1_arprot;
    assign c_aruser[0] = c0_aruser;     assign c_aruser[1] = c1_aruser;

    logic [1:0] c_awvalid, c_wvalid, c_bready;
    logic [IW-1:0]         c_awid [2];
    logic [ADDR_WIDTH-1:0] c_awaddr [2];
    logic [7:0]            c_awlen [2];
    logic [2:0]            c_awsize [2];
    logic [1:0]            c_awburst [2];
    logic                  c_awlock [2];
    logic [3:0]            c_awcache [2];
    logic [2:0]            c_awprot [2];
    logic [3:0]            c_awqos [2];
    logic [3:0]            c_awregion [2];
    logic [UW-1:0]         c_awuser [2];
    logic [BUS_WIDTH-1:0]  c_wdata [2];
    logic [STRB_W-1:0]     c_wstrb [2];
    logic                  c_wlast [2];

    assign c_awvalid = {c1_awvalid, c0_awvalid};
    assign c_wvalid  = {c1_wvalid, c0_wvalid};
    assign c_bready  = {c1_bready, c0_bready};
    assign c_awid[0] = c0_awid;         assign c_awid[1] = c1_awid;
    assign c_awaddr[0] = c0_awaddr;     assign c_awaddr[1] = c1_awaddr;
    assign c_awlen[0] = c0_awlen;       assign c_awlen[1] = c1_awlen;
    assign c_awsize[0] = c0_awsize;     assign c_awsize[1] = c1_awsize;
    assign c_awburst[0] = c0_awburst;   assign c_awburst[1] = c1_awburst;
    assign c_awlock[0] = c0_awlock;     assign c_awlock[1] = c1_awlock;
    assign c_awcache[0] = c0_awcache;   assign c_awcache[1] = c1_awcache;
    assign c_awprot[0] = c0_awprot;     assign c_awprot[1] = c1_awprot;
    assign c_awqos[0] = c0_awqos;       assign c_awqos[1] = c1_awqos;
    assign c_awregion[0] = c0_awregion; assign c_awregion[1] = c1_awregion;
    assign c_awuser[0] = c0_awuser;     assign c_awuser[1] = c1_awuser;
    assign c_wdata[0] = c0_wdata;       assign c_wdata[1] = c1_wdata;
    assign c_wstrb[0] = c0_wstrb;       assign c_wstrb[1] = c1_wstrb;
    assign c_wlast[0] = c0_wlast;       assign c_wlast[1] = c1_wlast;

    logic [1:0] acready, crvalid, cdvalid, cdlast;
    logic [AMBER_CRRESP_WIDTH-1:0] crresp_w [2];
    logic [BUS_WIDTH-1:0]          cddata_w [2];
    assign acready = {s1_acready, s0_acready};
    assign crvalid = {s1_crvalid, s0_crvalid};
    assign cdvalid = {s1_cdvalid, s0_cdvalid};
    assign cdlast  = {s1_cdlast, s0_cdlast};
    assign crresp_w[0] = s0_crresp;     assign crresp_w[1] = s1_crresp;
    assign cddata_w[0] = s0_cddata;     assign cddata_w[1] = s1_cddata;

    logic [1:0]            coh_req_vld;
    logic [ADDR_WIDTH-1:0] coh_req_addr [2];
    logic [2:0]            coh_req_type [2];
    assign coh_req_vld[0] = c0_coh_req_valid && (c0_coh_req_type != 3'(AMBER_ACE_WRITE_BACK));
    assign coh_req_vld[1] = c1_coh_req_valid && (c1_coh_req_type != 3'(AMBER_ACE_WRITE_BACK));
    assign coh_req_addr[0] = c0_coh_req_addr; assign coh_req_addr[1] = c1_coh_req_addr;
    assign coh_req_type[0] = c0_coh_req_type; assign coh_req_type[1] = c1_coh_req_type;

    logic [1:0]    coh_done_vld;
    logic [IW-1:0] coh_done_id [2];
    assign coh_done_vld   = {c1_coh_done_valid, c0_coh_done_valid};
    assign coh_done_id[0] = c0_coh_done_id;   assign coh_done_id[1] = c1_coh_done_id;

    // ------------------------------------------------------------------
    // Transaction table
    // ------------------------------------------------------------------
    logic [FAB_SLOTS-1:0]  r_vld;
    logic [FAB_SLOTS-1:0]  r_dir;
    logic [LINE_W-1:0]     r_line   [FAB_SLOTS];
    logic [2:0]            r_type   [FAB_SLOTS];
    logic [FAB_SLOTS-1:0]  r_nodata;
    logic [FAB_SLOTS-1:0]  r_ar_taken;
    logic [IW-1:0]         r_arid   [FAB_SLOTS];
    logic [3:0]            r_arcache[FAB_SLOTS];
    logic [2:0]            r_arprot [FAB_SLOTS];
    logic [UW-1:0]         r_aruser [FAB_SLOTS];
    logic [FAB_SLOTS-1:0]  r_ac_done;
    logic [FAB_SLOTS-1:0]  r_cr_done;
    logic [FAB_SLOTS-1:0]  r_dt;
    logic [FAB_SLOTS-1:0]  r_pd;
    logic [FAB_SLOTS-1:0]  r_mem_issued;
    logic [FAB_SLOTS-1:0]  r_mem_done;
    logic [FAB_SLOTS-1:0]  r_rpl_done;
    logic [FAB_SLOTS-1:0]  r_abs_issued;
    logic [FAB_SLOTS-1:0]  r_abs_done;
    logic [FAB_SLOTS-1:0]  r_rack;

    // the requester has every beat it will get from this transaction
    logic [FAB_SLOTS-1:0]  w_delivered;
    logic [FAB_SLOTS-1:0]  w_free_now;
    logic                  w_mar_vld;       // a memory AR is presented this cycle
    logic [SLOT_W-1:0]     w_mar_slot;      // (defined with the AR issue below)
    always_comb begin
        for (int s = 0; s < FAB_SLOTS; s++) begin
            w_delivered[s] = (r_dt[s] | r_nodata[s]) ? r_rpl_done[s] : r_mem_done[s];
            // a slot whose memory AR is presented this cycle is not free: the
            // AR is held and WILL issue (a DataTransfer verdict on a held AR
            // leaves the slot deliverable while its read is still to come,
            // and the free would otherwise fire in the handshake's own cycle
            // -- the fabric formal's ap_free_complete, step 4)
            w_free_now[s]  = r_vld[s] & r_cr_done[s] & w_delivered[s]
                             & (~r_mem_issued[s] | r_mem_done[s])
                             & ~(w_mar_vld & (w_mar_slot == SLOT_W'(s)))
                             & (~r_pd[s] | r_abs_done[s])
                             & r_rack[s];
        end
    end

    // ------------------------------------------------------------------
    // Per-direction pending-request queue (the sideband pulses, in order;
    // a request waits here ungranted while its line is held or the table
    // is full).  The cache's read transport skids its ARs, so a cache can
    // run a few launches ahead of the AR this fabric holds (the pulses and
    // the ARs stay in launch order); the depth covers the skid, and the
    // overflow flag is a TB-checked debug tap.
    // ------------------------------------------------------------------
    logic [2:0]              r_pend_cnt  [2];
    logic [ADDR_WIDTH-1:0]   r_pend_addr [2][PEND_DEPTH];
    logic [2:0]              r_pend_type [2][PEND_DEPTH];
    logic [1:0]              r_pend_ovf;   // debug only (TB-checked)

    // the request considered for a grant this cycle: the queue head, or
    // the live pulse when the queue is empty (bypass: one cycle saved on
    // every uncontended miss)
    logic [1:0]              w_cand_vld;
    logic [ADDR_WIDTH-1:0]   w_cand_addr [2];
    logic [2:0]              w_cand_type [2];
    logic [1:0]              w_cand_live;
    always_comb begin
        for (int d = 0; d < 2; d++) begin
            if (r_pend_cnt[d] != 3'd0) begin
                w_cand_vld[d]  = 1'b1;
                w_cand_live[d] = 1'b0;
                w_cand_addr[d] = r_pend_addr[d][0];
                w_cand_type[d] = r_pend_type[d][0];
            end else begin
                w_cand_vld[d]  = coh_req_vld[d];
                w_cand_live[d] = 1'b1;
                w_cand_addr[d] = coh_req_addr[d];
                w_cand_type[d] = coh_req_type[d];
            end
        end
    end

    // per-line lock: any valid slot on the candidate's line
    logic [1:0] w_cand_locked;
    always_comb begin
        for (int d = 0; d < 2; d++) begin
            w_cand_locked[d] = 1'b0;
            for (int s = 0; s < FAB_SLOTS; s++) begin
                if (r_vld[s] && (r_line[s] == line_of(w_cand_addr[d])))
                    w_cand_locked[d] = 1'b1;
            end
        end
    end

    // free slot (lowest index)
    logic              w_slot_free;
    logic [SLOT_W-1:0] w_slot_idx;
    always_comb begin
        w_slot_free = 1'b0;
        w_slot_idx  = '0;
        for (int s = FAB_SLOTS - 1; s >= 0; s--) begin
            if (!r_vld[s]) begin
                w_slot_free = 1'b1;
                w_slot_idx  = SLOT_W'(s);
            end
        end
    end

    // an AR waits to be taken for this direction (granted last cycle or
    // earlier, AR not yet handshaken): no second grant to the direction
    // until it is -- the cache presents ARs in launch order and the next
    // launch cannot happen before this AR is taken, so the pairing is
    // exact
    logic [1:0]        r_arw_vld;
    logic [SLOT_W-1:0] r_arw_slot [2];

    logic [1:0] w_cand_ok;
    logic       r_rr;
    logic       w_grant;
    logic       w_grant_dir;
    always_comb begin
        for (int d = 0; d < 2; d++)
            w_cand_ok[d] = w_cand_vld[d] & ~w_cand_locked[d] & w_slot_free & ~r_arw_vld[d];
        if (w_cand_ok[r_rr])
            w_grant_dir = r_rr;
        else
            w_grant_dir = ~r_rr;
        w_grant = w_cand_ok[0] | w_cand_ok[1];
    end

    // ------------------------------------------------------------------
    // Cache AR take: arready from registers only (the slot granted a cycle
    // or more ago); the AR's line must be the slot's (sim-checked)
    // ------------------------------------------------------------------
    assign c_arready[0] = r_arw_vld[0];
    assign c_arready[1] = r_arw_vld[1];
    assign c0_arready = c_arready[0];
    assign c1_arready = c_arready[1];
    wire [1:0] w_ar_take = c_arvalid & c_arready;

    // ------------------------------------------------------------------
    // Snoop queues: per peer p, the slots (dir = 1-p) awaiting an AC in
    // grant order, and the ACs accepted but not yet answered (CR pairs by
    // order; the responder serves one at a time, its transport skids the
    // next)
    // ------------------------------------------------------------------
    logic [SLOT_W-1:0] r_snq [2][FAB_SLOTS];
    logic [SNQ_W-1:0]  r_snq_cnt [2];
    logic [SLOT_W-1:0] r_sni [2][SNOOP_INFLIGHT];
    logic [SNI_W-1:0]  r_sni_cnt [2];
    logic [BEAT_INDEX_WIDTH-1:0] r_cd_beat [2];

    logic [1:0] w_ac_vld, w_ac_hs, w_cr_hs, w_cd_hs;
    logic [SLOT_W-1:0] w_ac_slot [2];
    logic [SLOT_W-1:0] w_sni_head [2];
    always_comb begin
        for (int p = 0; p < 2; p++) begin
            w_ac_slot[p]  = r_snq[p][0];
            w_ac_vld[p]   = (r_snq_cnt[p] != '0) && (r_sni_cnt[p] < SNI_W'(SNOOP_INFLIGHT));
            w_ac_hs[p]    = w_ac_vld[p] & acready[p];
            w_sni_head[p] = r_sni[p][0];
            w_cr_hs[p]    = crvalid[p] & (r_sni_cnt[p] != '0);
            w_cd_hs[p]    = cdvalid[p] & (r_sni_cnt[p] != '0);
        end
    end

    assign s0_acaddr  = {r_line[w_ac_slot[0]], OFFSET_W'(0)};
    assign s1_acaddr  = {r_line[w_ac_slot[1]], OFFSET_W'(0)};
    assign s0_acsnoop = map_snoop(r_type[w_ac_slot[0]]);
    assign s1_acsnoop = map_snoop(r_type[w_ac_slot[1]]);
    assign s0_acprot  = 3'b000;
    assign s1_acprot  = 3'b000;
    assign s0_acvalid = w_ac_vld[0];
    assign s1_acvalid = w_ac_vld[1];
    // CR / CD accepted whenever a snoop is outstanding at that peer (the
    // buffer write and the verdict land in the same cycle)
    assign s0_crready = (r_sni_cnt[0] != '0);
    assign s1_crready = (r_sni_cnt[1] != '0);
    assign s0_cdready = (r_sni_cnt[0] != '0);
    assign s1_cdready = (r_sni_cnt[1] != '0);

    // ------------------------------------------------------------------
    // Memory AR issue: a slot whose AR is taken, whose AC the peer has
    // accepted, with data to fetch and no DataTransfer verdict yet.
    // Lowest index first (every candidate issues within FAB_SLOTS cycles).
    // Once presented the AR is HELD until its handshake (AXI A3.2.1: a
    // presented AR is neither withdrawn nor changed) -- without the hold a
    // lower slot's AC acceptance during an arready stall re-pointed the
    // presented AR at the other slot (the fabric formal's ap_mar_stable,
    // step 4).  A DataTransfer verdict landing on a held AR therefore
    // drains the read's beats instead of suppressing it.
    // ------------------------------------------------------------------
    logic              w_marc_vld;      // the lowest-index candidate
    logic [SLOT_W-1:0] w_marc_slot;
    logic              r_mar_vld;       // a presented AR not yet taken
    logic [SLOT_W-1:0] r_mar_slot;
    always_comb begin
        w_marc_vld  = 1'b0;
        w_marc_slot = '0;
        for (int s = FAB_SLOTS - 1; s >= 0; s--) begin
            if (r_vld[s] && r_ar_taken[s] && !r_nodata[s] && !r_mem_issued[s]
                && r_ac_done[s] && !(r_cr_done[s] && r_dt[s])) begin
                w_marc_vld  = 1'b1;
                w_marc_slot = SLOT_W'(s);
            end
        end
    end
    assign w_mar_vld  = r_mar_vld | w_marc_vld;
    assign w_mar_slot = r_mar_vld ? r_mar_slot : w_marc_slot;
    wire   w_mar_hs   = w_mar_vld & mem_arready;

    assign mem_arid     = IW'(w_mar_slot);
    assign mem_araddr   = {r_line[w_mar_slot], OFFSET_W'(0)};
    assign mem_arlen    = 8'(FILL_BEATS - 1);
    assign mem_arsize   = 3'($clog2(STRB_W));
    assign mem_arburst  = 2'b01;
    assign mem_arlock   = 1'b0;
    assign mem_arcache  = r_arcache[w_mar_slot];
    assign mem_arprot   = r_arprot[w_mar_slot];
    assign mem_arqos    = 4'b0000;
    assign mem_arregion = 4'b0000;
    assign mem_aruser   = r_aruser[w_mar_slot];
    assign mem_arvalid  = w_mar_vld;

    // ------------------------------------------------------------------
    // Memory R: the beat's slot (rid) decides -- forward (no DT), drop
    // (DT, the replay carries the line), or hold until the verdict
    // ------------------------------------------------------------------
    wire [SLOT_W-1:0] w_mr_slot = mem_rid[SLOT_W-1:0];
    wire w_mr_fwd  = mem_rvalid & r_cr_done[w_mr_slot] & ~r_dt[w_mr_slot];
    wire w_mr_drop = mem_rvalid & r_cr_done[w_mr_slot] &  r_dt[w_mr_slot];
    wire w_mr_dir  = r_dir[w_mr_slot];

    // ------------------------------------------------------------------
    // Replay per direction: the DT line from the slot buffer, or the single
    // no-data beat of an upgrade.  A memory beat for the direction has
    // priority (the memory R channel is the shared resource); the replay
    // fills the gaps, and once presented it holds until accepted (AXI
    // payload stability).
    // ------------------------------------------------------------------
    logic [1:0]        r_rpl_vld;
    logic [SLOT_W-1:0] r_rpl_slot [2];
    logic [BEAT_INDEX_WIDTH-1:0] r_rpl_beat [2];
    logic [1:0]        r_rpl_hold;

    // replay candidate per direction (lowest index): verdict in, line
    // buffered (CD before CR) or no data to replay, not yet replayed
    logic [1:0]        w_rplc_vld;
    logic [SLOT_W-1:0] w_rplc_slot [2];
    always_comb begin
        for (int d = 0; d < 2; d++) begin
            w_rplc_vld[d]  = 1'b0;
            w_rplc_slot[d] = '0;
            for (int s = FAB_SLOTS - 1; s >= 0; s--) begin
                if (r_vld[s] && (r_dir[s] == 1'(d)) && r_cr_done[s] && r_ar_taken[s]
                    && (r_dt[s] || r_nodata[s]) && !r_rpl_done[s]
                    && !(r_rpl_vld[d] && (r_rpl_slot[d] == SLOT_W'(s)))) begin
                    w_rplc_vld[d]  = 1'b1;
                    w_rplc_slot[d] = SLOT_W'(s);
                end
            end
        end
    end

    // slot line buffers: one per PEER (the CD source), indexed {slot, beat}.
    // One write port each (that peer's CD beat) and two asynchronous reads
    // (the replay of the other direction, the absorption) -- distributed
    // RAM.  A single array written from both peers would have two write
    // ports and come out as flops behind 272:1 muxes (35 k LUT, measured
    // out of context on the first build of this fabric).
    localparam int BUF_DEPTH = FAB_SLOTS * FILL_BEATS;
    (* ram_style = "distributed" *)
    /* synthesis ramstyle = "MLAB" */
    logic [BUS_WIDTH-1:0] r_buf0 [BUF_DEPTH];
    (* ram_style = "distributed" *)
    /* synthesis ramstyle = "MLAB" */
    logic [BUS_WIDTH-1:0] r_buf1 [BUF_DEPTH];
    // direction d's line was supplied by peer 1-d, so it sits in that
    // peer's buffer
    logic [BUF_AW-1:0] w_rpl_raddr [2];
    logic [BUS_WIDTH-1:0] w_rpl_rdata [2];
    always_comb begin
        for (int d = 0; d < 2; d++)
            w_rpl_raddr[d] = {r_rpl_slot[d], r_rpl_beat[d]};
        w_rpl_rdata[0] = r_buf1[w_rpl_raddr[0]];
        w_rpl_rdata[1] = r_buf0[w_rpl_raddr[1]];
    end

    // per-direction R output: memory beat (priority) or replay beat
    logic [1:0] w_mem_want;      // a memory beat for this direction
    logic [1:0] w_rpl_pres;      // the replay is presented this direction
    logic [1:0] w_mem_pres;      // the memory beat is presented
    logic [1:0] w_rvalid;
    logic [1:0] w_rpl_hs, w_mem_hs;
    always_comb begin
        for (int d = 0; d < 2; d++) begin
            w_mem_want[d] = w_mr_fwd & (w_mr_dir == 1'(d));
            w_rpl_pres[d] = r_rpl_vld[d] & (r_rpl_hold[d] | ~w_mem_want[d]);
            w_mem_pres[d] = w_mem_want[d] & ~w_rpl_pres[d];
            w_rvalid[d]   = w_rpl_pres[d] | w_mem_pres[d];
            w_rpl_hs[d]   = w_rpl_pres[d] & c_rready[d];
            w_mem_hs[d]   = w_mem_pres[d] & c_rready[d];
        end
    end
    wire w_mr_hs = w_mem_hs[0] | w_mem_hs[1] | w_mr_drop;
    assign mem_rready = w_mr_drop | (w_mr_fwd & w_mem_pres[w_mr_dir] & c_rready[w_mr_dir]);

    logic [IW-1:0]        r_out_rid [2];
    logic [BUS_WIDTH-1:0] r_out_rdata [2];
    logic [1:0]           r_out_rresp [2];
    logic                 r_out_rlast [2];
    always_comb begin
        for (int d = 0; d < 2; d++) begin
            if (w_rpl_pres[d]) begin
                r_out_rid[d]   = r_arid[r_rpl_slot[d]];
                r_out_rdata[d] = r_nodata[r_rpl_slot[d]] ? '0 : w_rpl_rdata[d];
                r_out_rresp[d] = 2'b00;
                r_out_rlast[d] = r_nodata[r_rpl_slot[d]]
                                 | (r_rpl_beat[d] == BEAT_INDEX_WIDTH'(FILL_BEATS - 1));
            end else begin
                r_out_rid[d]   = r_arid[w_mr_slot];
                r_out_rdata[d] = mem_rdata;
                r_out_rresp[d] = mem_rresp;
                r_out_rlast[d] = mem_rlast;
            end
        end
    end

    assign c0_rid    = r_out_rid[0];
    assign c1_rid    = r_out_rid[1];
    assign c0_rdata  = r_out_rdata[0];
    assign c1_rdata  = r_out_rdata[1];
    assign c0_rresp  = r_out_rresp[0];
    assign c1_rresp  = r_out_rresp[1];
    assign c0_rlast  = r_out_rlast[0];
    assign c1_rlast  = r_out_rlast[1];
    assign c0_ruser  = w_rpl_pres[0] ? '0 : mem_ruser;
    assign c1_ruser  = w_rpl_pres[1] ? '0 : mem_ruser;
    assign c0_rvalid = w_rvalid[0];
    assign c1_rvalid = w_rvalid[1];

    // ------------------------------------------------------------------
    // Write port: write-back pass-through + PassDirty absorption, one
    // burst in flight system-wide, fair round-robin {wb0, wb1, absorb}.
    // A write-back to a line with a slot that has no verdict yet, or an
    // absorption not yet landed, holds.
    // ------------------------------------------------------------------
    localparam logic [1:0] W_IDLE = 2'd0;
    localparam logic [1:0] W_AW   = 2'd1;
    localparam logic [1:0] W_W    = 2'd2;
    localparam logic [1:0] W_B    = 2'd3;

    logic [1:0]        r_wstate;
    logic [1:0]        r_w_sel;        // 0/1 = wb of cache, 2 = absorb
    logic [SLOT_W-1:0] r_w_slot;
    logic [1:0]        r_w_rr;
    logic [BEAT_INDEX_WIDTH-1:0] r_w_beat;

    logic [1:0] w_wb_blocked;
    always_comb begin
        for (int d = 0; d < 2; d++) begin
            w_wb_blocked[d] = 1'b0;
            for (int s = 0; s < FAB_SLOTS; s++) begin
                if (r_vld[s] && (r_line[s] == line_of(c_awaddr[d]))
                    && (!r_cr_done[s] || (r_pd[s] && !r_abs_done[s])))
                    w_wb_blocked[d] = 1'b1;
            end
        end
    end

    // absorption candidate: lowest slot with PassDirty not yet written
    logic              w_absc_vld;
    logic [SLOT_W-1:0] w_absc_slot;
    always_comb begin
        w_absc_vld  = 1'b0;
        w_absc_slot = '0;
        for (int s = FAB_SLOTS - 1; s >= 0; s--) begin
            if (r_vld[s] && r_cr_done[s] && r_pd[s] && !r_abs_issued[s]) begin
                w_absc_vld  = 1'b1;
                w_absc_slot = SLOT_W'(s);
            end
        end
    end

    logic [2:0] w_wcand;
    assign w_wcand = {w_absc_vld,
                      (c_awvalid[1] && !w_wb_blocked[1]),
                      (c_awvalid[0] && !w_wb_blocked[0])};
    logic [1:0] w_wsel;
    always_comb begin
        w_wsel = r_w_rr;
        for (int k = 2; k >= 0; k--) begin
            if (w_wcand[(32'(r_w_rr) + k) % 3])
                w_wsel = 2'((32'(r_w_rr) + k) % 3);
        end
    end
    wire w_wvalid = |w_wcand;

    wire        w_cur_abs = (r_w_sel == 2'd2);
    wire        w_cur_dir = r_w_sel[0];
    logic [BUF_AW-1:0]    w_abs_raddr;
    logic [BUS_WIDTH-1:0] w_abs_rdata;
    assign w_abs_raddr = {r_w_slot, r_w_beat};
    // the absorbed line came from the requester's peer
    assign w_abs_rdata = r_dir[r_w_slot] ? r_buf0[w_abs_raddr] : r_buf1[w_abs_raddr];

    assign mem_awid     = w_cur_abs ? IW'(8'hA0 | 8'(r_dir[r_w_slot]))
                                    : c_awid[w_cur_dir];
    assign mem_awaddr   = w_cur_abs ? {r_line[r_w_slot], OFFSET_W'(0)}
                                    : c_awaddr[w_cur_dir];
    assign mem_awlen    = w_cur_abs ? 8'(FILL_BEATS - 1) : c_awlen[w_cur_dir];
    assign mem_awsize   = w_cur_abs ? 3'($clog2(STRB_W)) : c_awsize[w_cur_dir];
    assign mem_awburst  = w_cur_abs ? 2'b01 : c_awburst[w_cur_dir];
    assign mem_awlock   = w_cur_abs ? 1'b0 : c_awlock[w_cur_dir];
    assign mem_awcache  = w_cur_abs ? 4'b0000 : c_awcache[w_cur_dir];
    assign mem_awprot   = w_cur_abs ? 3'b000 : c_awprot[w_cur_dir];
    assign mem_awqos    = w_cur_abs ? 4'b0000 : c_awqos[w_cur_dir];
    assign mem_awregion = w_cur_abs ? 4'b0000 : c_awregion[w_cur_dir];
    assign mem_awuser   = w_cur_abs ? '0 : c_awuser[w_cur_dir];
    assign mem_awvalid  = (r_wstate == W_AW) && (w_cur_abs || c_awvalid[w_cur_dir]);

    wire w_wlast = w_cur_abs ? (r_w_beat == BEAT_INDEX_WIDTH'(FILL_BEATS - 1))
                             : c_wlast[w_cur_dir];
    assign mem_wdata  = w_cur_abs ? w_abs_rdata : c_wdata[w_cur_dir];
    assign mem_wstrb  = w_cur_abs ? {STRB_W{1'b1}} : c_wstrb[w_cur_dir];
    assign mem_wlast  = w_wlast;
    assign mem_wuser  = '0;
    assign mem_wvalid = (r_wstate == W_W) && (w_cur_abs || c_wvalid[w_cur_dir]);

    assign c0_awready = (r_wstate == W_AW) && !w_cur_abs && (w_cur_dir == 1'b0) && mem_awready;
    assign c1_awready = (r_wstate == W_AW) && !w_cur_abs && (w_cur_dir == 1'b1) && mem_awready;
    assign c0_wready  = (r_wstate == W_W) && !w_cur_abs && (w_cur_dir == 1'b0) && mem_wready;
    assign c1_wready  = (r_wstate == W_W) && !w_cur_abs && (w_cur_dir == 1'b1) && mem_wready;
    assign c0_bvalid  = (r_wstate == W_B) && !w_cur_abs && (w_cur_dir == 1'b0) && mem_bvalid;
    assign c1_bvalid  = (r_wstate == W_B) && !w_cur_abs && (w_cur_dir == 1'b1) && mem_bvalid;
    assign c0_bid     = mem_bid;
    assign c1_bid     = mem_bid;
    assign c0_bresp   = mem_bresp;
    assign c1_bresp   = mem_bresp;
    assign c0_buser   = mem_buser;
    assign c1_buser   = mem_buser;
    assign mem_bready = (r_wstate == W_B) && (w_cur_abs || c_bready[w_cur_dir]);

    // ------------------------------------------------------------------
    // Retire sideband: the requester's entry (by read ID) is gone -- the
    // line is committed in its array and the lock may drop once the
    // fabric's own bookkeeping for the slot is complete
    // ------------------------------------------------------------------
    logic [FAB_SLOTS-1:0] w_rack_hit;
    always_comb begin
        for (int s = 0; s < FAB_SLOTS; s++) begin
            w_rack_hit[s] = r_vld[s] & r_ar_taken[s] & ~r_rack[s]
                            & coh_done_vld[r_dir[s]]
                            & (coh_done_id[r_dir[s]] == r_arid[s]);
        end
    end

    // ------------------------------------------------------------------
    // Sequential: table, queues, replay, write FSM
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_vld        <= '0;
            r_dir        <= '0;
            r_nodata     <= '0;
            r_ar_taken   <= '0;
            r_ac_done    <= '0;
            r_cr_done    <= '0;
            r_dt         <= '0;
            r_pd         <= '0;
            r_mem_issued <= '0;
            r_mem_done   <= '0;
            r_rpl_done   <= '0;
            r_abs_issued <= '0;
            r_abs_done   <= '0;
            r_rack       <= '0;
            r_rr         <= 1'b0;
            r_pend_ovf   <= '0;
            r_arw_vld    <= '0;
            r_mar_vld    <= 1'b0;
            r_mar_slot   <= '0;
            r_rpl_vld    <= '0;
            r_rpl_hold   <= '0;
            r_wstate     <= W_IDLE;
            r_w_sel      <= '0;
            r_w_slot     <= '0;
            r_w_rr       <= '0;
            r_w_beat     <= '0;
            for (int d = 0; d < 2; d++) begin
                r_pend_cnt[d] <= '0;
                r_arw_slot[d] <= '0;
                r_snq_cnt[d]  <= '0;
                r_sni_cnt[d]  <= '0;
                r_cd_beat[d]  <= '0;
                r_rpl_slot[d] <= '0;
                r_rpl_beat[d] <= '0;
            end
        end else begin
            // ---------------- pending queues: push the pulse, pop the grant
            for (int d = 0; d < 2; d++) begin
                automatic logic push = coh_req_vld[d] & ~(w_grant & (w_grant_dir == 1'(d)) & w_cand_live[d]);
                automatic logic pop  = w_grant & (w_grant_dir == 1'(d)) & ~w_cand_live[d];
                if (pop) begin
                    for (int k = 0; k < PEND_DEPTH - 1; k++) begin
                        r_pend_addr[d][k] <= r_pend_addr[d][k+1];
                        r_pend_type[d][k] <= r_pend_type[d][k+1];
                    end
                    if (push) begin
                        // the new request takes the freed tail slot
                        r_pend_addr[d][2'(r_pend_cnt[d]) - 2'd1] <= coh_req_addr[d];
                        r_pend_type[d][2'(r_pend_cnt[d]) - 2'd1] <= coh_req_type[d];
                    end else begin
                        r_pend_cnt[d] <= r_pend_cnt[d] - 3'd1;
                    end
                end else if (push) begin
                    if (r_pend_cnt[d] < 3'(PEND_DEPTH)) begin
                        r_pend_addr[d][2'(r_pend_cnt[d])] <= coh_req_addr[d];
                        r_pend_type[d][2'(r_pend_cnt[d])] <= coh_req_type[d];
                        r_pend_cnt[d] <= r_pend_cnt[d] + 3'd1;
                    end else begin
                        r_pend_ovf[d] <= 1'b1;
                    end
                end
            end

            // ---------------- grant: allocate the slot, arm the AR take
            if (w_grant) begin
                r_vld[w_slot_idx]        <= 1'b1;
                r_dir[w_slot_idx]        <= w_grant_dir;
                r_line[w_slot_idx]       <= line_of(w_cand_addr[w_grant_dir]);
                r_type[w_slot_idx]       <= w_cand_type[w_grant_dir];
                r_nodata[w_slot_idx]     <= is_nodata(w_cand_type[w_grant_dir]);
                r_ar_taken[w_slot_idx]   <= 1'b0;
                r_ac_done[w_slot_idx]    <= 1'b0;
                r_cr_done[w_slot_idx]    <= 1'b0;
                r_dt[w_slot_idx]         <= 1'b0;
                r_pd[w_slot_idx]         <= 1'b0;
                r_mem_issued[w_slot_idx] <= 1'b0;
                r_mem_done[w_slot_idx]   <= 1'b0;
                r_rpl_done[w_slot_idx]   <= 1'b0;
                r_abs_issued[w_slot_idx] <= 1'b0;
                r_abs_done[w_slot_idx]   <= 1'b0;
                r_rack[w_slot_idx]       <= 1'b0;
                r_arw_vld[w_grant_dir]   <= 1'b1;
                r_arw_slot[w_grant_dir]  <= w_slot_idx;
                r_rr                     <= ~w_grant_dir;
            end

            // ---------------- AR take
            for (int d = 0; d < 2; d++) begin
                if (w_ar_take[d]) begin
                    r_ar_taken[r_arw_slot[d]] <= 1'b1;
                    r_arid[r_arw_slot[d]]     <= c_arid[d];
                    r_arcache[r_arw_slot[d]]  <= c_arcache[d];
                    r_arprot[r_arw_slot[d]]   <= c_arprot[d];
                    r_aruser[r_arw_slot[d]]   <= c_aruser[d];
                    r_arw_vld[d]              <= 1'b0;
                end
            end

            // ---------------- snoop queues per peer (a pop shifts first,
            // a same-cycle push then lands on the freed tail: the later
            // nonblocking assignment wins)
            for (int p = 0; p < 2; p++) begin
                automatic logic push_q = w_grant & (w_grant_dir == 1'(1 - p));
                if (w_ac_hs[p]) begin
                    for (int k = 0; k < FAB_SLOTS - 1; k++)
                        r_snq[p][k] <= r_snq[p][k+1];
                    r_ac_done[w_ac_slot[p]] <= 1'b1;
                end
                if (push_q)
                    r_snq[p][SLOT_W'(r_snq_cnt[p] - SNQ_W'(w_ac_hs[p]))] <= w_slot_idx;
                r_snq_cnt[p] <= r_snq_cnt[p] + SNQ_W'(push_q) - SNQ_W'(w_ac_hs[p]);
                if (w_cr_hs[p]) begin
                    for (int k = 0; k < SNOOP_INFLIGHT - 1; k++)
                        r_sni[p][k] <= r_sni[p][k+1];
                    r_cr_done[w_sni_head[p]] <= 1'b1;
                    r_dt[w_sni_head[p]]      <= crresp_w[p][AMBER_CRRESP_DT];
                    r_pd[w_sni_head[p]]      <= crresp_w[p][AMBER_CRRESP_DT]
                                                & crresp_w[p][AMBER_CRRESP_PD];
                    // the verdict beat the memory AR: nothing to drain (an
                    // AR presented this cycle is held and WILL issue -- its
                    // beats are drained)
                    if (crresp_w[p][AMBER_CRRESP_DT] && !r_mem_issued[w_sni_head[p]]
                        && !(w_mar_vld && (w_mar_slot == w_sni_head[p])))
                        r_mem_done[w_sni_head[p]] <= 1'b1;
                    r_cd_beat[p] <= '0;
                end
                if (w_ac_hs[p])
                    r_sni[p][SNI_IW'(r_sni_cnt[p] - SNI_W'(w_cr_hs[p]))] <= w_ac_slot[p];
                r_sni_cnt[p] <= r_sni_cnt[p] + SNI_W'(w_ac_hs[p]) - SNI_W'(w_cr_hs[p]);
                if (w_cd_hs[p]) begin
                    r_cd_beat[p] <= cdlast[p] ? '0 : r_cd_beat[p] + BEAT_INDEX_WIDTH'(1);
                end
            end

            // ---------------- memory AR / R (a presented AR holds until taken)
            if (w_mar_hs) begin
                r_mem_issued[w_mar_slot] <= 1'b1;
                r_mar_vld                <= 1'b0;
            end else if (w_mar_vld) begin
                r_mar_vld  <= 1'b1;
                r_mar_slot <= w_mar_slot;
            end
            if (w_mr_hs && mem_rlast) begin
                r_mem_done[w_mr_slot] <= 1'b1;
            end

            // ---------------- replay engines
            for (int d = 0; d < 2; d++) begin
                if (r_rpl_vld[d]) begin
                    if (w_rpl_hs[d]) begin
                        r_rpl_hold[d] <= 1'b0;
                        if (r_out_rlast[d]) begin
                            r_rpl_vld[d]               <= 1'b0;
                            r_rpl_done[r_rpl_slot[d]]  <= 1'b1;
                        end else begin
                            r_rpl_beat[d] <= r_rpl_beat[d] + BEAT_INDEX_WIDTH'(1);
                        end
                    end else if (w_rpl_pres[d]) begin
                        r_rpl_hold[d] <= 1'b1;
                    end
                end else if (w_rplc_vld[d]) begin
                    r_rpl_vld[d]  <= 1'b1;
                    r_rpl_slot[d] <= w_rplc_slot[d];
                    r_rpl_beat[d] <= '0;
                    r_rpl_hold[d] <= 1'b0;
                end
            end

            // ---------------- write port FSM
            unique case (r_wstate)
                W_IDLE: begin
                    if (w_wvalid) begin
                        r_w_sel  <= w_wsel;
                        r_w_slot <= w_absc_slot;
                        r_w_rr   <= 2'((32'(w_wsel) + 1) % 3);
                        r_w_beat <= '0;
                        r_wstate <= W_AW;
                        if (w_wsel == 2'd2)
                            r_abs_issued[w_absc_slot] <= 1'b1;
                    end
                end
                W_AW: begin
                    if (mem_awvalid && mem_awready) r_wstate <= W_W;
                end
                W_W: begin
                    if (mem_wvalid && mem_wready) begin
                        if (w_wlast) r_wstate <= W_B;
                        else         r_w_beat <= r_w_beat + BEAT_INDEX_WIDTH'(1);
                    end
                end
                W_B: begin
                    if (mem_bvalid && mem_bready) begin
                        r_wstate <= W_IDLE;
                        if (w_cur_abs) r_abs_done[r_w_slot] <= 1'b1;
                    end
                end
                default: r_wstate <= W_IDLE;
            endcase

            // ---------------- retire sideband, slot release
            for (int s = 0; s < FAB_SLOTS; s++) begin
                if (w_rack_hit[s]) r_rack[s] <= 1'b1;
                if (w_free_now[s]) r_vld[s]  <= 1'b0;
            end
        end
    )

    // slot line buffers: payload only, no reset (the CD beat of the
    // peer's current snoop lands at {its slot, beat}); one write port per
    // array, one array per peer
    always_ff @(posedge clk) begin
        if (w_cd_hs[0])
            r_buf0[{w_sni_head[0], r_cd_beat[0]}] <= cddata_w[0];
    end
    always_ff @(posedge clk) begin
        if (w_cd_hs[1])
            r_buf1[{w_sni_head[1], r_cd_beat[1]}] <= cddata_w[1];
    end

    // ------------------------------------------------------------------
    // Debug taps
    // ------------------------------------------------------------------
    assign dbg_busy       = |r_vld;
    assign dbg_slot_vld   = r_vld;
    assign dbg_pend_vld   = {(r_pend_cnt[1] != 3'd0), (r_pend_cnt[0] != 3'd0)};
    assign dbg_abs_pend   = |(r_vld & r_pd & ~r_abs_done);
    assign dbg_grant      = w_grant;
    assign dbg_grant_dir  = w_grant_dir;
    assign dbg_grant_addr = w_cand_addr[w_grant_dir];
    assign dbg_grant_slot = w_slot_idx;

    // ------------------------------------------------------------------
    // Unused-input roll-up (the AR sideband fields the fabric regenerates,
    // the write-side user fields it zeroes)
    // ------------------------------------------------------------------
    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_ar;
    assign unused_ar = &{1'b0, c_arlen[0], c0_arsize, c0_arburst, c0_arlock, c0_arqos, c0_arregion,
                         c_arlen[1], c1_arsize, c1_arburst, c1_arlock, c1_arqos, c1_arregion,
                         c0_wuser, c1_wuser, mem_rid[IW-1:SLOT_W]};
    /* verilator lint_on UNUSEDSIGNAL */

    // ------------------------------------------------------------------
    // Simulation-only contract checks
    // ------------------------------------------------------------------
    // pragma translate_off
    /* verilator lint_off SYNCASYNCNET */
    // the AR taken for a slot is the slot's line (pulse / AR pairing)
    always @(posedge clk) if (rst_n) begin
        for (int d = 0; d < 2; d++) begin
            if (w_ar_take[d] && (line_of(c_araddr[d]) != r_line[r_arw_slot[d]]))
                $error("jet_prime_pair_fabric: cache %0d AR line %h is not its granted slot's line %h",
                       d, line_of(c_araddr[d]), r_line[r_arw_slot[d]]);
            if (w_ar_take[d] && (is_nodata(r_type[r_arw_slot[d]]) != (c_arlen[d] == 8'd0)))
                $error("jet_prime_pair_fabric: cache %0d AR length disagrees with the request class", d);
        end
        // a memory beat names a slot with a read outstanding
        if (mem_rvalid && !(r_vld[w_mr_slot] && r_mem_issued[w_mr_slot] && !r_mem_done[w_mr_slot]))
            $error("jet_prime_pair_fabric: memory R beat for slot %0d with no read outstanding", w_mr_slot);
        // a granted line is held by exactly one slot
        for (int s = 0; s < FAB_SLOTS; s++)
            for (int t = s + 1; t < FAB_SLOTS; t++)
                if (r_vld[s] && r_vld[t] && (r_line[s] == r_line[t]))
                    $error("jet_prime_pair_fabric: slots %0d and %0d hold the same line %h", s, t, r_line[s]);
        // CD beats only while a snoop is outstanding
        for (int p = 0; p < 2; p++)
            if (cdvalid[p] && (r_sni_cnt[p] == '0))
                $error("jet_prime_pair_fabric: CD beat from cache %0d with no snoop outstanding", p);
        // the pending queue never overflows (a cache cannot launch past its held AR)
        if (|r_pend_ovf)
            $error("jet_prime_pair_fabric: pending queue overflow");
    end
    /* verilator lint_on SYNCASYNCNET */
    // pragma translate_on

endmodule : jet_prime_pair_fabric
