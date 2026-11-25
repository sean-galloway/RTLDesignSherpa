// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: onyx_ccu
// Purpose:
//   The onyx coherency unit, v1 (onyx TASK-001 step 2): N coherent L1
//   caches on the cache side, one AXI4 master toward memory, the snoop
//   fanout to every peer and the gather of their responses -- the
//   jet-prime pair fabric (jet_prime_pair_fabric, TASK-001 steps 3-5)
//   generalized from two ports to N_PORTS, with the D rulings of the onyx
//   PRD (v0.7, 2026-11-20): broadcast snoop (D3), tagged outstanding
//   transactions in a table with per-transaction completion (D4), per-line
//   serialization with different lines interleaving (D5), adjudicated data
//   source with the memory read issued alongside the snoop or deferred
//   until the gather (D6, DEFER_AR), single shareability domain (D8),
//   N_PORTS 2-4 (D11).
//
// Documentation: projects/components/cache-ip/onyx-ace-ccu/PRD.md
//                projects/components/cache-ip/onyx-ace-ccu/docs/onyx_has/onyx_has_index.md
// Subsystem: onyx (cache-ip)
//
// Author: sean galloway
// Created: 2026-11-21
//==============================================================================
// Module: onyx_ccu
//==============================================================================
// Description:
//   Per cache port d, onyx takes the cache's D-8 coherence sideband
//   (coh_req_valid/addr/type: one pulse per fill launch --
//   READ_NOT_SHARED_DIRTY / READ_UNIQUE on a miss, CLEAN_UNIQUE on an
//   upgrade -- and per dirty write-back launch, WRITE_BACK), the cache's
//   retire sideband (coh_done_valid/id: the MSHR entry retired, or
//   MSHR_COUNT for the upgrade), its plain-AXI4 memory side, and the
//   ACE-shaped snoop responder port the cache carries (AC in, CR/CD out --
//   jet_prime_top's m_axi_ac/cr/cd), and:
//
//     fill / upgrade : allocate a table slot when no slot holds the line;
//                      take the requester's AR; drive an AC to EVERY peer
//                      (N_PORTS-1 of them, never the requester: the
//                      broadcast of D3); once every peer has accepted its
//                      AC (DEFER_AR=0) -- or once every CR is in with no
//                      DataTransfer (DEFER_AR=1) -- issue the memory AR
//                      (data fills only; a CleanUnique has no data).  The
//                      gathered verdict routes the data: no DataTransfer
//                      from any peer -> the memory R beats pass through to
//                      the requester once the gather is complete;
//                      DataTransfer from a peer -> that peer is the
//                      supplier (D6: in MESI exactly one peer can hold the
//                      line Exclusive or Modified, so at most one answers
//                      with data), its CD line is buffered in the slot and
//                      replayed to the requester, the memory beats are
//                      consumed and dropped (or the AR suppressed if the
//                      verdict is in before it was presented); PassDirty ->
//                      the buffered line is also written to memory (the
//                      point of coherence).  The slot is freed when the
//                      requester has every beat, every peer's CR is in,
//                      the memory read (if any) is drained, the absorption
//                      (if any) has its BRESP, and the requester's retire
//                      pulse for the entry has been seen.
//     write-back     : pure write-port pass-through (AW/W/B), arbitrated
//                      onto the single memory write port with the
//                      absorptions, round-robin over the N ports and the
//                      absorption.
//
//   Snoop map (IHI0022 ACSNOOP[3:0]): READ_SHARED /
//   READ_NOT_SHARED_DIRTY -> SNOOP_READ_SHARED (4'h1), READ_UNIQUE ->
//   SNOOP_READ_UNIQUE (4'h7), CLEAN_UNIQUE / MAKE_UNIQUE ->
//   SNOOP_MAKE_INVALID (4'hC).  EVICT and WRITE_BACK pulses allocate
//   nothing: in a broadcast CCU without a directory a clean eviction needs
//   no coherence action, and the write-back is the write port's.
//
//   Per-line serialization, pulse to retire (D5).  A request whose line is
//   held by a valid slot (any port) waits ungranted; its AR stays at the
//   cache, so the entry is pre-AR and the cache's pre-AR rule answers any
//   snoop to it at the Invalid row.  The lock is held until the winner's
//   RETIRE (the coh_done sideband), the argument jet-prime delta 02 makes.
//   SERIAL_MODE=1 is the bring-up mode: one transaction in flight
//   system-wide.
//
//   The gather (D4).  Each slot counts the peers that have yet to accept
//   its AC and the peers whose CR is yet to arrive; the verdict is the OR
//   of the CRs' DataTransfer and the AND with PassDirty of the supplier's.
//   A memory beat arriving before the gather is complete holds the memory
//   R channel for the bounded remainder of the slowest peer's service; a
//   DataTransfer known before the gather completes already decides that
//   the memory beats are dropped.  Snoops carry no ID: each peer answers
//   its ACs in order, and the per-peer in-flight queue pairs every CR with
//   its slot.
//
//   The AR alongside the snoop (DEFER_AR=0, the pair fabric's rule) starts
//   the memory read as soon as the last peer has ACCEPTED its AC, so with
//   idle peers the CRs arrive before the first memory beat and nothing
//   stalls.  DEFER_AR=1 waits for the gather and reads memory only when no
//   peer supplied the line: fewer memory reads, a longer miss.  Both modes
//   are measured on the reference rig (PRD criterion 6).  The one hazard
//   the serial order prevented for free -- a write-back landing in memory
//   between the memory read and the snoop -- is covered as in the fabric:
//   a WB AW to a line holds while a slot on that line has an incomplete
//   gather or a pending absorption.
//
//   Snoop data buffers.  The supplier's CD line lands in the buffer of the
//   REQUESTER's port, indexed {slot, beat}; one buffer per port, one write
//   port each (the one peer supplying that requester this cycle -- two
//   peers supplying two slots of the same requester in the same cycle are
//   arbitrated round-robin on cdready, beat by beat) and two reads (the
//   port's replay, the absorption).  Distributed RAM, payload only.
//
//   Liveness: every wait resolves on an agent that does not wait on this
//   unit -- the CRs (a responder grants whenever its own commits have
//   retired), the requester's rready and retire (local), the memory, and
//   the write port's round-robin.  Fair round-robin at the grant over the
//   N ports, at the write port over N+1, and at each buffer's CD write.
//
//   Observation (D9): the unit exposes one-cycle event taps (evt_*) that
//   onyx_monlite turns into MonBus packets; onyx_top composes the two.
//   Nothing on the taps feeds back into the datapath.
//
//   The ACE-Lite IO port (D1, TASK-001 step 7).  One non-caching requester
//   (io_*: AXI4 plus AxSNOOP / AxDOMAIN / AxBAR, no snoop channels -- IHI
//   0022 D11) is requester N_PORTS of the table, beside the N caches:
//     ReadOnce       (ARDOMAIN shareable, ARSNOOP 0): a slot, an AC to
//                    EVERY cache (ACSNOOP ReadOnce), the memory read per
//                    the D6 mode; a peer's DataTransfer supplies the
//                    requested beats from the IO buffer (a ReadOnce leaves
//                    the holder's state to the cache: the house table
//                    passes a Modified line dirty, which onyx absorbs);
//                    the read must lie within one line at full-width beats.
//     ReadNoSnoop    (ARDOMAIN non-shareable or system): a slot with no
//                    peers -- the AR goes to memory as issued (any legal
//                    AXI burst), the beats return as they come.
//     WriteUnique /  (AWDOMAIN shareable, AWSNOOP 0 / 1): a slot, an AC to
//     WriteLineUnique every cache (ACSNOOP CleanInvalid: a Modified holder
//                    passes the line dirty and invalidates, a clean holder
//                    invalidates); the IO's AW is held un-accepted while the
//                    slot gathers and any PassDirty line is absorbed, then
//                    passes through the write port with the IO's own fields
//                    (partial strobes included) and its BRESP frees the slot.
//     WriteNoSnoop   (non-shareable): the write port, as a cache
//                    write-back is (the same hold against an incomplete
//                    gather or pending absorption on its line).
//   One IO read and one IO write are in flight at a time (the same-ID
//   ordering AXI requires of the port, by construction); the IO takes the
//   per-line lock like a cache and holds it until its last beat or its
//   BRESP.  A WriteUnique whose line a cache is writing back lets the
//   write-back land first (its AW is forwarded only when no cache presents
//   an AW to the line).  AxBAR is ignored (D8), ARSNOOP other than ReadOnce
//   and AWSNOOP other than WriteUnique / WriteLineUnique are not decoded
//   (sim-checked).  The IO port carries no retire sideband: its slot's
//   retire is its last beat / its BRESP.
//
//   Not in v1: ARSNOOP decode on the caches' AR (the caches carry the
//   request class on the sideband; the ACE-front-side flavor is the D7
//   adapter's second half).
//
//------------------------------------------------------------------------------
// Parameters:
//   N_PORTS        -- coherent cache ports, 2..4 (D11); the IO port is
//                     requester N_PORTS (one, always present).
//   SLOTS          -- transaction table depth, shared by all ports; also
//                     the memory read IDs in use (0 .. SLOTS-1).  At
//                     N_PORTS * (MSHR_COUNT + 1) nothing ever waits for a
//                     slot.
//   SNOOP_INFLIGHT -- ACs accepted by one peer and not yet answered.
//   DEFER_AR       -- D6 mode (see above).  SERIAL_MODE -- D5 bring-up.
//   Geometry per l1_pkg (ADDR_WIDTH, LINE_BYTES, BUS_WIDTH).
//------------------------------------------------------------------------------
//
// Notes:
//   - Single clock / active-low reset (clk / rst_n); ALWAYS_FF_RST macros.
//   - Cache-side signals are unpacked arrays over N_PORTS; a rig flattens
//     them to per-port names.  dbg_grant_dir keeps the pair fabric's tap
//     name (the requester of a grant: a cache port, or N_PORTS for the IO
//     port) so the pair-rig TB reads onyx unchanged.
//   - The memory read ID is the slot index; the requester sees its own
//     ARID back.  Beats of different slots may interleave on a cache's R
//     channel (AXI4 permits it per ID; jet_prime_fill demuxes by ID).
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: onyx_pair_rig_tb (two jet-primes, the pair fabric's
//     place), the Genesys2 reference harness (a later step)
//   - Consumes: N jet_prime_top memory sides + D-8 sidebands + ACE responders,
//     one ACE-Lite master (the pair rig's BFM; the reference rig's doorbell)
//   - Package: l1_pkg (ACE request classes, CRRESP bit positions)
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/onyx-ace-ccu/dv/tests/test_onyx_pair_rig.py
//   Run: cd projects/components/cache-ip/onyx-ace-ccu/dv/tests && make clean-all && make run-all-gate-parallel
//
//==============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"

module onyx_ccu
    import l1_pkg::*;
    import onyx_pkg::*;
#(
    parameter int N_PORTS        = 2,
    parameter int ADDR_WIDTH     = AMBER_ADDR_WIDTH,
    parameter int LINE_BYTES     = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH      = AMBER_BUS_WIDTH,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    parameter int SLOTS          = 18,
    parameter int SNOOP_INFLIGHT = 1,
    parameter bit DEFER_AR       = 1'b0,
    parameter bit SERIAL_MODE    = 1'b0,
    localparam int STRB_W           = BUS_WIDTH / 8,
    localparam int FILL_BEATS       = LINE_BYTES / STRB_W,
    localparam int BEAT_INDEX_WIDTH = $clog2(FILL_BEATS),
    localparam int IW               = AXI_ID_WIDTH,
    localparam int UW               = AXI_USER_WIDTH,
    localparam int SLOT_W           = (SLOTS > 1) ? $clog2(SLOTS) : 1,
    localparam int PORT_W           = (N_PORTS > 1) ? $clog2(N_PORTS) : 1,
    localparam int OFFSET_W         = $clog2(LINE_BYTES),
    localparam int LINE_W           = ADDR_WIDTH - OFFSET_W,
    localparam int BYTE_W           = $clog2(STRB_W),
    localparam int N_REQ            = N_PORTS + 1,          // the caches and the IO port
    localparam int RQ_W             = $clog2(N_REQ),        // a requester index
    localparam int IO               = N_PORTS,              // the IO port's requester index
    localparam int PC_W             = $clog2(N_PORTS + 1)   // a count of peers (0 .. N_PORTS)
) (
    input  logic                        clk,
    input  logic                        rst_n,

    // ------------------------------------------------------------------
    // Cache side: plain-AXI4 slave per port (the cache's memory side)
    // ------------------------------------------------------------------
    input  logic [IW-1:0]               c_arid     [N_PORTS],
    input  logic [ADDR_WIDTH-1:0]       c_araddr   [N_PORTS],
    input  logic [7:0]                  c_arlen    [N_PORTS],
    input  logic [2:0]                  c_arsize   [N_PORTS],
    input  logic [1:0]                  c_arburst  [N_PORTS],
    input  logic [N_PORTS-1:0]          c_arlock,
    input  logic [3:0]                  c_arcache  [N_PORTS],
    input  logic [2:0]                  c_arprot   [N_PORTS],
    input  logic [3:0]                  c_arqos    [N_PORTS],
    input  logic [3:0]                  c_arregion [N_PORTS],
    input  logic [UW-1:0]               c_aruser   [N_PORTS],
    input  logic [N_PORTS-1:0]          c_arvalid,
    output logic [N_PORTS-1:0]          c_arready,
    output logic [IW-1:0]               c_rid      [N_PORTS],
    output logic [BUS_WIDTH-1:0]        c_rdata    [N_PORTS],
    output logic [1:0]                  c_rresp    [N_PORTS],
    output logic [N_PORTS-1:0]          c_rlast,
    output logic [UW-1:0]               c_ruser    [N_PORTS],
    output logic [N_PORTS-1:0]          c_rvalid,
    input  logic [N_PORTS-1:0]          c_rready,

    input  logic [IW-1:0]               c_awid     [N_PORTS],
    input  logic [ADDR_WIDTH-1:0]       c_awaddr   [N_PORTS],
    input  logic [7:0]                  c_awlen    [N_PORTS],
    input  logic [2:0]                  c_awsize   [N_PORTS],
    input  logic [1:0]                  c_awburst  [N_PORTS],
    input  logic [N_PORTS-1:0]          c_awlock,
    input  logic [3:0]                  c_awcache  [N_PORTS],
    input  logic [2:0]                  c_awprot   [N_PORTS],
    input  logic [3:0]                  c_awqos    [N_PORTS],
    input  logic [3:0]                  c_awregion [N_PORTS],
    input  logic [UW-1:0]               c_awuser   [N_PORTS],
    input  logic [N_PORTS-1:0]          c_awvalid,
    output logic [N_PORTS-1:0]          c_awready,
    input  logic [BUS_WIDTH-1:0]        c_wdata    [N_PORTS],
    input  logic [STRB_W-1:0]           c_wstrb    [N_PORTS],
    input  logic [N_PORTS-1:0]          c_wlast,
    input  logic [UW-1:0]               c_wuser    [N_PORTS],
    input  logic [N_PORTS-1:0]          c_wvalid,
    output logic [N_PORTS-1:0]          c_wready,
    output logic [IW-1:0]               c_bid      [N_PORTS],
    output logic [1:0]                  c_bresp    [N_PORTS],
    output logic [UW-1:0]               c_buser    [N_PORTS],
    output logic [N_PORTS-1:0]          c_bvalid,
    input  logic [N_PORTS-1:0]          c_bready,

    // ------------------------------------------------------------------
    // Snoop side per port: onyx drives AC into the cache's responder;
    // CR/CD return (the ACE-shaped D7 port)
    // ------------------------------------------------------------------
    output logic [ADDR_WIDTH-1:0]       s_acaddr   [N_PORTS],
    output logic [3:0]                  s_acsnoop  [N_PORTS],
    output logic [2:0]                  s_acprot   [N_PORTS],
    output logic [N_PORTS-1:0]          s_acvalid,
    input  logic [N_PORTS-1:0]          s_acready,
    input  logic [AMBER_CRRESP_WIDTH-1:0] s_crresp [N_PORTS],
    input  logic [N_PORTS-1:0]          s_crvalid,
    output logic [N_PORTS-1:0]          s_crready,
    input  logic [BUS_WIDTH-1:0]        s_cddata   [N_PORTS],
    input  logic [N_PORTS-1:0]          s_cdlast,
    input  logic [N_PORTS-1:0]          s_cdvalid,
    output logic [N_PORTS-1:0]          s_cdready,

    // ------------------------------------------------------------------
    // D-8 coherence sideband (one pulse per fill / upgrade / WB) and the
    // retire sideband per port
    // ------------------------------------------------------------------
    input  logic [N_PORTS-1:0]          c_coh_req_valid,
    input  logic [ADDR_WIDTH-1:0]       c_coh_req_addr [N_PORTS],
    input  logic [2:0]                  c_coh_req_type [N_PORTS],
    input  logic [N_PORTS-1:0]          c_coh_done_valid,
    input  logic [IW-1:0]               c_coh_done_id  [N_PORTS],

    // ------------------------------------------------------------------
    // ACE-Lite IO port (D1): one non-caching master's AXI4 with the ACE
    // address fields (AxSNOOP, AxDOMAIN, AxBAR); no snoop channels
    // ------------------------------------------------------------------
    input  logic [IW-1:0]               io_arid,
    input  logic [ADDR_WIDTH-1:0]       io_araddr,
    input  logic [7:0]                  io_arlen,
    input  logic [2:0]                  io_arsize,
    input  logic [1:0]                  io_arburst,
    input  logic                        io_arlock,
    input  logic [3:0]                  io_arcache,
    input  logic [2:0]                  io_arprot,
    input  logic [3:0]                  io_arqos,
    input  logic [3:0]                  io_arregion,
    input  logic [UW-1:0]               io_aruser,
    input  logic [3:0]                  io_arsnoop,
    input  logic [1:0]                  io_ardomain,
    input  logic [1:0]                  io_arbar,
    input  logic                        io_arvalid,
    output logic                        io_arready,
    output logic [IW-1:0]               io_rid,
    output logic [BUS_WIDTH-1:0]        io_rdata,
    output logic [1:0]                  io_rresp,
    output logic                        io_rlast,
    output logic [UW-1:0]               io_ruser,
    output logic                        io_rvalid,
    input  logic                        io_rready,

    input  logic [IW-1:0]               io_awid,
    input  logic [ADDR_WIDTH-1:0]       io_awaddr,
    input  logic [7:0]                  io_awlen,
    input  logic [2:0]                  io_awsize,
    input  logic [1:0]                  io_awburst,
    input  logic                        io_awlock,
    input  logic [3:0]                  io_awcache,
    input  logic [2:0]                  io_awprot,
    input  logic [3:0]                  io_awqos,
    input  logic [3:0]                  io_awregion,
    input  logic [UW-1:0]               io_awuser,
    input  logic [2:0]                  io_awsnoop,
    input  logic [1:0]                  io_awdomain,
    input  logic [1:0]                  io_awbar,
    input  logic                        io_awvalid,
    output logic                        io_awready,
    input  logic [BUS_WIDTH-1:0]        io_wdata,
    input  logic [STRB_W-1:0]           io_wstrb,
    input  logic                        io_wlast,
    input  logic [UW-1:0]               io_wuser,
    input  logic                        io_wvalid,
    output logic                        io_wready,
    output logic [IW-1:0]               io_bid,
    output logic [1:0]                  io_bresp,
    output logic [UW-1:0]               io_buser,
    output logic                        io_bvalid,
    input  logic                        io_bready,

    // ------------------------------------------------------------------
    // Memory-side AXI4 master
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
    // Debug / observability taps (unused in the datapath; the pair-rig
    // TB's names)
    // ------------------------------------------------------------------
    output logic                        dbg_busy,
    output logic [SLOTS-1:0]            dbg_slot_vld,
    output logic [N_PORTS-1:0]          dbg_pend_vld,
    output logic                        dbg_abs_pend,
    output logic                        dbg_grant,
    output logic [RQ_W-1:0]             dbg_grant_dir,      // the requester: a cache port, or N_PORTS for the IO port
    output logic [ADDR_WIDTH-1:0]       dbg_grant_addr,
    output logic [SLOT_W-1:0]           dbg_grant_slot,

    // ------------------------------------------------------------------
    // Event taps for the D9 observer (onyx_monlite): one-cycle pulses with
    // their payload, driven from the datapath's own handshakes; nothing
    // here feeds back
    // ------------------------------------------------------------------
    output logic                        evt_grant,          // = dbg_grant; port dbg_grant_dir, slot dbg_grant_slot
    output logic [2:0]                  evt_grant_cls,      // the granted request class
    output logic [N_PORTS-1:0]          evt_ac,             // AC handshake per peer this cycle
    output logic [N_PORTS-1:0]          evt_gather,         // per answering port: its CR completed a slot's gather
    output logic [SLOT_W-1:0]           evt_gather_slot [N_PORTS],
    output logic [N_PORTS-1:0]          evt_gather_dt,      // the slot's verdict after this CR
    output logic [N_PORTS-1:0]          evt_gather_pd,
    output logic                        evt_mem_ar,         // memory AR handshake, slot mem_arid
    output logic [N_PORTS-1:0]          evt_read_wasted,    // per answering port: a DT verdict with the slot's read issued or presented
    output logic                        evt_absorb,         // absorption BRESP
    output logic [SLOT_W-1:0]           evt_absorb_slot,    // the absorbed slot (the write side's current slot)
    output logic                        evt_wb,             // a write taken on the write port other than an absorption: a cache write-back or an IO write (its address is mem_awaddr)
    output logic                        evt_wb_io,          // ... and it is the IO port's
    output logic [N_REQ-1:0]            evt_lock_wait,      // a requester's valid candidate is held by the per-line lock
    output logic [ADDR_WIDTH-1:0]       evt_lock_wait_addr [N_REQ]     // that candidate's address (for the observer's window)
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks
    // ------------------------------------------------------------------
    initial begin
        if (N_PORTS < 2 || N_PORTS > 4)
            $error("onyx_ccu: N_PORTS must be 2..4 (D11)");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("onyx_ccu: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0 || FILL_BEATS < 2)
            $error("onyx_ccu: LINE_BYTES / BUS_WIDTH*8 must be a power of two >= 2");
        if ((BUS_WIDTH % 8) != 0)
            $error("onyx_ccu: BUS_WIDTH must be a multiple of 8");
        if (SLOTS < 2 || (1 << SLOT_W) < SLOTS)
            $error("onyx_ccu: SLOTS must be >= 2");
        if ((1 << IW) < SLOTS)
            $error("onyx_ccu: 2**AXI_ID_WIDTH must cover SLOTS (the memory read IDs)");
        if (SNOOP_INFLIGHT < 1)
            $error("onyx_ccu: SNOOP_INFLIGHT must be >= 1");
    end

    // ------------------------------------------------------------------
    // Encodings
    // ------------------------------------------------------------------
    localparam logic [3:0] ACSNOOP_READ_ONCE     = 4'h0;   // IHI0022; the house decode (l1_snoop_resp)
    localparam logic [3:0] ACSNOOP_READ_SHARED   = 4'h1;
    localparam logic [3:0] ACSNOOP_READ_UNIQUE   = 4'h7;
    localparam logic [3:0] ACSNOOP_CLEAN_INVALID = 4'h9;
    localparam logic [3:0] ACSNOOP_MAKE_INVALID  = 4'hC;

    // the IO port's two transaction kinds in the request-class code space
    // (onyx_pkg): the grant's class on TXN_START, the slot's r_type
    localparam logic [2:0] CLS_IO_READ  = ONYX_CLS_IO_READ;
    localparam logic [2:0] CLS_IO_WRITE = ONYX_CLS_IO_WRITE;

    function automatic logic [3:0] map_snoop(input logic [2:0] req_type);
        case (req_type)
            AMBER_ACE_READ_SHARED,
            AMBER_ACE_READ_NOT_SHARED_DIRTY: return ACSNOOP_READ_SHARED;
            AMBER_ACE_READ_UNIQUE:           return ACSNOOP_READ_UNIQUE;
            CLS_IO_READ:                     return ACSNOOP_READ_ONCE;      // the IO's ReadOnce
            CLS_IO_WRITE:                    return ACSNOOP_CLEAN_INVALID;  // the IO's WriteUnique: dirty data first
            default:                         return ACSNOOP_MAKE_INVALID;
        endcase
    endfunction

    function automatic logic is_nodata(input logic [2:0] req_type);
        return (req_type == 3'(AMBER_ACE_CLEAN_UNIQUE))
            || (req_type == 3'(AMBER_ACE_MAKE_UNIQUE));
    endfunction

    // a sideband pulse that allocates a transaction (not a WB, not a
    // WriteClean -- amber TASK-004's clean-all write-back -- not an evict)
    function automatic logic is_coh_req(input logic [2:0] req_type);
        return (req_type != 3'(AMBER_ACE_WRITE_BACK))
            && (req_type != 3'(AMBER_ACE_WRITE_CLEAN))
            && (req_type != 3'(AMBER_ACE_EVICT));
    endfunction

    /* verilator lint_off UNUSEDSIGNAL */
    function automatic logic [LINE_W-1:0] line_of(input logic [ADDR_WIDTH-1:0] addr);
        return addr[ADDR_WIDTH-1 -: LINE_W];
    endfunction
    /* verilator lint_on UNUSEDSIGNAL */

    localparam int SNQ_W      = SLOT_W + 1;                 // snoop queue count
    localparam int SNI_W      = $clog2(SNOOP_INFLIGHT + 1); // issued count
    localparam int SNI_IW     = (SNOOP_INFLIGHT > 1) ? $clog2(SNOOP_INFLIGHT) : 1;
    localparam int PEND_DEPTH = 4;
    localparam int PEND_W     = 3;
    localparam int BUF_AW     = SLOT_W + BEAT_INDEX_WIDTH;  // {slot, beat}
    localparam int BUF_DEPTH  = SLOTS * FILL_BEATS;
    localparam int NW         = N_PORTS + 2;                // write-port candidates: wb_0..N-1, the absorption, the IO
    localparam int WSEL_W     = $clog2(NW);
    localparam int W_ABS      = N_PORTS;                    // the absorption's candidate index
    localparam int W_IO       = N_PORTS + 1;                // the IO write's
    localparam int NPEER      = N_PORTS - 1;                // peers of a cache's transaction

    // ------------------------------------------------------------------
    // IO decode: a shareable domain (inner 01 / outer 10) snoops; non-
    // shareable (00) and system (11) go straight to memory
    // ------------------------------------------------------------------
    wire w_io_ar_sh = io_ardomain[0] ^ io_ardomain[1];
    wire w_io_aw_sh = io_awdomain[0] ^ io_awdomain[1];

    // ------------------------------------------------------------------
    // Sideband decode
    // ------------------------------------------------------------------
    logic [N_PORTS-1:0] coh_req_vld;
    always_comb begin
        for (int d = 0; d < N_PORTS; d++)
            coh_req_vld[d] = c_coh_req_valid[d] & is_coh_req(c_coh_req_type[d]);
    end

    // ------------------------------------------------------------------
    // Transaction table
    // ------------------------------------------------------------------
    logic [SLOTS-1:0]      r_vld;
    logic [RQ_W-1:0]       r_dir     [SLOTS];     // the requester: a cache port, or IO
    logic [LINE_W-1:0]     r_line    [SLOTS];
    logic [2:0]            r_type    [SLOTS];
    logic [SLOTS-1:0]      r_nodata;
    logic [SLOTS-1:0]      r_ar_taken;
    logic [IW-1:0]         r_arid    [SLOTS];
    logic [3:0]            r_arcache [SLOTS];
    logic [2:0]            r_arprot  [SLOTS];
    logic [UW-1:0]         r_aruser  [SLOTS];
    logic [PC_W-1:0]       r_ac_left [SLOTS];     // peers yet to accept the AC (N_PORTS-1 for a cache, N_PORTS or 0 for the IO)
    logic [PC_W-1:0]       r_cr_left [SLOTS];     // peers whose CR is yet to arrive
    logic [SLOTS-1:0]      r_dt;                  // a peer supplies the line
    logic [SLOTS-1:0]      r_pd;                  // ... and passes dirty
    logic [SLOTS-1:0]      r_mem_issued;
    logic [SLOTS-1:0]      r_mem_done;
    logic [SLOTS-1:0]      r_rpl_done;
    logic [SLOTS-1:0]      r_abs_issued;
    logic [SLOTS-1:0]      r_abs_done;
    logic [SLOTS-1:0]      r_rack;
    logic [SLOTS-1:0]      r_iow;                 // the IO's WriteUnique: no read, delivered at its BRESP
    logic [SLOTS-1:0]      r_iow_done;

    // the IO port's state: one read and one write in flight at a time
    logic                  r_ior_busy;            // an IO read holds a slot (grant .. free)
    logic [SLOT_W-1:0]     r_ior_slot;
    logic [ADDR_WIDTH-1:0] r_io_araddr;           // the IO read's own AR, captured at the take
    logic [7:0]            r_io_arlen;
    logic [2:0]            r_io_arsize;
    logic [1:0]            r_io_arburst;
    logic                  r_io_arlock;
    logic [3:0]            r_io_arqos;
    logic [3:0]            r_io_arregion;
    logic                  r_iow_busy;            // an IO write is in flight (its grant or its selection .. BRESP)
    logic                  r_iow_slot_vld;        // ... and it is a WriteUnique with a slot
    logic [SLOT_W-1:0]     r_iow_slot;

    logic [SLOTS-1:0]      w_ac_all;              // every peer accepted its AC
    logic [SLOTS-1:0]      w_gathered;            // every peer's CR is in
    logic [SLOTS-1:0]      w_delivered;           // the requester has every beat
    logic [SLOTS-1:0]      w_free_now;
    logic                  w_mar_vld;             // a memory AR is presented this cycle
    logic [SLOT_W-1:0]     w_mar_slot;
    // (the gather flags in their own block: the free computation below reads
    // the presented memory AR, whose candidate reads these flags -- one
    // block for both looks like a combinational cycle to a scheduler)
    always_comb begin
        for (int s = 0; s < SLOTS; s++) begin
            w_ac_all[s]   = (r_ac_left[s] == '0);
            w_gathered[s] = (r_cr_left[s] == '0);
        end
    end
    always_comb begin
        for (int s = 0; s < SLOTS; s++) begin
            w_delivered[s] = r_iow[s] ? r_iow_done[s]
                             : (r_dt[s] | r_nodata[s]) ? r_rpl_done[s] : r_mem_done[s];
            // a slot whose memory AR is presented this cycle is not free
            // (the fabric formal's ap_free_complete)
            w_free_now[s]  = r_vld[s] & w_gathered[s] & w_delivered[s]
                             & (~r_mem_issued[s] | r_mem_done[s])
                             & ~(w_mar_vld & (w_mar_slot == SLOT_W'(s)))
                             & (~r_pd[s] | r_abs_done[s])
                             & r_rack[s];
        end
    end

    // ------------------------------------------------------------------
    // Per-port pending-request queue (the sideband pulses, in order)
    // ------------------------------------------------------------------
    logic [PEND_W-1:0]       r_pend_cnt  [N_PORTS];
    logic [ADDR_WIDTH-1:0]   r_pend_addr [N_PORTS][PEND_DEPTH];
    logic [2:0]              r_pend_type [N_PORTS][PEND_DEPTH];
    logic [N_PORTS-1:0]      r_pend_ovf;   // debug only (TB-checked)

    // the IO port's candidate is its own AR or AW, held by AXI until
    // accepted: a read whenever none is in flight, else a shareable write
    // whenever none is in flight (a non-shareable write is the write
    // port's, not the table's)
    wire w_io_rd_cand = io_arvalid & ~r_ior_busy;
    wire w_io_wr_cand = io_awvalid & w_io_aw_sh & ~r_iow_busy;

    logic [N_REQ-1:0]        w_cand_vld;
    logic [ADDR_WIDTH-1:0]   w_cand_addr [N_REQ];
    logic [2:0]              w_cand_type [N_REQ];
    logic [N_REQ-1:0]        w_cand_live;
    always_comb begin
        for (int d = 0; d < N_PORTS; d++) begin
            if (r_pend_cnt[d] != '0) begin
                w_cand_vld[d]  = 1'b1;
                w_cand_live[d] = 1'b0;
                w_cand_addr[d] = r_pend_addr[d][0];
                w_cand_type[d] = r_pend_type[d][0];
            end else begin
                w_cand_vld[d]  = coh_req_vld[d];
                w_cand_live[d] = 1'b1;
                w_cand_addr[d] = c_coh_req_addr[d];
                w_cand_type[d] = c_coh_req_type[d];
            end
        end
        w_cand_vld[IO]  = w_io_rd_cand | w_io_wr_cand;
        w_cand_live[IO] = 1'b1;
        w_cand_addr[IO] = w_io_rd_cand ? io_araddr : io_awaddr;
        w_cand_type[IO] = w_io_rd_cand ? CLS_IO_READ : CLS_IO_WRITE;
    end

    // per-line lock: any valid slot on the candidate's line (SERIAL_MODE:
    // any valid slot at all)
    logic [N_REQ-1:0] w_cand_locked;
    always_comb begin
        for (int d = 0; d < N_REQ; d++) begin
            w_cand_locked[d] = SERIAL_MODE & (|r_vld);
            for (int s = 0; s < SLOTS; s++) begin
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
        for (int s = SLOTS - 1; s >= 0; s--) begin
            if (!r_vld[s]) begin
                w_slot_free = 1'b1;
                w_slot_idx  = SLOT_W'(s);
            end
        end
    end

    // an AR waits to be taken for this requester (granted, AR not yet
    // handshaken): no second grant to the requester until it is
    logic [N_REQ-1:0]   r_arw_vld;
    logic [SLOT_W-1:0]  r_arw_slot [N_REQ];

    // grant: rotating priority from r_rr over the N ports and the IO
    logic [N_REQ-1:0]   w_cand_ok;
    logic [RQ_W-1:0]    r_rr;
    logic               w_grant;
    logic [RQ_W-1:0]    w_grant_dir;
    always_comb begin
        for (int d = 0; d < N_REQ; d++)
            w_cand_ok[d] = w_cand_vld[d] & ~w_cand_locked[d] & w_slot_free & ~r_arw_vld[d];
        w_grant     = |w_cand_ok;
        w_grant_dir = r_rr;
        for (int k = N_REQ - 1; k >= 0; k--) begin
            automatic int idx = (32'(r_rr) + k) % N_REQ;
            if (w_cand_ok[idx]) w_grant_dir = RQ_W'(idx);
        end
    end
    // the grant's requester and kind, and the peers it snoops: a cache's
    // transaction snoops the other N-1 caches; the IO's shareable read or
    // write snoops all N; its non-shareable read snoops none
    wire w_grant_io    = (w_grant_dir == RQ_W'(IO));
    wire w_grant_io_wr = w_grant_io & (w_cand_type[IO] == CLS_IO_WRITE);
    wire [PC_W-1:0] w_grant_npeer = !w_grant_io ? PC_W'(NPEER)
                                  : (w_grant_io_wr | w_io_ar_sh) ? PC_W'(N_PORTS) : '0;

    // ------------------------------------------------------------------
    // AR take: arready from registers only (the caches, the IO read)
    // ------------------------------------------------------------------
    assign c_arready  = r_arw_vld[N_PORTS-1:0];
    assign io_arready = r_arw_vld[IO];
    wire [N_PORTS-1:0] w_ar_take = c_arvalid & c_arready;
    wire               w_io_ar_take = io_arvalid & io_arready;

    // ------------------------------------------------------------------
    // Snoop queues: per peer p, the slots awaiting an AC to p in grant
    // order, and the ACs accepted but not yet answered (CR pairs by order)
    // ------------------------------------------------------------------
    logic [SLOT_W-1:0] r_snq [N_PORTS][SLOTS];
    logic [SNQ_W-1:0]  r_snq_cnt [N_PORTS];
    logic [SLOT_W-1:0] r_sni [N_PORTS][SNOOP_INFLIGHT];
    logic [SNI_W-1:0]  r_sni_cnt [N_PORTS];
    logic [BEAT_INDEX_WIDTH-1:0] r_cd_beat [N_PORTS];

    logic [N_PORTS-1:0] w_ac_vld, w_ac_hs, w_cr_hs, w_cd_want, w_cd_hs;
    logic [SLOT_W-1:0]  w_ac_slot  [N_PORTS];
    logic [SLOT_W-1:0]  w_sni_head [N_PORTS];
    always_comb begin
        for (int p = 0; p < N_PORTS; p++) begin
            w_ac_slot[p]  = r_snq[p][0];
            w_ac_vld[p]   = (r_snq_cnt[p] != '0) && (r_sni_cnt[p] < SNI_W'(SNOOP_INFLIGHT));
            w_ac_hs[p]    = w_ac_vld[p] & s_acready[p];
            w_sni_head[p] = r_sni[p][0];
            w_cr_hs[p]    = s_crvalid[p] & (r_sni_cnt[p] != '0);
            w_cd_want[p]  = s_cdvalid[p] & (r_sni_cnt[p] != '0);
        end
    end

    // The peers' handshakes per slot this cycle.  At N_PORTS = 2 a cache's
    // transaction has one peer; at N_PORTS >= 3, and always for the IO's
    // transaction (every cache is its peer), two peers can accept their
    // ACs or answer their CRs for the SAME slot in one cycle, so the
    // slot's counters step by the count, not by one --
    // a per-peer decrement written twice to one register lands once (the
    // first IO read against two sharers hung on exactly that).  The
    // verdict bits OR over the cycle's CRs the same way.
    logic [PC_W-1:0]    w_ac_dec [SLOTS];
    logic [PC_W-1:0]    w_cr_dec [SLOTS];
    logic [SLOTS-1:0]   w_cr_dt_now, w_cr_pd_now;
    logic [N_PORTS-1:0] w_cr_last;          // peer p's CR is the last of its slot's this cycle
    always_comb begin
        for (int s = 0; s < SLOTS; s++) begin
            w_ac_dec[s] = '0;
            w_cr_dec[s] = '0;
            w_cr_dt_now[s] = 1'b0;
            w_cr_pd_now[s] = 1'b0;
            for (int p = 0; p < N_PORTS; p++) begin
                if (w_ac_hs[p] && (w_ac_slot[p] == SLOT_W'(s))) w_ac_dec[s] = w_ac_dec[s] + PC_W'(1);
                if (w_cr_hs[p] && (w_sni_head[p] == SLOT_W'(s))) begin
                    w_cr_dec[s] = w_cr_dec[s] + PC_W'(1);
                    w_cr_dt_now[s] = w_cr_dt_now[s] | s_crresp[p][AMBER_CRRESP_DT];
                    w_cr_pd_now[s] = w_cr_pd_now[s] | (s_crresp[p][AMBER_CRRESP_DT] & s_crresp[p][AMBER_CRRESP_PD]);
                end
            end
        end
        for (int p = 0; p < N_PORTS; p++) begin
            w_cr_last[p] = w_cr_hs[p];
            for (int q = p + 1; q < N_PORTS; q++)
                if (w_cr_hs[q] && (w_sni_head[q] == w_sni_head[p])) w_cr_last[p] = 1'b0;
        end
    end

    always_comb begin
        for (int p = 0; p < N_PORTS; p++) begin
            s_acaddr[p]  = {r_line[w_ac_slot[p]], OFFSET_W'(0)};
            s_acsnoop[p] = map_snoop(r_type[w_ac_slot[p]]);
            s_acprot[p]  = 3'b000;
            s_acvalid[p] = w_ac_vld[p];
            // CR accepted whenever a snoop is outstanding at that peer
            s_crready[p] = (r_sni_cnt[p] != '0);
        end
    end

    // ------------------------------------------------------------------
    // CD write arbitration: the beat of peer p lands in the buffer of the
    // requester port of p's current snoop; one writer per buffer per
    // cycle, round-robin among the peers wanting it
    // ------------------------------------------------------------------
    logic [RQ_W-1:0]   w_cd_tgt [N_PORTS];      // the buffer peer p's beat targets (a requester's)
    logic [PORT_W-1:0] r_cd_rr  [N_REQ];        // per-buffer rotating pointer over the peers
    logic [N_REQ-1:0]  w_buf_we;
    logic [PORT_W-1:0] w_buf_src [N_REQ];       // the peer writing buffer a
    always_comb begin
        for (int p = 0; p < N_PORTS; p++)
            w_cd_tgt[p] = r_dir[w_sni_head[p]];
        for (int a = 0; a < N_REQ; a++) begin
            w_buf_we[a]  = 1'b0;
            w_buf_src[a] = r_cd_rr[a];
            for (int k = N_PORTS - 1; k >= 0; k--) begin
                automatic int p = (32'(r_cd_rr[a]) + k) % N_PORTS;
                if (w_cd_want[p] && (w_cd_tgt[p] == RQ_W'(a))) begin
                    w_buf_we[a]  = 1'b1;
                    w_buf_src[a] = PORT_W'(p);
                end
            end
        end
        for (int p = 0; p < N_PORTS; p++) begin
            s_cdready[p] = w_cd_want[p] & w_buf_we[w_cd_tgt[p]]
                           & (w_buf_src[w_cd_tgt[p]] == PORT_W'(p));   // the target is a live requester's buffer
            w_cd_hs[p]   = s_cdready[p];
        end
    end

    // ------------------------------------------------------------------
    // Memory AR issue: a slot whose AR is taken, with data to fetch, no
    // DataTransfer yet, and -- DEFER_AR=0 -- every peer's AC accepted, or
    // -- DEFER_AR=1 -- every peer's CR in.  Lowest index first; once
    // presented the AR is HELD until its handshake (ap_mar_stable).
    // ------------------------------------------------------------------
    logic              w_marc_vld;
    logic [SLOT_W-1:0] w_marc_slot;
    logic              r_mar_vld;
    logic [SLOT_W-1:0] r_mar_slot;
    always_comb begin
        w_marc_vld  = 1'b0;
        w_marc_slot = '0;
        for (int s = SLOTS - 1; s >= 0; s--) begin
            if (r_vld[s] && r_ar_taken[s] && !r_nodata[s] && !r_mem_issued[s]
                && !r_dt[s] && (DEFER_AR ? w_gathered[s] : w_ac_all[s])) begin
                w_marc_vld  = 1'b1;
                w_marc_slot = SLOT_W'(s);
            end
        end
    end
    assign w_mar_vld  = r_mar_vld | w_marc_vld;
    assign w_mar_slot = r_mar_vld ? r_mar_slot : w_marc_slot;
    wire   w_mar_hs   = w_mar_vld & mem_arready;

    // a cache's read is the slot's full line; the IO's read is its own AR
    // (one IO read in flight: the captured fields are the slot's)
    wire w_mar_io = (r_dir[w_mar_slot] == RQ_W'(IO));
    assign mem_arid     = IW'(w_mar_slot);
    assign mem_araddr   = w_mar_io ? r_io_araddr  : {r_line[w_mar_slot], OFFSET_W'(0)};
    assign mem_arlen    = w_mar_io ? r_io_arlen   : 8'(FILL_BEATS - 1);
    assign mem_arsize   = w_mar_io ? r_io_arsize  : 3'(BYTE_W);
    assign mem_arburst  = w_mar_io ? r_io_arburst : 2'b01;
    assign mem_arlock   = w_mar_io ? r_io_arlock  : 1'b0;
    assign mem_arcache  = r_arcache[w_mar_slot];
    assign mem_arprot   = r_arprot[w_mar_slot];
    assign mem_arqos    = w_mar_io ? r_io_arqos    : 4'b0000;
    assign mem_arregion = w_mar_io ? r_io_arregion : 4'b0000;
    assign mem_aruser   = r_aruser[w_mar_slot];
    assign mem_arvalid  = w_mar_vld;

    // ------------------------------------------------------------------
    // Memory R: the beat's slot (rid) decides -- forward (gathered, no
    // DT), drop (DT, the replay carries the line), or hold until the
    // gather completes.  Both routes also require a read outstanding for
    // the slot: an invalid slot has nothing left to gather (its counters
    // read zero), so without the qualifier a beat the memory was never
    // asked for would be forwarded to whatever port the stale slot named
    // -- the onyx formal found that at step 1, where the pair fabric's
    // explicit verdict bit had covered it.  A beat for no read is a memory
    // fault (the sim check below names it); it is held, not routed.
    // ------------------------------------------------------------------
    wire [SLOT_W-1:0] w_mr_slot = mem_rid[SLOT_W-1:0];
    wire w_mr_live = mem_rvalid & r_vld[w_mr_slot] & r_mem_issued[w_mr_slot] & ~r_mem_done[w_mr_slot];
    wire w_mr_fwd  = w_mr_live & w_gathered[w_mr_slot] & ~r_dt[w_mr_slot];
    wire w_mr_drop = w_mr_live & r_dt[w_mr_slot];
    wire [RQ_W-1:0] w_mr_dir = r_dir[w_mr_slot];

    // ------------------------------------------------------------------
    // Replay per requester: the DT line from the requester's buffer (the
    // IO's: the beats its AR asked for, from its offset), or the single
    // no-data beat of an upgrade; a memory beat for the requester has
    // priority.  An IO write slot has nothing to replay.
    // ------------------------------------------------------------------
    logic [N_REQ-1:0]   r_rpl_vld;
    logic [SLOT_W-1:0]  r_rpl_slot [N_REQ];
    logic [BEAT_INDEX_WIDTH-1:0] r_rpl_beat [N_REQ];   // the buffer beat
    logic [7:0]         r_rpl_cnt  [N_REQ];            // beats replayed so far (the IO's RLAST)
    logic [N_REQ-1:0]   r_rpl_hold;

    logic [N_REQ-1:0]   w_rplc_vld;
    logic [SLOT_W-1:0]  w_rplc_slot [N_REQ];
    always_comb begin
        for (int d = 0; d < N_REQ; d++) begin
            w_rplc_vld[d]  = 1'b0;
            w_rplc_slot[d] = '0;
            for (int s = SLOTS - 1; s >= 0; s--) begin
                if (r_vld[s] && (r_dir[s] == RQ_W'(d)) && w_gathered[s] && r_ar_taken[s]
                    && (r_dt[s] || r_nodata[s]) && !r_iow[s] && !r_rpl_done[s]
                    && !(r_rpl_vld[d] && (r_rpl_slot[d] == SLOT_W'(s)))) begin
                    w_rplc_vld[d]  = 1'b1;
                    w_rplc_slot[d] = SLOT_W'(s);
                end
            end
        end
    end

    // slot line buffers: one per requester (the caches, the IO), indexed
    // {slot, beat}; one write port (the arbitrated CD beat) and two
    // asynchronous reads (the requester's replay, the absorption) --
    // distributed RAM, payload only
    logic [BUF_AW-1:0]    w_buf_waddr [N_REQ];
    logic [BUS_WIDTH-1:0] w_buf_wdata [N_REQ];
    logic [BUF_AW-1:0]    w_rpl_raddr [N_REQ];
    logic [BUS_WIDTH-1:0] w_rpl_rdata [N_REQ];
    logic [BUF_AW-1:0]    w_abs_raddr;
    logic [BUS_WIDTH-1:0] w_abs_rdata_a [N_REQ];
    always_comb begin
        for (int a = 0; a < N_REQ; a++) begin
            w_buf_waddr[a] = {w_sni_head[w_buf_src[a]], r_cd_beat[w_buf_src[a]]};
            w_buf_wdata[a] = s_cddata[w_buf_src[a]];
        end
        for (int d = 0; d < N_REQ; d++)
            w_rpl_raddr[d] = {r_rpl_slot[d], r_rpl_beat[d]};
    end

    generate
        for (genvar a = 0; a < N_REQ; a++) begin : g_buf
            (* ram_style = "distributed" *)
            /* synthesis ramstyle = "MLAB" */
            logic [BUS_WIDTH-1:0] mem [BUF_DEPTH];
            always_ff @(posedge clk) begin
                if (w_buf_we[a])
                    mem[w_buf_waddr[a]] <= w_buf_wdata[a];
            end
            assign w_rpl_rdata[a]   = mem[w_rpl_raddr[a]];
            assign w_abs_rdata_a[a] = mem[w_abs_raddr];
        end
    endgenerate

    // per-requester R output: memory beat (priority) or replay beat; the
    // caches' and the IO's R channels are requester 0..N-1 and N
    logic [N_REQ-1:0] rq_rready;
    always_comb begin
        for (int d = 0; d < N_PORTS; d++) rq_rready[d] = c_rready[d];
        rq_rready[IO] = io_rready;
    end
    logic [N_REQ-1:0] w_mem_want, w_rpl_pres, w_mem_pres, w_rvalid, w_rpl_hs, w_mem_hs;
    always_comb begin
        for (int d = 0; d < N_REQ; d++) begin
            w_mem_want[d] = w_mr_fwd & (w_mr_dir == RQ_W'(d));
            w_rpl_pres[d] = r_rpl_vld[d] & (r_rpl_hold[d] | ~w_mem_want[d]);
            w_mem_pres[d] = w_mem_want[d] & ~w_rpl_pres[d];
            w_rvalid[d]   = w_rpl_pres[d] | w_mem_pres[d];
            w_rpl_hs[d]   = w_rpl_pres[d] & rq_rready[d];
            w_mem_hs[d]   = w_mem_pres[d] & rq_rready[d];
        end
    end
    wire w_mr_hs = (|w_mem_hs) | w_mr_drop;
    assign mem_rready = w_mr_drop | (w_mr_fwd & w_mem_pres[w_mr_dir] & rq_rready[w_mr_dir]);

    logic [IW-1:0]        rq_rid   [N_REQ];
    logic [BUS_WIDTH-1:0] rq_rdata [N_REQ];
    logic [1:0]           rq_rresp [N_REQ];
    logic [UW-1:0]        rq_ruser [N_REQ];
    logic [N_REQ-1:0]     w_out_rlast;
    always_comb begin
        for (int d = 0; d < N_REQ; d++) begin
            if (w_rpl_pres[d]) begin
                rq_rid[d]      = r_arid[r_rpl_slot[d]];
                rq_rdata[d]    = r_nodata[r_rpl_slot[d]] ? '0 : w_rpl_rdata[d];
                rq_rresp[d]    = 2'b00;
                // a cache's replay is the whole line; the IO's is the beats
                // its AR asked for (all within the line)
                w_out_rlast[d] = r_nodata[r_rpl_slot[d]]
                                 | ((d == IO) ? (r_rpl_cnt[d] == r_io_arlen)
                                              : (r_rpl_beat[d] == BEAT_INDEX_WIDTH'(FILL_BEATS - 1)));
                rq_ruser[d]    = '0;
            end else begin
                rq_rid[d]      = r_arid[w_mr_slot];
                rq_rdata[d]    = mem_rdata;
                rq_rresp[d]    = mem_rresp;
                w_out_rlast[d] = mem_rlast;
                rq_ruser[d]    = mem_ruser;
            end
        end
        for (int d = 0; d < N_PORTS; d++) begin
            c_rid[d]   = rq_rid[d];
            c_rdata[d] = rq_rdata[d];
            c_rresp[d] = rq_rresp[d];
            c_ruser[d] = rq_ruser[d];
        end
    end
    assign c_rlast   = w_out_rlast[N_PORTS-1:0];
    assign c_rvalid  = w_rvalid[N_PORTS-1:0];
    assign io_rid    = rq_rid[IO];
    assign io_rdata  = rq_rdata[IO];
    assign io_rresp  = rq_rresp[IO];
    assign io_ruser  = rq_ruser[IO];
    assign io_rlast  = w_out_rlast[IO];
    assign io_rvalid = w_rvalid[IO];

    // ------------------------------------------------------------------
    // Write port: write-back pass-through + PassDirty absorption + the IO
    // write, one burst in flight system-wide, round-robin over
    // {wb_0..wb_N-1, absorb, io}
    // ------------------------------------------------------------------
    localparam logic [1:0] W_IDLE = 2'd0;
    localparam logic [1:0] W_AW   = 2'd1;
    localparam logic [1:0] W_W    = 2'd2;
    localparam logic [1:0] W_B    = 2'd3;

    logic [1:0]        r_wstate;
    logic [WSEL_W-1:0] r_w_sel;        // 0..N-1 = wb of port, N = absorb, N+1 = the IO write
    logic [SLOT_W-1:0] r_w_slot;
    logic [WSEL_W-1:0] r_w_rr;
    logic [BEAT_INDEX_WIDTH-1:0] r_w_beat;

    // Write-backs to one line in presentation order (jet-prime BUG-002).
    // A cache whose victim drain had started when a snoop passed the line
    // dirty still drains it (its AW is presented and cannot be withdrawn);
    // the hold below keeps it until the absorption lands, and once
    // released it must not lose the round-robin to the NEW owner's later
    // write-back of the same line, or the stale bytes land last.  A
    // write-back presented while another port already presents one to the
    // same line yields until that one is taken; the one burst in flight
    // then orders the two in memory.  (Two first presented in the same
    // cycle cannot be a stale/new pair: the new owner's write-back follows
    // its own fill, which follows the verdict that the stale AW predates.)
    logic [N_PORTS-1:0] r_aw_pres;    // presented last cycle and not taken
    logic [N_PORTS-1:0] r_aw_yield;   // presented after another's, same line
    logic [N_PORTS-1:0] w_aw_younger;
    always_comb begin
        for (int d = 0; d < N_PORTS; d++) begin
            w_aw_younger[d] = 1'b0;
            for (int e = 0; e < N_PORTS; e++) begin
                if ((e != d) && c_awvalid[d] && c_awvalid[e]
                    && (line_of(c_awaddr[d]) == line_of(c_awaddr[e]))
                    && (r_aw_yield[d] || (r_aw_pres[e] && !r_aw_pres[d])))
                    w_aw_younger[d] = 1'b1;
            end
        end
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_aw_pres  <= '0;
            r_aw_yield <= '0;
        end else begin
            r_aw_pres  <= c_awvalid & ~c_awready;
            r_aw_yield <= w_aw_younger;
        end
    )

    logic [N_PORTS-1:0] w_wb_blocked;
    logic               w_wb_blocked_io;   // the IO's non-shareable write, the same hold
    always_comb begin
        for (int d = 0; d < N_PORTS; d++) begin
            w_wb_blocked[d] = w_aw_younger[d];
            for (int s = 0; s < SLOTS; s++) begin
                if (r_vld[s] && (r_line[s] == line_of(c_awaddr[d]))
                    && (!w_gathered[s] || (r_pd[s] && !r_abs_done[s])))
                    w_wb_blocked[d] = 1'b1;
            end
        end
        w_wb_blocked_io = 1'b0;
        for (int s = 0; s < SLOTS; s++) begin
            if (r_vld[s] && (r_line[s] == line_of(io_awaddr))
                && (!w_gathered[s] || (r_pd[s] && !r_abs_done[s])))
                w_wb_blocked_io = 1'b1;
        end
    end

    // the IO's WriteUnique forwards once its slot is gathered and any
    // PassDirty line absorbed -- and once no cache presents a write-back
    // to the line: a victim whose drain had started when the snoop passed
    // it dirty still drains (jet-prime's WB buffer cannot withdraw a
    // presented AW), and it must land before the IO's data, not after
    logic w_io_line_wb;
    always_comb begin
        w_io_line_wb = 1'b0;
        for (int d = 0; d < N_PORTS; d++)
            if (c_awvalid[d] && (line_of(c_awaddr[d]) == r_line[r_iow_slot]))
                w_io_line_wb = 1'b1;
    end
    wire w_io_w_slot = io_awvalid & w_io_aw_sh & r_iow_slot_vld & w_gathered[r_iow_slot]
                       & (~r_pd[r_iow_slot] | r_abs_done[r_iow_slot]) & ~w_io_line_wb;
    wire w_io_w_pass = io_awvalid & ~w_io_aw_sh & ~r_iow_busy & ~w_wb_blocked_io;

    // absorption candidate: lowest slot with PassDirty not yet written
    logic              w_absc_vld;
    logic [SLOT_W-1:0] w_absc_slot;
    always_comb begin
        w_absc_vld  = 1'b0;
        w_absc_slot = '0;
        for (int s = SLOTS - 1; s >= 0; s--) begin
            if (r_vld[s] && w_gathered[s] && r_pd[s] && !r_abs_issued[s]) begin
                w_absc_vld  = 1'b1;
                w_absc_slot = SLOT_W'(s);
            end
        end
    end

    logic [NW-1:0]     w_wcand;
    logic [WSEL_W-1:0] w_wsel;
    always_comb begin
        for (int d = 0; d < N_PORTS; d++)
            w_wcand[d] = c_awvalid[d] & ~w_wb_blocked[d];
        w_wcand[W_ABS] = w_absc_vld;
        w_wcand[W_IO]  = w_io_w_slot | w_io_w_pass;
        w_wsel = r_w_rr;
        for (int k = NW - 1; k >= 0; k--) begin
            automatic int idx = (32'(r_w_rr) + k) % NW;
            if (w_wcand[idx]) w_wsel = WSEL_W'(idx);
        end
    end
    wire w_wvalid = |w_wcand;

    wire               w_cur_abs = (r_w_sel == WSEL_W'(W_ABS));
    wire               w_cur_io  = (r_w_sel == WSEL_W'(W_IO));
    wire               w_cur_wb  = !w_cur_abs && !w_cur_io;
    wire [PORT_W-1:0]  w_cur_dir = PORT_W'(r_w_sel);
    logic [BUS_WIDTH-1:0] w_abs_rdata;
    assign w_abs_raddr = {r_w_slot, r_w_beat};
    assign w_abs_rdata = w_abs_rdata_a[r_dir[r_w_slot]];

    // the absorption's own burst, the IO's AW as issued, or the cache's
    assign mem_awid     = w_cur_abs ? IW'(8'hA0 | 8'(r_dir[r_w_slot]))
                        : w_cur_io  ? io_awid     : c_awid[w_cur_dir];
    assign mem_awaddr   = w_cur_abs ? {r_line[r_w_slot], OFFSET_W'(0)}
                        : w_cur_io  ? io_awaddr   : c_awaddr[w_cur_dir];
    assign mem_awlen    = w_cur_abs ? 8'(FILL_BEATS - 1) : w_cur_io ? io_awlen    : c_awlen[w_cur_dir];
    assign mem_awsize   = w_cur_abs ? 3'(BYTE_W)         : w_cur_io ? io_awsize   : c_awsize[w_cur_dir];
    assign mem_awburst  = w_cur_abs ? 2'b01              : w_cur_io ? io_awburst  : c_awburst[w_cur_dir];
    assign mem_awlock   = w_cur_abs ? 1'b0               : w_cur_io ? io_awlock   : c_awlock[w_cur_dir];
    assign mem_awcache  = w_cur_abs ? 4'b0000            : w_cur_io ? io_awcache  : c_awcache[w_cur_dir];
    assign mem_awprot   = w_cur_abs ? 3'b000             : w_cur_io ? io_awprot   : c_awprot[w_cur_dir];
    assign mem_awqos    = w_cur_abs ? 4'b0000            : w_cur_io ? io_awqos    : c_awqos[w_cur_dir];
    assign mem_awregion = w_cur_abs ? 4'b0000            : w_cur_io ? io_awregion : c_awregion[w_cur_dir];
    assign mem_awuser   = w_cur_abs ? '0                 : w_cur_io ? io_awuser   : c_awuser[w_cur_dir];
    assign mem_awvalid  = (r_wstate == W_AW) && (w_cur_abs || (w_cur_io ? io_awvalid : c_awvalid[w_cur_dir]));

    wire w_wlast = w_cur_abs ? (r_w_beat == BEAT_INDEX_WIDTH'(FILL_BEATS - 1))
                 : w_cur_io  ? io_wlast : c_wlast[w_cur_dir];
    assign mem_wdata  = w_cur_abs ? w_abs_rdata    : w_cur_io ? io_wdata : c_wdata[w_cur_dir];
    assign mem_wstrb  = w_cur_abs ? {STRB_W{1'b1}} : w_cur_io ? io_wstrb : c_wstrb[w_cur_dir];
    assign mem_wlast  = w_wlast;
    assign mem_wuser  = '0;
    assign mem_wvalid = (r_wstate == W_W) && (w_cur_abs || (w_cur_io ? io_wvalid : c_wvalid[w_cur_dir]));

    always_comb begin
        for (int d = 0; d < N_PORTS; d++) begin
            automatic logic mine = w_cur_wb && (w_cur_dir == PORT_W'(d));
            c_awready[d] = (r_wstate == W_AW) && mine && mem_awready;
            c_wready[d]  = (r_wstate == W_W)  && mine && mem_wready;
            c_bvalid[d]  = (r_wstate == W_B)  && mine && mem_bvalid;
            c_bid[d]     = mem_bid;
            c_bresp[d]   = mem_bresp;
            c_buser[d]   = mem_buser;
        end
    end
    assign io_awready = (r_wstate == W_AW) && w_cur_io && mem_awready;
    assign io_wready  = (r_wstate == W_W)  && w_cur_io && mem_wready;
    assign io_bvalid  = (r_wstate == W_B)  && w_cur_io && mem_bvalid;
    assign io_bid     = mem_bid;
    assign io_bresp   = mem_bresp;
    assign io_buser   = mem_buser;
    assign mem_bready = (r_wstate == W_B) && (w_cur_abs || (w_cur_io ? io_bready : c_bready[w_cur_dir]));

    // ------------------------------------------------------------------
    // Retire sideband: the requester's entry (by read ID) is gone.  A
    // cache's; the IO port has none (its slot's rack is set at the grant)
    // ------------------------------------------------------------------
    logic [SLOTS-1:0] w_rack_hit;
    always_comb begin
        for (int s = 0; s < SLOTS; s++) begin
            automatic logic [PORT_W-1:0] dp = PORT_W'(r_dir[s]);
            w_rack_hit[s] = r_vld[s] & r_ar_taken[s] & ~r_rack[s]
                            & (r_dir[s] != RQ_W'(IO))
                            & c_coh_done_valid[dp]
                            & (c_coh_done_id[dp] == r_arid[s]);
        end
    end

    // ------------------------------------------------------------------
    // Sequential: table, queues, replay, write FSM
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_vld        <= '0;
            r_nodata     <= '0;
            r_ar_taken   <= '0;
            r_dt         <= '0;
            r_pd         <= '0;
            r_mem_issued <= '0;
            r_mem_done   <= '0;
            r_rpl_done   <= '0;
            r_abs_issued <= '0;
            r_abs_done   <= '0;
            r_rack       <= '0;
            r_iow        <= '0;
            r_iow_done   <= '0;
            r_rr         <= '0;
            r_pend_ovf   <= '0;
            r_arw_vld    <= '0;
            r_ior_busy   <= 1'b0;
            r_ior_slot   <= '0;
            r_io_araddr  <= '0;
            r_io_arlen   <= '0;
            r_io_arsize  <= '0;
            r_io_arburst <= '0;
            r_io_arlock  <= 1'b0;
            r_io_arqos   <= '0;
            r_io_arregion <= '0;
            r_iow_busy   <= 1'b0;
            r_iow_slot_vld <= 1'b0;
            r_iow_slot   <= '0;
            r_mar_vld    <= 1'b0;
            r_mar_slot   <= '0;
            r_rpl_vld    <= '0;
            r_rpl_hold   <= '0;
            r_wstate     <= W_IDLE;
            r_w_sel      <= '0;
            r_w_slot     <= '0;
            r_w_rr       <= '0;
            r_w_beat     <= '0;
            for (int s = 0; s < SLOTS; s++) begin
                r_dir[s]     <= '0;
                r_ac_left[s] <= '0;
                r_cr_left[s] <= '0;
            end
            for (int d = 0; d < N_PORTS; d++) begin
                r_pend_cnt[d] <= '0;
                r_snq_cnt[d]  <= '0;
                r_sni_cnt[d]  <= '0;
                r_cd_beat[d]  <= '0;
            end
            for (int d = 0; d < N_REQ; d++) begin
                r_arw_slot[d] <= '0;
                r_cd_rr[d]    <= '0;
                r_rpl_slot[d] <= '0;
                r_rpl_beat[d] <= '0;
                r_rpl_cnt[d]  <= '0;
            end
        end else begin
            // ---------------- pending queues: push the pulse, pop the grant
            for (int d = 0; d < N_PORTS; d++) begin
                automatic logic push = coh_req_vld[d]
                                       & ~(w_grant & (w_grant_dir == RQ_W'(d)) & w_cand_live[d]);
                automatic logic pop  = w_grant & (w_grant_dir == RQ_W'(d)) & ~w_cand_live[d];
                if (pop) begin
                    for (int k = 0; k < PEND_DEPTH - 1; k++) begin
                        r_pend_addr[d][k] <= r_pend_addr[d][k+1];
                        r_pend_type[d][k] <= r_pend_type[d][k+1];
                    end
                    if (push) begin
                        r_pend_addr[d][2'(r_pend_cnt[d]) - 2'd1] <= c_coh_req_addr[d];
                        r_pend_type[d][2'(r_pend_cnt[d]) - 2'd1] <= c_coh_req_type[d];
                    end else begin
                        r_pend_cnt[d] <= r_pend_cnt[d] - PEND_W'(1);
                    end
                end else if (push) begin
                    if (r_pend_cnt[d] < PEND_W'(PEND_DEPTH)) begin
                        r_pend_addr[d][2'(r_pend_cnt[d])] <= c_coh_req_addr[d];
                        r_pend_type[d][2'(r_pend_cnt[d])] <= c_coh_req_type[d];
                        r_pend_cnt[d] <= r_pend_cnt[d] + PEND_W'(1);
                    end else begin
                        r_pend_ovf[d] <= 1'b1;
                    end
                end
            end

            // ---------------- grant: allocate the slot, arm the AR take.  A
            // cache's transaction: its class, N-1 peers, the AR awaited, the
            // retire awaited.  The IO's read: N peers (shareable) or none,
            // the AR awaited, no retire (rack set).  The IO's WriteUnique:
            // N peers, no AR (taken), no read (nodata), delivered at its B.
            if (w_grant) begin
                r_vld[w_slot_idx]        <= 1'b1;
                r_dir[w_slot_idx]        <= w_grant_dir;
                r_line[w_slot_idx]       <= line_of(w_cand_addr[w_grant_dir]);
                r_type[w_slot_idx]       <= w_cand_type[w_grant_dir];
                r_nodata[w_slot_idx]     <= w_grant_io ? w_grant_io_wr : is_nodata(w_cand_type[w_grant_dir]);
                r_ar_taken[w_slot_idx]   <= w_grant_io_wr;
                r_ac_left[w_slot_idx]    <= w_grant_npeer;
                r_cr_left[w_slot_idx]    <= w_grant_npeer;
                r_dt[w_slot_idx]         <= 1'b0;
                r_pd[w_slot_idx]         <= 1'b0;
                r_mem_issued[w_slot_idx] <= 1'b0;
                r_mem_done[w_slot_idx]   <= 1'b0;
                r_rpl_done[w_slot_idx]   <= 1'b0;
                r_abs_issued[w_slot_idx] <= 1'b0;
                r_abs_done[w_slot_idx]   <= 1'b0;
                r_rack[w_slot_idx]       <= w_grant_io;
                r_iow[w_slot_idx]        <= w_grant_io_wr;
                r_iow_done[w_slot_idx]   <= 1'b0;
                if (!w_grant_io_wr) begin
                    r_arw_vld[w_grant_dir]   <= 1'b1;
                    r_arw_slot[w_grant_dir]  <= w_slot_idx;
                end
                if (w_grant_io && !w_grant_io_wr) begin
                    r_ior_busy <= 1'b1;
                    r_ior_slot <= w_slot_idx;
                end
                if (w_grant_io_wr) begin
                    r_iow_busy     <= 1'b1;
                    r_iow_slot_vld <= 1'b1;
                    r_iow_slot     <= w_slot_idx;
                end
                r_rr                     <= RQ_W'((32'(w_grant_dir) + 1) % N_REQ);
            end
            // the IO read's slot frees: the port may read again
            if (r_ior_busy && w_free_now[r_ior_slot])
                r_ior_busy <= 1'b0;

            // ---------------- AR take (the caches, the IO read with its burst)
            for (int d = 0; d < N_PORTS; d++) begin
                if (w_ar_take[d]) begin
                    r_ar_taken[r_arw_slot[d]] <= 1'b1;
                    r_arid[r_arw_slot[d]]     <= c_arid[d];
                    r_arcache[r_arw_slot[d]]  <= c_arcache[d];
                    r_arprot[r_arw_slot[d]]   <= c_arprot[d];
                    r_aruser[r_arw_slot[d]]   <= c_aruser[d];
                    r_arw_vld[d]              <= 1'b0;
                end
            end
            if (w_io_ar_take) begin
                r_ar_taken[r_arw_slot[IO]] <= 1'b1;
                r_arid[r_arw_slot[IO]]     <= io_arid;
                r_arcache[r_arw_slot[IO]]  <= io_arcache;
                r_arprot[r_arw_slot[IO]]   <= io_arprot;
                r_aruser[r_arw_slot[IO]]   <= io_aruser;
                r_io_araddr   <= io_araddr;
                r_io_arlen    <= io_arlen;
                r_io_arsize   <= io_arsize;
                r_io_arburst  <= io_arburst;
                r_io_arlock   <= io_arlock;
                r_io_arqos    <= io_arqos;
                r_io_arregion <= io_arregion;
                r_arw_vld[IO] <= 1'b0;
            end

            // ---------------- snoop queues per peer (a pop shifts first, a
            // same-cycle push lands on the freed tail)
            for (int p = 0; p < N_PORTS; p++) begin
                // a grant snoops every port but its requester; the IO's
                // non-shareable read snoops none
                automatic logic push_q = w_grant & (w_grant_dir != RQ_W'(p)) & (w_grant_npeer != '0);
                if (w_ac_hs[p]) begin
                    for (int k = 0; k < SLOTS - 1; k++)
                        r_snq[p][k] <= r_snq[p][k+1];
                end
                if (push_q)
                    r_snq[p][SLOT_W'(r_snq_cnt[p] - SNQ_W'(w_ac_hs[p]))] <= w_slot_idx;
                r_snq_cnt[p] <= r_snq_cnt[p] + SNQ_W'(push_q) - SNQ_W'(w_ac_hs[p]);
                if (w_cr_hs[p]) begin
                    for (int k = 0; k < SNOOP_INFLIGHT - 1; k++)
                        r_sni[p][k] <= r_sni[p][k+1];
                    if (s_crresp[p][AMBER_CRRESP_DT]) begin
                        r_dt[w_sni_head[p]] <= 1'b1;
                        r_pd[w_sni_head[p]] <= s_crresp[p][AMBER_CRRESP_PD];
                        // the verdict beat the memory AR: nothing to drain
                        // (an AR presented this cycle is held and WILL
                        // issue -- its beats are drained)
                        if (!r_mem_issued[w_sni_head[p]]
                            && !(w_mar_vld && (w_mar_slot == w_sni_head[p])))
                            r_mem_done[w_sni_head[p]] <= 1'b1;
                    end
                    r_cd_beat[p] <= '0;
                end
                if (w_ac_hs[p])
                    r_sni[p][SNI_IW'(r_sni_cnt[p] - SNI_W'(w_cr_hs[p]))] <= w_ac_slot[p];
                r_sni_cnt[p] <= r_sni_cnt[p] + SNI_W'(w_ac_hs[p]) - SNI_W'(w_cr_hs[p]);
                if (w_cd_hs[p])
                    r_cd_beat[p] <= s_cdlast[p] ? '0 : r_cd_beat[p] + BEAT_INDEX_WIDTH'(1);
            end
            // the slots' peer counters step by this cycle's handshakes
            for (int s = 0; s < SLOTS; s++) begin
                if (w_ac_dec[s] != '0) r_ac_left[s] <= r_ac_left[s] - w_ac_dec[s];
                if (w_cr_dec[s] != '0) r_cr_left[s] <= r_cr_left[s] - w_cr_dec[s];
            end
            // the CD write pointers rotate past the peer that wrote
            for (int a = 0; a < N_REQ; a++) begin
                if (w_buf_we[a])
                    r_cd_rr[a] <= PORT_W'((32'(w_buf_src[a]) + 1) % N_PORTS);
            end

            // ---------------- memory AR / R (a presented AR holds until taken)
            if (w_mar_hs) begin
                r_mem_issued[w_mar_slot] <= 1'b1;
                r_mar_vld                <= 1'b0;
            end else if (w_mar_vld) begin
                r_mar_vld  <= 1'b1;
                r_mar_slot <= w_mar_slot;
            end
            if (w_mr_hs && mem_rlast)
                r_mem_done[w_mr_slot] <= 1'b1;

            // ---------------- replay engines (the IO's starts at its AR's
            // beat within the line and counts its ARLEN+1 beats)
            for (int d = 0; d < N_REQ; d++) begin
                if (r_rpl_vld[d]) begin
                    if (w_rpl_hs[d]) begin
                        r_rpl_hold[d] <= 1'b0;
                        if (w_out_rlast[d]) begin
                            r_rpl_vld[d]              <= 1'b0;
                            r_rpl_done[r_rpl_slot[d]] <= 1'b1;
                        end else begin
                            r_rpl_beat[d] <= r_rpl_beat[d] + BEAT_INDEX_WIDTH'(1);
                            r_rpl_cnt[d]  <= r_rpl_cnt[d] + 8'd1;
                        end
                    end else if (w_rpl_pres[d]) begin
                        r_rpl_hold[d] <= 1'b1;
                    end
                end else if (w_rplc_vld[d]) begin
                    r_rpl_vld[d]  <= 1'b1;
                    r_rpl_slot[d] <= w_rplc_slot[d];
                    r_rpl_beat[d] <= (d == IO) ? r_io_araddr[OFFSET_W-1 -: BEAT_INDEX_WIDTH] : '0;
                    r_rpl_cnt[d]  <= '0;
                    r_rpl_hold[d] <= 1'b0;
                end
            end

            // ---------------- write port FSM
            unique case (r_wstate)
                W_IDLE: begin
                    if (w_wvalid) begin
                        r_w_sel  <= w_wsel;
                        r_w_slot <= w_absc_slot;
                        r_w_rr   <= WSEL_W'((32'(w_wsel) + 1) % NW);
                        r_w_beat <= '0;
                        r_wstate <= W_AW;
                        if (w_wsel == WSEL_W'(W_ABS))
                            r_abs_issued[w_absc_slot] <= 1'b1;
                        // the IO's non-shareable write holds the port from its
                        // selection (its WriteUnique has held it since its grant)
                        if (w_wsel == WSEL_W'(W_IO))
                            r_iow_busy <= 1'b1;
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
                        // the IO write is done: its WriteUnique slot is
                        // delivered (and frees), the port may write again
                        if (w_cur_io) begin
                            r_iow_busy <= 1'b0;
                            if (r_iow_slot_vld) begin
                                r_iow_done[r_iow_slot] <= 1'b1;
                                r_iow_slot_vld         <= 1'b0;
                            end
                        end
                    end
                end
                default: r_wstate <= W_IDLE;
            endcase

            // ---------------- retire sideband, slot release
            for (int s = 0; s < SLOTS; s++) begin
                if (w_rack_hit[s]) r_rack[s] <= 1'b1;
                if (w_free_now[s]) r_vld[s]  <= 1'b0;
            end
        end
    )

    // ------------------------------------------------------------------
    // Event taps (D9)
    // ------------------------------------------------------------------
    assign evt_grant     = w_grant;
    assign evt_grant_cls = w_cand_type[w_grant_dir];
    assign evt_ac        = w_ac_hs;
    always_comb begin
        // the CR that completes a gather: the slot's count equals this
        // cycle's CRs for it, and this is the last of them (two peers of
        // one slot answering together report once).  Per answering port,
        // not one bit: two peers can each complete a different slot in the
        // same cycle (the pair rig does it once a run), and a single bit
        // would merge them -- an event lost that nothing counted.
        for (int p = 0; p < N_PORTS; p++) begin
            evt_gather[p]      = w_cr_last[p] && (r_cr_left[w_sni_head[p]] == w_cr_dec[w_sni_head[p]]);
            evt_gather_slot[p] = w_sni_head[p];
            evt_gather_dt[p]   = r_dt[w_sni_head[p]] | w_cr_dt_now[w_sni_head[p]];
            evt_gather_pd[p]   = r_pd[w_sni_head[p]] | w_cr_pd_now[w_sni_head[p]];
            evt_read_wasted[p] = w_cr_hs[p] && s_crresp[p][AMBER_CRRESP_DT]
                && (r_mem_issued[w_sni_head[p]] || (w_mar_vld && (w_mar_slot == w_sni_head[p])));
        end
        for (int d = 0; d < N_REQ; d++) begin
            evt_lock_wait[d]      = w_cand_vld[d] & w_cand_locked[d];
            // element-wise, not a whole-array alias: sv2v packs an aliased
            // array and the formal harness exposes w_cand_addr per element
            evt_lock_wait_addr[d] = w_cand_addr[d];
        end
    end
    assign evt_mem_ar = w_mar_hs;
    assign evt_absorb = (r_wstate == W_B) & w_cur_abs & mem_bvalid & mem_bready;
    assign evt_absorb_slot = r_w_slot;
    assign evt_wb     = mem_awvalid & mem_awready & ~w_cur_abs;
    assign evt_wb_io  = w_cur_io;

    // ------------------------------------------------------------------
    // Debug taps
    // ------------------------------------------------------------------
    assign dbg_busy       = |r_vld;
    assign dbg_slot_vld   = r_vld;
    always_comb begin
        for (int d = 0; d < N_PORTS; d++)
            dbg_pend_vld[d] = (r_pend_cnt[d] != '0);
    end
    assign dbg_abs_pend   = |(r_vld & r_pd & ~r_abs_done);
    assign dbg_grant      = w_grant;
    assign dbg_grant_dir  = w_grant_dir;
    assign dbg_grant_addr = w_cand_addr[w_grant_dir];
    assign dbg_grant_slot = w_slot_idx;

    // ------------------------------------------------------------------
    // Unused-input roll-up (the AR sideband fields onyx regenerates, the
    // write-side user fields it zeroes)
    // ------------------------------------------------------------------
    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_ar;
    always_comb begin
        unused_ar = 1'b0;
        for (int d = 0; d < N_PORTS; d++)
            unused_ar = unused_ar ^ (^{c_arlen[d], c_arsize[d], c_arburst[d], c_arlock[d],
                                       c_arqos[d], c_arregion[d], c_wuser[d]});
        unused_ar = unused_ar ^ (^mem_rid[IW-1:SLOT_W]);
        // the IO's snoop codes and barriers: decoded by the domain alone
        // (sim-checked below); its W user field is zeroed like the caches'
        unused_ar = unused_ar ^ (^{io_arsnoop, io_awsnoop, io_arbar, io_awbar, io_wuser});
    end
    /* verilator lint_on UNUSEDSIGNAL */

    // ------------------------------------------------------------------
    // Simulation-only contract checks
    // ------------------------------------------------------------------
    // pragma translate_off
    /* verilator lint_off SYNCASYNCNET */
    always @(posedge clk) if (rst_n) begin
        for (int d = 0; d < N_PORTS; d++) begin
            if (w_ar_take[d] && (line_of(c_araddr[d]) != r_line[r_arw_slot[d]]))
                $error("onyx_ccu: port %0d AR line %h is not its granted slot's line %h",
                       d, line_of(c_araddr[d]), r_line[r_arw_slot[d]]);
            if (w_ar_take[d] && (is_nodata(r_type[r_arw_slot[d]]) != (c_arlen[d] == 8'd0)))
                $error("onyx_ccu: port %0d AR length disagrees with the request class", d);
        end
        if (mem_rvalid && !(r_vld[w_mr_slot] && r_mem_issued[w_mr_slot] && !r_mem_done[w_mr_slot]))
            $error("onyx_ccu: memory R beat for slot %0d with no read outstanding", w_mr_slot);
        for (int s = 0; s < SLOTS; s++)
            for (int t = s + 1; t < SLOTS; t++)
                if (r_vld[s] && r_vld[t] && (r_line[s] == r_line[t]))
                    $error("onyx_ccu: slots %0d and %0d hold the same line %h", s, t, r_line[s]);
        for (int p = 0; p < N_PORTS; p++) begin
            if (s_cdvalid[p] && (r_sni_cnt[p] == '0))
                $error("onyx_ccu: CD beat from port %0d with no snoop outstanding", p);
            // D6 precondition: a second DataTransfer for a slot already
            // supplied (two peers holding the line E/M is not MESI)
            if (w_cr_hs[p] && s_crresp[p][AMBER_CRRESP_DT] && r_dt[w_sni_head[p]])
                $error("onyx_ccu: second DataTransfer for slot %0d from port %0d", w_sni_head[p], p);
        end
        if (|r_pend_ovf)
            $error("onyx_ccu: pending queue overflow");
        // the IO port's v1 contract: a shareable read is a ReadOnce within
        // one line at full-width INCR beats; a shareable write is a
        // WriteUnique / WriteLineUnique within one line
        if (w_io_ar_take && w_io_ar_sh) begin
            if (io_arsnoop != ACSNOOP_READ_ONCE)
                $error("onyx_ccu: IO shareable read with ARSNOOP %h (v1 decodes ReadOnce only)", io_arsnoop);
            if (io_arsize != 3'(BYTE_W) || io_arburst != 2'b01)
                $error("onyx_ccu: IO shareable read must be full-width INCR beats (size %0d burst %0d)",
                       io_arsize, io_arburst);
            if ((32'(io_araddr[OFFSET_W-1:0]) + ((32'(io_arlen) + 1) << io_arsize)) > LINE_BYTES)
                $error("onyx_ccu: IO shareable read crosses a line (addr %h len %0d)", io_araddr, io_arlen);
        end
        if (io_awvalid && io_awready && w_io_aw_sh) begin
            if (io_awsnoop > 3'd1)
                $error("onyx_ccu: IO shareable write with AWSNOOP %h (v1 decodes WriteUnique / WriteLineUnique)",
                       io_awsnoop);
            if ((32'(io_awaddr[OFFSET_W-1:0]) + ((32'(io_awlen) + 1) << io_awsize)) > LINE_BYTES)
                $error("onyx_ccu: IO shareable write crosses a line (addr %h len %0d)", io_awaddr, io_awlen);
        end
    end
    /* verilator lint_on SYNCASYNCNET */
    // pragma translate_on

endmodule : onyx_ccu
