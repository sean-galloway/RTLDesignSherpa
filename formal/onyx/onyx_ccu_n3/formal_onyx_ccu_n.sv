// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal wrapper for onyx_ccu at N_PORTS = 3 and 4 (yosys-compatible) --
// SAFETY + COVER.  ONE harness for both N: the .sby reads it with -DNP=3 or
// -DNP=4 (plus -DNP4 at N=4, for the per-element exposed ports whose count
// follows N).  Units: formal/onyx/onyx_ccu_n3 (this file's home) and
// formal/onyx/onyx_ccu_n4 (reads ../onyx_ccu_n3/formal_onyx_ccu_n.sv).  The
// N=2 unit is formal/onyx/onyx_ccu; this file is its property set
// generalized, not a copy of it.
//
// onyx TASK-001 "Done when": the serializer and the gather proven safe at
// N = 2, 3, 4 with mutations.  What changed from the N=2 harness:
//   - every per-port family is a packed free vector here (port d at
//     [d*W +: W]); a generate block reverses each unpacked-array family into
//     sv2v's packing (element 0 at the TOP of the vector) for the DUT;
//   - "the other direction" is "every other requester" throughout: P4 reads
//     the requester's own retire port, P14 any other requester, P16's CD
//     arbitration exception any other peer writing the same buffer, P17 /
//     P25 / P-IO4 every cache's write-back, the BUG-002 write-back order
//     every pair of caches presenting the same line, A-snoop's one-supplier
//     rule every other peer;
//   - widths follow N: the requester index (r_dir, dbg_grant_dir) and the
//     peer counts (r_ac_left / r_cr_left) are $clog2(N+1) bits -- 2 at N=3,
//     3 at N=4; the write-port selector is 3 bits (N+2 candidates: wb_0..
//     wb_N-1, the absorption N, the IO N+1); the IO is requester N;
//   - the per-peer shadow the N=2 header said a N=3 harness needs (below,
//     "Per-peer gather shadow"): per slot and per peer, OWED (set at the
//     grant from the requester and the IO's kind: a cache snoops the other
//     N-1 caches, the IO's shareable read or write all N, its non-shareable
//     read none), AC ACCEPTED (the AC handshake at that slot) and CR
//     ANSWERED (the CR handshake at that slot); plus, per peer, the harness's
//     own in-order queue of the slots whose AC it accepted (the CR answers
//     the oldest); plus the DT / PD verdict re-derived from the CRs.  Three
//     properties read it (a fourth, ap_snq_count: the AC each peer is owed and
//     has not accepted is queued at it -- the dropped-peer hang made a safety
//     property): ap_peer_shadow (the DUT's two counters are exactly
//     the shadow's owed-and-not-accepted / owed-and-not-answered counts, the
//     verdict bits are the CRs' OR, an answer only after an accept),
//     ap_ac_legal (an AC goes only to a peer the slot OWES and has not yet
//     accepted -- not to the requester, not twice) and ap_cr_slot (the slot
//     a peer's CR and CD land in is the oldest slot it accepted and has not
//     answered);
//   - new at N >= 3: ap_sn_count also asserts one CD writer per buffer per
//     cycle (two peers supplying two slots of one cache share that cache's
//     buffer -- at N=2 only the IO's slots could collide).
//
// Geometry: ADDR_WIDTH=8 (16 lines) / LINE_BYTES=16 / BUS_WIDTH=32 (four
// beats per line) / AXI_ID_WIDTH=3 / SLOTS=4 / SNOOP_INFLIGHT=2 /
// DEFER_AR=0 / SERIAL_MODE=0 -- as at N=2.  SLOTS stays 4: every property is
// per slot or per pair of slots (one per line, a grant to a held line, two
// slots of one requester sharing its buffer, a same-line request waiting
// behind a live one while a distinct line runs beside it), and 4 slots for
// N+1 requesters means the table can be FULL while requesters wait -- a
// state a bigger table hides (cp_table_full).  SNOOP_INFLIGHT=2 is the
// shipped value and lets a peer hold two slots' ACs, the CR-pairing case.
// Raising SLOTS widens every per-slot loop and the BMC cost with it, for no
// property that needs a fifth slot.
//
// Composition: the DUT alone.  Every cache, every snoop responder, the IO
// master and the shared memory are free inputs under the contracts below.
// No property claims data values; the properties are about WHICH beat goes
// WHERE and WHEN, and about every valid/ready pair onyx drives.
//
// Internal observability: the DUT flat is parameter-specialized (the
// Makefile) and the .sby exposes the transaction table and the queue heads
// as DUT output ports (read_verilog -mem2reg turns the unpacked arrays into
// per-element wires `\r_line[0]` etc.).
//
// Assumption inventory (environment obligations; identical in content to
// the N=2 harness, quantified over N caches / N responders):
//   - house reset protocol (reset for exactly the two steps before the
//     contracts arm); every environment VALID low under reset;
//   - A-req: a request pulse carries READ_NOT_SHARED_DIRTY, READ_UNIQUE,
//     CLEAN_UNIQUE, WRITE_BACK or WRITE_CLEAN; WRITE_BACK / WRITE_CLEAN
//     allocate nothing; a cache holds at most PEND_DEPTH (4) launches whose
//     AR onyx has not taken;
//   - A-ar: the cache presents its ARs in launch order, the class's length
//     (0 upgrade, 3 fill), a read ID not in flight; AXI stability;
//   - A-done: a retire names an in-flight ID whose last beat has landed;
//   - A-wb: AXI stability on the cache's AW and W;
//   - A-snoop: a responder answers only an accepted AC (CR, CD only while
//     one is outstanding), in order; a DT CR follows exactly 4 CD beats with
//     CDLAST on the last (it may share the CR's cycle), a non-DT CR none;
//     PassDirty only with DT; no data for MakeInvalid; at most one peer
//     supplies a slot -- none for a slot already supplied, and none while
//     ANOTHER peer is mid-supply for the same slot (MESI: one E/M holder; at
//     N >= 3 a cache's slot has two or three peers, so this is now exercised
//     by the caches' own transactions, not only the IO's);
//   - A-mem: an R beat names a read onyx issued and not drained, RLAST on
//     the AR's last beat, IDs interleave freely, AXI R stability; BVALID only
//     with a write outstanding;
//   - A-io: full-width INCR within one line, ARSNOOP 0, AWSNOOP 0 / 1, AXI
//     stability on AR / AW / W, W only after its AW, WLAST on the AWLEN+1-th.
//
// Mutations (2026-11-27, each on a scratch copy of the N=3 AND the N=4
// flat, BMC with every property group; the step and the property that
// failed, identical at both N):
//   M1  the gather declared complete at once (w_gathered = 1): step 4
//       ap_table_flags;
//   M2  the fanout includes the requester (push_q = w_grant): step 4
//       ap_ac_legal + ap_snq_count;
//   M3  a second grant with an AR untaken (~r_arw_vld dropped): step 4
//       ap_grant_one_ar (also under prove_fast alone, step 4);
//   M4  a slot's AC counter steps by one when two peers accept it in one
//       cycle (the historical IO-read hang, now reachable by a cache's own
//       slot): step 5 ap_peer_shadow;  M4b the same for CRs: step 6
//       ap_peer_shadow;
//   M5  the CD write arbitration bypassed (cdready = cdvalid & snoop
//       outstanding): step 6 ap_sn_count (two beats into one buffer);
//   M6  the CR paired with the second in-flight AC (r_sni[p][1]): step 5
//       ap_cr_slot;
//   M7  the fanout drops peer N-1 of a cache's transaction (the slot can
//       never gather -- a hang): step 4 ap_snq_count;
//   M8  the per-line lock checks requesters 0 and 1 only: step 4
//       ap_grant_unlocked;
// and the generalizations ("every other requester") narrowed back to
// ports 0 / 1 or to a one-bit index -- each a no-op or near-no-op at N=2:
//   M9  retire read from port (dir & 1): step 9 ap_rack_source;
//   M10 the write-back order hold only between ports 0 and 1: step 7
//       ap_wb_order;
//   M11 the write-back hold only for ports 0 / 1: step 5 ap_wb_select_hold;
//   M12 the IO WriteUnique waits only for ports 0 / 1's write-backs: step 8
//       ap_io_port;
//   M13 the absorption AWID from a one-bit requester: step 10 ap_abs_legal;
//   M14 memory beats routed by a one-bit requester: step 6 ap_route_mem
//       (+ ap_io_port; + ap_r_inflight at N=4);
//   M15 an absorption waits only for ports 0 / 1's old write-backs: step 10
//       ap_abs_after_old_wb;
//   M16 a slot freed before its requester has its beats: step 5
//       ap_free_complete;
//   M17 the memory read ignores a write in flight to its line: step 5
//       ap_mar_no_wr_race;
//   M18 the presented memory AR not held (re-picked each cycle): step 6
//       ap_mar_stable.
// Not individually mutated: ap_line_unique, ap_mo, ap_arready_slot,
// ap_ar_pairing, ap_mar_legal, ap_route_rpl, ap_no_pend_ovf, ap_pend_count,
// ap_engines_live, ap_r_stable, ap_ac_stable, ap_r_beats, ap_cd_slot (their
// N=2 forms carry over with only their loop bounds widened).
//
// Depths, wall times and the depth derivation: the .sby headers of
// onyx_ccu_n3 / onyx_ccu_n4.

`ifndef NP
`define NP 3
`endif

module formal_onyx_ccu_n #(
    parameter int AW = 8,         // ADDR_WIDTH of the specialized flat
    parameter int NP = `NP        // N_PORTS of the specialized flat
) (
    input  logic                clk,
    input  logic                rst_n,

    // caches (free), port d at [d*W +: W]
    input  logic [NP*3-1:0]     c_arid,
    input  logic [NP*AW-1:0]    c_araddr,
    input  logic [NP*8-1:0]     c_arlen,
    input  logic [NP*3-1:0]     c_arsize,
    input  logic [NP*2-1:0]     c_arburst,
    input  logic [NP-1:0]       c_arlock,
    input  logic [NP*4-1:0]     c_arcache,
    input  logic [NP*3-1:0]     c_arprot,
    input  logic [NP*4-1:0]     c_arqos,
    input  logic [NP*4-1:0]     c_arregion,
    input  logic [NP-1:0]       c_aruser,
    input  logic [NP-1:0]       c_arvalid,
    input  logic [NP-1:0]       c_rready,
    input  logic [NP*3-1:0]     c_awid,
    input  logic [NP*AW-1:0]    c_awaddr,
    input  logic [NP*8-1:0]     c_awlen,
    input  logic [NP*3-1:0]     c_awsize,
    input  logic [NP*2-1:0]     c_awburst,
    input  logic [NP-1:0]       c_awlock,
    input  logic [NP*4-1:0]     c_awcache,
    input  logic [NP*3-1:0]     c_awprot,
    input  logic [NP*4-1:0]     c_awqos,
    input  logic [NP*4-1:0]     c_awregion,
    input  logic [NP-1:0]       c_awuser,
    input  logic [NP-1:0]       c_awvalid,
    input  logic [NP*32-1:0]    c_wdata,
    input  logic [NP*4-1:0]     c_wstrb,
    input  logic [NP-1:0]       c_wlast,
    input  logic [NP-1:0]       c_wuser,
    input  logic [NP-1:0]       c_wvalid,
    input  logic [NP-1:0]       c_bready,

    // snoop responders (free)
    input  logic [NP-1:0]       s_acready,
    input  logic [NP*5-1:0]     s_crresp,
    input  logic [NP-1:0]       s_crvalid,
    input  logic [NP*32-1:0]    s_cddata,
    input  logic [NP-1:0]       s_cdlast,
    input  logic [NP-1:0]       s_cdvalid,

    // D-8 request / retire sidebands (free)
    input  logic [NP-1:0]       c_coh_req_valid,
    input  logic [NP*AW-1:0]    c_coh_req_addr,
    input  logic [NP*3-1:0]     c_coh_req_type,
    input  logic [NP-1:0]       c_coh_done_valid,
    input  logic [NP*3-1:0]     c_coh_done_id,

    // ACE-Lite IO port (free)
    input  logic [2:0]  io_arid,
    input  logic [AW-1:0] io_araddr,
    input  logic [7:0]  io_arlen,
    input  logic [2:0]  io_arsize,
    input  logic [1:0]  io_arburst,
    input  logic        io_arlock,
    input  logic [3:0]  io_arcache,
    input  logic [2:0]  io_arprot,
    input  logic [3:0]  io_arqos,
    input  logic [3:0]  io_arregion,
    input  logic        io_aruser,
    input  logic [3:0]  io_arsnoop,
    input  logic [1:0]  io_ardomain,
    input  logic [1:0]  io_arbar,
    input  logic        io_arvalid,
    input  logic        io_rready,
    input  logic [2:0]  io_awid,
    input  logic [AW-1:0] io_awaddr,
    input  logic [7:0]  io_awlen,
    input  logic [2:0]  io_awsize,
    input  logic [1:0]  io_awburst,
    input  logic        io_awlock,
    input  logic [3:0]  io_awcache,
    input  logic [2:0]  io_awprot,
    input  logic [3:0]  io_awqos,
    input  logic [3:0]  io_awregion,
    input  logic        io_awuser,
    input  logic [2:0]  io_awsnoop,
    input  logic [1:0]  io_awdomain,
    input  logic [1:0]  io_awbar,
    input  logic        io_awvalid,
    input  logic [31:0] io_wdata,
    input  logic [3:0]  io_wstrb,
    input  logic        io_wlast,
    input  logic        io_wuser,
    input  logic        io_wvalid,
    input  logic        io_bready,

    // shared memory (free)
    input  logic        mem_arready,
    input  logic [2:0]  mem_rid,
    input  logic [31:0] mem_rdata,
    input  logic [1:0]  mem_rresp,
    input  logic        mem_rlast,
    input  logic        mem_ruser,
    input  logic        mem_rvalid,
    input  logic        mem_awready,
    input  logic        mem_wready,
    input  logic [2:0]  mem_bid,
    input  logic [1:0]  mem_bresp,
    input  logic        mem_buser,
    input  logic        mem_bvalid
);

    // ------------------------------------------------------------------
    // Geometry (the specialized flat is parameterless; these mirror it)
    // ------------------------------------------------------------------
    localparam SLOTS   = 4;
    localparam LINE_W  = AW - 4;
    localparam OFF_W   = 4;
    localparam IW      = 3;
    localparam NRQ     = NP + 1;          // requesters: the caches and the IO
    localparam RQW     = $clog2(NP + 1);  // a requester index (onyx RQ_W)
    localparam PCW     = $clog2(NP + 1);  // a peer count (onyx PC_W)
    localparam WSW     = $clog2(NP + 2);  // the write-port selector (onyx WSEL_W)
    localparam IO      = NP;              // the IO port's requester index

    localparam [2:0] REQ_RU   = 3'b001;
    localparam [2:0] REQ_CU   = 3'b010;
    localparam [2:0] REQ_WB   = 3'b100;
    localparam [2:0] REQ_RNSD = 3'b110;
    localparam [2:0] REQ_WC   = 3'b111;
    localparam [2:0] CLS_IO_RD = 3'b111;
    localparam [2:0] CLS_IO_WR = 3'b101;
    localparam [3:0] ACSNOOP_READ_ONCE     = 4'h0;
    localparam [3:0] ACSNOOP_READ_SHARED   = 4'h1;
    localparam [3:0] ACSNOOP_READ_UNIQUE   = 4'h7;
    localparam [3:0] ACSNOOP_CLEAN_INVALID = 4'h9;
    localparam [3:0] ACSNOOP_MAKE_INVALID  = 4'hC;
    localparam CR_DT = 0;
    localparam CR_PD = 2;
    localparam [1:0] W_IDLE = 2'd0;
    localparam [1:0] W_AW   = 2'd1;
    localparam [1:0] W_B    = 2'd3;
    localparam [WSW-1:0] W_SEL_ABS = NP;
    localparam [WSW-1:0] W_SEL_IO  = NP + 1;

    function automatic [LINE_W-1:0] line_of(input [AW-1:0] a);
        line_of = a[AW-1:OFF_W];
    endfunction

    function automatic [3:0] map_snoop(input [2:0] t);
        case (t)
            3'b000, REQ_RNSD: map_snoop = ACSNOOP_READ_SHARED;
            REQ_RU:           map_snoop = ACSNOOP_READ_UNIQUE;
            REQ_CU:           map_snoop = ACSNOOP_CLEAN_INVALID;
            CLS_IO_RD:        map_snoop = ACSNOOP_READ_ONCE;
            CLS_IO_WR:        map_snoop = ACSNOOP_CLEAN_INVALID;
            default:          map_snoop = ACSNOOP_MAKE_INVALID;
        endcase
    endfunction

    function automatic is_wr_pulse(input [2:0] t);
        is_wr_pulse = (t == REQ_WB) || (t == REQ_WC);
    endfunction

    function automatic is_nodata(input [2:0] t);
        is_nodata = (t == REQ_CU) || (t == 3'b011);
    endfunction

    // ------------------------------------------------------------------
    // DUT outputs (harness order: port d at [d*W +: W])
    // ------------------------------------------------------------------
    logic [NP-1:0]     c_arready, c_rlast, c_rvalid, c_awready, c_wready, c_bvalid;
    logic [NP*3-1:0]   c_rid, c_bid;
    logic [NP*32-1:0]  c_rdata;
    logic [NP*2-1:0]   c_rresp, c_bresp;
    logic [NP-1:0]     c_ruser, c_buser;
    logic [NP*AW-1:0]  s_acaddr;
    logic [NP*4-1:0]   s_acsnoop;
    logic [NP*3-1:0]   s_acprot;
    logic [NP-1:0]     s_acvalid, s_crready, s_cdready;
    logic        io_arready, io_rvalid, io_rlast, io_ruser, io_awready, io_wready, io_bvalid, io_buser;
    logic [2:0]  io_rid, io_bid;
    logic [31:0] io_rdata;
    logic [1:0]  io_rresp, io_bresp;
    logic [2:0]  mem_arid;
    logic [AW-1:0] mem_araddr;
    logic [7:0]  mem_arlen;
    logic [2:0]  mem_arsize;
    logic [1:0]  mem_arburst;
    logic        mem_arlock;
    logic [3:0]  mem_arcache;
    logic [2:0]  mem_arprot;
    logic [3:0]  mem_arqos;
    logic [3:0]  mem_arregion;
    logic        mem_aruser;
    logic        mem_arvalid;
    logic        mem_rready;
    logic [2:0]  mem_awid;
    logic [AW-1:0] mem_awaddr;
    logic [7:0]  mem_awlen;
    logic [2:0]  mem_awsize;
    logic [1:0]  mem_awburst;
    logic        mem_awlock;
    logic [3:0]  mem_awcache;
    logic [2:0]  mem_awprot;
    logic [3:0]  mem_awqos;
    logic [3:0]  mem_awregion;
    logic        mem_awuser;
    logic        mem_awvalid;
    logic [31:0] mem_wdata;
    logic [3:0]  mem_wstrb;
    logic        mem_wlast;
    logic        mem_wuser;
    logic        mem_wvalid;
    logic        mem_bready;
    logic        dbg_busy;
    logic [3:0]  dbg_slot_vld;
    logic [NP-1:0] dbg_pend_vld;
    logic        dbg_abs_pend;
    logic        dbg_grant;
    logic [RQW-1:0] dbg_grant_dir;
    logic [AW-1:0] dbg_grant_addr;
    logic [1:0]  dbg_grant_slot;

    // exposed internals (the .sby `expose`)
    logic [3:0]  obs_vld, obs_nodata, obs_ar_taken, obs_ac_all;
    logic [3:0]  obs_gathered, obs_dt, obs_pd, obs_mem_issued, obs_mem_done;
    logic [3:0]  obs_rpl_done, obs_abs_issued, obs_abs_done, obs_rack;
    logic [3:0]  obs_iow, obs_iow_done;
    logic [SLOTS*RQW-1:0] obs_dir_f;
    logic [SLOTS*PCW-1:0] obs_ac_left_f, obs_cr_left_f;
    logic        obs_mar_vld;
    logic [1:0]  obs_mar_slot;
    logic [NRQ-1:0] obs_arw_vld, obs_rpl_vld;
    logic [NP-1:0]  obs_pend_ovf;
    logic [1:0]  obs_wstate, obs_w_slot;
    logic [WSW-1:0] obs_w_sel;
    logic [NRQ-1:0] obs_cand_locked, obs_mem_pres, obs_rpl_pres;
    logic [NP-1:0]  obs_wb_blocked;
    logic        obs_wb_blocked_io, obs_io_line_wb, obs_io_w_slot, obs_io_w_pass;
    logic        obs_mr_drop;
    logic        obs_ior_busy, obs_iow_busy, obs_iow_slot_vld;
    logic [1:0]  obs_ior_slot, obs_iow_slot;
    logic [AW-1:0] obs_io_araddr;
    logic [7:0]  obs_io_arlen;
    logic [SLOTS*LINE_W-1:0] obs_line_f;
    logic [SLOTS*3-1:0]      obs_type_f;
    logic [SLOTS*IW-1:0]     obs_arid_f;
    logic [NRQ*2-1:0]        obs_arw_slot_f, obs_rpl_slot_f;
    logic [NP*2-1:0]         obs_ac_slot_f, obs_sni_head_f;
    logic [NP*3-1:0]         obs_pend_cnt_f;
    logic [NRQ*AW-1:0]       obs_cand_addr_f;
    logic [NP*2-1:0]         obs_sni_cnt_f;
    logic [NP*3-1:0]         obs_snq_cnt_f;           // per peer: slots queued for an AC

    // ------------------------------------------------------------------
    // sv2v packing: an unpacked-array port has element 0 at the TOP of the
    // vector.  x_v is the DUT-side vector of family x.
    // ------------------------------------------------------------------
    wire [NP*3-1:0]  c_arid_v, c_arsize_v, c_arprot_v, c_awid_v, c_awsize_v, c_awprot_v;
    wire [NP*3-1:0]  c_coh_req_type_v, c_coh_done_id_v;
    wire [NP*AW-1:0] c_araddr_v, c_awaddr_v, c_coh_req_addr_v;
    wire [NP*8-1:0]  c_arlen_v, c_awlen_v;
    wire [NP*2-1:0]  c_arburst_v, c_awburst_v;
    wire [NP*4-1:0]  c_arcache_v, c_arqos_v, c_arregion_v, c_awcache_v, c_awqos_v, c_awregion_v, c_wstrb_v;
    wire [NP-1:0]    c_aruser_v, c_awuser_v, c_wuser_v;
    wire [NP*32-1:0] c_wdata_v, s_cddata_v;
    wire [NP*5-1:0]  s_crresp_v;
    wire [NP*3-1:0]  c_rid_v, c_bid_v, s_acprot_v;
    wire [NP*32-1:0] c_rdata_v;
    wire [NP*2-1:0]  c_rresp_v, c_bresp_v;
    wire [NP-1:0]    c_ruser_v, c_buser_v;
    wire [NP*AW-1:0] s_acaddr_v;
    wire [NP*4-1:0]  s_acsnoop_v;
    generate
        for (genvar g = 0; g < NP; g = g + 1) begin : g_pack
            localparam integer R = NP - 1 - g;   // the element's position in the DUT vector
            assign c_arid_v[R*3 +: 3]          = c_arid[g*3 +: 3];
            assign c_araddr_v[R*AW +: AW]      = c_araddr[g*AW +: AW];
            assign c_arlen_v[R*8 +: 8]         = c_arlen[g*8 +: 8];
            assign c_arsize_v[R*3 +: 3]        = c_arsize[g*3 +: 3];
            assign c_arburst_v[R*2 +: 2]       = c_arburst[g*2 +: 2];
            assign c_arcache_v[R*4 +: 4]       = c_arcache[g*4 +: 4];
            assign c_arprot_v[R*3 +: 3]        = c_arprot[g*3 +: 3];
            assign c_arqos_v[R*4 +: 4]         = c_arqos[g*4 +: 4];
            assign c_arregion_v[R*4 +: 4]      = c_arregion[g*4 +: 4];
            assign c_aruser_v[R]               = c_aruser[g];
            assign c_awid_v[R*3 +: 3]          = c_awid[g*3 +: 3];
            assign c_awaddr_v[R*AW +: AW]      = c_awaddr[g*AW +: AW];
            assign c_awlen_v[R*8 +: 8]         = c_awlen[g*8 +: 8];
            assign c_awsize_v[R*3 +: 3]        = c_awsize[g*3 +: 3];
            assign c_awburst_v[R*2 +: 2]       = c_awburst[g*2 +: 2];
            assign c_awcache_v[R*4 +: 4]       = c_awcache[g*4 +: 4];
            assign c_awprot_v[R*3 +: 3]        = c_awprot[g*3 +: 3];
            assign c_awqos_v[R*4 +: 4]         = c_awqos[g*4 +: 4];
            assign c_awregion_v[R*4 +: 4]      = c_awregion[g*4 +: 4];
            assign c_awuser_v[R]               = c_awuser[g];
            assign c_wdata_v[R*32 +: 32]       = c_wdata[g*32 +: 32];
            assign c_wstrb_v[R*4 +: 4]         = c_wstrb[g*4 +: 4];
            assign c_wuser_v[R]                = c_wuser[g];
            assign s_crresp_v[R*5 +: 5]        = s_crresp[g*5 +: 5];
            assign s_cddata_v[R*32 +: 32]      = s_cddata[g*32 +: 32];
            assign c_coh_req_addr_v[R*AW +: AW] = c_coh_req_addr[g*AW +: AW];
            assign c_coh_req_type_v[R*3 +: 3]  = c_coh_req_type[g*3 +: 3];
            assign c_coh_done_id_v[R*3 +: 3]   = c_coh_done_id[g*3 +: 3];
            // outputs back into harness order
            assign c_rid[g*3 +: 3]             = c_rid_v[R*3 +: 3];
            assign c_rdata[g*32 +: 32]         = c_rdata_v[R*32 +: 32];
            assign c_rresp[g*2 +: 2]           = c_rresp_v[R*2 +: 2];
            assign c_ruser[g]                  = c_ruser_v[R];
            assign c_bid[g*3 +: 3]             = c_bid_v[R*3 +: 3];
            assign c_bresp[g*2 +: 2]           = c_bresp_v[R*2 +: 2];
            assign c_buser[g]                  = c_buser_v[R];
            assign s_acaddr[g*AW +: AW]        = s_acaddr_v[R*AW +: AW];
            assign s_acsnoop[g*4 +: 4]         = s_acsnoop_v[R*4 +: 4];
            assign s_acprot[g*3 +: 3]          = s_acprot_v[R*3 +: 3];
        end
    endgenerate

    onyx_ccu dut (
        .clk(clk), .rst_n(rst_n),
        .c_arid(c_arid_v), .c_araddr(c_araddr_v), .c_arlen(c_arlen_v), .c_arsize(c_arsize_v),
        .c_arburst(c_arburst_v), .c_arlock(c_arlock), .c_arcache(c_arcache_v), .c_arprot(c_arprot_v),
        .c_arqos(c_arqos_v), .c_arregion(c_arregion_v), .c_aruser(c_aruser_v),
        .c_arvalid(c_arvalid), .c_arready(c_arready),
        .c_rid(c_rid_v), .c_rdata(c_rdata_v), .c_rresp(c_rresp_v), .c_rlast(c_rlast), .c_ruser(c_ruser_v),
        .c_rvalid(c_rvalid), .c_rready(c_rready),
        .c_awid(c_awid_v), .c_awaddr(c_awaddr_v), .c_awlen(c_awlen_v), .c_awsize(c_awsize_v),
        .c_awburst(c_awburst_v), .c_awlock(c_awlock), .c_awcache(c_awcache_v), .c_awprot(c_awprot_v),
        .c_awqos(c_awqos_v), .c_awregion(c_awregion_v), .c_awuser(c_awuser_v),
        .c_awvalid(c_awvalid), .c_awready(c_awready),
        .c_wdata(c_wdata_v), .c_wstrb(c_wstrb_v), .c_wlast(c_wlast), .c_wuser(c_wuser_v),
        .c_wvalid(c_wvalid), .c_wready(c_wready),
        .c_bid(c_bid_v), .c_bresp(c_bresp_v), .c_buser(c_buser_v), .c_bvalid(c_bvalid), .c_bready(c_bready),
        .s_acaddr(s_acaddr_v), .s_acsnoop(s_acsnoop_v), .s_acprot(s_acprot_v),
        .s_acvalid(s_acvalid), .s_acready(s_acready),
        .s_crresp(s_crresp_v), .s_crvalid(s_crvalid), .s_crready(s_crready),
        .s_cddata(s_cddata_v), .s_cdlast(s_cdlast), .s_cdvalid(s_cdvalid), .s_cdready(s_cdready),
        .c_coh_req_valid(c_coh_req_valid), .c_coh_req_addr(c_coh_req_addr_v), .c_coh_req_type(c_coh_req_type_v),
        .c_coh_done_valid(c_coh_done_valid), .c_coh_done_id(c_coh_done_id_v),
        .io_arid(io_arid), .io_araddr(io_araddr), .io_arlen(io_arlen), .io_arsize(io_arsize),
        .io_arburst(io_arburst), .io_arlock(io_arlock), .io_arcache(io_arcache), .io_arprot(io_arprot),
        .io_arqos(io_arqos), .io_arregion(io_arregion), .io_aruser(io_aruser), .io_arsnoop(io_arsnoop),
        .io_ardomain(io_ardomain), .io_arbar(io_arbar), .io_arvalid(io_arvalid), .io_arready(io_arready),
        .io_rid(io_rid), .io_rdata(io_rdata), .io_rresp(io_rresp), .io_rlast(io_rlast), .io_ruser(io_ruser),
        .io_rvalid(io_rvalid), .io_rready(io_rready),
        .io_awid(io_awid), .io_awaddr(io_awaddr), .io_awlen(io_awlen), .io_awsize(io_awsize),
        .io_awburst(io_awburst), .io_awlock(io_awlock), .io_awcache(io_awcache), .io_awprot(io_awprot),
        .io_awqos(io_awqos), .io_awregion(io_awregion), .io_awuser(io_awuser), .io_awsnoop(io_awsnoop),
        .io_awdomain(io_awdomain), .io_awbar(io_awbar), .io_awvalid(io_awvalid), .io_awready(io_awready),
        .io_wdata(io_wdata), .io_wstrb(io_wstrb), .io_wlast(io_wlast), .io_wuser(io_wuser),
        .io_wvalid(io_wvalid), .io_wready(io_wready), .io_bid(io_bid), .io_bresp(io_bresp),
        .io_buser(io_buser), .io_bvalid(io_bvalid), .io_bready(io_bready),
        .mem_arid(mem_arid), .mem_araddr(mem_araddr), .mem_arlen(mem_arlen), .mem_arsize(mem_arsize),
        .mem_arburst(mem_arburst), .mem_arlock(mem_arlock), .mem_arcache(mem_arcache), .mem_arprot(mem_arprot),
        .mem_arqos(mem_arqos), .mem_arregion(mem_arregion), .mem_aruser(mem_aruser), .mem_arvalid(mem_arvalid),
        .mem_arready(mem_arready), .mem_rid(mem_rid), .mem_rdata(mem_rdata), .mem_rresp(mem_rresp),
        .mem_rlast(mem_rlast), .mem_ruser(mem_ruser), .mem_rvalid(mem_rvalid), .mem_rready(mem_rready),
        .mem_awid(mem_awid), .mem_awaddr(mem_awaddr), .mem_awlen(mem_awlen), .mem_awsize(mem_awsize),
        .mem_awburst(mem_awburst), .mem_awlock(mem_awlock), .mem_awcache(mem_awcache), .mem_awprot(mem_awprot),
        .mem_awqos(mem_awqos), .mem_awregion(mem_awregion), .mem_awuser(mem_awuser), .mem_awvalid(mem_awvalid),
        .mem_awready(mem_awready), .mem_wdata(mem_wdata), .mem_wstrb(mem_wstrb), .mem_wlast(mem_wlast),
        .mem_wuser(mem_wuser), .mem_wvalid(mem_wvalid), .mem_wready(mem_wready), .mem_bid(mem_bid),
        .mem_bresp(mem_bresp), .mem_buser(mem_buser), .mem_bvalid(mem_bvalid), .mem_bready(mem_bready),
        .dbg_busy(dbg_busy), .dbg_slot_vld(dbg_slot_vld), .dbg_pend_vld(dbg_pend_vld),
        .dbg_abs_pend(dbg_abs_pend), .dbg_grant(dbg_grant), .dbg_grant_dir(dbg_grant_dir),
        .dbg_grant_addr(dbg_grant_addr), .dbg_grant_slot(dbg_grant_slot),
        // exposed
        .r_vld(obs_vld), .r_nodata(obs_nodata), .r_ar_taken(obs_ar_taken),
        .w_ac_all(obs_ac_all), .w_gathered(obs_gathered), .r_dt(obs_dt), .r_pd(obs_pd),
        .r_mem_issued(obs_mem_issued), .r_mem_done(obs_mem_done), .r_rpl_done(obs_rpl_done),
        .r_abs_issued(obs_abs_issued), .r_abs_done(obs_abs_done), .r_rack(obs_rack), .r_arw_vld(obs_arw_vld),
        .r_iow(obs_iow), .r_iow_done(obs_iow_done),
        .r_mar_vld(obs_mar_vld), .r_mar_slot(obs_mar_slot),
        .r_pend_ovf(obs_pend_ovf), .r_rpl_vld(obs_rpl_vld), .r_wstate(obs_wstate),
        .r_w_sel(obs_w_sel), .r_w_slot(obs_w_slot), .w_cand_locked(obs_cand_locked),
        .w_mem_pres(obs_mem_pres), .w_rpl_pres(obs_rpl_pres), .w_mr_drop(obs_mr_drop),
        .w_wb_blocked(obs_wb_blocked), .w_wb_blocked_io(obs_wb_blocked_io), .w_io_line_wb(obs_io_line_wb),
        .w_io_w_slot(obs_io_w_slot), .w_io_w_pass(obs_io_w_pass),
        .r_ior_busy(obs_ior_busy), .r_iow_busy(obs_iow_busy), .r_iow_slot_vld(obs_iow_slot_vld),
        .r_ior_slot(obs_ior_slot), .r_iow_slot(obs_iow_slot),
        .r_io_araddr(obs_io_araddr), .r_io_arlen(obs_io_arlen),
        // per slot (SLOTS = 4 at every N)
        .\r_dir[0] (obs_dir_f[0*RQW +: RQW]), .\r_dir[1] (obs_dir_f[1*RQW +: RQW]),
        .\r_dir[2] (obs_dir_f[2*RQW +: RQW]), .\r_dir[3] (obs_dir_f[3*RQW +: RQW]),
        .\r_ac_left[0] (obs_ac_left_f[0*PCW +: PCW]), .\r_ac_left[1] (obs_ac_left_f[1*PCW +: PCW]),
        .\r_ac_left[2] (obs_ac_left_f[2*PCW +: PCW]), .\r_ac_left[3] (obs_ac_left_f[3*PCW +: PCW]),
        .\r_cr_left[0] (obs_cr_left_f[0*PCW +: PCW]), .\r_cr_left[1] (obs_cr_left_f[1*PCW +: PCW]),
        .\r_cr_left[2] (obs_cr_left_f[2*PCW +: PCW]), .\r_cr_left[3] (obs_cr_left_f[3*PCW +: PCW]),
        .\r_line[0] (obs_line_f[0*LINE_W +: LINE_W]), .\r_line[1] (obs_line_f[1*LINE_W +: LINE_W]),
        .\r_line[2] (obs_line_f[2*LINE_W +: LINE_W]), .\r_line[3] (obs_line_f[3*LINE_W +: LINE_W]),
        .\r_type[0] (obs_type_f[0*3 +: 3]), .\r_type[1] (obs_type_f[1*3 +: 3]),
        .\r_type[2] (obs_type_f[2*3 +: 3]), .\r_type[3] (obs_type_f[3*3 +: 3]),
        .\r_arid[0] (obs_arid_f[0*IW +: IW]), .\r_arid[1] (obs_arid_f[1*IW +: IW]),
        .\r_arid[2] (obs_arid_f[2*IW +: IW]), .\r_arid[3] (obs_arid_f[3*IW +: IW]),
        // per requester (N+1) and per port (N): elements 0..3 / 0..2 at N=3, 0..4 / 0..3 at N=4
        .\r_arw_slot[0] (obs_arw_slot_f[0 +: 2]), .\r_arw_slot[1] (obs_arw_slot_f[2 +: 2]),
        .\r_arw_slot[2] (obs_arw_slot_f[4 +: 2]), .\r_arw_slot[3] (obs_arw_slot_f[6 +: 2]),
        .\r_rpl_slot[0] (obs_rpl_slot_f[0 +: 2]), .\r_rpl_slot[1] (obs_rpl_slot_f[2 +: 2]),
        .\r_rpl_slot[2] (obs_rpl_slot_f[4 +: 2]), .\r_rpl_slot[3] (obs_rpl_slot_f[6 +: 2]),
        .\w_cand_addr[0] (obs_cand_addr_f[0*AW +: AW]), .\w_cand_addr[1] (obs_cand_addr_f[1*AW +: AW]),
        .\w_cand_addr[2] (obs_cand_addr_f[2*AW +: AW]), .\w_cand_addr[3] (obs_cand_addr_f[3*AW +: AW]),
        .\w_ac_slot[0] (obs_ac_slot_f[0 +: 2]), .\w_ac_slot[1] (obs_ac_slot_f[2 +: 2]),
        .\w_ac_slot[2] (obs_ac_slot_f[4 +: 2]),
        .\w_sni_head[0] (obs_sni_head_f[0 +: 2]), .\w_sni_head[1] (obs_sni_head_f[2 +: 2]),
        .\w_sni_head[2] (obs_sni_head_f[4 +: 2]),
        .\r_pend_cnt[0] (obs_pend_cnt_f[0 +: 3]), .\r_pend_cnt[1] (obs_pend_cnt_f[3 +: 3]),
        .\r_pend_cnt[2] (obs_pend_cnt_f[6 +: 3]),
        .\r_sni_cnt[0] (obs_sni_cnt_f[0 +: 2]), .\r_sni_cnt[1] (obs_sni_cnt_f[2 +: 2]),
        .\r_sni_cnt[2] (obs_sni_cnt_f[4 +: 2]),
        .\r_snq_cnt[0] (obs_snq_cnt_f[0 +: 3]), .\r_snq_cnt[1] (obs_snq_cnt_f[3 +: 3]),
        .\r_snq_cnt[2] (obs_snq_cnt_f[6 +: 3])
`ifdef NP4
        ,
        .\r_arw_slot[4] (obs_arw_slot_f[8 +: 2]), .\r_rpl_slot[4] (obs_rpl_slot_f[8 +: 2]),
        .\w_cand_addr[4] (obs_cand_addr_f[4*AW +: AW]),
        .\w_ac_slot[3] (obs_ac_slot_f[6 +: 2]), .\w_sni_head[3] (obs_sni_head_f[6 +: 2]),
        .\r_pend_cnt[3] (obs_pend_cnt_f[9 +: 3]), .\r_sni_cnt[3] (obs_sni_cnt_f[6 +: 2]),
        .\r_snq_cnt[3] (obs_snq_cnt_f[9 +: 3])
`endif
    );

    // ------------------------------------------------------------------
    // Handshakes and field accessors
    // ------------------------------------------------------------------
    wire [NP-1:0] c_ar_hs = c_arvalid & c_arready;
    wire [NP-1:0] c_r_hs  = c_rvalid & c_rready;
    wire [NP-1:0] ac_hs   = s_acvalid & s_acready;
    wire [NP-1:0] cr_hs   = s_crvalid & s_crready;
    wire [NP-1:0] cd_hs   = s_cdvalid & s_cdready;
    wire [NP-1:0] req_vld = c_coh_req_valid;
    wire [NP-1:0] done_vld = c_coh_done_valid;
    wire [NP-1:0] cr_dt, cr_pd;
    generate
        for (genvar g = 0; g < NP; g = g + 1) begin : g_cr
            assign cr_dt[g] = s_crresp[g*5 + CR_DT];
            assign cr_pd[g] = s_crresp[g*5 + CR_PD];
        end
    endgenerate

    wire        mar_hs = mem_arvalid & mem_arready;
    wire        mr_hs  = mem_rvalid & mem_rready;
    wire        maw_hs = mem_awvalid & mem_awready;
    wire        mw_hs  = mem_wvalid & mem_wready;
    wire        mb_hs  = mem_bvalid & mem_bready;
    wire [1:0]  mr_slot = mem_rid[1:0];
    wire        w_abs   = (obs_w_sel == W_SEL_ABS);
    wire        w_io    = (obs_w_sel == W_SEL_IO);

    wire        io_ar_hs = io_arvalid & io_arready;
    wire        io_r_hs  = io_rvalid & io_rready;
    wire        io_aw_hs = io_awvalid & io_awready;
    wire        io_w_hs  = io_wvalid & io_wready;
    wire        io_b_hs  = io_bvalid & io_bready;
    wire        io_ar_sh = io_ardomain[0] ^ io_ardomain[1];
    wire        io_aw_sh = io_awdomain[0] ^ io_awdomain[1];

    // the N+1 requesters' R channels (bit d: the caches, then the IO at N)
    wire [NRQ-1:0]    rq_rvalid = {io_rvalid, c_rvalid};
    wire [NRQ-1:0]    rq_rready = {io_rready, c_rready};
    wire [NRQ-1:0]    rq_r_hs   = rq_rvalid & rq_rready;
    wire [NRQ*3-1:0]  rq_rid_f  = {io_rid, c_rid};
    wire [NRQ-1:0]    rq_rlast  = {io_rlast, c_rlast};
    wire [NRQ*32-1:0] rq_rdata_f = {io_rdata, c_rdata};
    wire [NRQ*2-1:0]  rq_rresp_f = {io_rresp, c_rresp};

    function automatic [LINE_W-1:0] sl_line(input [SLOTS*LINE_W-1:0] f, input [1:0] s);
        sl_line = f[s*LINE_W +: LINE_W];
    endfunction
    function automatic [RQW-1:0] sl_dir(input [1:0] s);
        sl_dir = obs_dir_f[s*RQW +: RQW];
    endfunction
    function automatic [PCW-1:0] sl_cnt(input [SLOTS*PCW-1:0] f, input [1:0] s);
        sl_cnt = f[s*PCW +: PCW];
    endfunction
    function automatic [1:0] rq_slot(input [NRQ*2-1:0] f, input [2:0] d);
        rq_slot = f[d*2 +: 2];
    endfunction
    function automatic [2:0] rq3(input [NRQ*3-1:0] f, input [2:0] d);
        rq3 = f[d*3 +: 3];
    endfunction
    function automatic [2:0] sl_type(input [SLOTS*3-1:0] f, input [1:0] s);
        sl_type = f[s*3 +: 3];
    endfunction
    function automatic [IW-1:0] sl_arid(input [SLOTS*IW-1:0] f, input [1:0] s);
        sl_arid = f[s*IW +: IW];
    endfunction
    function automatic [1:0] p2(input [NP*2-1:0] f, input [2:0] p);
        p2 = f[p*2 +: 2];
    endfunction
    function automatic [2:0] p3(input [NP*3-1:0] f, input [2:0] p);
        p3 = f[p*3 +: 3];
    endfunction
    function automatic [AW-1:0] pa(input [NP*AW-1:0] f, input [2:0] p);
        pa = f[p*AW +: AW];
    endfunction
    function automatic [7:0] p8(input [NP*8-1:0] f, input [2:0] p);
        p8 = f[p*8 +: 8];
    endfunction
    function automatic [3:0] p4(input [NP*4-1:0] f, input [2:0] p);
        p4 = f[p*4 +: 4];
    endfunction
    // the requester index, zero-extended to the three-bit absorption AWID
    function automatic [2:0] ext3(input [RQW-1:0] d);
        ext3 = d;
    endfunction
    // the retire port of a cache requester (0 for the IO / out of range)
    function automatic done_of(input [NP-1:0] v, input [RQW-1:0] d);
        integer i;
        done_of = 1'b0;
        for (i = 0; i < NP; i = i + 1)
            if (d == i) done_of = v[i];
    endfunction
    function automatic [2:0] done_id_of(input [NP*3-1:0] f, input [RQW-1:0] d);
        integer i;
        done_id_of = 3'd0;
        for (i = 0; i < NP; i = i + 1)
            if (d == i) done_id_of = f[i*3 +: 3];
    endfunction
    // a valid slot holds the line of address a (the WriteClean cover)
    function automatic wc_live_line(input [AW-1:0] a);
        integer i;
        wc_live_line = 1'b0;
        for (i = 0; i < SLOTS; i = i + 1)
            if (obs_vld[i] && (sl_line(obs_line_f, i) == line_of(a))) wc_live_line = 1'b1;
    endfunction

    // ------------------------------------------------------------------
    // House reset protocol; every environment VALID low under reset
    // ------------------------------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
        else                   assume (!rst_n);
    end
    always @(*) begin
        if (!rst_n) begin
            as_rst_quiet: assume ((c_arvalid == 0) && (c_awvalid == 0) && (c_wvalid == 0)
                                  && (s_crvalid == 0) && (s_cdvalid == 0) && (c_coh_req_valid == 0)
                                  && (c_coh_done_valid == 0) && !mem_rvalid && !mem_bvalid
                                  && !io_arvalid && !io_awvalid && !io_wvalid);
        end
    end

    // ------------------------------------------------------------------
    // Cache model (A-req / A-ar / A-done), per cache d
    // ------------------------------------------------------------------
    reg [2:0]           q_cnt   [0:NP-1];
    reg [4*LINE_W-1:0]  q_line  [0:NP-1];
    reg [3:0]           q_nd    [0:NP-1];
    reg [7:0]           f_infl  [0:NP-1];
    reg [7:0]           f_last  [0:NP-1];
    reg [7:0]           f_nd    [0:NP-1];
    reg [15:0]          f_beats [0:NP-1];

    integer d, p, q, s, k, e;
    always @(posedge clk) begin
        if (!rst_n) begin
            for (d = 0; d < NP; d = d + 1) begin
                q_cnt[d]   <= 3'd0;
                q_line[d]  <= '0;
                q_nd[d]    <= 4'd0;
                f_infl[d]  <= 8'd0;
                f_last[d]  <= 8'd0;
                f_nd[d]    <= 8'd0;
                f_beats[d] <= 16'd0;
            end
        end else begin
            for (d = 0; d < NP; d = d + 1) begin
                if (c_ar_hs[d]) begin
                    q_line[d] <= {{LINE_W{1'b0}}, q_line[d][4*LINE_W-1:LINE_W]};
                    q_nd[d]   <= {1'b0, q_nd[d][3:1]};
                end
                if (req_vld[d] && !is_wr_pulse(p3(c_coh_req_type, d))) begin
                    for (k = 0; k < 4; k = k + 1) begin
                        if (k == (q_cnt[d] - (c_ar_hs[d] ? 1 : 0))) begin
                            q_line[d][k*LINE_W +: LINE_W] <= line_of(pa(c_coh_req_addr, d));
                            q_nd[d][k] <= is_nodata(p3(c_coh_req_type, d));
                        end
                    end
                    q_cnt[d] <= q_cnt[d] + 3'd1 - (c_ar_hs[d] ? 3'd1 : 3'd0);
                end else if (c_ar_hs[d]) begin
                    q_cnt[d] <= q_cnt[d] - 3'd1;
                end
                if (c_ar_hs[d]) begin
                    f_infl[d][p3(c_arid, d)]  <= 1'b1;
                    f_nd[d][p3(c_arid, d)]    <= (p8(c_arlen, d) == 8'd0);
                    f_beats[d][p3(c_arid, d)*2 +: 2] <= 2'd0;
                end
                if (c_r_hs[d]) begin
                    f_beats[d][p3(c_rid, d)*2 +: 2] <= f_beats[d][p3(c_rid, d)*2 +: 2] + 2'd1;
                    if (c_rlast[d]) f_last[d][p3(c_rid, d)] <= 1'b1;
                end
                if (done_vld[d]) begin
                    f_infl[d][p3(c_coh_done_id, d)] <= 1'b0;
                    f_last[d][p3(c_coh_done_id, d)] <= 1'b0;
                end
            end
        end
    end

    reg [NP-1:0]    ar_v_d, ar_r_d, aw_v_d, aw_r_d, w_v_d, w_r_d, w_last_d;
    reg [NP*3-1:0]  ar_id_d, aw_id_d;
    reg [NP*AW-1:0] ar_addr_d, aw_addr_d;
    reg [NP*8-1:0]  ar_len_d, aw_len_d;
    always @(posedge clk) begin
        ar_v_d <= c_arvalid;  ar_r_d <= c_arready;  ar_id_d <= c_arid;
        ar_addr_d <= c_araddr;  ar_len_d <= c_arlen;
        aw_v_d <= c_awvalid;  aw_r_d <= c_awready;  aw_id_d <= c_awid;
        aw_addr_d <= c_awaddr;  aw_len_d <= c_awlen;
        w_v_d <= c_wvalid;  w_r_d <= c_wready;  w_last_d <= c_wlast;
    end

    always @(posedge clk) begin
        if (rst_n && (f_past_valid >= 2)) begin
            for (d = 0; d < NP; d = d + 1) begin
                assume /* as_req_type */ (!req_vld[d]
                    || (p3(c_coh_req_type, d) == REQ_RNSD) || (p3(c_coh_req_type, d) == REQ_RU)
                    || (p3(c_coh_req_type, d) == REQ_CU)   || (p3(c_coh_req_type, d) == REQ_WB)
                    || (p3(c_coh_req_type, d) == REQ_WC));
                assume /* as_req_depth */ (!(req_vld[d] && !is_wr_pulse(p3(c_coh_req_type, d)))
                    || (q_cnt[d] < 3'd4) || c_ar_hs[d]);
                assume /* as_ar_head */ (!c_arvalid[d]
                    || ((q_cnt[d] != 3'd0)
                        && (line_of(pa(c_araddr, d)) == q_line[d][0 +: LINE_W])
                        && (p8(c_arlen, d) == (q_nd[d][0] ? 8'd0 : 8'd3))));
                assume /* as_ar_fresh */ (!c_arvalid[d] || !f_infl[d][p3(c_arid, d)]);
                assume /* as_ar_stable */ (!(ar_v_d[d] && !ar_r_d[d])
                    || (c_arvalid[d] && (p3(c_arid, d) == p3(ar_id_d, d))
                        && (pa(c_araddr, d) == pa(ar_addr_d, d))
                        && (p8(c_arlen, d) == p8(ar_len_d, d))));
                assume /* as_done */ (!done_vld[d]
                    || (f_infl[d][p3(c_coh_done_id, d)] && f_last[d][p3(c_coh_done_id, d)]));
                assume /* as_aw_stable */ (!(aw_v_d[d] && !aw_r_d[d])
                    || (c_awvalid[d] && (p3(c_awid, d) == p3(aw_id_d, d))
                        && (pa(c_awaddr, d) == pa(aw_addr_d, d))
                        && (p8(c_awlen, d) == p8(aw_len_d, d))));
                assume /* as_w_stable */ (!(w_v_d[d] && !w_r_d[d])
                    || (c_wvalid[d] && (c_wlast[d] == w_last_d[d])));
            end
        end
    end

    // ------------------------------------------------------------------
    // Snoop responder model (A-snoop), per peer p
    // ------------------------------------------------------------------
    reg [1:0] sn_out  [0:NP-1];
    reg [7:0] sn_type [0:NP-1];   // 2 entries x ACSNOOP, head at [3:0]
    reg [2:0] cd_cnt  [0:NP-1];
    always @(posedge clk) begin
        if (!rst_n) begin
            for (p = 0; p < NP; p = p + 1) begin
                sn_out[p]  <= 2'd0;
                sn_type[p] <= 8'd0;
                cd_cnt[p]  <= 3'd0;
            end
        end else begin
            for (p = 0; p < NP; p = p + 1) begin
                if (cr_hs[p]) sn_type[p] <= {4'd0, sn_type[p][7:4]};
                if (ac_hs[p]) begin
                    if ((sn_out[p] - (cr_hs[p] ? 2'd1 : 2'd0)) == 2'd0)
                        sn_type[p][3:0] <= p4(s_acsnoop, p);
                    else
                        sn_type[p][7:4] <= p4(s_acsnoop, p);
                end
                sn_out[p] <= sn_out[p] + (ac_hs[p] ? 2'd1 : 2'd0) - (cr_hs[p] ? 2'd1 : 2'd0);
                if (cr_hs[p])      cd_cnt[p] <= 3'd0;
                else if (cd_hs[p]) cd_cnt[p] <= cd_cnt[p] + 3'd1;
            end
        end
    end

    // peer p is supplying (a CD beat or a DT verdict presented, or mid-stream)
    reg [NP-1:0] f_supplying;
    always @(*) begin
        for (p = 0; p < NP; p = p + 1)
            f_supplying[p] = (sn_out[p] != 2'd0)
                             && (s_cdvalid[p] || (s_crvalid[p] && cr_dt[p]) || (cd_cnt[p] != 3'd0));
    end

    always @(posedge clk) begin
        if (rst_n && (f_past_valid >= 2)) begin
            for (p = 0; p < NP; p = p + 1) begin
                assume /* as_cr_outstanding */ (!s_crvalid[p] || (sn_out[p] != 2'd0));
                assume /* as_cd_outstanding */ (!s_cdvalid[p] || ((sn_out[p] != 2'd0) && (cd_cnt[p] < 3'd4)));
                assume /* as_cd_last */ (!s_cdvalid[p] || (s_cdlast[p] == (cd_cnt[p] == 3'd3)));
                assume /* as_cr_cd_pairing */ (!s_crvalid[p]
                    || (cr_dt[p] ? ((cd_cnt[p] == 3'd4) || ((cd_cnt[p] == 3'd3) && s_cdvalid[p]))
                                 : (cd_cnt[p] == 3'd0)));
                assume /* as_cr_pd_dt */ (!s_crvalid[p] || !cr_pd[p] || cr_dt[p]);
                assume /* as_cr_mi_nodt */ (!(s_crvalid[p] && (sn_type[p][3:0] == ACSNOOP_MAKE_INVALID))
                    || !cr_dt[p]);
                // one supplier per slot: no data for a slot already supplied,
                // and not while ANY other peer supplies the same slot
                assume /* as_one_supplier */ (!((s_cdvalid[p] || (s_crvalid[p] && cr_dt[p])) && (sn_out[p] != 2'd0)
                                                && obs_dt[p2(obs_sni_head_f, p)]));
                for (q = 0; q < NP; q = q + 1)
                    if (q != p)
                        assume /* as_one_supplier_now */ (!((s_cdvalid[p] || (s_crvalid[p] && cr_dt[p]))
                                                            && (sn_out[p] != 2'd0) && f_supplying[q]
                                                            && (p2(obs_sni_head_f, p) == p2(obs_sni_head_f, q))));
            end
        end
    end

    // ------------------------------------------------------------------
    // IO master model (A-io)
    // ------------------------------------------------------------------
    reg        f_io_rd;
    reg [2:0]  f_io_rid;
    reg [1:0]  f_io_rlen;
    reg [1:0]  f_io_rbeats;
    reg        f_io_wr;
    reg [1:0]  f_io_wlen;
    reg [1:0]  f_io_wbeats;
    reg        io_ar_v_d, io_ar_r_d, io_aw_v_d, io_aw_r_d, io_w_v_d, io_w_r_d, io_w_last_d;
    reg [2:0]  io_ar_id_d, io_aw_id_d;
    reg [AW-1:0] io_ar_addr_d, io_aw_addr_d;
    reg [7:0]  io_ar_len_d, io_aw_len_d;
    reg [1:0]  io_ar_dom_d, io_aw_dom_d;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_io_rd <= 1'b0;  f_io_rid <= 3'd0;  f_io_rlen <= 2'd0;  f_io_rbeats <= 2'd0;
            f_io_wr <= 1'b0;  f_io_wlen <= 2'd0;  f_io_wbeats <= 2'd0;
        end else begin
            if (io_ar_hs) begin
                f_io_rd <= 1'b1;  f_io_rid <= io_arid;  f_io_rlen <= io_arlen[1:0];  f_io_rbeats <= 2'd0;
            end
            if (io_r_hs) begin
                f_io_rbeats <= f_io_rbeats + 2'd1;
                if (io_rlast) f_io_rd <= 1'b0;
            end
            if (io_aw_hs) begin
                f_io_wr <= 1'b1;  f_io_wlen <= io_awlen[1:0];  f_io_wbeats <= 2'd0;
            end
            if (io_w_hs) begin
                f_io_wbeats <= f_io_wbeats + 2'd1;
                if (io_wlast) f_io_wr <= 1'b0;
            end
        end
        io_ar_v_d <= io_arvalid;  io_ar_r_d <= io_arready;  io_ar_id_d <= io_arid;
        io_ar_addr_d <= io_araddr;  io_ar_len_d <= io_arlen;  io_ar_dom_d <= io_ardomain;
        io_aw_v_d <= io_awvalid;  io_aw_r_d <= io_awready;  io_aw_id_d <= io_awid;
        io_aw_addr_d <= io_awaddr;  io_aw_len_d <= io_awlen;  io_aw_dom_d <= io_awdomain;
        io_w_v_d <= io_wvalid;  io_w_r_d <= io_wready;  io_w_last_d <= io_wlast;
    end

    always @(posedge clk) begin
        if (rst_n && (f_past_valid >= 2)) begin
            as_io_ar_shape: assume (!io_arvalid
                || ((io_arsize == 3'd2) && (io_arburst == 2'b01) && (io_arlen <= 8'd3)
                    && ({1'b0, io_araddr[OFF_W-1:2]} + io_arlen[2:0] <= 3'd3)
                    && (io_arsnoop == 4'h0)));
            as_io_aw_shape: assume (!io_awvalid
                || ((io_awsize == 3'd2) && (io_awburst == 2'b01) && (io_awlen <= 8'd3)
                    && ({1'b0, io_awaddr[OFF_W-1:2]} + io_awlen[2:0] <= 3'd3)
                    && (io_awsnoop <= 3'd1)));
            as_io_ar_stable: assume (!(io_ar_v_d && !io_ar_r_d)
                || (io_arvalid && (io_arid == io_ar_id_d) && (io_araddr == io_ar_addr_d)
                    && (io_arlen == io_ar_len_d) && (io_ardomain == io_ar_dom_d)));
            as_io_aw_stable: assume (!(io_aw_v_d && !io_aw_r_d)
                || (io_awvalid && (io_awid == io_aw_id_d) && (io_awaddr == io_aw_addr_d)
                    && (io_awlen == io_aw_len_d) && (io_awdomain == io_aw_dom_d)));
            as_io_w_stable: assume (!(io_w_v_d && !io_w_r_d) || (io_wvalid && (io_wlast == io_w_last_d)));
            as_io_w_after_aw: assume (!io_wvalid || f_io_wr);
            as_io_w_last: assume (!io_wvalid || (io_wlast == (f_io_wbeats == f_io_wlen)));
        end
    end

    // ------------------------------------------------------------------
    // Memory model (A-mem)
    // ------------------------------------------------------------------
    reg [3:0] mo;
    reg [7:0] mbeat;
    reg [7:0] mlen;
    reg       wo;
    reg       mr_v_d, mr_r_d, mr_last_d;
    reg [2:0] mr_id_d;
    reg [31:0] mr_data_d;
    reg [1:0] mr_resp_d;
    always @(posedge clk) begin
        if (!rst_n) begin
            mo <= 4'd0;  mbeat <= 8'd0;  mlen <= 8'd0;  wo <= 1'b0;
        end else begin
            if (mar_hs) begin
                mo[mem_arid[1:0]] <= 1'b1;
                mbeat[mem_arid[1:0]*2 +: 2] <= 2'd0;
                mlen[mem_arid[1:0]*2 +: 2] <= mem_arlen[1:0];
            end
            if (mr_hs) begin
                mbeat[mr_slot*2 +: 2] <= mbeat[mr_slot*2 +: 2] + 2'd1;
                if (mem_rlast) mo[mr_slot] <= 1'b0;
            end
            if (mw_hs && mem_wlast) wo <= 1'b1;
            if (mb_hs) wo <= 1'b0;
        end
        mr_v_d <= mem_rvalid;  mr_r_d <= mem_rready;  mr_id_d <= mem_rid;
        mr_data_d <= mem_rdata;  mr_resp_d <= mem_rresp;  mr_last_d <= mem_rlast;
    end

    always @(posedge clk) begin
        if (rst_n && (f_past_valid >= 2)) begin
            as_mr_outstanding: assume (!mem_rvalid || (!mem_rid[2] && mo[mr_slot]));
            as_mr_last: assume (!mem_rvalid || (mem_rlast == (mbeat[mr_slot*2 +: 2] == mlen[mr_slot*2 +: 2])));
            as_mr_stable: assume (!(mr_v_d && !mr_r_d)
                || (mem_rvalid && (mem_rid == mr_id_d) && (mem_rdata == mr_data_d)
                    && (mem_rresp == mr_resp_d) && (mem_rlast == mr_last_d)));
            as_mb_outstanding: assume (!mem_bvalid || wo);
        end
    end

    // ------------------------------------------------------------------
    // Per-peer gather shadow (new at N >= 3).  Driven only by what the
    // harness sees: the grant (requester, slot, the IO's kind from its own
    // AR / AW and the IO read-busy bit that P-IO2 proves), and the AC / CR
    // handshakes at the slot each names.  f_owed / f_acc / f_ans: SLOTS x NP
    // bits, slot s peer p at [s*NP + p].  h_sni: per peer the slots whose AC
    // it accepted and has not answered, oldest at [1:0].
    // ------------------------------------------------------------------
    reg [SLOTS*NP-1:0] f_owed, f_acc, f_ans;
    reg [SLOTS-1:0]    f_dt, f_pd;
    reg [3:0]          h_sni [0:NP-1];
    wire        g_io      = (dbg_grant_dir == IO);
    wire        g_io_rd   = g_io && io_arvalid && !obs_ior_busy;    // the DUT's w_io_rd_cand
    wire        g_snoops  = !g_io || !g_io_rd || io_ar_sh;          // the IO's non-shareable read snoops none
    always @(posedge clk) begin
        if (!rst_n) begin
            f_owed <= '0;  f_acc <= '0;  f_ans <= '0;  f_dt <= '0;  f_pd <= '0;
            for (p = 0; p < NP; p = p + 1) h_sni[p] <= 4'd0;
        end else begin
            if (dbg_grant) begin
                for (p = 0; p < NP; p = p + 1) begin
                    f_owed[dbg_grant_slot*NP + p] <= g_snoops && (dbg_grant_dir != p);
                    f_acc[dbg_grant_slot*NP + p]  <= 1'b0;
                    f_ans[dbg_grant_slot*NP + p]  <= 1'b0;
                end
                f_dt[dbg_grant_slot] <= 1'b0;
                f_pd[dbg_grant_slot] <= 1'b0;
            end
            for (p = 0; p < NP; p = p + 1) begin
                if (ac_hs[p]) f_acc[p2(obs_ac_slot_f, p)*NP + p] <= 1'b1;
                if (cr_hs[p]) begin
                    f_ans[h_sni[p][1:0]*NP + p] <= 1'b1;
                    if (cr_dt[p]) begin
                        f_dt[h_sni[p][1:0]] <= 1'b1;
                        f_pd[h_sni[p][1:0]] <= cr_pd[p];
                    end
                end
                // the in-order queue of accepted ACs: pop the CR, push the AC
                if (cr_hs[p]) h_sni[p] <= {2'd0, h_sni[p][3:2]};
                if (ac_hs[p]) begin
                    if ((sn_out[p] - (cr_hs[p] ? 2'd1 : 2'd0)) == 2'd0)
                        h_sni[p][1:0] <= p2(obs_ac_slot_f, p);
                    else
                        h_sni[p][3:2] <= p2(obs_ac_slot_f, p);
                end
            end
        end
    end
    function automatic [PCW-1:0] popc(input [NP-1:0] v);
        integer i;
        popc = '0;
        for (i = 0; i < NP; i = i + 1) popc = popc + v[i];
    endfunction
    function automatic [NP-1:0] sl_peers(input [SLOTS*NP-1:0] f, input [1:0] sl);
        sl_peers = f[sl*NP +: NP];
    endfunction

    // ------------------------------------------------------------------
    // Wrapper shadows for the assertions (the previous cycle's table, the
    // requester's delivered beats per slot, the DUT's valid/ready pairs)
    // ------------------------------------------------------------------
    reg [3:0]  vld_d, rack_d, gathered_d, pd_d, abs_done_d;
    reg [SLOTS*LINE_W-1:0] line_d;
    reg [1:0]  wstate_d;
    reg [WSW-1:0] w_sel_d;
    reg [NP-1:0]  done_vld_d;
    reg [NP*3-1:0] done_id_d;
    reg        mar_v_d, mar_r_d;
    reg [2:0]  mar_id_d;
    reg [AW-1:0] mar_addr_d;
    reg [NRQ-1:0] r_v_d, r_r_d, r_last_d;
    reg [NRQ*3-1:0] r_id_d;
    reg [NRQ*32-1:0] r_data_d;
    reg [NRQ*2-1:0]  r_resp_d;
    reg        iow_slot_vld_d;
    reg [1:0]  iow_slot_d;
    reg        io_aw_sh_d;
    reg [AW-1:0] io_aw_addr_dd;
    reg [NP-1:0] ac_v_d, ac_r_d;
    reg [NP*AW-1:0] ac_addr_d;
    reg [NP*4-1:0] ac_snoop_d;
    reg [3:0]  h_delivered;
    reg  [NP-1:0] f_aw_old, f_aw_old_d;
    reg  [NP-1:0] f_wb_gather;
    always @(*) begin
        for (d = 0; d < NP; d = d + 1) begin
            f_wb_gather[d] = 1'b0;
            for (s = 0; s < SLOTS; s = s + 1)
                if (obs_vld[s] && !obs_gathered[s]
                    && (sl_line(obs_line_f, s) == line_of(pa(c_awaddr, d))))
                    f_wb_gather[d] = 1'b1;
        end
    end
    always @(posedge clk) begin
        if (!rst_n) f_aw_old <= '0;
        else        f_aw_old <= c_awvalid & ~c_awready & (f_aw_old | f_wb_gather);
        f_aw_old_d <= f_aw_old;
    end
    reg        f_wfly;
    reg [LINE_W-1:0] f_wfly_line;
    always @(posedge clk) begin
        if (!rst_n) begin
            f_wfly <= 1'b0;  f_wfly_line <= '0;
        end else if (maw_hs) begin
            f_wfly <= 1'b1;  f_wfly_line <= line_of(mem_awaddr);
        end else if (mb_hs) begin
            f_wfly <= 1'b0;
        end
    end
    always @(posedge clk) begin
        vld_d <= obs_vld;  rack_d <= obs_rack;  gathered_d <= obs_gathered;
        pd_d <= obs_pd;  abs_done_d <= obs_abs_done;  line_d <= obs_line_f;
        wstate_d <= obs_wstate;  w_sel_d <= obs_w_sel;
        done_vld_d <= done_vld;  done_id_d <= c_coh_done_id;
        mar_v_d <= mem_arvalid;  mar_r_d <= mem_arready;  mar_id_d <= mem_arid;  mar_addr_d <= mem_araddr;
        r_v_d <= rq_rvalid;  r_r_d <= rq_rready;  r_last_d <= rq_rlast;
        r_id_d <= rq_rid_f;  r_data_d <= rq_rdata_f;  r_resp_d <= rq_rresp_f;
        ac_v_d <= s_acvalid;  ac_r_d <= s_acready;  ac_addr_d <= s_acaddr;  ac_snoop_d <= s_acsnoop;
        iow_slot_vld_d <= obs_iow_slot_vld;  iow_slot_d <= obs_iow_slot;
        io_aw_sh_d <= io_aw_sh;  io_aw_addr_dd <= io_awaddr;
        if (!rst_n) h_delivered <= 4'd0;
        else begin
            for (s = 0; s < SLOTS; s = s + 1) begin
                if (dbg_grant && (dbg_grant_slot == s)) h_delivered[s] <= 1'b0;
                else if (obs_vld[s] && obs_ar_taken[s] && !obs_iow[s]
                         && rq_r_hs[sl_dir(s)] && rq_rlast[sl_dir(s)]
                         && (rq3(rq_rid_f, sl_dir(s)) == sl_arid(obs_arid_f, s)))
                    h_delivered[s] <= 1'b1;
                else if (obs_vld[s] && obs_iow[s] && io_b_hs && obs_iow_slot_vld && (obs_iow_slot == s))
                    h_delivered[s] <= 1'b1;
            end
        end
    end

    // violation vectors, asserted zero below so a counterexample names the offender
    reg [3:0] v_line_dup, v_grant_locked, v_release, v_rack_src, v_mo, v_free, v_wb_hold, v_abs_order;
    reg [NRQ-1:0] v_arready, v_ar_pair, v_route_mem, v_route_rpl, v_r_stable;
    reg [NP-1:0] v_r_infl, v_r_beats;
    reg [NP-1:0] v_ac_legal, v_ac_stable, v_sn_count, v_cd_slot, v_cr_slot, v_snq;
    reg [2:0]    owed_open;
    reg [3:0] v_shadow;
    reg       v_mar_legal, v_mar_stable, v_abs_legal, v_mar_race;
    reg [3:0] v_flags;
    reg [2:0] v_engines;
    reg [3:0] v_io;
    reg [NP-1:0] wb_sel_now;
    reg       io_sel_now;
    reg       any_aw_line;
    reg       any_cd_peer;
    reg       any_ior;
    always @(*) begin
        v_line_dup = '0;  v_grant_locked = '0;  v_release = '0;  v_rack_src = '0;
        v_mo = '0;  v_free = '0;  v_wb_hold = '0;  v_abs_order = '0;
        v_arready = '0;  v_ar_pair = '0;  v_route_mem = '0;  v_route_rpl = '0;
        v_r_stable = '0;  v_r_infl = '0;  v_r_beats = '0;
        v_ac_legal = '0;  v_ac_stable = '0;  v_sn_count = '0;  v_cd_slot = '0;  v_cr_slot = '0;
        v_shadow = '0;  v_snq = '0;
        v_mar_legal = 1'b0;  v_mar_stable = 1'b0;  v_abs_legal = 1'b0;  v_mar_race = 1'b0;
        v_flags = '0;  v_engines = '0;  v_io = '0;
        any_aw_line = 1'b0;  any_cd_peer = 1'b0;
        for (d = 0; d < NP; d = d + 1)
            wb_sel_now[d] = (wstate_d == W_IDLE) && (obs_wstate == W_AW) && (obs_w_sel == d);
        io_sel_now = (wstate_d == W_IDLE) && (obs_wstate == W_AW) && (obs_w_sel == W_SEL_IO);

        for (s = 0; s < SLOTS; s = s + 1) begin
            // P1 the per-line rule: one valid slot per line
            for (k = 0; k < SLOTS; k = k + 1)
                if ((k != s) && obs_vld[s] && obs_vld[k]
                    && (sl_line(obs_line_f, s) == sl_line(obs_line_f, k)))
                    v_line_dup[s] = 1'b1;
            // P2 a grant never goes to a held line
            if (dbg_grant && obs_vld[s] && (sl_line(obs_line_f, s) == line_of(dbg_grant_addr)))
                v_grant_locked[s] = 1'b1;
            // P3 the lock drops only after the requester's retire
            if (vld_d[s] && !obs_vld[s] && !rack_d[s])
                v_release[s] = 1'b1;
            // P4 the retire bit is set only by the requester's OWN done pulse naming the slot's ID
            if (!rack_d[s] && obs_rack[s] && vld_d[s]
                && !((sl_dir(s) != IO) && done_of(done_vld_d, sl_dir(s))
                     && (done_id_of(done_id_d, sl_dir(s)) == sl_arid(obs_arid_f, s))))
                v_rack_src[s] = 1'b1;
            // P9 the memory bookkeeping matches the reads actually outstanding
            if (mo[s] != (obs_vld[s] & obs_mem_issued[s] & ~obs_mem_done[s]))
                v_mo[s] = 1'b1;
            // P20 a slot frees only once the requester has its last beat and its read is drained
            if (vld_d[s] && !obs_vld[s] && !(h_delivered[s] && !mo[s]))
                v_free[s] = 1'b1;
            // P17 a write-back (any cache's) is selected only when no slot on its line lacks a
            //     verdict, nor -- unless OLD (BUG-003) -- has an absorption pending
            for (k = 0; k < NP; k = k + 1)
                if (wb_sel_now[k] && vld_d[s] && (sl_line(line_d, s) == line_of(pa(aw_addr_d, k)))
                    && (!gathered_d[s] || (pd_d[s] && !abs_done_d[s] && !f_aw_old_d[k])))
                    v_wb_hold[s] = 1'b1;
            // P25 (BUG-003) an absorption is not selected while an old write-back to its line is presented
            for (k = 0; k < NP; k = k + 1)
                if ((wstate_d == W_IDLE) && (obs_wstate == W_AW) && (obs_w_sel == W_SEL_ABS)
                    && (obs_w_slot == s[1:0]) && aw_v_d[k] && f_aw_old_d[k]
                    && (line_of(pa(aw_addr_d, k)) == sl_line(line_d, s)))
                    v_abs_order[s] = 1'b1;
            if (io_sel_now && !io_aw_sh_d && vld_d[s] && (sl_line(line_d, s) == line_of(io_aw_addr_dd))
                && (!gathered_d[s] || (pd_d[s] && !abs_done_d[s])))
                v_wb_hold[s] = 1'b1;
            // P26 (per-peer shadow) the slot's counters are exactly the peers it owes and that
            //     have not accepted / not answered; an answer only after an accept; the verdict
            //     bits are the OR of the answering CRs
            if (obs_vld[s]
                && ((sl_cnt(obs_ac_left_f, s) != popc(sl_peers(f_owed, s) & ~sl_peers(f_acc, s)))
                    || (sl_cnt(obs_cr_left_f, s) != popc(sl_peers(f_owed, s) & ~sl_peers(f_ans, s)))
                    || ((sl_peers(f_ans, s) & ~sl_peers(f_acc, s)) != '0)
                    || ((sl_peers(f_acc, s) & ~sl_peers(f_owed, s)) != '0)
                    || (obs_dt[s] != f_dt[s]) || (obs_pd[s] != f_pd[s])))
                v_shadow[s] = 1'b1;
        end

        for (d = 0; d < NRQ; d = d + 1) begin
            // P5 arready only for a granted slot of this requester with its AR untaken
            if (((d < NP) ? c_arready[d] : io_arready)
                && !(obs_vld[rq_slot(obs_arw_slot_f, d)]
                     && (sl_dir(rq_slot(obs_arw_slot_f, d)) == d)
                     && !obs_ar_taken[rq_slot(obs_arw_slot_f, d)]
                     && !obs_iow[rq_slot(obs_arw_slot_f, d)]))
                v_arready[d] = 1'b1;
            // P6 the AR taken is the slot's line (and, a cache's, its class's length)
            if (d < NP) begin
                if (c_ar_hs[d] && !((line_of(pa(c_araddr, d)) == sl_line(obs_line_f, rq_slot(obs_arw_slot_f, d)))
                                    && ((p8(c_arlen, d) == 8'd0) == obs_nodata[rq_slot(obs_arw_slot_f, d)])))
                    v_ar_pair[d] = 1'b1;
            end else begin
                if (io_ar_hs && !((line_of(io_araddr) == sl_line(obs_line_f, rq_slot(obs_arw_slot_f, d)))
                                  && !obs_nodata[rq_slot(obs_arw_slot_f, d)]))
                    v_ar_pair[d] = 1'b1;
            end
            // P10 a forwarded memory beat / a replayed beat belongs to this requester's slot
            if (obs_mem_pres[d] && !(mem_rvalid && obs_vld[mr_slot] && (sl_dir(mr_slot) == d)
                                      && obs_gathered[mr_slot] && !obs_dt[mr_slot]
                                      && (rq3(rq_rid_f, d) == sl_arid(obs_arid_f, mr_slot))))
                v_route_mem[d] = 1'b1;
            if (obs_rpl_pres[d] && !(obs_vld[rq_slot(obs_rpl_slot_f, d)]
                                      && (sl_dir(rq_slot(obs_rpl_slot_f, d)) == d)
                                      && obs_gathered[rq_slot(obs_rpl_slot_f, d)]
                                      && (obs_dt[rq_slot(obs_rpl_slot_f, d)] | obs_nodata[rq_slot(obs_rpl_slot_f, d)])
                                      && !obs_iow[rq_slot(obs_rpl_slot_f, d)]
                                      && !obs_rpl_done[rq_slot(obs_rpl_slot_f, d)]
                                      && (rq3(rq_rid_f, d) == sl_arid(obs_arid_f, rq_slot(obs_rpl_slot_f, d)))))
                v_route_rpl[d] = 1'b1;
            if (rq_rvalid[d] != (obs_mem_pres[d] | obs_rpl_pres[d]))
                v_route_mem[d] = 1'b1;
            // P11 AXI R stability
            if (r_v_d[d] && !r_r_d[d]
                && !(rq_rvalid[d] && (rq3(rq_rid_f, d) == rq3(r_id_d, d))
                     && (rq_rdata_f[d*32 +: 32] == r_data_d[d*32 +: 32])
                     && (rq_rresp_f[d*2 +: 2] == r_resp_d[d*2 +: 2])
                     && (rq_rlast[d] == r_last_d[d])))
                v_r_stable[d] = 1'b1;
        end
        for (d = 0; d < NP; d = d + 1) begin
            // P12 a cache sees exactly the IDs it issued, none after their last beat
            if (c_rvalid[d] && !(f_infl[d][p3(c_rid, d)] && !f_last[d][p3(c_rid, d)]))
                v_r_infl[d] = 1'b1;
            // P13 every AR gets its beats
            if (c_r_hs[d] && !(f_nd[d][p3(c_rid, d)]
                                 ? (c_rlast[d] && (f_beats[d][p3(c_rid, d)*2 +: 2] == 2'd0))
                                 : (c_rlast[d] == (f_beats[d][p3(c_rid, d)*2 +: 2] == 2'd3))))
                v_r_beats[d] = 1'b1;
        end
        // P-IO1 the IO's R
        if (io_rvalid && !(f_io_rd && (io_rid == f_io_rid)))
            v_io[0] = 1'b1;
        if (io_r_hs && (io_rlast != (f_io_rbeats == f_io_rlen)))
            v_io[0] = 1'b1;
        // P-IO2 one IO read and one IO write in flight
        any_ior = 1'b0;
        for (s = 0; s < SLOTS; s = s + 1)
            if (obs_vld[s] && (sl_dir(s) == IO) && !obs_iow[s]) any_ior = 1'b1;
        if (obs_ior_busy != any_ior)
            v_io[1] = 1'b1;
        if (obs_iow_slot_vld && !(obs_vld[obs_iow_slot] && (sl_dir(obs_iow_slot) == IO) && obs_iow[obs_iow_slot]))
            v_io[1] = 1'b1;
        if (obs_iow_slot_vld && !obs_iow_busy)
            v_io[1] = 1'b1;
        // P-IO3 the IO's write handshakes only in its own selection
        if (io_awready && !((obs_wstate == W_AW) && w_io))
            v_io[2] = 1'b1;
        if (io_wready && !((obs_wstate == 2'd2) && w_io))
            v_io[2] = 1'b1;
        if (io_bvalid && !((obs_wstate == W_B) && w_io && mem_bvalid))
            v_io[2] = 1'b1;
        // P-IO4 the IO's WriteUnique selected only gathered, absorbed if dirty, its own line, and
        //       no cache presenting a write-back to that line; a non-shareable write never while a
        //       WriteUnique slot is live
        for (k = 0; k < NP; k = k + 1)
            if (aw_v_d[k] && (line_of(pa(aw_addr_d, k)) == sl_line(line_d, iow_slot_d)))
                any_aw_line = 1'b1;
        if (io_sel_now && io_aw_sh_d
            && !(iow_slot_vld_d && gathered_d[iow_slot_d] && (!pd_d[iow_slot_d] || abs_done_d[iow_slot_d])
                 && (sl_line(line_d, iow_slot_d) == line_of(io_aw_addr_dd)) && !any_aw_line))
            v_io[3] = 1'b1;
        if (io_sel_now && !io_aw_sh_d && iow_slot_vld_d)
            v_io[3] = 1'b1;

        for (p = 0; p < NP; p = p + 1) begin
            // P14 an AC names a valid slot of ANOTHER requester that OWES peer p an AC it has not
            //     yet accepted (per-peer shadow), with the slot's line and the class's snoop
            if (s_acvalid[p] && !(obs_vld[p2(obs_ac_slot_f, p)]
                                   && (sl_dir(p2(obs_ac_slot_f, p)) != p)
                                   && !obs_ac_all[p2(obs_ac_slot_f, p)]
                                   && f_owed[p2(obs_ac_slot_f, p)*NP + p]
                                   && !f_acc[p2(obs_ac_slot_f, p)*NP + p]
                                   && (pa(s_acaddr, p) == {sl_line(obs_line_f, p2(obs_ac_slot_f, p)), 4'd0})
                                   && (p4(s_acsnoop, p) == map_snoop(sl_type(obs_type_f, p2(obs_ac_slot_f, p))))))
                v_ac_legal[p] = 1'b1;
            // P15 ACE AC stability
            if (ac_v_d[p] && !ac_r_d[p]
                && !(s_acvalid[p] && (pa(s_acaddr, p) == pa(ac_addr_d, p))
                     && (p4(s_acsnoop, p) == p4(ac_snoop_d, p))))
                v_ac_stable[p] = 1'b1;
            // P16 the snoop bookkeeping: outstanding count exact, bounded, CR taken whenever one is
            //     outstanding; a CD beat taken only with one outstanding, and taken unless another
            //     peer's beat for the same requester's buffer is taken this cycle; and never two
            //     beats into one buffer in one cycle (one write port per buffer)
            any_cd_peer = 1'b0;
            for (q = 0; q < NP; q = q + 1)
                if ((q != p) && cd_hs[q]
                    && (sl_dir(p2(obs_sni_head_f, q)) == sl_dir(p2(obs_sni_head_f, p))))
                    any_cd_peer = 1'b1;
            if ((p2(obs_sni_cnt_f, p) != sn_out[p]) || (sn_out[p] > 2'd2)
                || (s_crready[p] != (sn_out[p] != 2'd0))
                || (s_cdready[p] && !(s_cdvalid[p] && (sn_out[p] != 2'd0)))
                || (s_cdvalid[p] && (sn_out[p] != 2'd0) && !s_cdready[p] && !any_cd_peer)
                || (cd_hs[p] && any_cd_peer))
                v_sn_count[p] = 1'b1;
            // P21 a CD beat lands in a live slot of another requester awaiting its verdict
            if (cd_hs[p] && !(obs_vld[p2(obs_sni_head_f, p)]
                               && (sl_dir(p2(obs_sni_head_f, p)) != p)
                               && !obs_gathered[p2(obs_sni_head_f, p)]))
                v_cd_slot[p] = 1'b1;
            // P28 (per-peer shadow) every AC a live slot owes peer p and p has not accepted is
            //     queued at p: the snoop queue holds exactly that many slots (a fanout that drops
            //     a peer -- an AC owed and never queued -- is otherwise a hang no safety property sees)
            owed_open = 3'd0;
            for (s = 0; s < SLOTS; s = s + 1)
                owed_open = owed_open + (obs_vld[s] && f_owed[s*NP + p] && !f_acc[s*NP + p]);
            if (p3(obs_snq_cnt_f, p) != owed_open)
                v_snq[p] = 1'b1;
            // P27 (per-peer shadow) the slot a peer's CR / CD lands in is the oldest slot whose AC
            //     it accepted and has not answered, and that slot owes it the answer
            if ((sn_out[p] != 2'd0)
                && ((p2(obs_sni_head_f, p) != h_sni[p][1:0])
                    || !(f_acc[h_sni[p][1:0]*NP + p] && !f_ans[h_sni[p][1:0]*NP + p])))
                v_cr_slot[p] = 1'b1;
        end

        // P22 table flag order: every flag implies the ones before it in the slot's life
        for (s = 0; s < SLOTS; s = s + 1) begin
            if (obs_vld[s] && (
                   (obs_gathered[s] && !obs_ac_all[s])
                || (sl_dir(s) > IO)
                || (obs_ac_all[s] != (sl_cnt(obs_ac_left_f, s) == 0)) || (obs_gathered[s] != (sl_cnt(obs_cr_left_f, s) == 0))
                || (sl_cnt(obs_ac_left_f, s) > ((sl_dir(s) == IO) ? NP : NP - 1))
                || (sl_cnt(obs_cr_left_f, s) > ((sl_dir(s) == IO) ? NP : NP - 1))
                || (sl_cnt(obs_cr_left_f, s) < sl_cnt(obs_ac_left_f, s))
                || (obs_dt[s] && (sl_cnt(obs_ac_left_f, s) == ((sl_dir(s) == IO) ? NP : NP - 1)))
                || (obs_pd[s] && !obs_dt[s])
                || (obs_mem_issued[s] && !(obs_ac_all[s] && obs_ar_taken[s] && !obs_nodata[s]))
                || (obs_mem_done[s] && !(obs_mem_issued[s] || obs_dt[s]))
                || (obs_rpl_done[s] && !(obs_gathered[s] && obs_ar_taken[s] && (obs_dt[s] || obs_nodata[s]) && !obs_iow[s]))
                || (obs_abs_issued[s] && !(obs_pd[s] && obs_gathered[s]))
                || (obs_abs_done[s] && !obs_abs_issued[s])
                || (obs_rack[s] && !obs_ar_taken[s] && (sl_dir(s) != IO))
                || ((sl_dir(s) == IO) && !obs_rack[s])
                || (obs_iow[s] && !((sl_dir(s) == IO) && obs_nodata[s] && obs_ar_taken[s]))
                || (obs_iow_done[s] && !(obs_iow[s] && obs_gathered[s]))
                || ((sl_dir(s) == IO) && (sl_type(obs_type_f, s) != CLS_IO_RD) && (sl_type(obs_type_f, s) != CLS_IO_WR))
                || ((sl_dir(s) == IO) && (obs_iow[s] != (sl_type(obs_type_f, s) == CLS_IO_WR)))))
                v_flags[s] = 1'b1;
            if (obs_vld[s] && (h_delivered[s] != (obs_iow[s] ? obs_iow_done[s]
                                                   : (obs_dt[s] | obs_nodata[s]) ? obs_rpl_done[s] : obs_mem_done[s])))
                v_flags[s] = 1'b1;
        end
        // P23 the engines' held state names a live slot in the matching phase
        for (d = 0; d < NRQ; d = d + 1) begin
            if (obs_rpl_vld[d] && !(obs_vld[rq_slot(obs_rpl_slot_f, d)] && (sl_dir(rq_slot(obs_rpl_slot_f, d)) == d)
                                     && obs_gathered[rq_slot(obs_rpl_slot_f, d)] && obs_ar_taken[rq_slot(obs_rpl_slot_f, d)]
                                     && (obs_dt[rq_slot(obs_rpl_slot_f, d)] | obs_nodata[rq_slot(obs_rpl_slot_f, d)])
                                     && !obs_iow[rq_slot(obs_rpl_slot_f, d)]
                                     && !obs_rpl_done[rq_slot(obs_rpl_slot_f, d)]))
                v_engines[2] = 1'b1;
            if (obs_arw_vld[d] && !(obs_vld[rq_slot(obs_arw_slot_f, d)] && (sl_dir(rq_slot(obs_arw_slot_f, d)) == d)
                                     && !obs_ar_taken[rq_slot(obs_arw_slot_f, d)]))
                v_engines[2] = 1'b1;
        end
        if ((obs_wstate != W_IDLE) && w_io && !obs_iow_busy)
            v_engines[2] = 1'b1;
        if ((obs_wstate != W_IDLE) && (obs_w_sel > W_SEL_IO))
            v_engines[2] = 1'b1;
        if (obs_mar_vld && !(obs_vld[obs_mar_slot] && obs_ar_taken[obs_mar_slot] && obs_ac_all[obs_mar_slot]
                             && !obs_nodata[obs_mar_slot] && !obs_mem_issued[obs_mar_slot]))
            v_engines[0] = 1'b1;
        if ((obs_wstate != W_IDLE) && w_abs
            && !(obs_vld[obs_w_slot] && obs_gathered[obs_w_slot] && obs_pd[obs_w_slot]
                 && obs_abs_issued[obs_w_slot] && !obs_abs_done[obs_w_slot]))
            v_engines[1] = 1'b1;
        if ((obs_wstate == W_IDLE) && (obs_abs_issued & ~obs_abs_done & obs_vld) != 4'd0)
            v_engines[1] = 1'b1;

        // P7 the memory AR (see the N=2 harness: AC accepted by every peer, no DT unless held)
        if (mem_arvalid && !(!mem_arid[2] && obs_vld[mem_arid[1:0]] && obs_ar_taken[mem_arid[1:0]]
                             && obs_ac_all[mem_arid[1:0]] && !obs_nodata[mem_arid[1:0]]
                             && !obs_mem_issued[mem_arid[1:0]]
                             && (!obs_dt[mem_arid[1:0]] || (mar_v_d && !mar_r_d))
                             && ((sl_dir(mem_arid[1:0]) == IO)
                                 ? ((mem_araddr == obs_io_araddr) && (mem_arlen == obs_io_arlen)
                                    && (line_of(mem_araddr) == sl_line(obs_line_f, mem_arid[1:0]))
                                    && (mem_arlen <= 8'd3))
                                 : ((mem_araddr == {sl_line(obs_line_f, mem_arid[1:0]), 4'd0})
                                    && (mem_arlen == 8'd3)))
                             && !mo[mem_arid[1:0]]))
            v_mar_legal = 1'b1;
        // P24 (BUG-002) a memory read is not first presented while a write to its line is in flight
        if (mem_arvalid && !(mar_v_d && !mar_r_d) && f_wfly
            && (line_of(mem_araddr) == f_wfly_line))
            v_mar_race = 1'b1;
        // P8 AXI AR stability on the memory port
        if (mar_v_d && !mar_r_d && !(mem_arvalid && (mem_arid == mar_id_d) && (mem_araddr == mar_addr_d)))
            v_mar_stable = 1'b1;
        // P18 an absorption writes a PassDirty slot's line, once, with the fabric's own ID
        if (mem_awvalid && w_abs
            && !(obs_vld[obs_w_slot] && obs_gathered[obs_w_slot] && obs_pd[obs_w_slot]
                 && !obs_abs_done[obs_w_slot]
                 && (mem_awaddr == {sl_line(obs_line_f, obs_w_slot), 4'd0})
                 && (mem_awlen == 8'd3)
                 && (mem_awid == ext3(sl_dir(obs_w_slot)))))
            v_abs_legal = 1'b1;
    end

    // ------------------------------------------------------------------
    // Write-back order (jet-prime BUG-002), every pair of caches: of two
    // write-backs presented to one line, the one presented first is taken
    // first.  f_since counts the cycles a port's AW has been presented.
    // ------------------------------------------------------------------
    reg [4:0] f_since [0:NP-1];
    always @(posedge clk) begin
        for (d = 0; d < NP; d = d + 1) begin
            if (!rst_n || !c_awvalid[d] || c_awready[d]) f_since[d] <= 5'd0;
            else if (f_since[d] != 5'd31) f_since[d] <= f_since[d] + 5'd1;
        end
    end
    reg [NP-1:0] v_pend;
    always @(*) begin
        for (d = 0; d < NP; d = d + 1)
            v_pend[d] = (q_cnt[d] != (p3(obs_pend_cnt_f, d) + {2'd0, obs_arw_vld[d]}));
    end
    reg [NP-1:0] v_wb_order;
    reg          f_aw_same_any, f_aw_same_wait;
    always @(*) begin
        v_wb_order = '0;  f_aw_same_any = 1'b0;  f_aw_same_wait = 1'b0;
        for (d = 0; d < NP; d = d + 1)
            for (e = 0; e < NP; e = e + 1)
                if ((e != d) && c_awvalid[d] && c_awvalid[e]
                    && (line_of(pa(c_awaddr, d)) == line_of(pa(c_awaddr, e)))) begin
                    f_aw_same_any = 1'b1;
                    if (c_awready[d] && (f_since[e] > f_since[d])) v_wb_order[d] = 1'b1;
                    if (c_awready[d] && (f_since[e] != f_since[d])) f_aw_same_wait = 1'b1;
                end
    end

    // Three safety tasks (the .sby): PROVE_CORE is all 29 "local" properties;
    // PROVE_FAST is the 17 of them whose refutation needs only a few cycles of
    // state (measured one at a time at N=4, BMC depth 15: 15-42 s each, against
    // 75 s - 3 min+ for the other 12), re-proven to a deeper bound on their
    // own; PROVE_BOOK the four end-to-end bookkeeping properties.  The cheap
    // 17 stay in PROVE_CORE too: smtbmc assumes every assertion at the earlier
    // steps, and alone the dear 12 were SLOWER (they lose those lemmas).
`ifdef PROVE_CORE
`define PROVE_FAST_ON
`endif
`ifdef PROVE_FAST
`define PROVE_FAST_ON
`endif
`ifdef PROVE_FAST_ON
    always @(posedge clk) begin
        if (rst_n && (f_past_valid >= 2)) begin
            ap_line_unique:   assert (v_line_dup == 0);
            ap_grant_unlocked: assert (v_grant_locked == 0);
            ap_grant_one_ar:  assert (!dbg_grant || !obs_arw_vld[dbg_grant_dir]);
            ap_mo:            assert (v_mo == 0);
            ap_arready_slot:  assert (v_arready == 0);
            ap_route_mem:     assert (v_route_mem == 0);
            ap_sn_count:      assert (v_sn_count == 0);
            ap_no_pend_ovf:   assert (obs_pend_ovf == 0);
            // the launches a cache holds with their AR untaken are exactly onyx's
            // pending pulses plus the one granted and awaiting its AR
            ap_pend_count:    assert (v_pend == 0);
        end
        if (rst_n && (f_past_valid >= 3)) begin
            ap_release_after_retire: assert (v_release == 0);
            ap_rack_source:   assert (v_rack_src == 0);
            ap_free_complete: assert (v_free == 0);
            ap_wb_select_hold: assert (v_wb_hold == 0);
            ap_abs_after_old_wb: assert (v_abs_order == 0);
            ap_wb_order:      assert (v_wb_order == 0);
            ap_mar_stable:    assert (!v_mar_stable);
            ap_mar_no_wr_race: assert (!v_mar_race);
        end
    end
`endif
`ifdef PROVE_CORE
    always @(posedge clk) begin
        if (rst_n && (f_past_valid >= 2)) begin
            ap_ar_pairing:    assert (v_ar_pair == 0);
            ap_mar_legal:     assert (!v_mar_legal);
            ap_route_rpl:     assert (v_route_rpl == 0);
            ap_io_port:       assert (v_io == 0);
            ap_ac_legal:      assert (v_ac_legal == 0);
            ap_abs_legal:     assert (!v_abs_legal);
            ap_table_flags:   assert (v_flags == 0);
            ap_engines_live:  assert (v_engines == 0);
            ap_peer_shadow:   assert (v_shadow == 0);
            ap_snq_count:     assert (v_snq == 0);
        end
        if (rst_n && (f_past_valid >= 3)) begin
            ap_r_stable:      assert (v_r_stable == 0);
            ap_ac_stable:     assert (v_ac_stable == 0);
        end
    end
`endif
`ifdef PROVE_BOOK
    always @(posedge clk) begin
        if (rst_n && (f_past_valid >= 2)) begin
            ap_r_inflight:    assert (v_r_infl == 0);
            ap_r_beats:       assert (v_r_beats == 0);
            ap_cd_slot:       assert (v_cd_slot == 0);
            ap_cr_slot:       assert (v_cr_slot == 0);
        end
    end
`endif

    // ------------------------------------------------------------------
    // Covers
    // ------------------------------------------------------------------
    reg [NP-1:0]        blk_vld;
    reg [NP*LINE_W-1:0] blk_line_f;
    reg [NP-1:0]        wbblk_seen;
    reg [3:0]           freed_seen;
    always @(posedge clk) begin
        if (!rst_n) begin
            blk_vld <= '0;  blk_line_f <= '0;  wbblk_seen <= '0;  freed_seen <= 4'd0;
        end else begin
            for (d = 0; d < NP; d = d + 1) begin
                if (obs_cand_locked[d] && dbg_pend_vld[d]) begin
                    blk_vld[d] <= 1'b1;
                    blk_line_f[d*LINE_W +: LINE_W] <= line_of(obs_cand_addr_f[d*AW +: AW]);
                end
                if (obs_wb_blocked[d] && c_awvalid[d]) wbblk_seen[d] <= 1'b1;
            end
            freed_seen <= freed_seen | (vld_d & ~obs_vld);
        end
    end

    // cover helpers
    reg [NRQ-1:0] c_live_dir;      // requester d holds a live slot
    reg [2:0]     c_n_vld, c_n_mo;
    reg           c_cache_ac_pair; // two peers accept one cache slot's ACs in one cycle
    reg           c_cache_cr_pair; // two peers answer one cache slot in one cycle
    reg           c_dt_after_ans;  // a DT CR for a cache slot another peer already answered
    reg           c_cd_arb;        // two peers want one buffer, one held
    reg           c_cache_two_dt_peers;   // a cache slot gathered from N-1 peers with a DT
    always @(*) begin
        c_live_dir = '0;  c_n_vld = 3'd0;  c_n_mo = 3'd0;
        c_cache_ac_pair = 1'b0;  c_cache_cr_pair = 1'b0;  c_dt_after_ans = 1'b0;  c_cd_arb = 1'b0;
        c_cache_two_dt_peers = 1'b0;
        for (s = 0; s < SLOTS; s = s + 1) begin
            if (obs_vld[s]) c_live_dir[sl_dir(s)] = 1'b1;
            c_n_vld = c_n_vld + obs_vld[s];
            c_n_mo  = c_n_mo + mo[s];
        end
        for (p = 0; p < NP; p = p + 1) begin
            for (q = p + 1; q < NP; q = q + 1) begin
                if (ac_hs[p] && ac_hs[q] && (p2(obs_ac_slot_f, p) == p2(obs_ac_slot_f, q))
                    && (sl_dir(p2(obs_ac_slot_f, p)) != IO))
                    c_cache_ac_pair = 1'b1;
                if (cr_hs[p] && cr_hs[q] && (p2(obs_sni_head_f, p) == p2(obs_sni_head_f, q))
                    && (sl_dir(p2(obs_sni_head_f, p)) != IO))
                    c_cache_cr_pair = 1'b1;
            end
            if (cr_hs[p] && cr_dt[p] && (sl_dir(p2(obs_sni_head_f, p)) != IO)
                && ((sl_peers(f_ans, p2(obs_sni_head_f, p)) & ~(1 << p)) != '0))
                c_dt_after_ans = 1'b1;
            for (q = 0; q < NP; q = q + 1)
                if ((q != p) && s_cdvalid[p] && (sn_out[p] != 2'd0) && !s_cdready[p] && cd_hs[q]
                    && (sl_dir(p2(obs_sni_head_f, q)) == sl_dir(p2(obs_sni_head_f, p))))
                    c_cd_arb = 1'b1;
            if (cr_hs[p] && (sl_dir(p2(obs_sni_head_f, p)) != IO)
                && (sl_cnt(obs_cr_left_f, p2(obs_sni_head_f, p)) == 1)
                && (obs_dt[p2(obs_sni_head_f, p)] || cr_dt[p]))
                c_cache_two_dt_peers = 1'b1;
        end
    end

    always @(posedge clk) begin
        if (rst_n && (f_past_valid >= 3)) begin
            // carried from N=2
            cp_two_dirs_live: cover (c_live_dir[0] && c_live_dir[1]);
            cp_three_live:    cover (c_n_vld == 3'd3);
            cp_conflict_regrant: cover (dbg_grant && (dbg_grant_dir < NP) && blk_vld[dbg_grant_dir]
                                        && (line_of(dbg_grant_addr) == blk_line_f[dbg_grant_dir*LINE_W +: LINE_W])
                                        && (freed_seen != 4'd0));
            cp_locked_wait:   cover ((obs_cand_locked[NP-1:0] & dbg_pend_vld) != 0);
            cp_pend_two:      cover ((p3(obs_pend_cnt_f, 0) >= 3'd2) || (p3(obs_pend_cnt_f, NP-1) >= 3'd2));
            cp_dt_drop:       cover (obs_mr_drop && mem_rready);
            cp_dt_suppress:   cover ((cr_hs[0] && cr_dt[0] && !obs_mem_issued[p2(obs_sni_head_f, 0)])
                                     || (cr_hs[NP-1] && cr_dt[NP-1] && !obs_mem_issued[p2(obs_sni_head_f, NP-1)]));
            cp_pass_through:  cover (c_r_hs[0] && obs_mem_pres[0] && c_rlast[0]);
            cp_replay_last:   cover (c_r_hs[1] && obs_rpl_pres[1] && c_rlast[1] && !obs_nodata[rq_slot(obs_rpl_slot_f, 1)]);
            cp_nodata_beat:   cover (c_r_hs[0] && obs_rpl_pres[0] && obs_nodata[rq_slot(obs_rpl_slot_f, 0)]);
            cp_abs_landed:    cover (mb_hs && w_abs);
            cp_wb_landed:     cover (mb_hs && !w_abs && !w_io);
            cp_wb_blocked_then_hs: cover (maw_hs && !w_abs && !w_io && wbblk_seen[obs_w_sel]);
            cp_both_r:        cover (c_rvalid[0] && c_rvalid[1]);
            cp_rpl_behind_mem: cover (obs_rpl_vld[0] && obs_mem_pres[0]);
            cp_sn_two:        cover ((sn_out[0] == 2'd2) || (sn_out[NP-1] == 2'd2));
            cp_mar_stall:     cover (mem_arvalid && !mem_arready);
            cp_two_reads_out: cover (c_n_mo >= 3'd2);
            cp_slot_freed:    cover ((vld_d & ~obs_vld) != 4'd0);
            cp_wb_order_wait: cover (f_aw_same_wait);
            cp_io_rd_replay:  cover (io_r_hs && obs_rpl_pres[IO] && io_rlast);
            cp_io_rd_mem:     cover (io_r_hs && obs_mem_pres[IO] && io_rlast);
            cp_io_rd_nosnoop: cover (io_ar_hs && !io_ar_sh);
            cp_io_wu_landed:  cover (mb_hs && w_io && obs_iow_slot_vld);
            cp_io_wn_landed:  cover (mb_hs && w_io && !obs_iow_slot_vld);
            cp_io_absorb:     cover (mb_hs && w_abs && (sl_dir(obs_w_slot) == IO));
            cp_io_two_live:   cover (obs_ior_busy && obs_iow_busy);
            cp_io_all_ac:     cover (ac_hs == {NP{1'b1}});
            cp_cu_dt:         cover ((cr_hs[0] && cr_dt[0] && obs_nodata[p2(obs_sni_head_f, 0)]
                                      && (sl_dir(p2(obs_sni_head_f, 0)) != IO))
                                  || (cr_hs[1] && cr_dt[1] && obs_nodata[p2(obs_sni_head_f, 1)]
                                      && (sl_dir(p2(obs_sni_head_f, 1)) != IO)));
            cp_mar_wr_wait:   cover (f_wfly && (obs_wstate == W_B) && (|(obs_vld & obs_ar_taken & ~obs_nodata & ~obs_mem_issued & obs_ac_all & ~obs_dt))
                                     && !mem_arvalid);
            cp_old_wb_before_abs: cover (maw_hs && !w_abs && !w_io && f_aw_old[obs_w_sel]
                                         && (|(obs_vld & obs_gathered & obs_pd & ~obs_abs_issued)));
            cp_wc_on_live_line: cover ((req_vld[0] && (p3(c_coh_req_type, 0) == REQ_WC)
                                        && wc_live_line(pa(c_coh_req_addr, 0)))
                                    || (req_vld[1] && (p3(c_coh_req_type, 1) == REQ_WC)
                                        && wc_live_line(pa(c_coh_req_addr, 1))));
            // new at N >= 3: the gather over several peers of a CACHE's slot
            cp_all_caches_live: cover (c_live_dir[NP-1:0] == {NP{1'b1}});
            cp_last_cache_live: cover (c_live_dir[NP-1] && obs_ar_taken[0] && (sl_dir(2'd0) == NP-1));
            cp_cache_ac_pair: cover (c_cache_ac_pair);
            cp_cache_cr_pair: cover (c_cache_cr_pair);
            cp_dt_after_ans:  cover (c_dt_after_ans);
            cp_cache_gather_dt: cover (c_cache_two_dt_peers);
            cp_cd_arb:        cover (c_cd_arb);
            cp_table_full:    cover ((obs_vld == 4'b1111) && (dbg_pend_vld != 0));
            cp_wb_order_far:  cover (maw_hs && !w_abs && !w_io && (obs_w_sel == NP-1) && f_aw_same_any);
        end
    end

endmodule
