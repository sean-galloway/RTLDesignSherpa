// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal wrapper for onyx_ccu (yosys-compatible) -- SAFETY + COVER.
// Run with: sby onyx_ccu.sby
//
// onyx TASK-001 step 4: the coherency unit's per-line rule, its gather and
// the contracts around it, at the tiny geometry ADDR_WIDTH=8 (16 lines) /
// LINE_BYTES=16 / BUS_WIDTH=32 (four beats per line) / AXI_ID_WIDTH=3 /
// N_PORTS=2 / SLOTS=4 / SNOOP_INFLIGHT=2 / DEFER_AR=0 -- the pair fabric's
// formal geometry, so every one of its 27 properties is re-stated here for
// onyx and the two proofs are comparable.  This is the jet_prime_pair_fabric
// harness (jet-prime TASK-001 step 4) carried over; what changed is what
// onyx changed:
//   - the per-slot "AC accepted" and "CR in" bits became counters of the
//     peers yet to accept / yet to answer (N_PORTS-1 of them): the harness
//     reads the DUT's own all-accepted (w_ac_all) and gathered (w_gathered)
//     flags where the fabric's r_ac_done / r_cr_done stood;
//   - the memory AR waits only for every peer's AC accept and the absence
//     of a DataTransfer verdict (the verdict may be known before the gather
//     completes, so "no DT" replaces "no (CR and DT)");
//   - a DataTransfer CR sets the slot's DT (and PD) before the gather is
//     complete, so the flag order is DT -> all ACs accepted, PD -> DT,
//     gathered -> all ACs accepted;
//   - cdready depends on cdvalid (the per-buffer CD write arbitration;
//     AXI allows READY to wait for VALID): at N_PORTS=2 each peer is the
//     only writer of the other port's buffer, so cdready = cdvalid & (a
//     snoop outstanding);
//   - the DUT's cache-side ports are per-port arrays, which sv2v packs with
//     element 0 at the TOP of the vector; the instance below concatenates
//     {c0, c1} accordingly.
// A N_PORTS=3 harness needs the per-peer accept/answer shadow the counters
// summarize; it is the next formal item, not this one.
//
// Mutations (2026-11-21, each on a scratch copy of the flat; `prove` task):
//   M1 the gather declared complete at once (w_gathered = 1): FAIL
//      ap_table_flags at step 3 (the gathered flag no longer tracks the
//      counter, and a verdict is used before every peer answered);
//   M2 the fanout includes the requester (push_q = w_grant): FAIL
//      ap_ac_legal at step 3 (an AC to the requesting port);
//   M3 a second grant to a port with its AR still untaken (the
//      ~r_arw_vld term dropped): FAIL ap_grant_one_ar at step 3.
// The real harness, first run: ap_table_flags at step 3 and ap_r_inflight
// at step 5 -- the memory could present a beat nobody asked for in the one
// cycle after reset where its contract was not yet armed, and onyx's
// gather counters read "complete" for an invalid slot, so the beat was
// forwarded; fixed by qualifying the memory R routes with a read
// outstanding (onyx_ccu w_mr_live) and by holding reset for the two
// steps before the contracts arm (above).
//
// Composition: the DUT alone.  Both caches, both snoop responders and the
// shared memory are free inputs under the documented contracts below --
// onyx is argued against what its neighbours are obliged to do, not
// against jet_prime_top's behaviour (the pair rig covers the composition).
// No property claims data values; the properties are about WHICH beat goes
// WHERE and WHEN, and about every valid/ready pair onyx drives.
//
// Internal observability: the DUT flat is parameter-specialized (see the
// Makefile) and onyx_ccu.sby exposes the transaction table and the queue
// heads as DUT output ports (read_verilog -mem2reg turns the unpacked
// arrays into per-element wires `\r_line[0]` etc., which expose then
// reaches).  Everything else comes from the ports or the wrapper's own
// shadow bookkeeping, driven by the handshakes it watches.
//
// Assumption inventory (environment obligations; each recorded):
//   - house reset protocol; every environment VALID low under reset;
//   - A-req: a request pulse carries one of the four classes jet_prime_top
//     emits (READ_NOT_SHARED_DIRTY, READ_UNIQUE, CLEAN_UNIQUE, WRITE_BACK);
//     a cache holds at most PEND_DEPTH (4) launches whose AR onyx has
//     not taken (the read transport skids up to three launches ahead of
//     the held AR -- delta 02);
//   - A-ar: the cache presents its ARs in launch order -- the AR is the
//     oldest launch whose AR is untaken, with the class's length (0 for an
//     upgrade, FILL_BEATS-1 for a fill) and a read ID not in flight (one
//     ID per MSHR entry); AXI valid/payload stability;
//   - A-done: the retire pulse names an in-flight read ID whose last beat
//     the cache has received (an entry retires after its fill);
//   - A-wb: AXI stability on the cache's AW and W (the write side is a
//     pass-through; nothing else is assumed of it);
//   - A-snoop: a responder answers only an accepted AC (CR, CD only while
//     one is outstanding), in order; a DataTransfer CR follows exactly
//     FILL_BEATS CD beats with CDLAST on the last (the last may share the
//     CR's cycle), a non-DT CR follows none; PassDirty only with DT; a
//     MakeInvalid snoop is never answered with data (IHI0022 Table 3.0);
//   - A-mem: a memory R beat names a read onyx issued and not yet
//     drained, RLAST on its FILL_BEATS-th beat, bursts of different IDs
//     interleaving freely; AXI R stability; BVALID only with a write
//     outstanding.

module formal_onyx_ccu #(
    parameter int AW = 8      // ADDR_WIDTH of the specialized flat
) (
    input  logic        clk,
    input  logic        rst_n,

    // cache 0 read side (free)
    input  logic [2:0]  c0_arid,
    input  logic [AW-1:0] c0_araddr,
    input  logic [7:0]  c0_arlen,
    input  logic [2:0]  c0_arsize,
    input  logic [1:0]  c0_arburst,
    input  logic        c0_arlock,
    input  logic [3:0]  c0_arcache,
    input  logic [2:0]  c0_arprot,
    input  logic [3:0]  c0_arqos,
    input  logic [3:0]  c0_arregion,
    input  logic        c0_aruser,
    input  logic        c0_arvalid,
    input  logic        c0_rready,
    // cache 0 write side (free)
    input  logic [2:0]  c0_awid,
    input  logic [AW-1:0] c0_awaddr,
    input  logic [7:0]  c0_awlen,
    input  logic [2:0]  c0_awsize,
    input  logic [1:0]  c0_awburst,
    input  logic        c0_awlock,
    input  logic [3:0]  c0_awcache,
    input  logic [2:0]  c0_awprot,
    input  logic [3:0]  c0_awqos,
    input  logic [3:0]  c0_awregion,
    input  logic        c0_awuser,
    input  logic        c0_awvalid,
    input  logic [31:0] c0_wdata,
    input  logic [3:0]  c0_wstrb,
    input  logic        c0_wlast,
    input  logic        c0_wuser,
    input  logic        c0_wvalid,
    input  logic        c0_bready,

    // cache 1 read side (free)
    input  logic [2:0]  c1_arid,
    input  logic [AW-1:0] c1_araddr,
    input  logic [7:0]  c1_arlen,
    input  logic [2:0]  c1_arsize,
    input  logic [1:0]  c1_arburst,
    input  logic        c1_arlock,
    input  logic [3:0]  c1_arcache,
    input  logic [2:0]  c1_arprot,
    input  logic [3:0]  c1_arqos,
    input  logic [3:0]  c1_arregion,
    input  logic        c1_aruser,
    input  logic        c1_arvalid,
    input  logic        c1_rready,
    // cache 1 write side (free)
    input  logic [2:0]  c1_awid,
    input  logic [AW-1:0] c1_awaddr,
    input  logic [7:0]  c1_awlen,
    input  logic [2:0]  c1_awsize,
    input  logic [1:0]  c1_awburst,
    input  logic        c1_awlock,
    input  logic [3:0]  c1_awcache,
    input  logic [2:0]  c1_awprot,
    input  logic [3:0]  c1_awqos,
    input  logic [3:0]  c1_awregion,
    input  logic        c1_awuser,
    input  logic        c1_awvalid,
    input  logic [31:0] c1_wdata,
    input  logic [3:0]  c1_wstrb,
    input  logic        c1_wlast,
    input  logic        c1_wuser,
    input  logic        c1_wvalid,
    input  logic        c1_bready,

    // snoop responders (free)
    input  logic        s0_acready,
    input  logic [4:0]  s0_crresp,
    input  logic        s0_crvalid,
    input  logic [31:0] s0_cddata,
    input  logic        s0_cdlast,
    input  logic        s0_cdvalid,
    input  logic        s1_acready,
    input  logic [4:0]  s1_crresp,
    input  logic        s1_crvalid,
    input  logic [31:0] s1_cddata,
    input  logic        s1_cdlast,
    input  logic        s1_cdvalid,

    // D-8 request / retire sidebands (free)
    input  logic        c0_coh_req_valid,
    input  logic [AW-1:0] c0_coh_req_addr,
    input  logic [2:0]  c0_coh_req_type,
    input  logic        c1_coh_req_valid,
    input  logic [AW-1:0] c1_coh_req_addr,
    input  logic [2:0]  c1_coh_req_type,
    input  logic        c0_coh_done_valid,
    input  logic [2:0]  c0_coh_done_id,
    input  logic        c1_coh_done_valid,
    input  logic [2:0]  c1_coh_done_id,

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
    localparam LINE_W  = AW - 4;      // log2(LINE_BYTES) = 4 offset bits
    localparam OFF_W   = 4;
    localparam IW      = 3;
    localparam FB      = 4;           // beats per line
    localparam BW      = 2;           // beat index width
    localparam PEND_DEPTH = 4;
    localparam SN_INFL = 2;

    // l1_pkg ACE request classes jet_prime_top emits, IHI0022 ACSNOOP
    localparam [2:0] REQ_RU   = 3'b001;
    localparam [2:0] REQ_CU   = 3'b010;
    localparam [2:0] REQ_WB   = 3'b100;
    localparam [2:0] REQ_RNSD = 3'b110;
    localparam [3:0] ACSNOOP_READ_SHARED  = 4'h1;
    localparam [3:0] ACSNOOP_READ_UNIQUE  = 4'h7;
    localparam [3:0] ACSNOOP_MAKE_INVALID = 4'hC;
    localparam CR_DT = 0;             // l1_pkg AMBER_CRRESP_DT
    localparam CR_PD = 2;             // l1_pkg AMBER_CRRESP_PD
    // write-port FSM (onyx_ccu localparams; w_sel 2 = the absorption)
    localparam [1:0] W_IDLE = 2'd0;
    localparam [1:0] W_AW   = 2'd1;
    localparam [1:0] W_B    = 2'd3;

    function automatic [LINE_W-1:0] line_of(input [AW-1:0] a);
        line_of = a[AW-1:OFF_W];
    endfunction

    function automatic [3:0] map_snoop(input [2:0] t);
        case (t)
            3'b000, REQ_RNSD: map_snoop = ACSNOOP_READ_SHARED;
            REQ_RU:           map_snoop = ACSNOOP_READ_UNIQUE;
            default:          map_snoop = ACSNOOP_MAKE_INVALID;
        endcase
    endfunction

    function automatic is_nodata(input [2:0] t);
        is_nodata = (t == REQ_CU) || (t == 3'b011);
    endfunction

    // ------------------------------------------------------------------
    // DUT outputs
    // ------------------------------------------------------------------
    logic        c0_arready, c1_arready;
    logic [2:0]  c0_rid, c1_rid;
    logic [31:0] c0_rdata, c1_rdata;
    logic [1:0]  c0_rresp, c1_rresp;
    logic        c0_rlast, c1_rlast;
    logic        c0_ruser, c1_ruser;
    logic        c0_rvalid, c1_rvalid;
    logic        c0_awready, c1_awready;
    logic        c0_wready, c1_wready;
    logic [2:0]  c0_bid, c1_bid;
    logic [1:0]  c0_bresp, c1_bresp;
    logic        c0_buser, c1_buser;
    logic        c0_bvalid, c1_bvalid;
    logic [AW-1:0] s0_acaddr, s1_acaddr;
    logic [3:0]  s0_acsnoop, s1_acsnoop;
    logic [2:0]  s0_acprot, s1_acprot;
    logic        s0_acvalid, s1_acvalid;
    logic        s0_crready, s1_crready;
    logic        s0_cdready, s1_cdready;
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
    logic [1:0]  dbg_pend_vld;
    logic        dbg_abs_pend;
    logic        dbg_grant;
    logic        dbg_grant_dir;
    logic [AW-1:0] dbg_grant_addr;
    logic [1:0]  dbg_grant_slot;

    // exposed internals (onyx_ccu.sby `expose`)
    logic [3:0]  obs_vld, obs_dir, obs_nodata, obs_ar_taken, obs_ac_all;
    logic [3:0]  obs_gathered, obs_dt, obs_pd, obs_mem_issued, obs_mem_done;
    logic [3:0]  obs_ac_left, obs_cr_left;   // one peer at N_PORTS=2: one bit each
    logic [3:0]  obs_rpl_done, obs_abs_issued, obs_abs_done, obs_rack;
    logic        obs_mar_vld;
    logic [1:0]  obs_mar_slot;
    logic [1:0]  obs_arw_vld, obs_pend_ovf, obs_rpl_vld;
    logic [1:0]  obs_wstate, obs_w_sel, obs_w_slot;
    logic [1:0]  obs_cand_locked, obs_mem_pres, obs_rpl_pres, obs_wb_blocked;
    logic        obs_mr_drop;
    logic [SLOTS*LINE_W-1:0] obs_line_f;
    logic [SLOTS*3-1:0]      obs_type_f;
    logic [SLOTS*IW-1:0]     obs_arid_f;
    logic [2*2-1:0]          obs_arw_slot_f, obs_rpl_slot_f, obs_ac_slot_f, obs_sni_head_f;
    logic [2*3-1:0]          obs_pend_cnt_f;
    logic [2*AW-1:0]         obs_cand_addr_f;
    logic [2*2-1:0]          obs_sni_cnt_f;

    onyx_ccu dut (
        .clk(clk), .rst_n(rst_n),
        // per-port arrays, element 0 at the top (sv2v packing)
        .c_arid({c0_arid, c1_arid}), .c_araddr({c0_araddr, c1_araddr}), .c_arlen({c0_arlen, c1_arlen}),
        .c_arsize({c0_arsize, c1_arsize}), .c_arburst({c0_arburst, c1_arburst}),
        .c_arlock({c1_arlock, c0_arlock}), .c_arcache({c0_arcache, c1_arcache}),
        .c_arprot({c0_arprot, c1_arprot}), .c_arqos({c0_arqos, c1_arqos}),
        .c_arregion({c0_arregion, c1_arregion}), .c_aruser({c0_aruser, c1_aruser}),
        .c_arvalid({c1_arvalid, c0_arvalid}), .c_arready({c1_arready, c0_arready}),
        .c_rid({c0_rid, c1_rid}), .c_rdata({c0_rdata, c1_rdata}), .c_rresp({c0_rresp, c1_rresp}),
        .c_rlast({c1_rlast, c0_rlast}), .c_ruser({c0_ruser, c1_ruser}),
        .c_rvalid({c1_rvalid, c0_rvalid}), .c_rready({c1_rready, c0_rready}),
        .c_awid({c0_awid, c1_awid}), .c_awaddr({c0_awaddr, c1_awaddr}), .c_awlen({c0_awlen, c1_awlen}),
        .c_awsize({c0_awsize, c1_awsize}), .c_awburst({c0_awburst, c1_awburst}),
        .c_awlock({c1_awlock, c0_awlock}), .c_awcache({c0_awcache, c1_awcache}),
        .c_awprot({c0_awprot, c1_awprot}), .c_awqos({c0_awqos, c1_awqos}),
        .c_awregion({c0_awregion, c1_awregion}), .c_awuser({c0_awuser, c1_awuser}),
        .c_awvalid({c1_awvalid, c0_awvalid}), .c_awready({c1_awready, c0_awready}),
        .c_wdata({c0_wdata, c1_wdata}), .c_wstrb({c0_wstrb, c1_wstrb}), .c_wlast({c1_wlast, c0_wlast}),
        .c_wuser({c0_wuser, c1_wuser}), .c_wvalid({c1_wvalid, c0_wvalid}), .c_wready({c1_wready, c0_wready}),
        .c_bid({c0_bid, c1_bid}), .c_bresp({c0_bresp, c1_bresp}), .c_buser({c0_buser, c1_buser}),
        .c_bvalid({c1_bvalid, c0_bvalid}), .c_bready({c1_bready, c0_bready}),
        .s_acaddr({s0_acaddr, s1_acaddr}), .s_acsnoop({s0_acsnoop, s1_acsnoop}), .s_acprot({s0_acprot, s1_acprot}),
        .s_acvalid({s1_acvalid, s0_acvalid}), .s_acready({s1_acready, s0_acready}),
        .s_crresp({s0_crresp, s1_crresp}), .s_crvalid({s1_crvalid, s0_crvalid}), .s_crready({s1_crready, s0_crready}),
        .s_cddata({s0_cddata, s1_cddata}), .s_cdlast({s1_cdlast, s0_cdlast}),
        .s_cdvalid({s1_cdvalid, s0_cdvalid}), .s_cdready({s1_cdready, s0_cdready}),
        .c_coh_req_valid({c1_coh_req_valid, c0_coh_req_valid}),
        .c_coh_req_addr({c0_coh_req_addr, c1_coh_req_addr}), .c_coh_req_type({c0_coh_req_type, c1_coh_req_type}),
        .c_coh_done_valid({c1_coh_done_valid, c0_coh_done_valid}), .c_coh_done_id({c0_coh_done_id, c1_coh_done_id}),
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
        .r_mar_vld(obs_mar_vld), .r_mar_slot(obs_mar_slot),
        .r_pend_ovf(obs_pend_ovf), .r_rpl_vld(obs_rpl_vld), .r_wstate(obs_wstate),
        .r_w_sel(obs_w_sel), .r_w_slot(obs_w_slot), .w_cand_locked(obs_cand_locked),
        .w_mem_pres(obs_mem_pres), .w_rpl_pres(obs_rpl_pres), .w_mr_drop(obs_mr_drop),
        .w_wb_blocked(obs_wb_blocked),
        .\r_dir[0] (obs_dir[0]), .\r_dir[1] (obs_dir[1]), .\r_dir[2] (obs_dir[2]), .\r_dir[3] (obs_dir[3]),
        .\r_ac_left[0] (obs_ac_left[0]), .\r_ac_left[1] (obs_ac_left[1]),
        .\r_ac_left[2] (obs_ac_left[2]), .\r_ac_left[3] (obs_ac_left[3]),
        .\r_cr_left[0] (obs_cr_left[0]), .\r_cr_left[1] (obs_cr_left[1]),
        .\r_cr_left[2] (obs_cr_left[2]), .\r_cr_left[3] (obs_cr_left[3]),
        .\r_line[0] (obs_line_f[0*LINE_W +: LINE_W]), .\r_line[1] (obs_line_f[1*LINE_W +: LINE_W]),
        .\r_line[2] (obs_line_f[2*LINE_W +: LINE_W]), .\r_line[3] (obs_line_f[3*LINE_W +: LINE_W]),
        .\r_type[0] (obs_type_f[0*3 +: 3]), .\r_type[1] (obs_type_f[1*3 +: 3]),
        .\r_type[2] (obs_type_f[2*3 +: 3]), .\r_type[3] (obs_type_f[3*3 +: 3]),
        .\r_arid[0] (obs_arid_f[0*IW +: IW]), .\r_arid[1] (obs_arid_f[1*IW +: IW]),
        .\r_arid[2] (obs_arid_f[2*IW +: IW]), .\r_arid[3] (obs_arid_f[3*IW +: IW]),
        .\r_arw_slot[0] (obs_arw_slot_f[0 +: 2]), .\r_arw_slot[1] (obs_arw_slot_f[2 +: 2]),
        .\r_rpl_slot[0] (obs_rpl_slot_f[0 +: 2]), .\r_rpl_slot[1] (obs_rpl_slot_f[2 +: 2]),
        .\w_ac_slot[0] (obs_ac_slot_f[0 +: 2]), .\w_ac_slot[1] (obs_ac_slot_f[2 +: 2]),
        .\w_sni_head[0] (obs_sni_head_f[0 +: 2]), .\w_sni_head[1] (obs_sni_head_f[2 +: 2]),
        .\r_pend_cnt[0] (obs_pend_cnt_f[0 +: 3]), .\r_pend_cnt[1] (obs_pend_cnt_f[3 +: 3]),
        .\r_sni_cnt[0] (obs_sni_cnt_f[0 +: 2]), .\r_sni_cnt[1] (obs_sni_cnt_f[2 +: 2]),
        .\w_cand_addr[0] (obs_cand_addr_f[0 +: AW]), .\w_cand_addr[1] (obs_cand_addr_f[AW +: AW])
    );

    // ------------------------------------------------------------------
    // Per-direction / per-peer aggregation (packed, bit d / p)
    // ------------------------------------------------------------------
    wire [1:0]  c_arvalid  = {c1_arvalid, c0_arvalid};
    wire [1:0]  c_arready  = {c1_arready, c0_arready};
    wire [1:0]  c_ar_hs    = c_arvalid & c_arready;
    wire [5:0]  c_arid_f   = {c1_arid, c0_arid};
    wire [2*AW-1:0] c_araddr_f = {c1_araddr, c0_araddr};
    wire [15:0] c_arlen_f  = {c1_arlen, c0_arlen};
    wire [1:0]  c_rvalid   = {c1_rvalid, c0_rvalid};
    wire [1:0]  c_rready   = {c1_rready, c0_rready};
    wire [1:0]  c_r_hs     = c_rvalid & c_rready;
    wire [5:0]  c_rid_f    = {c1_rid, c0_rid};
    wire [63:0] c_rdata_f  = {c1_rdata, c0_rdata};
    wire [3:0]  c_rresp_f  = {c1_rresp, c0_rresp};
    wire [1:0]  c_rlast    = {c1_rlast, c0_rlast};
    wire [1:0]  c_awvalid  = {c1_awvalid, c0_awvalid};
    wire [1:0]  c_awready  = {c1_awready, c0_awready};
    wire [5:0]  c_awid_f   = {c1_awid, c0_awid};
    wire [2*AW-1:0] c_awaddr_f = {c1_awaddr, c0_awaddr};
    wire [15:0] c_awlen_f  = {c1_awlen, c0_awlen};
    wire [1:0]  c_wvalid   = {c1_wvalid, c0_wvalid};
    wire [1:0]  c_wready   = {c1_wready, c0_wready};
    wire [1:0]  c_wlast    = {c1_wlast, c0_wlast};
    wire [1:0]  c_bvalid   = {c1_bvalid, c0_bvalid};

    wire [1:0]  req_vld    = {c1_coh_req_valid, c0_coh_req_valid};
    wire [2*AW-1:0] req_addr_f = {c1_coh_req_addr, c0_coh_req_addr};
    wire [5:0]  req_type_f = {c1_coh_req_type, c0_coh_req_type};
    wire [1:0]  done_vld   = {c1_coh_done_valid, c0_coh_done_valid};
    wire [5:0]  done_id_f  = {c1_coh_done_id, c0_coh_done_id};

    wire [1:0]  acvalid    = {s1_acvalid, s0_acvalid};
    wire [1:0]  acready    = {s1_acready, s0_acready};
    wire [1:0]  ac_hs      = acvalid & acready;
    wire [2*AW-1:0] acaddr_f   = {s1_acaddr, s0_acaddr};
    wire [7:0]  acsnoop_f  = {s1_acsnoop, s0_acsnoop};
    wire [1:0]  crvalid    = {s1_crvalid, s0_crvalid};
    wire [1:0]  crready    = {s1_crready, s0_crready};
    wire [1:0]  cr_hs      = crvalid & crready;
    wire [9:0]  crresp_f   = {s1_crresp, s0_crresp};
    wire [1:0]  cr_dt      = {s1_crresp[CR_DT], s0_crresp[CR_DT]};
    wire [1:0]  cr_pd      = {s1_crresp[CR_PD], s0_crresp[CR_PD]};
    wire [1:0]  cdvalid    = {s1_cdvalid, s0_cdvalid};
    wire [1:0]  cdready    = {s1_cdready, s0_cdready};
    wire [1:0]  cd_hs      = cdvalid & cdready;
    wire [1:0]  cdlast     = {s1_cdlast, s0_cdlast};

    wire        mar_hs = mem_arvalid & mem_arready;
    wire        mr_hs  = mem_rvalid & mem_rready;
    wire        maw_hs = mem_awvalid & mem_awready;
    wire        mw_hs  = mem_wvalid & mem_wready;
    wire        mb_hs  = mem_bvalid & mem_bready;
    wire [1:0]  mr_slot = mem_rid[1:0];
    wire        w_abs   = (obs_w_sel == 2'd2);
    wire        w_wdir  = obs_w_sel[0];

    // slot-field accessors
    function automatic [LINE_W-1:0] sl_line(input [SLOTS*LINE_W-1:0] f, input [1:0] s);
        sl_line = f[s*LINE_W +: LINE_W];
    endfunction
    function automatic [2:0] sl_type(input [SLOTS*3-1:0] f, input [1:0] s);
        sl_type = f[s*3 +: 3];
    endfunction
    function automatic [IW-1:0] sl_arid(input [SLOTS*IW-1:0] f, input [1:0] s);
        sl_arid = f[s*IW +: IW];
    endfunction
    function automatic [1:0] d2(input [3:0] f, input d);
        d2 = f[d*2 +: 2];
    endfunction
    function automatic [2:0] d3(input [5:0] f, input d);
        d3 = f[d*3 +: 3];
    endfunction

    // ------------------------------------------------------------------
    // House reset protocol; every environment VALID low under reset
    // ------------------------------------------------------------------
    reg [7:0] f_past_valid = 0;
    always @(posedge clk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    // reset held for exactly the two steps before the environment's
    // contracts arm (they are gated on f_past_valid >= 2): the fabric's
    // harness left rst_n free at step 1, which left the memory free to
    // present a beat nobody asked for in that one cycle -- the pair
    // fabric's verdict bit happened to shield it, onyx's gather counters
    // did not (now also qualified in the RTL)
    initial assume (!rst_n);
    always @(posedge clk) begin
        if (f_past_valid >= 2) assume (rst_n);
        else                   assume (!rst_n);
    end
    always @(*) begin
        if (!rst_n) begin
            as_rst_quiet: assume (!c0_arvalid && !c1_arvalid && !c0_awvalid && !c1_awvalid
                                  && !c0_wvalid && !c1_wvalid && !s0_crvalid && !s1_crvalid
                                  && !s0_cdvalid && !s1_cdvalid && !c0_coh_req_valid
                                  && !c1_coh_req_valid && !c0_coh_done_valid && !c1_coh_done_valid
                                  && !mem_rvalid && !mem_bvalid);
        end
    end

    // ------------------------------------------------------------------
    // Cache model (A-req / A-ar / A-done): per direction the launches whose
    // AR the fabric has not yet taken, in order; the read IDs in flight;
    // the last beat seen per ID; the beat count per ID
    // ------------------------------------------------------------------
    reg [2:0]           q_cnt   [0:1];
    reg [4*LINE_W-1:0]  q_line  [0:1];   // 4 entries, head at [0 +: LINE_W]
    reg [3:0]           q_nd    [0:1];
    reg [7:0]           f_infl  [0:1];   // AR taken, retire not seen
    reg [7:0]           f_last  [0:1];   // last beat seen, retire not seen
    reg [7:0]           f_nd    [0:1];   // the AR was an upgrade's (len 0)
    reg [15:0]          f_beats [0:1];   // 2 bits per ID: beats seen so far

    integer d, p, s, k;
    always @(posedge clk) begin
        if (!rst_n) begin
            for (d = 0; d < 2; d = d + 1) begin
                q_cnt[d]   <= 3'd0;
                q_line[d]  <= '0;
                q_nd[d]    <= 4'd0;
                f_infl[d]  <= 8'd0;
                f_last[d]  <= 8'd0;
                f_nd[d]    <= 8'd0;
                f_beats[d] <= 16'd0;
            end
        end else begin
            for (d = 0; d < 2; d = d + 1) begin
                // launch queue: push a non-WB pulse, pop the AR take
                if (c_ar_hs[d]) begin
                    q_line[d] <= {{LINE_W{1'b0}}, q_line[d][4*LINE_W-1:LINE_W]};
                    q_nd[d]   <= {1'b0, q_nd[d][3:1]};
                end
                if (req_vld[d] && (d3(req_type_f, d) != REQ_WB)) begin
                    for (k = 0; k < 4; k = k + 1) begin
                        if (k == (q_cnt[d] - (c_ar_hs[d] ? 1 : 0))) begin
                            q_line[d][k*LINE_W +: LINE_W] <= line_of(req_addr_f[d*AW +: AW]);
                            q_nd[d][k] <= is_nodata(d3(req_type_f, d));
                        end
                    end
                    q_cnt[d] <= q_cnt[d] + 3'd1 - (c_ar_hs[d] ? 3'd1 : 3'd0);
                end else if (c_ar_hs[d]) begin
                    q_cnt[d] <= q_cnt[d] - 3'd1;
                end
                // read IDs in flight
                if (c_ar_hs[d]) begin
                    f_infl[d][d3(c_arid_f, d)]  <= 1'b1;
                    f_nd[d][d3(c_arid_f, d)]    <= (c_arlen_f[d*8 +: 8] == 8'd0);
                    f_beats[d][d3(c_arid_f, d)*2 +: 2] <= 2'd0;
                end
                if (c_r_hs[d]) begin
                    f_beats[d][d3(c_rid_f, d)*2 +: 2] <= f_beats[d][d3(c_rid_f, d)*2 +: 2] + 2'd1;
                    if (c_rlast[d]) f_last[d][d3(c_rid_f, d)] <= 1'b1;
                end
                if (done_vld[d]) begin
                    f_infl[d][d3(done_id_f, d)] <= 1'b0;
                    f_last[d][d3(done_id_f, d)] <= 1'b0;
                end
            end
        end
    end

    // AXI stability: the previous cycle's AR / AW / W
    reg [1:0]  ar_v_d, ar_r_d, aw_v_d, aw_r_d, w_v_d, w_r_d, w_last_d;
    reg [5:0]  ar_id_d, aw_id_d;
    reg [2*AW-1:0] ar_addr_d, aw_addr_d;
    reg [15:0] ar_len_d, aw_len_d;
    always @(posedge clk) begin
        ar_v_d <= c_arvalid;  ar_r_d <= c_arready;  ar_id_d <= c_arid_f;
        ar_addr_d <= c_araddr_f;  ar_len_d <= c_arlen_f;
        aw_v_d <= c_awvalid;  aw_r_d <= c_awready;  aw_id_d <= c_awid_f;
        aw_addr_d <= c_awaddr_f;  aw_len_d <= c_awlen_f;
        w_v_d <= c_wvalid;  w_r_d <= c_wready;  w_last_d <= c_wlast;
    end

    always @(posedge clk) begin
        if (rst_n && (f_past_valid >= 2)) begin
            for (d = 0; d < 2; d = d + 1) begin
                // A-req
                assume /* as_req_type */ (!req_vld[d]
                    || (d3(req_type_f, d) == REQ_RNSD) || (d3(req_type_f, d) == REQ_RU)
                    || (d3(req_type_f, d) == REQ_CU)   || (d3(req_type_f, d) == REQ_WB));
                assume /* as_req_depth */ (!(req_vld[d] && (d3(req_type_f, d) != REQ_WB))
                    || (q_cnt[d] < 3'd4) || c_ar_hs[d]);
                // A-ar: the oldest untaken launch, its class's length, a fresh ID
                assume /* as_ar_head */ (!c_arvalid[d]
                    || ((q_cnt[d] != 3'd0)
                        && (line_of(c_araddr_f[d*AW +: AW]) == q_line[d][0 +: LINE_W])
                        && (c_arlen_f[d*8 +: 8] == (q_nd[d][0] ? 8'd0 : 8'd3))));
                assume /* as_ar_fresh */ (!c_arvalid[d] || !f_infl[d][d3(c_arid_f, d)]);
                assume /* as_ar_stable */ (!(ar_v_d[d] && !ar_r_d[d])
                    || (c_arvalid[d] && (d3(c_arid_f, d) == d3(ar_id_d, d))
                        && (c_araddr_f[d*AW +: AW] == ar_addr_d[d*AW +: AW])
                        && (c_arlen_f[d*8 +: 8] == ar_len_d[d*8 +: 8])));
                // A-done: an in-flight ID whose last beat has landed
                assume /* as_done */ (!done_vld[d]
                    || (f_infl[d][d3(done_id_f, d)] && f_last[d][d3(done_id_f, d)]));
                // A-wb: AXI stability on the pass-through write side
                assume /* as_aw_stable */ (!(aw_v_d[d] && !aw_r_d[d])
                    || (c_awvalid[d] && (d3(c_awid_f, d) == d3(aw_id_d, d))
                        && (c_awaddr_f[d*AW +: AW] == aw_addr_d[d*AW +: AW])
                        && (c_awlen_f[d*8 +: 8] == aw_len_d[d*8 +: 8])));
                assume /* as_w_stable */ (!(w_v_d[d] && !w_r_d[d])
                    || (c_wvalid[d] && (c_wlast[d] == w_last_d[d])));
            end
        end
    end

    // ------------------------------------------------------------------
    // Snoop responder model (A-snoop): per peer the ACs accepted and not
    // answered (in order, with their snoop type), the CD beats of the
    // oldest since its AC
    // ------------------------------------------------------------------
    reg [1:0] sn_out  [0:1];
    reg [7:0] sn_type [0:1];   // 2 entries x ACSNOOP, head at [3:0]
    reg [2:0] cd_cnt  [0:1];
    always @(posedge clk) begin
        if (!rst_n) begin
            for (p = 0; p < 2; p = p + 1) begin
                sn_out[p]  <= 2'd0;
                sn_type[p] <= 8'd0;
                cd_cnt[p]  <= 3'd0;
            end
        end else begin
            for (p = 0; p < 2; p = p + 1) begin
                if (cr_hs[p]) sn_type[p] <= {4'd0, sn_type[p][7:4]};
                if (ac_hs[p]) begin
                    if ((sn_out[p] - (cr_hs[p] ? 2'd1 : 2'd0)) == 2'd0)
                        sn_type[p][3:0] <= acsnoop_f[p*4 +: 4];
                    else
                        sn_type[p][7:4] <= acsnoop_f[p*4 +: 4];
                end
                sn_out[p] <= sn_out[p] + (ac_hs[p] ? 2'd1 : 2'd0) - (cr_hs[p] ? 2'd1 : 2'd0);
                if (cr_hs[p])      cd_cnt[p] <= 3'd0;
                else if (cd_hs[p]) cd_cnt[p] <= cd_cnt[p] + 3'd1;
            end
        end
    end

    always @(posedge clk) begin
        if (rst_n && (f_past_valid >= 2)) begin
            for (p = 0; p < 2; p = p + 1) begin
                assume /* as_cr_outstanding */ (!crvalid[p] || (sn_out[p] != 2'd0));
                assume /* as_cd_outstanding */ (!cdvalid[p] || ((sn_out[p] != 2'd0) && (cd_cnt[p] < 3'd4)));
                assume /* as_cd_last */ (!cdvalid[p] || (cdlast[p] == (cd_cnt[p] == 3'd3)));
                // a DT verdict after exactly FB beats (the last may share its
                // cycle); a non-DT verdict after none
                assume /* as_cr_cd_pairing */ (!crvalid[p]
                    || (cr_dt[p] ? ((cd_cnt[p] == 3'd4) || ((cd_cnt[p] == 3'd3) && cdvalid[p]))
                                 : (cd_cnt[p] == 3'd0)));
                assume /* as_cr_pd_dt */ (!crvalid[p] || !cr_pd[p] || cr_dt[p]);
                assume /* as_cr_mi_nodt */ (!(crvalid[p] && (sn_type[p][3:0] == ACSNOOP_MAKE_INVALID))
                    || !cr_dt[p]);
            end
        end
    end

    // ------------------------------------------------------------------
    // Memory model (A-mem): reads outstanding by ID, beats seen per ID, one
    // write outstanding (the fabric's port runs one burst at a time)
    // ------------------------------------------------------------------
    reg [3:0] mo;
    reg [7:0] mbeat;   // 2 bits per slot
    reg       wo;
    reg       mr_v_d, mr_r_d, mr_last_d;
    reg [2:0] mr_id_d;
    reg [31:0] mr_data_d;
    reg [1:0] mr_resp_d;
    always @(posedge clk) begin
        if (!rst_n) begin
            mo <= 4'd0;  mbeat <= 8'd0;  wo <= 1'b0;
        end else begin
            if (mar_hs) begin
                mo[mem_arid[1:0]] <= 1'b1;
                mbeat[mem_arid[1:0]*2 +: 2] <= 2'd0;
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
            as_mr_last: assume (!mem_rvalid || (mem_rlast == (mbeat[mr_slot*2 +: 2] == 2'd3)));
            as_mr_stable: assume (!(mr_v_d && !mr_r_d)
                || (mem_rvalid && (mem_rid == mr_id_d) && (mem_rdata == mr_data_d)
                    && (mem_rresp == mr_resp_d) && (mem_rlast == mr_last_d)));
            as_mb_outstanding: assume (!mem_bvalid || wo);
        end
    end

    // ------------------------------------------------------------------
    // Wrapper shadows for the assertions: the previous cycle's table, the
    // beats the requester has received per slot, the DUT's previous-cycle
    // valid/ready pairs
    // ------------------------------------------------------------------
    reg [3:0]  vld_d, rack_d, gathered_d, pd_d, abs_done_d;
    reg [SLOTS*LINE_W-1:0] line_d;
    reg [1:0]  wstate_d, w_sel_d;
    reg [1:0]  done_vld_d;
    reg [5:0]  done_id_d;
    reg        grant_d;
    reg [1:0]  grant_slot_d;
    reg        mar_v_d, mar_r_d;
    reg [2:0]  mar_id_d;
    reg [AW-1:0] mar_addr_d;
    reg [1:0]  r_v_d, r_r_d, r_last_d;
    reg [5:0]  r_id_d;
    reg [63:0] r_data_d;
    reg [3:0]  r_resp_d;
    reg [1:0]  ac_v_d, ac_r_d;
    reg [2*AW-1:0] ac_addr_d;
    reg [7:0]  ac_snoop_d;
    reg [3:0]  h_delivered;   // the requester received the slot's last beat
    always @(posedge clk) begin
        vld_d <= obs_vld;  rack_d <= obs_rack;  gathered_d <= obs_gathered;
        pd_d <= obs_pd;  abs_done_d <= obs_abs_done;  line_d <= obs_line_f;
        wstate_d <= obs_wstate;  w_sel_d <= obs_w_sel;
        done_vld_d <= done_vld;  done_id_d <= done_id_f;
        grant_d <= dbg_grant;  grant_slot_d <= dbg_grant_slot;
        mar_v_d <= mem_arvalid;  mar_r_d <= mem_arready;  mar_id_d <= mem_arid;  mar_addr_d <= mem_araddr;
        r_v_d <= c_rvalid;  r_r_d <= c_rready;  r_last_d <= c_rlast;
        r_id_d <= c_rid_f;  r_data_d <= c_rdata_f;  r_resp_d <= c_rresp_f;
        ac_v_d <= acvalid;  ac_r_d <= acready;  ac_addr_d <= acaddr_f;  ac_snoop_d <= acsnoop_f;
        if (!rst_n) h_delivered <= 4'd0;
        else begin
            for (s = 0; s < SLOTS; s = s + 1) begin
                if (dbg_grant && (dbg_grant_slot == s)) h_delivered[s] <= 1'b0;
                else if (obs_vld[s] && obs_ar_taken[s] && c_r_hs[obs_dir[s]] && c_rlast[obs_dir[s]]
                         && (d3(c_rid_f, obs_dir[s]) == sl_arid(obs_arid_f, s)))
                    h_delivered[s] <= 1'b1;
            end
        end
    end

    // violation vectors (one bit per slot / direction / peer), asserted
    // zero below so a counterexample names the offender
    reg [3:0] v_line_dup, v_grant_locked, v_release, v_rack_src, v_mo, v_free, v_wb_hold;
    reg [1:0] v_arready, v_ar_pair, v_route_mem, v_route_rpl, v_r_stable, v_r_infl, v_r_beats;
    reg [1:0] v_ac_legal, v_ac_stable, v_sn_count, v_cd_slot;
    reg       v_mar_legal, v_mar_stable, v_abs_legal;
    reg [3:0] v_flags;
    reg [1:0] v_engines;
    reg [1:0] wb_sel_now;   // a WB of direction d was selected this edge
    always @(*) begin
        v_line_dup = 4'd0;  v_grant_locked = 4'd0;  v_release = 4'd0;  v_rack_src = 4'd0;
        v_mo = 4'd0;  v_free = 4'd0;  v_wb_hold = 4'd0;
        v_arready = 2'd0;  v_ar_pair = 2'd0;  v_route_mem = 2'd0;  v_route_rpl = 2'd0;
        v_r_stable = 2'd0;  v_r_infl = 2'd0;  v_r_beats = 2'd0;
        v_ac_legal = 2'd0;  v_ac_stable = 2'd0;  v_sn_count = 2'd0;  v_cd_slot = 2'd0;
        v_mar_legal = 1'b0;  v_mar_stable = 1'b0;  v_abs_legal = 1'b0;
        v_flags = 4'd0;  v_engines = 2'd0;
        wb_sel_now = {(wstate_d == W_IDLE) && (obs_wstate == W_AW) && (obs_w_sel == 2'd1),
                      (wstate_d == W_IDLE) && (obs_wstate == W_AW) && (obs_w_sel == 2'd0)};

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
            // P4 the retire bit is set only by the requester's own done pulse naming the slot's ID
            if (!rack_d[s] && obs_rack[s] && vld_d[s]
                && !(done_vld_d[obs_dir[s]] && (d3(done_id_d, obs_dir[s]) == sl_arid(obs_arid_f, s))))
                v_rack_src[s] = 1'b1;
            // P9 the memory bookkeeping matches the reads actually outstanding
            if (mo[s] != (obs_vld[s] & obs_mem_issued[s] & ~obs_mem_done[s]))
                v_mo[s] = 1'b1;
            // P20 a slot frees only once the requester has its last beat and its read is drained
            if (vld_d[s] && !obs_vld[s] && !(h_delivered[s] && !mo[s]))
                v_free[s] = 1'b1;
            // P17 a write-back is selected only when no slot on its line lacks a verdict or
            //     has an absorption pending (the previous cycle's table, the selected AW)
            for (k = 0; k < 2; k = k + 1)
                if (wb_sel_now[k] && vld_d[s] && (sl_line(line_d, s) == line_of(aw_addr_d[k*AW +: AW]))
                    && (!gathered_d[s] || (pd_d[s] && !abs_done_d[s])))
                    v_wb_hold[s] = 1'b1;
        end

        for (d = 0; d < 2; d = d + 1) begin
            // P5 arready only for a granted slot of this direction with its AR untaken
            if (c_arready[d] && !(obs_vld[d2(obs_arw_slot_f, d)]
                                   && (obs_dir[d2(obs_arw_slot_f, d)] == d)
                                   && !obs_ar_taken[d2(obs_arw_slot_f, d)]))
                v_arready[d] = 1'b1;
            // P6 the AR taken is the slot's line and class
            if (c_ar_hs[d] && !((line_of(c_araddr_f[d*AW +: AW]) == sl_line(obs_line_f, d2(obs_arw_slot_f, d)))
                                 && ((c_arlen_f[d*8 +: 8] == 8'd0) == obs_nodata[d2(obs_arw_slot_f, d)])))
                v_ar_pair[d] = 1'b1;
            // P10 a forwarded memory beat belongs to this direction's slot, verdict in, no DT,
            //     carrying the requester's own ID; a replayed beat likewise for a DT / no-data slot
            if (obs_mem_pres[d] && !(mem_rvalid && obs_vld[mr_slot] && (obs_dir[mr_slot] == d)
                                      && obs_gathered[mr_slot] && !obs_dt[mr_slot]
                                      && (d3(c_rid_f, d) == sl_arid(obs_arid_f, mr_slot))))
                v_route_mem[d] = 1'b1;
            if (obs_rpl_pres[d] && !(obs_vld[d2(obs_rpl_slot_f, d)]
                                      && (obs_dir[d2(obs_rpl_slot_f, d)] == d)
                                      && obs_gathered[d2(obs_rpl_slot_f, d)]
                                      && (obs_dt[d2(obs_rpl_slot_f, d)] | obs_nodata[d2(obs_rpl_slot_f, d)])
                                      && !obs_rpl_done[d2(obs_rpl_slot_f, d)]
                                      && (d3(c_rid_f, d) == sl_arid(obs_arid_f, d2(obs_rpl_slot_f, d)))))
                v_route_rpl[d] = 1'b1;
            if (c_rvalid[d] != (obs_mem_pres[d] | obs_rpl_pres[d]))
                v_route_mem[d] = 1'b1;
            // P11 AXI R stability
            if (r_v_d[d] && !r_r_d[d]
                && !(c_rvalid[d] && (d3(c_rid_f, d) == d3(r_id_d, d))
                     && (c_rdata_f[d*32 +: 32] == r_data_d[d*32 +: 32])
                     && (c_rresp_f[d*2 +: 2] == r_resp_d[d*2 +: 2])
                     && (c_rlast[d] == r_last_d[d])))
                v_r_stable[d] = 1'b1;
            // P12 a cache sees exactly the IDs it issued, none after their last beat
            if (c_rvalid[d] && !(f_infl[d][d3(c_rid_f, d)] && !f_last[d][d3(c_rid_f, d)]))
                v_r_infl[d] = 1'b1;
            // P13 every AR gets its beats: one for an upgrade, FB with RLAST on the last for a fill
            if (c_r_hs[d] && !(f_nd[d][d3(c_rid_f, d)]
                                 ? (c_rlast[d] && (f_beats[d][d3(c_rid_f, d)*2 +: 2] == 2'd0))
                                 : (c_rlast[d] == (f_beats[d][d3(c_rid_f, d)*2 +: 2] == 2'd3))))
                v_r_beats[d] = 1'b1;
        end

        for (p = 0; p < 2; p = p + 1) begin
            // P14 an AC names a valid slot of the OTHER direction, not yet accepted, with the
            //     slot's line and the class's snoop
            if (acvalid[p] && !(obs_vld[d2(obs_ac_slot_f, p)]
                                 && (obs_dir[d2(obs_ac_slot_f, p)] == (1 - p))
                                 && !obs_ac_all[d2(obs_ac_slot_f, p)]
                                 && (acaddr_f[p*AW +: AW] == {sl_line(obs_line_f, d2(obs_ac_slot_f, p)), 4'd0})
                                 && (acsnoop_f[p*4 +: 4] == map_snoop(sl_type(obs_type_f, d2(obs_ac_slot_f, p))))))
                v_ac_legal[p] = 1'b1;
            // P15 ACE AC stability
            if (ac_v_d[p] && !ac_r_d[p]
                && !(acvalid[p] && (acaddr_f[p*AW +: AW] == ac_addr_d[p*AW +: AW])
                     && (acsnoop_f[p*4 +: 4] == ac_snoop_d[p*4 +: 4])))
                v_ac_stable[p] = 1'b1;
            // P16 the snoop bookkeeping: outstanding count exact, bounded, CR/CD taken whenever one is outstanding
            if ((d2(obs_sni_cnt_f, p) != sn_out[p]) || (sn_out[p] > 2'd2)
                || (crready[p] != (sn_out[p] != 2'd0))
                || (cdready[p] != (cdvalid[p] && (sn_out[p] != 2'd0))))
                v_sn_count[p] = 1'b1;
            // P21 a CD beat lands in a live slot of the other direction awaiting its verdict
            if (cd_hs[p] && !(obs_vld[d2(obs_sni_head_f, p)]
                               && (obs_dir[d2(obs_sni_head_f, p)] == (1 - p))
                               && !obs_gathered[d2(obs_sni_head_f, p)]))
                v_cd_slot[p] = 1'b1;
        end

        // P22 table flag order: every flag implies the ones before it in the slot's life
        for (s = 0; s < SLOTS; s = s + 1) begin
            if (obs_vld[s] && (
                   (obs_gathered[s] && !obs_ac_all[s])
                || (obs_ac_all[s] != (obs_ac_left[s] == 1'b0)) || (obs_gathered[s] != (obs_cr_left[s] == 1'b0))
                || (obs_dt[s] && !obs_ac_all[s])
                || (obs_pd[s] && !obs_dt[s])
                || (obs_mem_issued[s] && !(obs_ac_all[s] && obs_ar_taken[s] && !obs_nodata[s]))
                || (obs_mem_done[s] && !(obs_mem_issued[s] || (obs_dt[s] && !obs_nodata[s])))
                || (obs_rpl_done[s] && !(obs_gathered[s] && obs_ar_taken[s] && (obs_dt[s] || obs_nodata[s])))
                || (obs_abs_issued[s] && !(obs_pd[s] && obs_gathered[s]))
                || (obs_abs_done[s] && !obs_abs_issued[s])
                || (obs_rack[s] && !obs_ar_taken[s])))
                v_flags[s] = 1'b1;
            // the harness's "requester has its last beat" is the table's delivered bit
            if (obs_vld[s] && (h_delivered[s] != ((obs_dt[s] | obs_nodata[s]) ? obs_rpl_done[s] : obs_mem_done[s])))
                v_flags[s] = 1'b1;
        end
        // P23 the engines' held state names a live slot in the matching phase
        for (d = 0; d < 2; d = d + 1) begin
            if (obs_rpl_vld[d] && !(obs_vld[d2(obs_rpl_slot_f, d)] && (obs_dir[d2(obs_rpl_slot_f, d)] == d)
                                     && obs_gathered[d2(obs_rpl_slot_f, d)] && obs_ar_taken[d2(obs_rpl_slot_f, d)]
                                     && (obs_dt[d2(obs_rpl_slot_f, d)] | obs_nodata[d2(obs_rpl_slot_f, d)])
                                     && !obs_rpl_done[d2(obs_rpl_slot_f, d)]))
                v_engines[d] = 1'b1;
            if (obs_arw_vld[d] && !(obs_vld[d2(obs_arw_slot_f, d)] && (obs_dir[d2(obs_arw_slot_f, d)] == d)
                                     && !obs_ar_taken[d2(obs_arw_slot_f, d)]))
                v_engines[d] = 1'b1;
        end
        if (obs_mar_vld && !(obs_vld[obs_mar_slot] && obs_ar_taken[obs_mar_slot] && obs_ac_all[obs_mar_slot]
                             && !obs_nodata[obs_mar_slot] && !obs_mem_issued[obs_mar_slot]))
            v_engines[0] = 1'b1;
        if ((obs_wstate != W_IDLE) && w_abs
            && !(obs_vld[obs_w_slot] && obs_gathered[obs_w_slot] && obs_pd[obs_w_slot]
                 && obs_abs_issued[obs_w_slot] && !obs_abs_done[obs_w_slot]))
            v_engines[1] = 1'b1;
        if ((obs_wstate == W_IDLE) && (obs_abs_issued & ~obs_abs_done & obs_vld) != 4'd0)
            v_engines[1] = 1'b1;

        // P7 the memory AR: a valid slot, AR taken, AC accepted, data class, not yet issued; the
        //    slot's line, a full line, the slot's ID, no read of that ID outstanding; and no DT
        //    verdict UNLESS the AR was already presented when the verdict landed (a presented
        //    AR is held -- AXI -- and its beats are drained instead)
        if (mem_arvalid && !(!mem_arid[2] && obs_vld[mem_arid[1:0]] && obs_ar_taken[mem_arid[1:0]]
                             && obs_ac_all[mem_arid[1:0]] && !obs_nodata[mem_arid[1:0]]
                             && !obs_mem_issued[mem_arid[1:0]]
                             && (!obs_dt[mem_arid[1:0]]
                                 || (mar_v_d && !mar_r_d))
                             && (mem_araddr == {sl_line(obs_line_f, mem_arid[1:0]), 4'd0})
                             && (mem_arlen == 8'd3) && !mo[mem_arid[1:0]]))
            v_mar_legal = 1'b1;
        // P8 AXI AR stability on the memory port
        if (mar_v_d && !mar_r_d && !(mem_arvalid && (mem_arid == mar_id_d) && (mem_araddr == mar_addr_d)))
            v_mar_stable = 1'b1;
        // P18 an absorption writes a PassDirty slot's line, once, with the fabric's own ID
        if (mem_awvalid && w_abs
            && !(obs_vld[obs_w_slot] && obs_gathered[obs_w_slot] && obs_pd[obs_w_slot]
                 && !obs_abs_done[obs_w_slot]
                 && (mem_awaddr == {sl_line(obs_line_f, obs_w_slot), 4'd0})
                 && (mem_awlen == 8'd3)
                 && (mem_awid == {2'b00, obs_dir[obs_w_slot]})))
            v_abs_legal = 1'b1;
    end

    // Two proof tasks (onyx_ccu.sby): PROVE_CORE is every property
    // whose refutation is local to a few cycles of state (BMC to depth 24 in
    // under an hour); PROVE_BOOK is the three end-to-end bookkeeping
    // properties whose unsatisfiability proof has to carry the whole trace
    // (which ID was taken when, what the snoop queue holds) -- an order of
    // magnitude dearer per step, proven to depth 16, past every cover's
    // witness and one slot lifetime plus its reuse.
`ifdef PROVE_CORE
    always @(posedge clk) begin
        if (rst_n && (f_past_valid >= 2)) begin
            ap_line_unique:   assert (v_line_dup == 4'd0);
            ap_grant_unlocked: assert (v_grant_locked == 4'd0);
            ap_grant_one_ar:  assert (!dbg_grant || !obs_arw_vld[dbg_grant_dir]);
            ap_mo:            assert (v_mo == 4'd0);
            ap_arready_slot:  assert (v_arready == 2'd0);
            ap_ar_pairing:    assert (v_ar_pair == 2'd0);
            ap_mar_legal:     assert (!v_mar_legal);
            ap_route_mem:     assert (v_route_mem == 2'd0);
            ap_route_rpl:     assert (v_route_rpl == 2'd0);
            ap_ac_legal:      assert (v_ac_legal == 2'd0);
            ap_sn_count:      assert (v_sn_count == 2'd0);
            ap_abs_legal:     assert (!v_abs_legal);
            ap_no_pend_ovf:   assert (obs_pend_ovf == 2'd0);
            // the launches the cache holds with their AR untaken are exactly the
            // fabric's pending pulses plus the one granted and awaiting its AR
            ap_pend_count:    assert ((q_cnt[0] == (d3(obs_pend_cnt_f, 0) + {2'd0, obs_arw_vld[0]}))
                                      && (q_cnt[1] == (d3(obs_pend_cnt_f, 1) + {2'd0, obs_arw_vld[1]})));
            ap_wstate_legal:  assert (!((obs_wstate != W_IDLE) && (obs_w_sel == 2'd3)));
            ap_table_flags:   assert (v_flags == 4'd0);
            ap_engines_live:  assert (v_engines == 2'd0);
        end
        if (rst_n && (f_past_valid >= 3)) begin
            ap_release_after_retire: assert (v_release == 4'd0);
            ap_rack_source:   assert (v_rack_src == 4'd0);
            ap_free_complete: assert (v_free == 4'd0);
            ap_wb_select_hold: assert (v_wb_hold == 4'd0);
            ap_mar_stable:    assert (!v_mar_stable);
            ap_r_stable:      assert (v_r_stable == 2'd0);
            ap_ac_stable:     assert (v_ac_stable == 2'd0);
        end
    end
`endif
`ifdef PROVE_BOOK
    always @(posedge clk) begin
        if (rst_n && (f_past_valid >= 2)) begin
            ap_r_inflight:    assert (v_r_infl == 2'd0);
            ap_r_beats:       assert (v_r_beats == 2'd0);
            ap_cd_slot:       assert (v_cd_slot == 2'd0);
        end
    end
`endif

    // ------------------------------------------------------------------
    // Covers: the scenarios the properties are meant to range over
    // ------------------------------------------------------------------
    reg [1:0]        blk_vld;          // direction d once waited behind a held line
    reg [2*LINE_W-1:0] blk_line_f;
    reg [1:0]        wbblk_seen;       // direction d's WB was once blocked
    reg [3:0]        freed_seen;
    always @(posedge clk) begin
        if (!rst_n) begin
            blk_vld <= 2'd0;  blk_line_f <= '0;  wbblk_seen <= 2'd0;  freed_seen <= 4'd0;
        end else begin
            for (d = 0; d < 2; d = d + 1) begin
                if (obs_cand_locked[d] && dbg_pend_vld[d]) begin
                    // the pending queue's head waits behind a held line
                    blk_vld[d] <= 1'b1;
                    blk_line_f[d*LINE_W +: LINE_W] <= line_of(obs_cand_addr_f[d*AW +: AW]);
                end
                if (obs_wb_blocked[d] && c_awvalid[d]) wbblk_seen[d] <= 1'b1;
            end
            freed_seen <= freed_seen | (vld_d & ~obs_vld);
        end
    end

    always @(posedge clk) begin
        if (rst_n && (f_past_valid >= 3)) begin
            cp_two_dirs_live: cover (((obs_vld & obs_dir) != 4'd0) && ((obs_vld & ~obs_dir) != 4'd0));
            cp_three_live:    cover ((obs_vld == 4'b0111) || (obs_vld == 4'b1011)
                                     || (obs_vld == 4'b1101) || (obs_vld == 4'b1110));
            cp_conflict_regrant: cover (dbg_grant && blk_vld[dbg_grant_dir]
                                        && (line_of(dbg_grant_addr) == blk_line_f[dbg_grant_dir*LINE_W +: LINE_W])
                                        && (freed_seen != 4'd0));
            cp_locked_wait:   cover ((obs_cand_locked & dbg_pend_vld) != 2'd0);
            cp_pend_two:      cover ((d3(obs_pend_cnt_f, 0) >= 3'd2) || (d3(obs_pend_cnt_f, 1) >= 3'd2));
            cp_dt_drop:       cover (obs_mr_drop && mem_rready);
            cp_dt_suppress:   cover ((cr_hs[0] && cr_dt[0] && !obs_mem_issued[d2(obs_sni_head_f, 0)])
                                     || (cr_hs[1] && cr_dt[1] && !obs_mem_issued[d2(obs_sni_head_f, 1)]));
            cp_pass_through:  cover (c_r_hs[0] && obs_mem_pres[0] && c_rlast[0]);
            cp_replay_last:   cover (c_r_hs[1] && obs_rpl_pres[1] && c_rlast[1] && !obs_nodata[d2(obs_rpl_slot_f, 1)]);
            cp_nodata_beat:   cover (c_r_hs[0] && obs_rpl_pres[0] && obs_nodata[d2(obs_rpl_slot_f, 0)]);
            cp_abs_landed:    cover (mb_hs && w_abs);
            cp_wb_landed:     cover (mb_hs && !w_abs);
            cp_wb_blocked_then_hs: cover (maw_hs && !w_abs && wbblk_seen[w_wdir]);
            cp_both_r:        cover (c_rvalid[0] && c_rvalid[1]);
            cp_rpl_behind_mem: cover (obs_rpl_vld[0] && obs_mem_pres[0]);
            cp_sn_two:        cover ((sn_out[0] == 2'd2) || (sn_out[1] == 2'd2));
            cp_mar_stall:     cover (mem_arvalid && !mem_arready);
            cp_two_reads_out: cover ((mo == 4'b0011) || (mo == 4'b0101) || (mo == 4'b0110)
                                     || (mo == 4'b1001) || (mo == 4'b1010) || (mo == 4'b1100));
            cp_slot_freed:    cover ((vld_d & ~obs_vld) != 4'd0);
        end
    end

endmodule
