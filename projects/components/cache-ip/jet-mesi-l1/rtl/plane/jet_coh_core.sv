// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_coh_core
// Purpose:
//   Coherence-core plane for the jet lockup-free MESI L1 (cache-ip plane
//   restructure, Task 4): the jet control blocks (jet_control + jet_mshr
//   + jet_wb_buffer), the UNCHANGED common-ip slice (l1_tag_array,
//   l1_data_array, l1_repl, l1_fill, l1_drain, l1_monlite), the J7
//   jet_monlite observer, and the integration logic that binds them.
//   The CPU plane (jet_cpu_plane) and the fabric planes (l1_axi4_plane /
//   l1_ace_plane) are separate named boundaries; this module consumes
//   the lookup seam and the fabric snoop seam, and drives the engine
//   seam. Extracted from jet_top.sv / jet_ace_top.sv by move-don't-edit;
//   the sn_want AC-pending throttle enters as a port from the fabric
//   plane.
//
// Documentation: projects/components/cache-ip/jet-mesi-l1/docs/jet_mas/ch01_overview/02_port_list.md
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-11-01

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: jet_coh_core
//==============================================================================
// Description:
//   Hierarchy (MAS ch01 hierarchy, coherence core extracted):
//
//     jet_coh_core
//     |-- u_control      jet_control      the lookup/commit core
//     |-- u_mshr         jet_mshr         J1 miss-status file
//     |-- u_wb           jet_wb_buffer    J5 dirty-victim capture
//     |-- u_tag          l1_tag_array     port A CPU/fill, port B snoop
//     |-- u_data         l1_data_array    port A CPU/fill beats, port B
//     |--                                  victim capture + snoop CD
//     |-- u_repl         l1_repl          victim-way select + policy state
//     |-- u_fill         l1_fill          AXI4 read sequencing -> fub_axi_*
//     |-- u_drain        l1_drain         AXI4 write sequencing -> fub_axi_*
//     |-- u_monlite      l1_monlite       drop-and-count MonBus observer
//     `-- u_jet_monlite  jet_monlite      J7 MSHR/occupancy observer
//
//   Integration glue that is NOT pure wiring (all of it the launch level,
//   none of it touching common-ip), moved verbatim from the jet tops:
//
//   * Fill-launch adapter.  jet_control's fill contract is start-held-
//     until-accept; l1_fill has no accept output (it is a
//     single-outstanding F_IDLE -> F_AR -> F_R -> F_DONE engine).  The
//     adapter accepts a presented launch exactly when the engine is idle
//     AND no victim capture is streaming (cap_busy_o) AND no dirty-victim
//     capture opens this very cycle (alloc with wb_valid) -- the MAS
//     ch02/01 fill-engine contract ("start no beat stream while
//     cap_busy_o is high") enforced at the launch, since l1_fill cannot
//     be gated.  The adapter tracks the in-flight fill's MSHR identity
//     (alloc-order, one-deep pending record: an alloc can only exist
//     unlaunched while the launch register holds it, and the classify
//     holds new allocs in that window) to route the engine's beats to
//     jet_control as {entry index, beat number}.
//
//   * Fill-class map: jet's 2-bit JET_CLS_* onto l1_fill's 3-bit
//     amber_ace_req_t (RNSD -> READ_NOT_SHARED_DIRTY, RU -> READ_UNIQUE,
//     CU -> CLEAN_UNIQUE).
//
//   * Data-array W-port mux: fill beats (adapter way/set + engine
//     beat/data) win over jet_control's commit-merge/write-hit port --
//     the MAS fill > commit > hit order; jet_control yields while a beat
//     is presented, so the two never actually contend (same landed idiom
//     as l1_core's mux and the jet_control unit harness).
//
//   * Pair-rig coherence sideband (DECISION D-8) with the drain-collision
//     replay: the sideband carries ONE event per cycle; jet (unlike
//     amber's blocking FSM, where MISS_DRAIN and MISS_FILL are separate
//     states) fires the drain arbiter and the launch adapter concurrently
//     -- the cycle a victim capture completes, drain_start_o and the held
//     fill's accept coincide.  The fill launch wins the slot (the fabric
//     queues it -- dropping it would hang the fill's AR); the drain's
//     WRITE_BACK pulse replays the next cycle (the fabric never queues
//     WRITE_BACK, so the one-cycle delay is invisible downstream).
//
//   * l1_monlite tap encoder (observation only, drives nothing in the
//     datapath): jet has no blocking ctrl FSM, so the observer's
//     amber-style state-entry taps are fed by a pseudo-state encoder over
//     the jet events (init walk / hit / alloc / launch / drain /
//     commit-install / snoop effect).  Read-only hierarchical taps into
//     u_control follow the sanctioned l1_core pattern.  The J7 event
//     classes are a future monlite extension (MAS ch04).
//
//   Fill beats land in the data array at {claimed set, beat} of the
//   in-flight entry's claimed victim way; the claim context lives in
//   jet_control and the adapter (read-only hierarchical taps, the
//   sanctioned l1_core pattern).
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / WAYS / LINE_BYTES / BUS_WIDTH / REPL_POLICY /
//   AXI_ID_WIDTH / AXI_USER_WIDTH / USE_MONITOR:
//     as jet_top (geometry per l1_pkg defaults)
//   MSHR_COUNT / VICTIM_DEPTH:
//     J1 / J5 geometry (jet_pkg defaults)
//
//------------------------------------------------------------------------------
// Notes:
//   - Single clock / active-low reset (aclk / aresetn). The plane is
//     reset-synchronized by its top (jet_top / jet_ace_top), so this
//     module consumes the synchronized reset.
//   - The fub_axi_* ports are the raw engine-side master pins; the
//     fabric plane closes the monlite transports.
//   - fill_ar_done is the top-level tap of the fabric plane's m_axi AR
//     handshake (the engines' fill-launch progress marker).
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: jet_top, jet_ace_top
//   - Instantiates: jet_control, jet_mshr, jet_wb_buffer, l1_tag_array,
//     l1_data_array, l1_repl, l1_fill, l1_drain, l1_monlite, jet_monlite
//   - Package: jet_pkg, l1_pkg
//
//==============================================================================

module jet_coh_core
    import jet_pkg::*;
    import l1_pkg::*;
#(
    parameter int ADDR_WIDTH     = AMBER_ADDR_WIDTH,
    parameter int SETS           = AMBER_SETS,
    parameter int WAYS           = AMBER_WAYS,
    parameter int LINE_BYTES     = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH      = AMBER_BUS_WIDTH,
    parameter int REPL_POLICY    = int'(AMBER_REPL_LRU),
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    parameter bit USE_MONITOR    = 1'b1,
    parameter int MSHR_COUNT     = jet_pkg::MSHR_COUNT,
    parameter int VICTIM_DEPTH   = jet_pkg::VICTIM_DEPTH,
    // Data array in block RAM (registered read, one-cycle address lead in
    // jet_control) -- the FPGA default; 0 keeps the combinational LUTRAM
    // read for a comparison build.
    parameter bit DATA_SYNC_READ = 1'b1,
    localparam int SET_W       = $clog2(SETS),
    localparam int OFF_W       = $clog2(LINE_BYTES),
    localparam int TAG_W       = ADDR_WIDTH - SET_W - OFF_W,
    localparam int TSW         = TAG_W + 3,
    localparam int STRB_W      = BUS_WIDTH / 8,
    localparam int FILL_BEATS  = LINE_BYTES / STRB_W,
    localparam int BEAT_W      = $clog2(FILL_BEATS),
    localparam int WAY_W       = $clog2(WAYS),
    localparam int MEM_ADDR_W  = SET_W + BEAT_W,
    localparam int LINE_W      = ADDR_WIDTH - OFF_W,
    localparam int MW          = $clog2(MSHR_COUNT),
    localparam int RSP_DEPTH   = MSHR_COUNT + 2,
    localparam int SEQ_W       = $clog2(RSP_DEPTH),
    localparam int WB_W        = (VICTIM_DEPTH <= 2) ? 1 : $clog2(VICTIM_DEPTH),
    localparam int LINE_BITS   = LINE_BYTES * 8,
    localparam int IW          = AXI_ID_WIDTH,
    localparam int UW          = AXI_USER_WIDTH
)(
    input  logic                        aclk,
    input  logic                        aresetn,

    // ------------------------------------------------------------------
    // Lookup seam from the CPU plane (the D-6 skid's held request)
    // ------------------------------------------------------------------
    input  logic                        lkup_valid,
    input  logic [ADDR_WIDTH-1:0]       lkup_addr,
    input  logic                        lkup_we,
    input  logic [STRB_W-1:0]           lkup_be,
    input  logic [BUS_WIDTH-1:0]        lkup_wdata,
    output logic                        lkup_ready,

    // CTRL_ERROR dead-stop (the CPU plane gates its request ready)
    output logic                        ctrl_error,

    // ------------------------------------------------------------------
    // Response-sequencer seam to the CPU plane (J4: in-issue-order
    // release; the tag is granted at the lookup accept)
    // ------------------------------------------------------------------
    output logic                        ctrl_tag_req,
    input  logic                        rsp_tag_gnt,
    input  logic [SEQ_W-1:0]            rsp_tag,
    output logic                        ctrl_cpl_valid,
    output logic [SEQ_W-1:0]            ctrl_cpl_tag,
    output logic [BUS_WIDTH-1:0]        ctrl_cpl_data,

    // ------------------------------------------------------------------
    // Fabric (snoop) seam to the fabric plane (names per l1_axi4_plane /
    // l1_ace_plane, so the tops wire the seam direct)
    // ------------------------------------------------------------------
    input  logic                        ctrl_snoop_req,
    input  logic                        sn_want_i,
    input  logic [2:0]                  ctrl_snoop_type,
    input  logic [ADDR_WIDTH-1:0]       ctrl_snoop_addr,
    output logic                        ctrl_snoop_ready,
    output logic                        ctrl_snoop_safe,
    output logic [AMBER_CRRESP_WIDTH-1:0] ctrl_crresp,
    output logic [BUS_WIDTH-1:0]        ctrl_cddata,
    output logic                        ctrl_cdlast,
    output logic                        ctrl_cdvalid,
    input  logic                        ctrl_cdready,

    // ------------------------------------------------------------------
    // fub_axi read master side (l1_fill -> the fabric plane's transports)
    // ------------------------------------------------------------------
    output logic [IW-1:0]               fub_axi_arid,
    output logic [ADDR_WIDTH-1:0]       fub_axi_araddr,
    output logic [7:0]                  fub_axi_arlen,
    output logic [2:0]                  fub_axi_arsize,
    output logic [1:0]                  fub_axi_arburst,
    output logic                        fub_axi_arlock,
    output logic [3:0]                  fub_axi_arcache,
    output logic [2:0]                  fub_axi_arprot,
    output logic [3:0]                  fub_axi_arqos,
    output logic [3:0]                  fub_axi_arregion,
    output logic [UW-1:0]               fub_axi_aruser,
    output logic                        fub_axi_arvalid,
    input  logic                        fub_axi_arready,
    input  logic [IW-1:0]               fub_axi_rid,
    input  logic [BUS_WIDTH-1:0]        fub_axi_rdata,
    input  logic [3:0]                  fub_axi_rresp,
    input  logic                        fub_axi_rlast,
    input  logic [UW-1:0]               fub_axi_ruser,
    input  logic                        fub_axi_rvalid,
    output logic                        fub_axi_rready,

    // ------------------------------------------------------------------
    // fub_axi write master side (l1_drain -> the fabric plane)
    // ------------------------------------------------------------------
    output logic [IW-1:0]               fub_axi_awid,
    output logic [ADDR_WIDTH-1:0]       fub_axi_awaddr,
    output logic [7:0]                  fub_axi_awlen,
    output logic [2:0]                  fub_axi_awsize,
    output logic [1:0]                  fub_axi_awburst,
    output logic                        fub_axi_awlock,
    output logic [3:0]                  fub_axi_awcache,
    output logic [2:0]                  fub_axi_awprot,
    output logic [3:0]                  fub_axi_awqos,
    output logic [3:0]                  fub_axi_awregion,
    output logic [UW-1:0]               fub_axi_awuser,
    output logic                        fub_axi_awvalid,
    input  logic                        fub_axi_awready,
    output logic [BUS_WIDTH-1:0]        fub_axi_wdata,
    output logic [STRB_W-1:0]           fub_axi_wstrb,
    output logic                        fub_axi_wlast,
    output logic [UW-1:0]               fub_axi_wuser,
    output logic                        fub_axi_wvalid,
    input  logic                        fub_axi_wready,
    input  logic [IW-1:0]               fub_axi_bid,
    input  logic [1:0]                  fub_axi_bresp,
    input  logic [UW-1:0]               fub_axi_buser,
    input  logic                        fub_axi_bvalid,
    output logic                        fub_axi_bready,

    // ------------------------------------------------------------------
    // Fill-launch progress: the top taps the fabric plane's m_axi AR
    // handshake (jet_control's r_ar_done marker)
    // ------------------------------------------------------------------
    input  logic                        fill_ar_done,

    // ------------------------------------------------------------------
    // Pair-rig coherence sideband (DECISION D-8; one pulse per fill
    // launch accept / dirty-drain start, with the collision replay)
    // ------------------------------------------------------------------
    output logic                        coh_req_valid,
    output logic [ADDR_WIDTH-1:0]       coh_req_addr,
    output logic [2:0]                  coh_req_type,

    // ------------------------------------------------------------------
    // MonBus observation (l1_monlite cache events + the J7 jet_monlite
    // stream; the top merges both with the fabric-plane observers)
    // ------------------------------------------------------------------
    input  logic [63:0]                 mon_time,
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [127:0]                mon_packet,
    output logic [63:0]                 mon_timestamp,
    output logic [7:0]                  mon_dropped,
    output logic                        j7_mon_valid,
    input  logic                        j7_mon_ready,
    output logic [127:0]                j7_mon_packet,
    output logic [63:0]                 j7_mon_timestamp,

    // ------------------------------------------------------------------
    // Status / observability
    // ------------------------------------------------------------------
    output logic                        init_busy,
    output logic [3:0]                  ctrl_state,
    output logic                        busy
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the core blocks)
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("jet_coh_core: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("jet_coh_core: LINE_BYTES must be a power of two");
        if ((BUS_WIDTH % 8) != 0)
            $error("jet_coh_core: BUS_WIDTH must be a multiple of 8");
        if (WAYS < 2)
            $error("jet_coh_core: WAYS must be >= 2");
    end

    // ------------------------------------------------------------------
    // control <-> block wiring
    // ------------------------------------------------------------------
    // tag array port A
    logic [SET_W-1:0]           ctrl_tag_a_set;
    logic [WAYS-1:0][TSW-1:0]   ctrl_tag_a_tag_state;
    logic                       ctrl_tag_a_wr_en;
    logic [WAYS-1:0]            ctrl_tag_a_wr_way_onehot;
    logic [SET_W-1:0]           ctrl_tag_a_wr_set;
    logic [TSW-1:0]             ctrl_tag_a_wr_tag_state;
    // tag array port B (snoop probe)
    logic                       ctrl_tag_b_req;
    logic [SET_W-1:0]           ctrl_tag_b_set;
    logic [WAYS-1:0][TSW-1:0]   ctrl_tag_b_tag_state;
    // data array port A
    logic [MEM_ADDR_W-1:0]      ctrl_dat_a_addr;
    logic [WAY_W-1:0]           ctrl_dat_a_way;
    logic [BUS_WIDTH-1:0]       ctrl_dat_a_rdata;
    logic                       ctrl_dat_a_wr_en;
    logic [WAYS-1:0]            ctrl_dat_a_wr_way_onehot;
    logic [MEM_ADDR_W-1:0]      ctrl_dat_a_wr_addr;
    logic [BUS_WIDTH-1:0]       ctrl_dat_a_wr_wdata;
    logic [STRB_W-1:0]          ctrl_dat_a_wr_be;
    // data array port B (victim capture + snoop CD)
    logic [MEM_ADDR_W-1:0]      ctrl_dat_b_addr;
    logic [WAY_W-1:0]           ctrl_dat_b_way;
    logic [BUS_WIDTH-1:0]       ctrl_dat_b_rdata;
    // repl
    logic                       ctrl_repl_req;
    logic [SET_W-1:0]           ctrl_repl_set;
    logic [WAY_W-1:0]           repl_victim_way;
    logic                       ctrl_repl_hit;
    logic                       ctrl_repl_update;
    logic [WAY_W-1:0]           ctrl_repl_hit_way;
    // classify observability (MonBus taps + status)
    logic                       ctrl_lkup_hit;
    logic                       ctrl_lkup_merge;
    logic                       ctrl_lkup_miss_alloc;
    logic                       ctrl_lkup_upgrade;
    logic                       ctrl_lkup_stall;
    logic [2:0]                 ctrl_lkup_stall_reason;
    logic                       ctrl_lkup_wr_yield;
    logic                       ctrl_cap_busy;
    logic                       ctrl_cmt_busy;
    logic                       ctrl_init_busy;
    // MSHR: control -> file
    logic                       ctrl_mshr_alloc;
    logic [LINE_W-1:0]          ctrl_mshr_alloc_line;
    logic [SET_W-1:0]           ctrl_mshr_alloc_set;
    logic [1:0]                 ctrl_mshr_alloc_cls;
    logic                       ctrl_mshr_alloc_install;
    logic [WAY_W-1:0]           ctrl_mshr_alloc_victim_way;
    logic [WB_W-1:0]            ctrl_mshr_alloc_wb_slot;
    logic                       ctrl_mshr_alloc_wb_valid;
    logic [SEQ_W-1:0]           ctrl_mshr_alloc_seq;
    logic [LINE_W-1:0]          ctrl_mshr_lkup_line;
    logic [MW-1:0]              ctrl_mshr_cpl_idx;
    logic                       ctrl_mshr_merge;
    logic [MW-1:0]              ctrl_mshr_merge_idx;
    logic [SEQ_W-1:0]           ctrl_mshr_merge_seq;
    logic                       ctrl_mshr_beat;
    logic [MW-1:0]              ctrl_mshr_beat_idx;
    logic [BEAT_W-1:0]          ctrl_mshr_beat_num;
    logic                       ctrl_mshr_retire;
    logic [MW-1:0]              ctrl_mshr_retire_idx;
    // MSHR: file -> control
    logic                       mshr_alloc_gnt;
    logic [MW-1:0]              mshr_alloc_idx;
    logic                       mshr_full;
    logic                       mshr_set_full;
    logic                       mshr_lkup_reg_match;
    logic [MW-1:0]              mshr_lkup_reg_match_idx;
    logic [1:0]                 mshr_lkup_reg_match_cls;
    logic [MW:0]                mshr_cpl_merge_count;
    logic [LINE_W-1:0]          mshr_cpl_line;
    logic [1:0]                 mshr_cpl_pend_eff;
    logic [MSHR_COUNT*SEQ_W-1:0] mshr_cpl_merge_seqs;
    logic [MW:0]                mshr_occupancy;
    // MSHR: J7 MonBus event taps
    logic                       mshr_alloc_ev;
    logic [SET_W-1:0]           mshr_alloc_ev_set;
    logic [1:0]                 mshr_alloc_ev_cls;
    logic [MW-1:0]              mshr_alloc_ev_idx;
    logic                       mshr_merge_ev;
    logic [MW-1:0]              mshr_merge_ev_idx;
    logic [MW:0]                mshr_merge_ev_depth;
    logic                       mshr_retire_ev;
    logic [MW-1:0]              mshr_retire_ev_idx;
    // MSHR: snoop probe + deferred-effect record
    logic [LINE_W-1:0]          ctrl_mshr_sn_line;
    logic                       ctrl_mshr_sn_eff;
    logic [MW-1:0]              ctrl_mshr_sn_eff_idx;
    logic [1:0]                 ctrl_mshr_sn_eff_value;
    logic                       mshr_sn_match;
    logic [MW-1:0]              mshr_sn_match_idx;
    logic [FILL_BEATS-1:0]      mshr_sn_beats_rcvd;
    logic                       mshr_sn_install;
    // WB buffer
    logic                       ctrl_wb_cap;
    logic [LINE_W-1:0]          ctrl_wb_cap_line;
    logic                       ctrl_wb_cap_beat;
    logic [BUS_WIDTH-1:0]       ctrl_wb_cap_beat_data;
    logic                       wb_cap_gnt;
    logic [WB_W-1:0]            wb_cap_slot;
    logic                       wb_full;
    logic [LINE_W-1:0]          ctrl_wb_sn_line;
    logic                       wb_sn_hit;
    logic [1:0]                 ctrl_wb_sn_eff;
    logic [WB_W-1:0]            wb_sn_match_idx;
    logic                       ctrl_wb_sn_lock;
    logic [WB_W-1:0]            ctrl_wb_sn_rd_slot;
    logic [BEAT_W-1:0]          ctrl_wb_sn_rd_beat;
    logic [BUS_WIDTH-1:0]       wb_sn_rd_data;
    logic                       wb_sn_bresp_cycle;
    logic                       wb_drain_valid;
    logic [ADDR_WIDTH-1:0]      wb_drain_addr;
    logic [BEAT_W-1:0]          wb_drain_beat_idx;
    logic [BUS_WIDTH-1:0]       wb_drain_beat_data;
    logic [$clog2(VICTIM_DEPTH+1)-1:0] wb_occupancy;
    logic                       ctrl_drain_start;
    logic                       eng_drain_done;
    // fill engine (control side)
    logic                       ctrl_fill_start;
    logic [ADDR_WIDTH-1:0]      ctrl_fill_addr;
    logic [1:0]                 ctrl_fill_cls;
    logic                       w_fill_accept;
    logic                       eng_fill_done;
    logic                       eng_fill_pass_dirty;
    logic                       eng_fill_inflight;
    logic                       eng_fill_beat_valid;
    logic [BUS_WIDTH-1:0]       eng_fill_beat_data;
    logic [BEAT_W-1:0]          eng_fill_beat_idx;

    // ------------------------------------------------------------------
    // Fill-launch adapter (the MAS ch02/01 engine contract, enforced at
    // the launch since l1_fill cannot be gated):
    //   accept a presented launch exactly when
    //     - the engine is idle (single-outstanding FSM: the adapter's
    //       busy register tracks F_IDLE occupancy exactly -- set at the
    //       accept, cleared at fill_done, both in lockstep with the
    //       engine's own state transitions), AND
    //     - no victim capture is streaming (cap_busy_o), AND
    //     - no dirty-victim capture opens this very cycle (the alloc's
    //       wb_valid: cap_busy_o only rises next cycle, and an immediate
    //       launch could put the first fill beat ahead of the capture's
    //       last read of the doomed victim's way).
    //   The in-flight fill's MSHR identity rides r_flight_*: captured at
    //   the accept from the same-cycle alloc pins (fast path) or the
    //   one-deep pending record (held-launch path; allocs are held while
    //   a launch pends, so one record suffices).  CU launches carry no
    //   entry and no beats.
    // ------------------------------------------------------------------
    logic                  r_eng_busy;
    logic                  r_pend_valid;
    logic [MW-1:0]         r_pend_idx;
    logic [SET_W-1:0]      r_pend_set;
    logic [WAY_W-1:0]      r_pend_way;
    logic [MW-1:0]         r_flight_idx;
    logic [SET_W-1:0]      r_flight_set;
    logic [WAY_W-1:0]      r_flight_way;
    logic [2:0]            eng_fill_class;

    assign w_fill_accept = ctrl_fill_start & ~r_eng_busy & ~ctrl_cap_busy
                           & ~(ctrl_mshr_alloc & ctrl_mshr_alloc_wb_valid);

    always_comb begin
        unique case (ctrl_fill_cls)
            JET_CLS_RU:   eng_fill_class = AMBER_ACE_READ_UNIQUE;
            JET_CLS_CU:   eng_fill_class = AMBER_ACE_CLEAN_UNIQUE;
            default:      eng_fill_class = AMBER_ACE_READ_NOT_SHARED_DIRTY;
        endcase
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_eng_busy   <= 1'b0;
            r_pend_valid <= 1'b0;
            r_pend_idx   <= '0;
            r_pend_set   <= '0;
            r_pend_way   <= '0;
            r_flight_idx <= '0;
            r_flight_set <= '0;
            r_flight_way <= '0;
        end else begin
            // alloc record (the launch may be held; the classify blocks
            // further allocs while the launch register is occupied, so one
            // pending record is exact)
            if (ctrl_mshr_alloc & mshr_alloc_gnt) begin
                r_pend_valid <= 1'b1;
                r_pend_idx   <= mshr_alloc_idx;
                r_pend_set   <= ctrl_mshr_alloc_set;
                r_pend_way   <= ctrl_mshr_alloc_victim_way;
            end
            if (w_fill_accept) begin
                r_eng_busy <= 1'b1;
                if (ctrl_fill_cls != JET_CLS_CU) begin
                    if (ctrl_mshr_alloc & mshr_alloc_gnt) begin
                        // fast path: the alloc's own launch, same cycle
                        r_flight_idx <= mshr_alloc_idx;
                        r_flight_set <= ctrl_mshr_alloc_set;
                        r_flight_way <= ctrl_mshr_alloc_victim_way;
                    end else begin
                        r_flight_idx <= r_pend_idx;
                        r_flight_set <= r_pend_set;
                        r_flight_way <= r_pend_way;
                    end
                    // the pending record is consumed by this accept (on
                    // the fast path the same-cycle alloc's record is
                    // never launched-from-held)
                    r_pend_valid <= 1'b0;
                end
            end else if (eng_fill_done) begin
                r_eng_busy <= 1'b0;
            end
        end
    )

    // ------------------------------------------------------------------
    // Data-array W-port mux: fill beats > control (commit store merge /
    // write hit).  jet_control yields while a beat is presented
    // (fill_beat_valid_i), so the two never contend.
    // ------------------------------------------------------------------
    logic [WAYS-1:0]         fill_way_onehot;
    logic                    dat_wr_en;
    logic [WAYS-1:0]         dat_wr_way_onehot;
    logic [MEM_ADDR_W-1:0]   dat_wr_addr;
    logic [BUS_WIDTH-1:0]    dat_wr_wdata;
    logic [STRB_W-1:0]       dat_wr_be;

    always_comb begin
        for (int w = 0; w < WAYS; w++) begin
            fill_way_onehot[w] = (r_flight_way == WAY_W'(w));
        end
    end

    assign dat_wr_en         = eng_fill_beat_valid | ctrl_dat_a_wr_en;
    assign dat_wr_way_onehot = eng_fill_beat_valid ? fill_way_onehot
                                                   : ctrl_dat_a_wr_way_onehot;
    assign dat_wr_addr       = eng_fill_beat_valid
                               ? {r_flight_set, eng_fill_beat_idx}
                               : ctrl_dat_a_wr_addr;
    assign dat_wr_wdata      = eng_fill_beat_valid ? eng_fill_beat_data
                                                   : ctrl_dat_a_wr_wdata;
    assign dat_wr_be         = eng_fill_beat_valid ? {STRB_W{1'b1}}
                                                   : ctrl_dat_a_wr_be;

    // ------------------------------------------------------------------
    // jet_control (the lookup/commit core)
    // ------------------------------------------------------------------
    jet_control #(
        .ADDR_WIDTH   (ADDR_WIDTH),
        .SETS         (SETS),
        .WAYS         (WAYS),
        .LINE_BYTES   (LINE_BYTES),
        .BUS_WIDTH    (BUS_WIDTH),
        .MSHR_COUNT   (MSHR_COUNT),
        .VICTIM_DEPTH (VICTIM_DEPTH),
        .DATA_SYNC_READ (DATA_SYNC_READ)
    ) u_control (
        .clk                     (aclk),
        .rst_n                   (aresetn),
        .init_busy_o             (ctrl_init_busy),
        .lkup_valid_i            (lkup_valid),
        .lkup_addr_i             (lkup_addr),
        .lkup_we_i               (lkup_we),
        .lkup_be_i               (lkup_be),
        .lkup_wdata_i            (lkup_wdata),
        .lkup_ready_o            (lkup_ready),
        .lkup_hit_o              (ctrl_lkup_hit),
        .lkup_merge_o            (ctrl_lkup_merge),
        .lkup_miss_alloc_o       (ctrl_lkup_miss_alloc),
        .lkup_upgrade_o          (ctrl_lkup_upgrade),
        .lkup_stall_o            (ctrl_lkup_stall),
        .lkup_stall_reason_o     (ctrl_lkup_stall_reason),
        .lkup_wr_yield_o         (ctrl_lkup_wr_yield),
        .cap_busy_o              (ctrl_cap_busy),
        .cmt_busy_o              (ctrl_cmt_busy),
        .ctrl_error_o            (ctrl_error),
        .tag_req_o               (ctrl_tag_req),
        .tag_gnt_i               (rsp_tag_gnt),
        .tag_i                   (rsp_tag),
        .cpl_valid_o             (ctrl_cpl_valid),
        .cpl_tag_o               (ctrl_cpl_tag),
        .cpl_data_o              (ctrl_cpl_data),
        .tag_a_set_o             (ctrl_tag_a_set),
        .tag_a_tag_state_i       (ctrl_tag_a_tag_state),
        .tag_a_wr_en_o           (ctrl_tag_a_wr_en),
        .tag_a_wr_way_onehot_o   (ctrl_tag_a_wr_way_onehot),
        .tag_a_wr_set_o          (ctrl_tag_a_wr_set),
        .tag_a_wr_tag_state_o    (ctrl_tag_a_wr_tag_state),
        .dat_a_addr_o            (ctrl_dat_a_addr),
        .dat_a_way_o             (ctrl_dat_a_way),
        .dat_a_rdata_i           (ctrl_dat_a_rdata),
        .dat_a_wr_en_o           (ctrl_dat_a_wr_en),
        .dat_a_wr_way_onehot_o   (ctrl_dat_a_wr_way_onehot),
        .dat_a_wr_addr_o         (ctrl_dat_a_wr_addr),
        .dat_a_wr_wdata_o        (ctrl_dat_a_wr_wdata),
        .dat_a_wr_be_o           (ctrl_dat_a_wr_be),
        .dat_b_addr_o            (ctrl_dat_b_addr),
        .dat_b_way_o             (ctrl_dat_b_way),
        .dat_b_rdata_i           (ctrl_dat_b_rdata),
        .repl_req_o              (ctrl_repl_req),
        .repl_set_o              (ctrl_repl_set),
        .repl_victim_way_i       (repl_victim_way),
        .repl_hit_o              (ctrl_repl_hit),
        .repl_update_o           (ctrl_repl_update),
        .repl_hit_way_o          (ctrl_repl_hit_way),
        .mshr_alloc_o            (ctrl_mshr_alloc),
        .mshr_alloc_line_o       (ctrl_mshr_alloc_line),
        .mshr_alloc_set_o        (ctrl_mshr_alloc_set),
        .mshr_alloc_cls_o        (ctrl_mshr_alloc_cls),
        .mshr_alloc_install_o    (ctrl_mshr_alloc_install),
        .mshr_alloc_victim_way_o (ctrl_mshr_alloc_victim_way),
        .mshr_alloc_wb_slot_o    (ctrl_mshr_alloc_wb_slot),
        .mshr_alloc_wb_valid_o   (ctrl_mshr_alloc_wb_valid),
        .mshr_alloc_seq_o        (ctrl_mshr_alloc_seq),
        .mshr_alloc_gnt_i        (mshr_alloc_gnt),
        .mshr_alloc_idx_i        (mshr_alloc_idx),
        .mshr_full_i             (mshr_full),
        .mshr_set_full_i         (mshr_set_full),
        .mshr_lkup_line_o        (ctrl_mshr_lkup_line),
        .mshr_lkup_reg_match_i   (mshr_lkup_reg_match),
        .mshr_lkup_reg_match_idx_i(mshr_lkup_reg_match_idx),
        .mshr_lkup_reg_match_cls_i(mshr_lkup_reg_match_cls),
        .mshr_cpl_idx_o          (ctrl_mshr_cpl_idx),
        .mshr_cpl_merge_count_i  (mshr_cpl_merge_count),
        .mshr_cpl_line_i         (mshr_cpl_line),
        .mshr_cpl_pend_eff_i     (mshr_cpl_pend_eff),
        .mshr_cpl_merge_seqs_i   (mshr_cpl_merge_seqs),
        .mshr_merge_o            (ctrl_mshr_merge),
        .mshr_merge_idx_o        (ctrl_mshr_merge_idx),
        .mshr_merge_seq_o        (ctrl_mshr_merge_seq),
        .mshr_beat_o             (ctrl_mshr_beat),
        .mshr_beat_idx_o         (ctrl_mshr_beat_idx),
        .mshr_beat_num_o         (ctrl_mshr_beat_num),
        .mshr_retire_o           (ctrl_mshr_retire),
        .mshr_retire_idx_o       (ctrl_mshr_retire_idx),
        .wb_cap_o                (ctrl_wb_cap),
        .wb_cap_line_o           (ctrl_wb_cap_line),
        .wb_cap_beat_o           (ctrl_wb_cap_beat),
        .wb_cap_beat_data_o      (ctrl_wb_cap_beat_data),
        .wb_cap_gnt_i            (wb_cap_gnt),
        .wb_cap_slot_i           (wb_cap_slot),
        .wb_full_i               (wb_full),
        .wb_sn_line_o            (ctrl_wb_sn_line),
        .wb_sn_hit_i             (wb_sn_hit),
        .wb_sn_eff_o             (ctrl_wb_sn_eff),
        .wb_sn_match_idx_i       (wb_sn_match_idx),
        .wb_sn_lock_o            (ctrl_wb_sn_lock),
        .wb_sn_rd_slot_o         (ctrl_wb_sn_rd_slot),
        .wb_sn_rd_beat_o         (ctrl_wb_sn_rd_beat),
        .wb_sn_rd_data_i         (wb_sn_rd_data),
        .wb_sn_bresp_cycle_i     (wb_sn_bresp_cycle),
        .wb_drain_valid_i        (wb_drain_valid),
        .drain_start_o           (ctrl_drain_start),
        .drain_done_i            (eng_drain_done),
        .tag_b_req_o             (ctrl_tag_b_req),
        .tag_b_set_o             (ctrl_tag_b_set),
        .tag_b_tag_state_i       (ctrl_tag_b_tag_state),
        .mshr_sn_line_o          (ctrl_mshr_sn_line),
        .mshr_sn_match_i         (mshr_sn_match),
        .mshr_sn_match_idx_i     (mshr_sn_match_idx),
        .mshr_sn_beats_rcvd_i    (mshr_sn_beats_rcvd),
        .mshr_sn_install_i       (mshr_sn_install),
        .mshr_sn_eff_o           (ctrl_mshr_sn_eff),
        .mshr_sn_eff_idx_o       (ctrl_mshr_sn_eff_idx),
        .mshr_sn_eff_value_o     (ctrl_mshr_sn_eff_value),
        .sn_req_i                (ctrl_snoop_req),
        .sn_want_i               (sn_want_i),
        .sn_addr_i               (ctrl_snoop_addr),
        .sn_type_i               (ctrl_snoop_type),
        .sn_ready_o              (ctrl_snoop_ready),
        .sn_safe_o               (ctrl_snoop_safe),
        .sn_crresp_o             (ctrl_crresp),
        .sn_cddata_o             (ctrl_cddata),
        .sn_cdlast_o             (ctrl_cdlast),
        .sn_cdvalid_o            (ctrl_cdvalid),
        .sn_cdready_i            (ctrl_cdready),
        .fill_start_o            (ctrl_fill_start),
        .fill_addr_o             (ctrl_fill_addr),
        .fill_cls_o              (ctrl_fill_cls),
        .fill_accept_i           (w_fill_accept),
        .fill_pass_dirty_i       (eng_fill_pass_dirty),
        .fill_beat_valid_i       (eng_fill_beat_valid),
        .fill_beat_idx_i         (r_flight_idx),
        .fill_beat_num_i         (eng_fill_beat_idx),
        .fill_done_i             (eng_fill_done),
        .fill_ar_done_i          (fill_ar_done)
    );

    // ------------------------------------------------------------------
    // MSHR file
    // ------------------------------------------------------------------
    jet_mshr #(
        .MSHR_COUNT   (MSHR_COUNT),
        .SETS         (SETS),
        .WAYS         (WAYS),
        .LINE_W       (LINE_W),
        .SEQ_W        (SEQ_W),
        .VICTIM_DEPTH (VICTIM_DEPTH)
    ) u_mshr (
        .clk               (aclk),
        .rst_n             (aresetn),
        .alloc_i           (ctrl_mshr_alloc),
        .alloc_line_i      (ctrl_mshr_alloc_line),
        .alloc_set_i       (ctrl_mshr_alloc_set),
        .alloc_cls_i       (ctrl_mshr_alloc_cls),
        .alloc_install_i   (ctrl_mshr_alloc_install),
        .alloc_victim_way_i(ctrl_mshr_alloc_victim_way),
        .alloc_wb_slot_i   (ctrl_mshr_alloc_wb_slot),
        .alloc_wb_valid_i  (ctrl_mshr_alloc_wb_valid),
        .alloc_seq_i       (ctrl_mshr_alloc_seq),
        .alloc_gnt_o       (mshr_alloc_gnt),
        .alloc_idx_o       (mshr_alloc_idx),
        .full_o            (mshr_full),
        .set_full_o        (mshr_set_full),
        .lkup_line_i       (ctrl_mshr_lkup_line),
        .lkup_match_o      (),
        .lkup_reg_match_o  (mshr_lkup_reg_match),
        .lkup_reg_match_idx_o(mshr_lkup_reg_match_idx),
        .lkup_reg_match_cls_o(mshr_lkup_reg_match_cls),
        .lkup_match_idx_o  (),
        .lkup_match_cls_o  (),
        .sn_line_i         (ctrl_mshr_sn_line),
        .sn_match_o        (mshr_sn_match),
        .sn_match_idx_o    (mshr_sn_match_idx),
        .sn_beats_rcvd_o   (mshr_sn_beats_rcvd),
        .sn_install_o      (mshr_sn_install),
        .merge_i           (ctrl_mshr_merge),
        .merge_idx_i       (ctrl_mshr_merge_idx),
        .merge_seq_i       (ctrl_mshr_merge_seq),
        .beat_i            (ctrl_mshr_beat),
        .beat_idx_i        (ctrl_mshr_beat_idx),
        .beat_num_i        (ctrl_mshr_beat_num),
        .sn_eff_i          (ctrl_mshr_sn_eff),
        .sn_eff_idx_i      (ctrl_mshr_sn_eff_idx),
        .sn_eff_value_i    (ctrl_mshr_sn_eff_value),
        .retire_i          (ctrl_mshr_retire),
        .retire_idx_i      (ctrl_mshr_retire_idx),
        .cpl_idx_i         (ctrl_mshr_cpl_idx),
        .cpl_line_o        (mshr_cpl_line),
        .cpl_install_o     (),
        .cpl_pend_eff_o    (mshr_cpl_pend_eff),
        .cpl_merge_seqs_o  (mshr_cpl_merge_seqs),
        .cpl_merge_count_o (mshr_cpl_merge_count),
        .cpl_wb_slot_o     (),
        .cpl_wb_valid_o    (),
        .occupancy_o       (mshr_occupancy),
        .alloc_o           (mshr_alloc_ev),
        .alloc_set_o       (mshr_alloc_ev_set),
        .alloc_cls_o       (mshr_alloc_ev_cls),
        .merge_o           (mshr_merge_ev),
        .merge_idx_o       (mshr_merge_ev_idx),
        .merge_depth_o     (mshr_merge_ev_depth),
        .retire_o          (mshr_retire_ev),
        .retire_idx_o      (mshr_retire_ev_idx)
    );

    assign mshr_alloc_ev_idx = mshr_alloc_idx;

    // ------------------------------------------------------------------
    // Writeback buffer (J5)
    // ------------------------------------------------------------------
    jet_wb_buffer #(
        .VICTIM_DEPTH (VICTIM_DEPTH),
        .LINE_W       (LINE_W),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .LINE_BYTES   (LINE_BYTES),
        .BUS_WIDTH    (BUS_WIDTH)
    ) u_wb (
        .clk             (aclk),
        .rst_n           (aresetn),
        .cap_i           (ctrl_wb_cap),
        .cap_line_i      (ctrl_wb_cap_line),
        .cap_beat_i      (ctrl_wb_cap_beat),
        .cap_beat_data_i (ctrl_wb_cap_beat_data),
        .cap_gnt_o       (wb_cap_gnt),
        .cap_slot_o      (wb_cap_slot),
        .wb_full_o       (wb_full),
        .drain_valid_o   (wb_drain_valid),
        .drain_addr_o    (wb_drain_addr),
        .drain_beat_idx_i (wb_drain_beat_idx),
        .drain_beat_data_o(wb_drain_beat_data),
        .drain_done_i    (eng_drain_done),
        .sn_line_i       (ctrl_wb_sn_line),
        .sn_hit_o        (wb_sn_hit),
        .sn_match_idx_o  (wb_sn_match_idx),
        .sn_lock_i       (ctrl_wb_sn_lock),
        .sn_rd_slot_i    (ctrl_wb_sn_rd_slot),
        .sn_rd_beat_i    (ctrl_wb_sn_rd_beat),
        .sn_rd_data_o    (wb_sn_rd_data),
        .sn_bresp_cycle_o(wb_sn_bresp_cycle),
        .sn_eff_i        (ctrl_wb_sn_eff),
        .wb_occupancy_o  (wb_occupancy)
    );

    // ------------------------------------------------------------------
    // Arrays + replacement engine (common-ip, unchanged)
    // ------------------------------------------------------------------
    l1_tag_array #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES)
    ) u_tag (
        .clk           (aclk),
        .a_set         (ctrl_tag_a_set),
        .a_tag_state   (ctrl_tag_a_tag_state),
        .b_set         (ctrl_tag_b_set),
        .b_tag_state   (ctrl_tag_b_tag_state),
        .wr_en         (ctrl_tag_a_wr_en),
        .wr_way_onehot (ctrl_tag_a_wr_way_onehot),
        .wr_set        (ctrl_tag_a_wr_set),
        .wr_tag_state  (ctrl_tag_a_wr_tag_state)
    );

    l1_data_array #(
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH),
        .SYNC_READ  (DATA_SYNC_READ)
    ) u_data (
        .clk           (aclk),
        .a_addr        (ctrl_dat_a_addr),
        .a_way         (ctrl_dat_a_way),
        .a_rdata       (ctrl_dat_a_rdata),
        .b_addr        (ctrl_dat_b_addr),
        .b_way         (ctrl_dat_b_way),
        .b_rdata       (ctrl_dat_b_rdata),
        .wr_en         (dat_wr_en),
        .wr_way_onehot (dat_wr_way_onehot),
        .wr_addr       (dat_wr_addr),
        .wr_wdata      (dat_wr_wdata),
        .wr_be         (dat_wr_be)
    );

    l1_repl #(
        .SETS        (SETS),
        .WAYS        (WAYS),
        .REPL_POLICY (REPL_POLICY)
    ) u_repl (
        .clk             (aclk),
        .rst_n           (aresetn),
        .repl_req        (ctrl_repl_req),
        .repl_set        (ctrl_repl_set),
        .repl_victim_way (repl_victim_way),
        .repl_hit        (ctrl_repl_hit),
        .repl_update     (ctrl_repl_update),
        .repl_hit_way    (ctrl_repl_hit_way)
    );

    // ------------------------------------------------------------------
    // Fill engine (AXI4 read sequencing -> raw fub_axi_* pins)
    // ------------------------------------------------------------------
    l1_fill #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH)
    ) u_fill (
        .clk               (aclk),
        .rst_n             (aresetn),
        .fill_start        (w_fill_accept),
        .fill_addr         (ctrl_fill_addr),
        .fill_req_class    (eng_fill_class),
        .fill_done         (eng_fill_done),
        .fill_pass_dirty   (eng_fill_pass_dirty),
        .fill_inflight     (eng_fill_inflight),
        .fill_beat_valid   (eng_fill_beat_valid),
        .fill_beat_data    (eng_fill_beat_data),
        .fill_beat_idx     (eng_fill_beat_idx),
        .fill_last         (),
        .fub_axi_arid      (fub_axi_arid),
        .fub_axi_araddr    (fub_axi_araddr),
        .fub_axi_arlen     (fub_axi_arlen),
        .fub_axi_arsize    (fub_axi_arsize),
        .fub_axi_arburst   (fub_axi_arburst),
        .fub_axi_arlock    (fub_axi_arlock),
        .fub_axi_arcache   (fub_axi_arcache),
        .fub_axi_arprot    (fub_axi_arprot),
        .fub_axi_arqos     (fub_axi_arqos),
        .fub_axi_arregion  (fub_axi_arregion),
        .fub_axi_aruser    (fub_axi_aruser),
        .fub_axi_arvalid   (fub_axi_arvalid),
        .fub_axi_arready   (fub_axi_arready),
        .fub_axi_rid       (fub_axi_rid),
        .fub_axi_rdata     (fub_axi_rdata),
        .fub_axi_rresp     (fub_axi_rresp),
        .fub_axi_rlast     (fub_axi_rlast),
        .fub_axi_ruser     (fub_axi_ruser),
        .fub_axi_rvalid    (fub_axi_rvalid),
        .fub_axi_rready    (fub_axi_rready)
    );

    // ------------------------------------------------------------------
    // Drain engine (the WB head is l1_victim-shaped: valid/addr/data held
    // until the BRESP-cycle drain_done)
    // ------------------------------------------------------------------
    l1_drain #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH)
    ) u_drain (
        .clk              (aclk),
        .rst_n            (aresetn),
        .drain_start      (ctrl_drain_start),
        .victim_addr      (wb_drain_addr),
        .victim_beat_idx  (wb_drain_beat_idx),
        .victim_beat_data (wb_drain_beat_data),
        .drain_done       (eng_drain_done),
        .fub_axi_awid     (fub_axi_awid),
        .fub_axi_awaddr   (fub_axi_awaddr),
        .fub_axi_awlen    (fub_axi_awlen),
        .fub_axi_awsize   (fub_axi_awsize),
        .fub_axi_awburst  (fub_axi_awburst),
        .fub_axi_awlock   (fub_axi_awlock),
        .fub_axi_awcache  (fub_axi_awcache),
        .fub_axi_awprot   (fub_axi_awprot),
        .fub_axi_awqos    (fub_axi_awqos),
        .fub_axi_awregion (fub_axi_awregion),
        .fub_axi_awuser   (fub_axi_awuser),
        .fub_axi_awvalid  (fub_axi_awvalid),
        .fub_axi_awready  (fub_axi_awready),
        .fub_axi_wdata    (fub_axi_wdata),
        .fub_axi_wstrb    (fub_axi_wstrb),
        .fub_axi_wlast    (fub_axi_wlast),
        .fub_axi_wuser    (fub_axi_wuser),
        .fub_axi_wvalid   (fub_axi_wvalid),
        .fub_axi_wready   (fub_axi_wready),
        .fub_axi_bid      (fub_axi_bid),
        .fub_axi_bresp    (fub_axi_bresp),
        .fub_axi_buser    (fub_axi_buser),
        .fub_axi_bvalid   (fub_axi_bvalid),
        .fub_axi_bready   (fub_axi_bready)
    );

    // ------------------------------------------------------------------
    // Pair-rig coherence sideband (D-8): one pulse per fill launch
    // (accept) / dirty-drain start.  Pure observation output.
    //   The sideband carries ONE event per cycle; jet (unlike amber's
    //   blocking FSM, where MISS_DRAIN and MISS_FILL are separate states)
    // fires the drain arbiter and the launch adapter concurrently -- the
    // cycle a victim capture completes, drain_start_o and the held fill's
    // accept coincide.  The fill launch wins the slot (the fabric queues
    // it -- dropping it would hang the fill's AR); the drain's
    // WRITE_BACK pulse replays the next cycle (the fabric never queues
    // WRITE_BACK, so the one-cycle delay is invisible downstream).
    // ------------------------------------------------------------------
    logic                  r_wb_coh_pend;
    logic [ADDR_WIDTH-1:0] r_wb_coh_addr;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wb_coh_pend <= 1'b0;
            r_wb_coh_addr <= '0;
        end else begin
            // set on the collision; held while fill launches keep winning
            // the slot (the pulse is informational -- the fabric never
            // queues WRITE_BACK -- so the delay is invisible downstream)
            r_wb_coh_pend <= (ctrl_drain_start & w_fill_accept)
                             | (r_wb_coh_pend & w_fill_accept);
            if (ctrl_drain_start & w_fill_accept) begin
                r_wb_coh_addr <= wb_drain_addr;
            end
        end
    )

    // Registered one cycle at the plane boundary (ISSUE-001): the
    // combinational cone cpu_req skid -> classify/tag-hit -> fill accept ->
    // coh_req -> fabric kill-rule compare -> peer AC skid measured 35
    // levels / ~15.2 ns on Kintex-7 (fails 90 MHz).  The fabric consumes
    // the pulse purely as an announcement -- its live tap and its
    // registered pend queue shift together, so all relative ordering is
    // preserved and every fabric decision simply happens one cycle later.
    logic                  w_coh_req_valid;
    logic [ADDR_WIDTH-1:0] w_coh_req_addr;
    logic [2:0]            w_coh_req_type;

    assign w_coh_req_valid = w_fill_accept | ctrl_drain_start | r_wb_coh_pend;
    assign w_coh_req_addr  = w_fill_accept ? ctrl_fill_addr
                           : r_wb_coh_pend ? r_wb_coh_addr
                                           : wb_drain_addr;
    assign w_coh_req_type  = w_fill_accept ? eng_fill_class
                                           : 3'(AMBER_ACE_WRITE_BACK);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            coh_req_valid <= 1'b0;
            coh_req_addr  <= '0;
            coh_req_type  <= '0;
        end else begin
            coh_req_valid <= w_coh_req_valid;
            coh_req_addr  <= w_coh_req_addr;
            coh_req_type  <= w_coh_req_type;
        end
    )

    // ------------------------------------------------------------------
    // Status roll-ups
    // ------------------------------------------------------------------
    assign init_busy = ctrl_init_busy;
    assign busy      = ctrl_init_busy | ctrl_cap_busy | ctrl_cmt_busy
                       | r_eng_busy | (mshr_occupancy != '0)
                       | (wb_occupancy != '0);

    // ------------------------------------------------------------------
    // l1_monlite tap encoder (observation only): jet has no blocking ctrl
    // FSM, so the observer's amber-style state-entry taps are fed by a
    // pseudo-state synthesized from the jet events.  Priority order when
    // several events coincide (one state per cycle; the dropped views are
    // measurement-only): ERROR > INIT > snoop service > commit install
    // (FILL_END) > fill launch > drain start > alloc (MISS) > write hit >
    // read hit > IDLE.  Read-only hierarchical taps into u_control follow
    // the sanctioned l1_core pattern (the observer drives nothing in the
    // datapath).
    // ------------------------------------------------------------------
    logic [3:0] mon_state;
    logic       w_cmt_install;
    logic       w_sn_active;

    assign w_cmt_install = (u_control.r_cmt_state == 4'd2)    // C_INSTALL
                           | (u_control.r_cmt_state == 4'd3)  // C_PEND
                           | (u_control.r_cmt_state == 4'd7); // C_CU_INSTALL
    assign w_sn_active   = (u_control.r_sn_state != 2'd0);

    always_comb begin
        if (ctrl_error) begin
            mon_state = 4'(AMBER_CTRL_ERROR);
        end else if (ctrl_init_busy) begin
            mon_state = 4'(AMBER_CTRL_INIT);
        end else if (w_sn_active) begin
            mon_state = 4'(AMBER_CTRL_SNOOP);
        end else if (w_cmt_install) begin
            mon_state = 4'(AMBER_CTRL_FILL_WRITE);
        end else if (w_fill_accept) begin
            mon_state = 4'(AMBER_CTRL_MISS_FILL);
        end else if (ctrl_drain_start) begin
            mon_state = 4'(AMBER_CTRL_MISS_DRAIN);
        end else if (ctrl_lkup_miss_alloc) begin
            mon_state = 4'(AMBER_CTRL_MISS_VICTIM);
        end else if (ctrl_lkup_hit & lkup_we) begin
            mon_state = 4'(AMBER_CTRL_HIT_WR);
        end else if (ctrl_lkup_hit | ctrl_lkup_upgrade) begin
            mon_state = 4'(AMBER_CTRL_HIT_RD);
        end else begin
            mon_state = 4'(AMBER_CTRL_IDLE);
        end
    end

    assign ctrl_state = mon_state;

    // the deferred MISS packet samples tap_miss_set one cycle after the
    // MISS_VICTIM pseudo-state entry -- hold the alloc set for it
    logic [SET_W-1:0] r_mon_miss_set;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_mon_miss_set <= '0;
        end else if (ctrl_lkup_miss_alloc) begin
            r_mon_miss_set <= ctrl_mshr_alloc_set;
        end
    )

    // tag-write old-state view per cause (the TRANSITION packet payload)
    logic [2:0] mon_state_old;
    always_comb begin
        if (u_control.r_cmt_state == 4'd7) begin
            mon_state_old = AMBER_STATE_S;        // CU commit: S -> M (or I)
        end else if (u_control.r_cmt_state == 4'd3) begin
            mon_state_old = u_control.r_cmt_cls == JET_CLS_RNSD
                            ? AMBER_STATE_S : AMBER_STATE_M;
        end else if (w_sn_active) begin
            mon_state_old = u_control.r_sn_ref;
        end else begin
            mon_state_old = AMBER_STATE_I;        // installs land on I
        end
    end

    logic [WAY_W-1:0] mon_tag_wr_way;
    always_comb begin
        mon_tag_wr_way = '0;
        for (int w = 0; w < WAYS; w++) begin
            if (ctrl_tag_a_wr_way_onehot[w]) begin
                mon_tag_wr_way = WAY_W'(w);
            end
        end
    end

    // ------------------------------------------------------------------
    // Observation tap pipeline (ISSUE-001 v2, 2026-11-03).  Both monitors
    // tap the deep classify cone (w_hit_way / crresp / alloc pulses), and
    // at 100 MHz the worst paths in the design END inside them (route-
    // dominated: the monitor logic is placed far from the classify).
    // Observation is cycle-shift-insensitive, so register every tap (and
    // mon_time with them, keeping events and timestamps in lockstep);
    // every relative relationship the monitors rely on (miss-set sample
    // vs MISS_VICTIM pseudo-state, alloc->retire latency, stall duration)
    // is a delta and survives the uniform one-cycle shift.
    // ------------------------------------------------------------------
    logic [63:0]                     r_mon_time;
    // l1_monlite bundle (constants tap_miss_class/tap_victim_state stay direct)
    logic [3:0]                      r_mt_ctrl_state;
    logic [SET_W-1:0]                r_mt_hit_set;
    logic [WAY_W-1:0]                r_mt_hit_way;
    logic [2:0]                      r_mt_hit_state_before;
    logic                            r_mt_req_we;
    logic [SET_W-1:0]                r_mt_miss_set;
    logic                            r_mt_snoop_fire;
    logic [2:0]                      r_mt_snoop_type;
    logic                            r_mt_snoop_hit;
    logic [AMBER_CRRESP_WIDTH-1:0]   r_mt_snoop_resp;
    logic                            r_mt_victim_load;
    logic [ADDR_WIDTH-1:0]           r_mt_victim_addr;
    logic [WAY_W-1:0]                r_mt_victim_way;
    logic                            r_mt_tag_wr_en;
    logic [SET_W-1:0]                r_mt_tag_wr_set;
    logic [WAY_W-1:0]                r_mt_tag_wr_way;
    logic [2:0]                      r_mt_tag_wr_new_state;
    logic [2:0]                      r_mt_state_old;
    logic [ADDR_WIDTH-1:0]           r_mt_fill_addr;
    logic                            r_mt_drain_done;
    // jet_monlite bundle
    logic                            r_jm_alloc;
    logic [SET_W-1:0]                r_jm_alloc_set;
    logic [1:0]                      r_jm_alloc_cls;
    logic [MW-1:0]                   r_jm_alloc_idx;
    logic                            r_jm_merge;
    logic [MW-1:0]                   r_jm_merge_idx;
    logic [MW:0]                     r_jm_merge_depth;
    logic                            r_jm_retire;
    logic [MW-1:0]                   r_jm_retire_idx;
    logic [MW:0]                     r_jm_occ;
    logic [$clog2(VICTIM_DEPTH+1)-1:0] r_jm_wb_occ;
    logic                            r_jm_stall;
    logic [2:0]                      r_jm_stall_reason;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_mon_time            <= '0;
            r_mt_ctrl_state       <= 4'(AMBER_CTRL_INIT);
            r_mt_hit_set          <= '0;
            r_mt_hit_way          <= '0;
            r_mt_hit_state_before <= '0;
            r_mt_req_we           <= 1'b0;
            r_mt_miss_set         <= '0;
            r_mt_snoop_fire       <= 1'b0;
            r_mt_snoop_type       <= '0;
            r_mt_snoop_hit        <= 1'b0;
            r_mt_snoop_resp       <= '0;
            r_mt_victim_load      <= 1'b0;
            r_mt_victim_addr      <= '0;
            r_mt_victim_way       <= '0;
            r_mt_tag_wr_en        <= 1'b0;
            r_mt_tag_wr_set       <= '0;
            r_mt_tag_wr_way       <= '0;
            r_mt_tag_wr_new_state <= '0;
            r_mt_state_old        <= '0;
            r_mt_fill_addr        <= '0;
            r_mt_drain_done       <= 1'b0;
            r_jm_alloc            <= 1'b0;
            r_jm_alloc_set        <= '0;
            r_jm_alloc_cls        <= '0;
            r_jm_alloc_idx        <= '0;
            r_jm_merge            <= 1'b0;
            r_jm_merge_idx        <= '0;
            r_jm_merge_depth      <= '0;
            r_jm_retire           <= 1'b0;
            r_jm_retire_idx       <= '0;
            r_jm_occ              <= '0;
            r_jm_wb_occ           <= '0;
            r_jm_stall            <= 1'b0;
            r_jm_stall_reason     <= '0;
        end else begin
            r_mon_time            <= mon_time;
            r_mt_ctrl_state       <= mon_state;
            r_mt_hit_set          <= lkup_addr[OFF_W +: SET_W];
            r_mt_hit_way          <= u_control.w_hit_way;
            r_mt_hit_state_before <= u_control.w_hit_state;
            r_mt_req_we           <= lkup_we;
            r_mt_miss_set         <= r_mon_miss_set;
            r_mt_snoop_fire       <= ctrl_snoop_req & ctrl_snoop_ready;
            r_mt_snoop_type       <= ctrl_snoop_type;
            r_mt_snoop_hit        <= (ctrl_crresp != '0);
            r_mt_snoop_resp       <= ctrl_crresp;
            r_mt_victim_load      <= ctrl_mshr_alloc & mshr_alloc_gnt
                                     & ctrl_mshr_alloc_wb_valid;
            r_mt_victim_addr      <= {ctrl_wb_cap_line, {OFF_W{1'b0}}};
            r_mt_victim_way       <= ctrl_mshr_alloc_victim_way;
            r_mt_tag_wr_en        <= ctrl_tag_a_wr_en;
            r_mt_tag_wr_set       <= ctrl_tag_a_wr_set;
            r_mt_tag_wr_way       <= mon_tag_wr_way;
            r_mt_tag_wr_new_state <= ctrl_tag_a_wr_tag_state[2:0];
            r_mt_state_old        <= mon_state_old;
            r_mt_fill_addr        <= ctrl_fill_addr;
            r_mt_drain_done       <= eng_drain_done;
            r_jm_alloc            <= mshr_alloc_ev;
            r_jm_alloc_set        <= mshr_alloc_ev_set;
            r_jm_alloc_cls        <= mshr_alloc_ev_cls;
            r_jm_alloc_idx        <= mshr_alloc_ev_idx;
            r_jm_merge            <= mshr_merge_ev;
            r_jm_merge_idx        <= mshr_merge_ev_idx;
            r_jm_merge_depth      <= mshr_merge_ev_depth;
            r_jm_retire           <= mshr_retire_ev;
            r_jm_retire_idx       <= mshr_retire_ev_idx;
            r_jm_occ              <= mshr_occupancy;
            r_jm_wb_occ           <= wb_occupancy;
            r_jm_stall            <= ctrl_lkup_stall;
            r_jm_stall_reason     <= ctrl_lkup_stall_reason;
        end
    )

    l1_monlite #(
        .ADDR_WIDTH  (ADDR_WIDTH),
        .SETS        (SETS),
        .WAYS        (WAYS),
        .LINE_BYTES  (LINE_BYTES),
        .BUS_WIDTH   (BUS_WIDTH),
        .USE_MONITOR (USE_MONITOR)
    ) u_monlite (
        .clk                 (aclk),
        .rst_n               (aresetn),
        .tap_ctrl_state      (r_mt_ctrl_state),
        .tap_hit_set         (r_mt_hit_set),
        .tap_hit_way         (r_mt_hit_way),
        .tap_hit_state_before(r_mt_hit_state_before),
        .tap_req_we          (r_mt_req_we),
        .tap_miss_set        (r_mt_miss_set),
        .tap_miss_class      (2'(AMBER_MISS_UNKNOWN)),
        .tap_snoop_fire      (r_mt_snoop_fire),
        .tap_snoop_type      (r_mt_snoop_type),
        .tap_snoop_hit       (r_mt_snoop_hit),
        .tap_snoop_resp      (r_mt_snoop_resp),
        .tap_victim_load     (r_mt_victim_load),
        .tap_victim_addr     (r_mt_victim_addr),
        .tap_victim_way      (r_mt_victim_way),
        .tap_victim_state    (AMBER_STATE_M),
        .tap_tag_wr_en       (r_mt_tag_wr_en),
        .tap_tag_wr_set      (r_mt_tag_wr_set),
        .tap_tag_wr_way      (r_mt_tag_wr_way),
        .tap_tag_wr_new_state(r_mt_tag_wr_new_state),
        .tap_state_old       (r_mt_state_old),
        .tap_fill_addr       (r_mt_fill_addr),
        .tap_drain_done      (r_mt_drain_done),
        .i_mon_time          (r_mon_time),
        .monbus_valid        (mon_valid),
        .monbus_ready        (mon_ready),
        .monbus_packet       (mon_packet),
        .monbus_timestamp    (mon_timestamp),
        .dropped_count       (mon_dropped)
    );

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_core_mon;
    assign unused_core_mon = &{1'b0, eng_fill_inflight, ctrl_lkup_merge,
                               ctrl_lkup_wr_yield};
    /* verilator lint_on UNUSEDSIGNAL */

    // ------------------------------------------------------------------
    // J7 MonBus observer: MSHR alloc/merge/retire, occupancy gauges,
    // tag-full stall events.
    // ------------------------------------------------------------------
    jet_monlite #(
        .MSHR_COUNT  (MSHR_COUNT),
        .VICTIM_DEPTH (VICTIM_DEPTH),
        .SETS        (SETS),
        .WAYS        (WAYS),
        .USE_MONITOR (USE_MONITOR)
    ) u_jet_monlite (
        .clk                 (aclk),
        .rst_n               (aresetn),
        .mshr_alloc_i        (r_jm_alloc),
        .mshr_alloc_set_i    (r_jm_alloc_set),
        .mshr_alloc_cls_i    (r_jm_alloc_cls),
        .mshr_alloc_idx_i    (r_jm_alloc_idx),
        .mshr_merge_i        (r_jm_merge),
        .mshr_merge_idx_i    (r_jm_merge_idx),
        .mshr_merge_depth_i  (r_jm_merge_depth),
        .mshr_retire_i       (r_jm_retire),
        .mshr_retire_idx_i   (r_jm_retire_idx),
        .mshr_occupancy_i    (r_jm_occ),
        .wb_occupancy_i      (r_jm_wb_occ),
        .ctrl_stall_i        (r_jm_stall),
        .ctrl_stall_reason_i (r_jm_stall_reason),
        .i_mon_time          (r_mon_time),
        .monbus_valid        (j7_mon_valid),
        .monbus_ready        (j7_mon_ready),
        .monbus_packet       (j7_mon_packet),
        .monbus_timestamp    (j7_mon_timestamp),
        .dropped_count       ()
    );

endmodule : jet_coh_core
