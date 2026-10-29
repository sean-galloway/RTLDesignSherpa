// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_top
// Purpose:
//   The jet pair-rig top (MAS ch01 hierarchy): the lockup-free MESI L1
//   composed from the jet control blocks (jet_control + jet_mshr +
//   jet_wb_buffer + jet_rsp_seq) and the UNCHANGED common-ip slice
//   (l1_cpu_frontend, l1_tag_array, l1_data_array, l1_repl, l1_fill,
//   l1_drain, l1_snoop_resp, l1_monlite), wrapped with the house AXI4
//   transports the core deliberately does not contain (DECISION D3) --
//   axi4_master_rd_monlite / axi4_master_wr_monlite -- so the m_axi_*
//   memory side is the monlite-wrapped (measured) path.  A house
//   monbus_arbiter (D-7) merges the three observer streams onto the one
//   MonBus port pair.  Mirrors amber_top's structure with
//   l1_control -> jet_control swapped.
//
// Documentation: projects/components/cache-ip/jet-mesi-l1/docs/jet_mas/ch01_overview/02_port_list.md
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-29

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: jet_top
//==============================================================================
// Description:
//   External shape = amber_top's (MAS ch01/02 port contract, inherited):
//   aclk/aresetn, CPU GAXI slave, AXI4 m_axi_* rd/wr masters (house wrapper
//   signal names), ACE snoop responder, single MonBus, the D-8 coherence
//   sideband, the rig-level mon_time source, init_busy/ctrl_state status.
//   Plus the jet `busy` roll-up (MAS ch01/02: ctrl non-idle OR MSHR/WB
//   non-empty OR an engine in flight).
//
//   Integration glue that is NOT pure wiring (all of it the launch level,
//   none of it touching common-ip):
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
//   * l1_monlite tap encoder (observation only, drives nothing in the
//     datapath): jet has no blocking ctrl FSM, so the observer's
//     amber-style state-entry taps are fed by a pseudo-state encoder over
//     the jet events (init walk / hit / alloc / launch / drain /
//     commit-install / snoop effect).  The J7 event classes are a future
//     monlite extension (MAS ch04).
//
//   * Request/response skid adaptation (DECISION D-6 queue).  The common
//     l1_cpu_frontend is amber's pulse-style boundary: it presents
//     req_valid only in the cycle ctrl_req_ready is already high
//     (req_valid = cpu_req_wr_valid & cpu_req_wr_ready), which jet's
//     hold-until-accepted lookup contract would deadlock (a stall holds
//     ready low, so the request is never re-presented) -- and closes a
//     combinational loop through the classify.  A 2-deep gaxi_fifo_sync
//     request skid sits between the frontend and the lookup stage: the
//     frontend handshakes into the skid (wr_ready = ctrl_req_ready, the
//     pulse lands once), the skid holds the request presented until
//     lkup_ready_o.  On the response side, jet releases are level-held
//     (jet_rsp_seq): rsp_ready_i is the frontend staging FIFO's room
//     (the read-only u_frontend.stage_wr_ready tap, the sanctioned
//     l1_core pattern) and the FIFO write is the same qualifier, so a
//     backed-up CPU response channel backpressures the release pointer
//     instead of overflowing the depth-2 staging queue.
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
//     as amber_top (geometry per l1_pkg defaults)
//   MSHR_COUNT / VICTIM_DEPTH:
//     J1 / J5 geometry (jet_pkg defaults)
//
//------------------------------------------------------------------------------
// Notes:
//   - Single clock / active-low reset: the port aresetn is async-assert,
//     synchronized internally (reset_sync, N=3) -- integrators may
//     deassert it asynchronously (same pattern as amber_top).
//   - ctrl_state is the amber-family 4-bit observability encoding: the
//     pseudo-state event view (IDLE/INIT/HIT_*/MISS_*/FILL_WRITE/SNOOP)
//     with AMBER_CTRL_ERROR driven sticky once jet_control latches its
//     CTRL_ERROR (MAS ch02/01 "Illegal states"; reset is the only exit).
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: dv/tb/jet_core_th.sv (Task 8 core TB)
//   - Instantiated: jet_control, jet_mshr, jet_wb_buffer, jet_rsp_seq,
//     l1_cpu_frontend, l1_tag_array, l1_data_array, l1_repl, l1_fill,
//     l1_drain, l1_snoop_resp, l1_monlite, axi4_master_rd/wr_monlite,
//     monbus_arbiter, reset_sync
//   - Package: jet_pkg, l1_pkg, ocelus_common_pkg
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/jet-mesi-l1/dv/tests/test_jet_core.py
//   Plan: dv/testplans/jet_core_testplan.yaml
//   Run: pytest projects/components/cache-ip/jet-mesi-l1/dv/tests/test_jet_core.py -v
//
//==============================================================================

module jet_top
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
    localparam int UW          = AXI_USER_WIDTH,
    localparam int CPU_REQ_W   = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH,
    localparam int CPU_RSP_W   = BUS_WIDTH
)(
    input  logic                        aclk,
    input  logic                        aresetn,

    // ------------------------------------------------------------------
    // CPU GAXI slave (MAS ch03/01)
    // ------------------------------------------------------------------
    input  logic                        cpu_req_wr_valid,
    output logic                        cpu_req_wr_ready,
    input  logic [CPU_REQ_W-1:0]        cpu_req_wr_data,
    output logic                        cpu_rsp_rd_valid,
    input  logic                        cpu_rsp_rd_ready,
    output logic [CPU_RSP_W-1:0]        cpu_rsp_rd_data,

    // ------------------------------------------------------------------
    // AXI4 memory masters via the monlite-wrapped transports (D3)
    // ------------------------------------------------------------------
    output logic [IW-1:0]               m_axi_arid,
    output logic [ADDR_WIDTH-1:0]       m_axi_araddr,
    output logic [7:0]                  m_axi_arlen,
    output logic [2:0]                  m_axi_arsize,
    output logic [1:0]                  m_axi_arburst,
    output logic                        m_axi_arlock,
    output logic [3:0]                  m_axi_arcache,
    output logic [2:0]                  m_axi_arprot,
    output logic [3:0]                  m_axi_arqos,
    output logic [3:0]                  m_axi_arregion,
    output logic [UW-1:0]               m_axi_aruser,
    output logic                        m_axi_arvalid,
    input  logic                        m_axi_arready,
    input  logic [IW-1:0]               m_axi_rid,
    input  logic [BUS_WIDTH-1:0]        m_axi_rdata,
    input  logic [1:0]                  m_axi_rresp,
    input  logic                        m_axi_rlast,
    input  logic [UW-1:0]               m_axi_ruser,
    input  logic                        m_axi_rvalid,
    output logic                        m_axi_rready,

    output logic [IW-1:0]               m_axi_awid,
    output logic [ADDR_WIDTH-1:0]       m_axi_awaddr,
    output logic [7:0]                  m_axi_awlen,
    output logic [2:0]                  m_axi_awsize,
    output logic [1:0]                  m_axi_awburst,
    output logic                        m_axi_awlock,
    output logic [3:0]                  m_axi_awcache,
    output logic [2:0]                  m_axi_awprot,
    output logic [3:0]                  m_axi_awqos,
    output logic [3:0]                  m_axi_awregion,
    output logic [UW-1:0]               m_axi_awuser,
    output logic                        m_axi_awvalid,
    input  logic                        m_axi_awready,
    output logic [BUS_WIDTH-1:0]        m_axi_wdata,
    output logic [STRB_W-1:0]           m_axi_wstrb,
    output logic                        m_axi_wlast,
    output logic [UW-1:0]               m_axi_wuser,
    output logic                        m_axi_wvalid,
    input  logic                        m_axi_wready,
    input  logic [IW-1:0]               m_axi_bid,
    input  logic [1:0]                  m_axi_bresp,
    input  logic [UW-1:0]               m_axi_buser,
    input  logic                        m_axi_bvalid,
    output logic                        m_axi_bready,

    // ------------------------------------------------------------------
    // ACE snoop responder (MAS ch03/03)
    // ------------------------------------------------------------------
    input  logic [ADDR_WIDTH-1:0]       m_axi_acaddr,
    input  logic [3:0]                  m_axi_acsnoop,
    input  logic [2:0]                  m_axi_acprot,
    input  logic                        m_axi_acvalid,
    output logic                        m_axi_acready,
    output logic [AMBER_CRRESP_WIDTH-1:0] m_axi_crresp,
    output logic                        m_axi_crvalid,
    input  logic                        m_axi_crready,
    output logic [BUS_WIDTH-1:0]        m_axi_cddata,
    output logic                        m_axi_cdlast,
    output logic                        m_axi_cdvalid,
    input  logic                        m_axi_cdready,

    // ------------------------------------------------------------------
    // Pair-rig coherence sideband (D-8)
    // ------------------------------------------------------------------
    output logic                        coh_req_valid,
    output logic [ADDR_WIDTH-1:0]       coh_req_addr,
    output logic [2:0]                  coh_req_type,

    // ------------------------------------------------------------------
    // Rig-level timestamp source + merged MonBus (D-7)
    // ------------------------------------------------------------------
    input  logic [63:0]                 i_mon_time,
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [127:0]                mon_packet,
    output logic [63:0]                 mon_timestamp,

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
            $error("jet_top: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("jet_top: LINE_BYTES must be a power of two");
        if ((BUS_WIDTH % 8) != 0)
            $error("jet_top: BUS_WIDTH must be a multiple of 8");
        if (WAYS < 2)
            $error("jet_top: WAYS must be >= 2");
    end

    // ------------------------------------------------------------------
    // Boundary reset synchronization (async-assert port, synchronous
    // release inside; the amber_top pattern)
    // ------------------------------------------------------------------
    logic w_aresetn;
    reset_sync #(
        .N             (3),
        .KEEP_ATTRS    (1'b1),
        .IN_ACTIVE_LOW (1'b1),
        .OUT_ACTIVE_LOW(1'b1),
        .ASYNC_ASSERT  (1'b1)
    ) u_reset_sync (
        .clk        (aclk),
        .rst_n      (aresetn),
        .sync_rst_n (w_aresetn)
    );

    // ------------------------------------------------------------------
    // frontend <-> control request/response contract, with the D-6
    // request skid between (see the header: the frontend's pulse-style
    // req_valid cannot drive jet's hold-until-accepted lookup directly)
    // ------------------------------------------------------------------
    logic                     fe_req_valid;
    logic [ADDR_WIDTH-1:0]    fe_req_addr;
    logic                     fe_req_we;
    logic [STRB_W-1:0]        fe_req_be;
    logic [BUS_WIDTH-1:0]     fe_req_wdata;
    logic                     ctrl_req_ready;
    logic                     rsp_valid;
    logic [BUS_WIDTH-1:0]     rsp_data;
    logic                     rsp_room;     // frontend staging FIFO room
    logic                     ctrl_error;   // jet_control's sticky error

    // request skid: the frontend's one-cycle pulse lands here; the skid
    // holds the request presented to the lookup stage until lkup_ready_o.
    // The frontend's ready is gated with the synchronized reset: without
    // the gate the empty skid's wr_ready is high through the reset-sync
    // tail, and a request handshaked there would be dropped by the FIFO's
    // own reset (the pair-rig fabric may present a request the cycle the
    // port aresetn releases).  And with CTRL_ERROR latched the boundary
    // dead-stops (amber's contract: a dead cache admits no work).
    logic                     skid_rd_valid;
    logic [CPU_REQ_W-1:0]     skid_rd_data;
    logic                     lkup_ready;
    logic                     skid_wr_ready;

    assign ctrl_req_ready = skid_wr_ready & w_aresetn & ~ctrl_error;

    gaxi_fifo_sync #(
        .DATA_WIDTH (CPU_REQ_W),
        .DEPTH      (2)
    ) u_req_skid (
        .axi_aclk    (aclk),
        .axi_aresetn (w_aresetn),
        .wr_valid    (fe_req_valid),
        .wr_ready    (skid_wr_ready),
        .wr_data     ({fe_req_addr, fe_req_we, fe_req_be, fe_req_wdata}),
        .rd_ready    (lkup_ready),
        .count       (),
        .rd_valid    (skid_rd_valid),
        .rd_data     (skid_rd_data)
    );

    l1_cpu_frontend #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_frontend (
        .clk               (aclk),
        .rst_n             (w_aresetn),
        .cpu_req_wr_valid  (cpu_req_wr_valid),
        .cpu_req_wr_ready  (cpu_req_wr_ready),
        .cpu_req_wr_data   (cpu_req_wr_data),
        .cpu_rsp_rd_valid  (cpu_rsp_rd_valid),
        .cpu_rsp_rd_ready  (cpu_rsp_rd_ready),
        .cpu_rsp_rd_data   (cpu_rsp_rd_data),
        .req_valid         (fe_req_valid),
        .req_addr          (fe_req_addr),
        .req_we            (fe_req_we),
        .req_be            (fe_req_be),
        .req_wdata         (fe_req_wdata),
        .ctrl_req_ready    (ctrl_req_ready),
        .ctrl_rsp_valid    (rsp_valid & rsp_room),
        .ctrl_rsp_data     (rsp_data)
    );

    // response staging room (the read-only tap; the FIFO write and the
    // rsp_seq release are the same qualifier, so the depth-2 staging
    // queue can never overflow)
    assign rsp_room = u_frontend.stage_wr_ready;

    // the skid-presented request fields (valid at the lookup window)
    logic [ADDR_WIDTH-1:0]    lkup_addr;
    logic                     lkup_we;
    assign lkup_addr = skid_rd_data[CPU_REQ_W-1 -: ADDR_WIDTH];
    assign lkup_we   = skid_rd_data[BUS_WIDTH + STRB_W];

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
    // rsp sequencer front end
    logic                       ctrl_tag_req;
    logic                       rsp_tag_gnt;
    logic [SEQ_W-1:0]           rsp_tag;
    logic                       ctrl_cpl_valid;
    logic [SEQ_W-1:0]           ctrl_cpl_tag;
    logic [BUS_WIDTH-1:0]       ctrl_cpl_data;
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
    logic [LINE_BITS-1:0]       wb_sn_data;
    logic                       wb_sn_bresp_cycle;
    logic                       wb_drain_valid;
    logic [ADDR_WIDTH-1:0]      wb_drain_addr;
    logic [LINE_BITS-1:0]       wb_drain_data;
    logic [WB_W:0]              wb_occupancy;
    logic                       ctrl_drain_start;
    logic                       eng_drain_done;
    // snoop responder core-facing contract
    logic                       sn_req;
    logic [ADDR_WIDTH-1:0]      sn_addr;
    logic [2:0]                 sn_type;
    logic                       sn_ready;
    logic                       sn_safe;
    logic [AMBER_CRRESP_WIDTH-1:0] sn_crresp;
    logic [BUS_WIDTH-1:0]       sn_cddata;
    logic                       sn_cdlast;
    logic                       sn_cdvalid;
    logic                       sn_cdready;
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

    `ALWAYS_FF_RST(aclk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
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
        .VICTIM_DEPTH (VICTIM_DEPTH)
    ) u_control (
        .clk                     (aclk),
        .rst_n                   (w_aresetn),
        .init_busy_o             (ctrl_init_busy),
        .lkup_valid_i            (skid_rd_valid),
        .lkup_addr_i             (skid_rd_data[CPU_REQ_W-1 -: ADDR_WIDTH]),
        .lkup_we_i               (skid_rd_data[BUS_WIDTH + STRB_W]),
        .lkup_be_i               (skid_rd_data[BUS_WIDTH + STRB_W - 1 -: STRB_W]),
        .lkup_wdata_i            (skid_rd_data[BUS_WIDTH-1:0]),
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
        .wb_sn_data_i            (wb_sn_data),
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
        .sn_req_i                (sn_req),
        .sn_addr_i               (sn_addr),
        .sn_type_i               (sn_type),
        .sn_ready_o              (sn_ready),
        .sn_safe_o               (sn_safe),
        .sn_crresp_o             (sn_crresp),
        .sn_cddata_o             (sn_cddata),
        .sn_cdlast_o             (sn_cdlast),
        .sn_cdvalid_o            (sn_cdvalid),
        .sn_cdready_i            (sn_cdready),
        .fill_start_o            (ctrl_fill_start),
        .fill_addr_o             (ctrl_fill_addr),
        .fill_cls_o              (ctrl_fill_cls),
        .fill_accept_i           (w_fill_accept),
        .fill_pass_dirty_i       (eng_fill_pass_dirty),
        .fill_beat_valid_i       (eng_fill_beat_valid),
        .fill_beat_idx_i         (r_flight_idx),
        .fill_beat_num_i         (eng_fill_beat_idx),
        .fill_done_i             (eng_fill_done),
        .fill_ar_done_i          (m_axi_arvalid & m_axi_arready)
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
        .rst_n             (w_aresetn),
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
        .occupancy_o       (mshr_occupancy)
    );

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
        .rst_n           (w_aresetn),
        .cap_i           (ctrl_wb_cap),
        .cap_line_i      (ctrl_wb_cap_line),
        .cap_beat_i      (ctrl_wb_cap_beat),
        .cap_beat_data_i (ctrl_wb_cap_beat_data),
        .cap_gnt_o       (wb_cap_gnt),
        .cap_slot_o      (wb_cap_slot),
        .wb_full_o       (wb_full),
        .drain_valid_o   (wb_drain_valid),
        .drain_addr_o    (wb_drain_addr),
        .drain_data_o    (wb_drain_data),
        .drain_done_i    (eng_drain_done),
        .sn_line_i       (ctrl_wb_sn_line),
        .sn_hit_o        (wb_sn_hit),
        .sn_data_o       (wb_sn_data),
        .sn_bresp_cycle_o(wb_sn_bresp_cycle),
        .sn_eff_i        (ctrl_wb_sn_eff),
        .wb_occupancy_o  (wb_occupancy)
    );

    // ------------------------------------------------------------------
    // Response sequencer (J4: in-issue-order release); the frontend's
    // response staging always accepts (same contract as amber's core).
    // ------------------------------------------------------------------
    jet_rsp_seq #(
        .RSP_DEPTH (RSP_DEPTH),
        .BUS_WIDTH (BUS_WIDTH),
        .SEQ_W     (SEQ_W)
    ) u_rsp (
        .clk         (aclk),
        .rst_n       (w_aresetn),
        .tag_req_i   (ctrl_tag_req),
        .tag_gnt_o   (rsp_tag_gnt),
        .tag_o       (rsp_tag),
        .cpl_i       (ctrl_cpl_valid),
        .cpl_tag_i   (ctrl_cpl_tag),
        .cpl_data_i  (ctrl_cpl_data),
        .rsp_valid_o (rsp_valid),
        .rsp_data_o  (rsp_data),
        .rsp_ready_i (rsp_room)
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
        .BUS_WIDTH  (BUS_WIDTH)
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
        .rst_n           (w_aresetn),
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
    logic [IW-1:0]        fub_arid, fub_rid;
    logic [ADDR_WIDTH-1:0] fub_araddr;
    logic [7:0]           fub_arlen;
    logic [2:0]           fub_arsize;
    logic [1:0]           fub_arburst;
    logic                 fub_arlock;
    logic [3:0]           fub_arcache;
    logic [2:0]           fub_arprot;
    logic [3:0]           fub_arqos;
    logic [3:0]           fub_arregion;
    logic [UW-1:0]        fub_aruser;
    logic                 fub_arvalid, fub_arready;
    logic [BUS_WIDTH-1:0] fub_rdata;
    logic [1:0]           fub_rresp_raw;
    logic [3:0]           fub_rresp;
    logic                 fub_rlast;
    logic [UW-1:0]        fub_ruser;
    logic                 fub_rvalid, fub_rready;

    assign fub_rresp = {2'b0, fub_rresp_raw};

    logic [IW-1:0]        fub_awid, fub_bid;
    logic [ADDR_WIDTH-1:0] fub_awaddr;
    logic [7:0]           fub_awlen;
    logic [2:0]           fub_awsize;
    logic [1:0]           fub_awburst;
    logic                 fub_awlock;
    logic [3:0]           fub_awcache;
    logic [2:0]           fub_awprot;
    logic [3:0]           fub_awqos;
    logic [3:0]           fub_awregion;
    logic [UW-1:0]        fub_awuser;
    logic                 fub_awvalid, fub_awready;
    logic [BUS_WIDTH-1:0] fub_wdata;
    logic [STRB_W-1:0]    fub_wstrb;
    logic                 fub_wlast;
    logic [UW-1:0]        fub_wuser;
    logic                 fub_wvalid, fub_wready;
    logic [1:0]           fub_bresp;
    logic [UW-1:0]        fub_buser;
    logic                 fub_bvalid, fub_bready;

    l1_fill #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH)
    ) u_fill (
        .clk               (aclk),
        .rst_n             (w_aresetn),
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
        .fub_axi_arid      (fub_arid),
        .fub_axi_araddr    (fub_araddr),
        .fub_axi_arlen     (fub_arlen),
        .fub_axi_arsize    (fub_arsize),
        .fub_axi_arburst   (fub_arburst),
        .fub_axi_arlock    (fub_arlock),
        .fub_axi_arcache   (fub_arcache),
        .fub_axi_arprot    (fub_arprot),
        .fub_axi_arqos     (fub_arqos),
        .fub_axi_arregion  (fub_arregion),
        .fub_axi_aruser    (fub_aruser),
        .fub_axi_arvalid   (fub_arvalid),
        .fub_axi_arready   (fub_arready),
        .fub_axi_rid       (fub_rid),
        .fub_axi_rdata     (fub_rdata),
        .fub_axi_rresp     (fub_rresp),
        .fub_axi_rlast     (fub_rlast),
        .fub_axi_ruser     (fub_ruser),
        .fub_axi_rvalid    (fub_rvalid),
        .fub_axi_rready    (fub_rready)
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
        .rst_n            (w_aresetn),
        .drain_start      (ctrl_drain_start),
        .victim_addr      (wb_drain_addr),
        .victim_data      (wb_drain_data),
        .drain_done       (eng_drain_done),
        .fub_axi_awid     (fub_awid),
        .fub_axi_awaddr   (fub_awaddr),
        .fub_axi_awlen    (fub_awlen),
        .fub_axi_awsize   (fub_awsize),
        .fub_axi_awburst  (fub_awburst),
        .fub_axi_awlock   (fub_awlock),
        .fub_axi_awcache  (fub_awcache),
        .fub_axi_awprot   (fub_awprot),
        .fub_axi_awqos    (fub_awqos),
        .fub_axi_awregion (fub_awregion),
        .fub_axi_awuser   (fub_awuser),
        .fub_axi_awvalid  (fub_awvalid),
        .fub_axi_awready  (fub_awready),
        .fub_axi_wdata    (fub_wdata),
        .fub_axi_wstrb    (fub_wstrb),
        .fub_axi_wlast    (fub_wlast),
        .fub_axi_wuser    (fub_wuser),
        .fub_axi_wvalid   (fub_wvalid),
        .fub_axi_wready   (fub_wready),
        .fub_axi_bid      (fub_bid),
        .fub_axi_bresp    (fub_bresp),
        .fub_axi_buser    (fub_buser),
        .fub_axi_bvalid   (fub_bvalid),
        .fub_axi_bready   (fub_bready)
    );

    // ------------------------------------------------------------------
    // ACE snoop responder (wraps the house axi4ace_snoop_slave transport)
    // ------------------------------------------------------------------
    l1_snoop_resp #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (BUS_WIDTH),
        .LINE_BYTES (LINE_BYTES)
    ) u_snoop (
        .aclk           (aclk),
        .aresetn        (w_aresetn),
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
        .ctrl_snoop_req    (sn_req),
        .ctrl_snoop_addr   (sn_addr),
        .ctrl_snoop_type   (sn_type),
        .ctrl_snoop_ready  (sn_ready),
        .ctrl_snoop_safe   (sn_safe),
        .ctrl_crresp       (sn_crresp),
        .ctrl_cddata       (sn_cddata),
        .ctrl_cdlast       (sn_cdlast),
        .ctrl_cdvalid      (sn_cdvalid),
        .ctrl_cdready      (sn_cdready)
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

    `ALWAYS_FF_RST(aclk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
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

    assign coh_req_valid = w_fill_accept | ctrl_drain_start | r_wb_coh_pend;
    assign coh_req_addr  = w_fill_accept ? ctrl_fill_addr
                         : r_wb_coh_pend ? r_wb_coh_addr
                                         : wb_drain_addr;
    assign coh_req_type  = w_fill_accept ? eng_fill_class
                                         : 3'(AMBER_ACE_WRITE_BACK);

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
    `ALWAYS_FF_RST(aclk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
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

    logic        core_mon_valid;
    logic        core_mon_ready;
    logic [127:0] core_mon_packet;
    logic [63:0] core_mon_timestamp;
    logic [7:0]  core_mon_dropped_unused;

    l1_monlite #(
        .ADDR_WIDTH  (ADDR_WIDTH),
        .SETS        (SETS),
        .WAYS        (WAYS),
        .LINE_BYTES  (LINE_BYTES),
        .BUS_WIDTH   (BUS_WIDTH),
        .USE_MONITOR (USE_MONITOR)
    ) u_monlite (
        .clk                 (aclk),
        .rst_n               (w_aresetn),
        .tap_ctrl_state      (mon_state),
        .tap_hit_set         (lkup_addr[OFF_W +: SET_W]),
        .tap_hit_way         (u_control.w_hit_way),
        .tap_hit_state_before(u_control.w_hit_state),
        .tap_req_we          (lkup_we),
        .tap_miss_set        (r_mon_miss_set),
        .tap_miss_class      (2'(AMBER_MISS_UNKNOWN)),
        .tap_snoop_fire      (sn_req & sn_ready),
        .tap_snoop_type      (sn_type),
        .tap_snoop_hit       (sn_crresp != '0),
        .tap_snoop_resp      (sn_crresp),
        .tap_victim_load     (ctrl_mshr_alloc & mshr_alloc_gnt
                              & ctrl_mshr_alloc_wb_valid),
        .tap_victim_addr     ({ctrl_wb_cap_line, {OFF_W{1'b0}}}),
        .tap_victim_way      (ctrl_mshr_alloc_victim_way),
        .tap_victim_state    (AMBER_STATE_M),
        .tap_tag_wr_en       (ctrl_tag_a_wr_en),
        .tap_tag_wr_set      (ctrl_tag_a_wr_set),
        .tap_tag_wr_way      (mon_tag_wr_way),
        .tap_tag_wr_new_state(ctrl_tag_a_wr_tag_state[2:0]),
        .tap_state_old       (mon_state_old),
        .tap_fill_addr       (ctrl_fill_addr),
        .tap_drain_done      (eng_drain_done),
        .i_mon_time          (i_mon_time),
        .monbus_valid        (core_mon_valid),
        .monbus_ready        (core_mon_ready),
        .monbus_packet       (core_mon_packet),
        .monbus_timestamp    (core_mon_timestamp),
        .dropped_count       (core_mon_dropped_unused)
    );

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_core_mon;
    assign unused_core_mon = &{1'b0, core_mon_dropped_unused,
                               eng_fill_inflight, ctrl_lkup_merge,
                               ctrl_lkup_stall, ctrl_lkup_stall_reason,
                               ctrl_lkup_wr_yield};
    /* verilator lint_on UNUSEDSIGNAL */

    // ------------------------------------------------------------------
    // Read transport: fub_axi (the fill engine) -> m_axi AR/R, observed
    // ------------------------------------------------------------------
    logic        rd_mon_valid;
    logic        rd_mon_ready;
    logic [127:0] rd_mon_packet;
    logic [63:0] rd_mon_timestamp;

    axi4_master_rd_monlite #(
        .USE_MONITOR      (USE_MONITOR),
        .UNIT_ID          (8'h02),
        .AGENT_ID         (16'h00A1),
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (ADDR_WIDTH),
        .AXI_DATA_WIDTH   (BUS_WIDTH),
        .AXI_USER_WIDTH   (AXI_USER_WIDTH)
    ) u_rd_monlite (
        .aclk                    (aclk),
        .aresetn                 (w_aresetn),
        .fub_axi_arid            (fub_arid),
        .fub_axi_araddr          (fub_araddr),
        .fub_axi_arlen           (fub_arlen),
        .fub_axi_arsize          (fub_arsize),
        .fub_axi_arburst         (fub_arburst),
        .fub_axi_arlock          (fub_arlock),
        .fub_axi_arcache         (fub_arcache),
        .fub_axi_arprot          (fub_arprot),
        .fub_axi_arqos           (fub_arqos),
        .fub_axi_arregion        (fub_arregion),
        .fub_axi_aruser          (fub_aruser),
        .fub_axi_arvalid         (fub_arvalid),
        .fub_axi_arready         (fub_arready),
        .fub_axi_rid             (fub_rid),
        .fub_axi_rdata           (fub_rdata),
        .fub_axi_rresp           (fub_rresp_raw),
        .fub_axi_rlast           (fub_rlast),
        .fub_axi_ruser           (fub_ruser),
        .fub_axi_rvalid          (fub_rvalid),
        .fub_axi_rready          (fub_rready),
        .m_axi_arid              (m_axi_arid),
        .m_axi_araddr            (m_axi_araddr),
        .m_axi_arlen             (m_axi_arlen),
        .m_axi_arsize            (m_axi_arsize),
        .m_axi_arburst           (m_axi_arburst),
        .m_axi_arlock            (m_axi_arlock),
        .m_axi_arcache           (m_axi_arcache),
        .m_axi_arprot            (m_axi_arprot),
        .m_axi_arqos             (m_axi_arqos),
        .m_axi_arregion          (m_axi_arregion),
        .m_axi_aruser            (m_axi_aruser),
        .m_axi_arvalid           (m_axi_arvalid),
        .m_axi_arready           (m_axi_arready),
        .m_axi_rid               (m_axi_rid),
        .m_axi_rdata             (m_axi_rdata),
        .m_axi_rresp             (m_axi_rresp),
        .m_axi_rlast             (m_axi_rlast),
        .m_axi_ruser             (m_axi_ruser),
        .m_axi_rvalid            (m_axi_rvalid),
        .m_axi_rready            (m_axi_rready),
        .busy                    (),
        .cam_clear               (1'b0),
        .cfg_monitor_enable      (1'b1),
        .cfg_error_enable        (1'b0),
        .cfg_timeout_enable      (1'b0),
        .cfg_compl_enable        (1'b0),
        .cfg_threshold_enable    (1'b0),
        .cfg_timeout_cycles      (16'h0000),
        .cfg_freq_sel            (4'h0),
        .cfg_axi_pkt_mask        (16'h0000),
        .cfg_latency_threshold   (32'h0000_0000),
        .cfg_addr_check_enable   (1'b0),
        .cfg_addr_match_enable   (1'b0),
        .cfg_addr_range_enable   ('0),
        .cfg_addr_range_low      ('0),
        .cfg_addr_range_high     ('0),
        .i_mon_time              (i_mon_time),
        .monbus_valid            (rd_mon_valid),
        .monbus_ready            (rd_mon_ready),
        .monbus_packet           (rd_mon_packet),
        .monbus_timestamp        (rd_mon_timestamp),
        .active_transactions     (),
        .error_count             (),
        .transaction_count       (),
        .dropped_count           (),
        .refused_count           ()
    );

    // ------------------------------------------------------------------
    // Write transport: fub_axi (the drain engine) -> m_axi AW/W/B, observed
    // ------------------------------------------------------------------
    logic        wr_mon_valid;
    logic        wr_mon_ready;
    logic [127:0] wr_mon_packet;
    logic [63:0] wr_mon_timestamp;

    axi4_master_wr_monlite #(
        .USE_MONITOR      (USE_MONITOR),
        .UNIT_ID          (8'h03),
        .AGENT_ID         (16'h00A1),
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH   (ADDR_WIDTH),
        .AXI_DATA_WIDTH   (BUS_WIDTH),
        .AXI_USER_WIDTH   (AXI_USER_WIDTH)
    ) u_wr_monlite (
        .aclk                    (aclk),
        .aresetn                 (w_aresetn),
        .fub_axi_awid            (fub_awid),
        .fub_axi_awaddr          (fub_awaddr),
        .fub_axi_awlen           (fub_awlen),
        .fub_axi_awsize          (fub_awsize),
        .fub_axi_awburst         (fub_awburst),
        .fub_axi_awlock          (fub_awlock),
        .fub_axi_awcache         (fub_awcache),
        .fub_axi_awprot          (fub_awprot),
        .fub_axi_awqos           (fub_awqos),
        .fub_axi_awregion        (fub_awregion),
        .fub_axi_awuser          (fub_awuser),
        .fub_axi_awvalid         (fub_awvalid),
        .fub_axi_awready         (fub_awready),
        .fub_axi_wdata           (fub_wdata),
        .fub_axi_wstrb           (fub_wstrb),
        .fub_axi_wlast           (fub_wlast),
        .fub_axi_wuser           (fub_wuser),
        .fub_axi_wvalid          (fub_wvalid),
        .fub_axi_wready          (fub_wready),
        .fub_axi_bid             (fub_bid),
        .fub_axi_bresp           (fub_bresp),
        .fub_axi_buser           (fub_buser),
        .fub_axi_bvalid          (fub_bvalid),
        .fub_axi_bready          (fub_bready),
        .m_axi_awid              (m_axi_awid),
        .m_axi_awaddr            (m_axi_awaddr),
        .m_axi_awlen             (m_axi_awlen),
        .m_axi_awsize            (m_axi_awsize),
        .m_axi_awburst           (m_axi_awburst),
        .m_axi_awlock            (m_axi_awlock),
        .m_axi_awcache           (m_axi_awcache),
        .m_axi_awprot            (m_axi_awprot),
        .m_axi_awqos             (m_axi_awqos),
        .m_axi_awregion          (m_axi_awregion),
        .m_axi_awuser            (m_axi_awuser),
        .m_axi_awvalid           (m_axi_awvalid),
        .m_axi_awready           (m_axi_awready),
        .m_axi_wdata             (m_axi_wdata),
        .m_axi_wstrb             (m_axi_wstrb),
        .m_axi_wlast             (m_axi_wlast),
        .m_axi_wuser             (m_axi_wuser),
        .m_axi_wvalid            (m_axi_wvalid),
        .m_axi_wready            (m_axi_wready),
        .m_axi_bid               (m_axi_bid),
        .m_axi_bresp             (m_axi_bresp),
        .m_axi_buser             (m_axi_buser),
        .m_axi_bvalid            (m_axi_bvalid),
        .m_axi_bready            (m_axi_bready),
        .busy                    (),
        .cam_clear               (1'b0),
        .cfg_monitor_enable      (1'b1),
        .cfg_error_enable        (1'b0),
        .cfg_timeout_enable      (1'b0),
        .cfg_compl_enable        (1'b0),
        .cfg_threshold_enable    (1'b0),
        .cfg_timeout_cycles      (16'h0000),
        .cfg_freq_sel            (4'h0),
        .cfg_axi_pkt_mask        (16'h0000),
        .cfg_latency_threshold   (32'h0000_0000),
        .cfg_addr_check_enable   (1'b0),
        .cfg_addr_match_enable   (1'b0),
        .cfg_addr_range_enable   ('0),
        .cfg_addr_range_low      ('0),
        .cfg_addr_range_high     ('0),
        .i_mon_time              (i_mon_time),
        .monbus_valid            (wr_mon_valid),
        .monbus_ready            (wr_mon_ready),
        .monbus_packet           (wr_mon_packet),
        .monbus_timestamp        (wr_mon_timestamp),
        .active_transactions     (),
        .error_count             (),
        .transaction_count       (),
        .dropped_count           (),
        .refused_count           ()
    );

    // ------------------------------------------------------------------
    // D-7 MonBus arbiter: {l1_monlite, rd_monlite, wr_monlite} -> the one
    // MonBus port pair
    // ------------------------------------------------------------------
    logic                    arb_vld [3];
    logic                    arb_rdy [3];
    ocelus_common_pkg::monitor_packet_t   arb_pkt [3];
    ocelus_common_pkg::monbus_timestamp_t arb_ts  [3];

    assign arb_vld[0] = core_mon_valid;
    assign arb_vld[1] = rd_mon_valid;
    assign arb_vld[2] = wr_mon_valid;
    assign core_mon_ready = arb_rdy[0];
    assign rd_mon_ready   = arb_rdy[1];
    assign wr_mon_ready   = arb_rdy[2];
    assign arb_pkt[0] = core_mon_packet;
    assign arb_pkt[1] = rd_mon_packet;
    assign arb_pkt[2] = wr_mon_packet;
    assign arb_ts[0]  = core_mon_timestamp;
    assign arb_ts[1]  = rd_mon_timestamp;
    assign arb_ts[2]  = wr_mon_timestamp;

    monbus_arbiter #(
        .CLIENTS            (3),
        .INPUT_SKID_ENABLE  (1),
        .OUTPUT_SKID_ENABLE (1),
        .INPUT_SKID_DEPTH   (2),
        .OUTPUT_SKID_DEPTH  (2)
    ) u_monbus_arbiter (
        .axi_aclk            (aclk),
        .axi_aresetn         (w_aresetn),
        .block_arb           (1'b0),
        .monbus_valid_in     (arb_vld),
        .monbus_ready_in     (arb_rdy),
        .monbus_packet_in    (arb_pkt),
        .monbus_timestamp_in (arb_ts),
        .monbus_valid        (mon_valid),
        .monbus_ready        (mon_ready),
        .monbus_packet       (mon_packet),
        .monbus_timestamp    (mon_timestamp),
        .grant_valid         (),
        .grant               (),
        .grant_id            (),
        .last_grant          ()
    );

    // ------------------------------------------------------------------
    // Simulation-only integration checks
    // ------------------------------------------------------------------
    // pragma translate_off
    // The launch adapter never lets a fill's beats race the victim
    // capture (MAS ch02/01 fill-engine contract): no accept while a
    // capture streams, and never on the cycle a dirty-victim capture
    // opens (cap_busy_o rises one cycle later).
    assert property (@(posedge aclk) disable iff (!w_aresetn)
        (w_fill_accept |-> !ctrl_cap_busy))
        else $error("jet_top: fill launch accepted during a victim capture");

    assert property (@(posedge aclk) disable iff (!w_aresetn)
        (w_fill_accept |-> !(ctrl_mshr_alloc & ctrl_mshr_alloc_wb_valid)))
        else $error("jet_top: fill launch accepted on a dirty-victim alloc cycle");

    // The engine is idle exactly when the adapter is not busy.
    assert property (@(posedge aclk) disable iff (!w_aresetn)
        (w_fill_accept |-> !r_eng_busy))
        else $error("jet_top: fill launch accepted while the engine is busy");

    // A held launch is always the pending record's (no same-cycle alloc).
    assert property (@(posedge aclk) disable iff (!w_aresetn)
        ((w_fill_accept & (ctrl_fill_cls != JET_CLS_CU)
          & ~(ctrl_mshr_alloc & mshr_alloc_gnt)) |-> r_pend_valid))
        else $error("jet_top: held fill launch with no pending alloc record");

    // The D-8 sideband never drops a fill launch (a drain-start collision
    // replays the WRITE_BACK the next cycle -- see the sideband note).
    assert property (@(posedge aclk) disable iff (!w_aresetn)
        (w_fill_accept |-> (coh_req_valid
                            && (coh_req_type != 3'(AMBER_ACE_WRITE_BACK)))))
        else $error("jet_top: fill launch dropped from the coh sideband");
    // a drain-start/fill-launch collision registers the replay
    assert property (@(posedge aclk) disable iff (!w_aresetn)
        ((ctrl_drain_start & w_fill_accept) |=> r_wb_coh_pend))
        else $error("jet_top: collided drain start not replayed");
    // a pending replay always drives the sideband when no fill wins
    wire w_wb_replay_fires = r_wb_coh_pend & ~w_fill_accept;
    assert property (@(posedge aclk) disable iff (!w_aresetn)
        (w_wb_replay_fires |-> (coh_req_valid
                                && (coh_req_type == 3'(AMBER_ACE_WRITE_BACK)))))
        else $error("jet_top: pending WRITE_BACK replay not driven");
    // pragma translate_on

endmodule : jet_top
