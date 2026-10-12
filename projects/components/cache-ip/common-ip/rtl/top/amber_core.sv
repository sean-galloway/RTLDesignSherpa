// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_core
// Purpose:
//   First end-to-end cache top for the amber MESI L1 (MAS ch01 hierarchy):
//   the shipping structural integrator for the nine landed FUBs --
//   amber_cpu_frontend, amber_control (with the amber_pending_fill_bypass /
//   amber_victim leaves), amber_tag_array, amber_data_array, amber_repl,
//   amber_fill, amber_drain, amber_snoop_resp, amber_monlite. Pure
//   structural integration: no new control logic. The external shape is
//   MAS ch01/02 minus the top-level masters: CPU GAXI slave, the raw
//   fub_axi_* rd/wr master sides the engines drive (the house
//   axi4_master_rd/wr transports are a rig-top concern, DECISION D3), the
//   ACE snoop responder, MonBus observation (*_monlite only, PRD D8), and
//   the pair-rig coherence sideband coh_req_{valid,addr,type} (DECISION
//   D-8) for Task 11. amber_top / amber_ace_top wrap this core later.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch01_overview/01_architecture.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-08

`timescale 1ns / 1ps

//==============================================================================
// Module: amber_core
//==============================================================================
// Description:
//   Hierarchy (MAS ch01 block diagram):
//
//     amber_core
//     |-- u_frontend  amber_cpu_frontend   GAXI slave <-> control contract
//     |-- u_control   amber_control        the only FSM; owns the pf /
//     |    |                               victim leaves and every
//     |    |                               partner handshake
//     |-- u_tag       amber_tag_array      port A CPU/fill, port B snoop
//     |-- u_data      amber_data_array     port A CPU/fill beats, port B CD
//     |-- u_repl      amber_repl           victim-way select + policy state
//     |-- u_fill      amber_fill           AXI4 read sequencing -> fub_axi_*
//     |-- u_drain     amber_drain          AXI4 write sequencing -> fub_axi_*
//     |-- u_snoop     amber_snoop_resp     ACE transport + SR sequencing
//     `-- u_monlite   amber_monlite        drop-and-count MonBus observer
//
//   Structural decisions pinned here:
//
//   * Data-array write port (single, MAS ch02_blocks/03): amber_control's
//     CPU merge wins over amber_fill's received beats -- never simultaneous
//     by construction (control merges only in CTRL_HIT_WR, fill beats only
//     land in CTRL_MISS_FILL), the same landed harness idiom. Fill beats
//     install into the victim way at {fill set, beat idx}: the fill's set
//     is the in-flight request's set, which control holds on the port-A
//     tag lookup pins for the whole transaction, and the victim way exists
//     only inside the control context -- it is tapped read-only (see
//     below). repl_victim_way is NOT a substitute: the RANDOM policy
//     advances at the MISS_VICTIM request, so it is unstable across the
//     MISS_VICTIM -> MISS_FILL boundary.
//
//   * MonBus observation taps (MAS ch04): signals that name control
//     context the port contract does not export (hit/miss/snoop/victim
//     payload registers) use READ-ONLY hierarchical references into
//     u_control -- the same sanctioned pattern the landed harnesses use
//     (dv/tb/amber_monlite_th.sv: "amber_core owns the real wiring in
//     integration"); the landed block port contracts (MAS ch02) are pinned
//     and do not grow. The observer still drives nothing in the datapath.
//
//   * coh_req sideband (DECISION D-8): one pulse per coherence request the
//     cache raises -- fill launches (READ_SHARED / READ_UNIQUE on a miss,
//     CLEAN_UNIQUE on an upgrade; the class rides ctrl_req_class) and dirty
//     write-back launches (WRITE_BACK; the victim address rides
//     ctrl_victim_addr_in). Clean evictions are silent (a clean drop is
//     invisible to the coherence domain). Pure observation output: honest
//     for standalone use, consumed by the Task 11 pair rig.
//
//   * D11 queue inventory (this closure): the two DECISION D-6
//     gaxi_fifo_sync queues -- the frontend response staging FIFO and the
//     monlite observer queue -- plus the fill R-beat staging FIFO, are the
//     landed shared-storage primitives; see the amber_core.f header.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / WAYS / LINE_BYTES / BUS_WIDTH:
//     Description: geometry per amber_pkg defaults (HAS Table 5.0)
//     Type: int
//   REPL_POLICY:
//     Description: replacement policy; amber_repl_t encodings (0=lru,
//                  1=tree_plru, 2=fifo, 3=random), int for -G overrides
//     Type: int
//   AXI_ID_WIDTH / AXI_USER_WIDTH:
//     Description: fub_axi id/user field widths, matching the engines
//     Type: int
//   USE_MONITOR:
//     Description: 0 ties the MonBus observer outputs off (house idiom)
//     Type: bit
//
//------------------------------------------------------------------------------
// Notes:
//   - Single clock / active-low reset domain (clk / rst_n), MAS ch01/03.
//   - The fub_axi_* ports are the raw engine-side master pins; the
//     axi4_master_rd/wr wrappers (AR/R and AW/W/B skids) are instantiated
//     by the rig top, not here (DECISION D3: amber wraps the core "with"
//     the transports).
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: amber_top / amber_ace_top (Tasks 10/12)
//   - Instantiated: the nine amber FUBs (see hierarchy above)
//   - Package: amber_pkg (geometry, ace_req_t)
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_core.py
//   Plan: dv/testplans/amber_core_testplan.yaml
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_core.py -v
//
//==============================================================================

module amber_core
    import amber_pkg::*;
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
    localparam int SET_INDEX_WIDTH   = $clog2(SETS),
    localparam int LINE_OFFSET_WIDTH = $clog2(LINE_BYTES),
    localparam int TAG_WIDTH         = ADDR_WIDTH - SET_INDEX_WIDTH
                                       - LINE_OFFSET_WIDTH,
    localparam int TAG_STATE_WIDTH   = TAG_WIDTH + 3,
    localparam int STRB_W            = BUS_WIDTH / 8,
    localparam int FILL_BEATS        = LINE_BYTES / STRB_W,
    localparam int BEAT_INDEX_WIDTH  = $clog2(FILL_BEATS),
    localparam int WAY_INDEX_WIDTH   = $clog2(WAYS),
    localparam int MEM_ADDR_WIDTH    = SET_INDEX_WIDTH + BEAT_INDEX_WIDTH,
    localparam int IW                = AXI_ID_WIDTH,
    localparam int UW                = AXI_USER_WIDTH,
    localparam int CPU_REQ_W         = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH,
    localparam int CPU_RSP_W         = BUS_WIDTH
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // ------------------------------------------------------------------
    // CPU GAXI slave (MAS ch03/01; packed {addr, we, be, wdata} /
    // {rdata})
    // ------------------------------------------------------------------
    input  logic                        cpu_req_wr_valid,
    output logic                        cpu_req_wr_ready,
    input  logic [CPU_REQ_W-1:0]        cpu_req_wr_data,
    output logic                        cpu_rsp_rd_valid,
    input  logic                        cpu_rsp_rd_ready,
    output logic [CPU_RSP_W-1:0]        cpu_rsp_rd_data,

    // ------------------------------------------------------------------
    // fub_axi read master side (amber_fill -> axi4_master_rd in the rig
    // top; DECISION D3)
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
    input  logic [1:0]                  fub_axi_rresp,
    input  logic                        fub_axi_rlast,
    input  logic [UW-1:0]               fub_axi_ruser,
    input  logic                        fub_axi_rvalid,
    output logic                        fub_axi_rready,

    // ------------------------------------------------------------------
    // fub_axi write master side (amber_drain -> axi4_master_wr)
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
    // Pair-rig coherence sideband (DECISION D-8; amber_ace_req_t type)
    // ------------------------------------------------------------------
    output logic                        coh_req_valid,
    output logic [ADDR_WIDTH-1:0]       coh_req_addr,
    output logic [2:0]                  coh_req_type,

    // ------------------------------------------------------------------
    // MonBus observation (*_monlite only, PRD D8; MAS ch03/05)
    // ------------------------------------------------------------------
    input  logic [63:0]                 mon_time,
    output logic                        mon_valid,
    input  logic                        mon_ready,
    output logic [127:0]                mon_packet,
    output logic [63:0]                 mon_timestamp,
    output logic [7:0]                  mon_dropped,

    // ------------------------------------------------------------------
    // Status / observability
    // ------------------------------------------------------------------
    output logic                        init_busy,
    output logic [3:0]                  ctrl_state
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the FUBs)
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("amber_core: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("amber_core: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0 || FILL_BEATS < 2)
            $error("amber_core: LINE_BYTES / BUS_WIDTH*8 must be a power of two >= 2");
        if ((BUS_WIDTH % 8) != 0)
            $error("amber_core: BUS_WIDTH must be a multiple of 8");
        if (WAYS < 2)
            $error("amber_core: WAYS must be >= 2");
        if (TAG_WIDTH < 1)
            $error("amber_core: ADDR_WIDTH too small for SETS/LINE_BYTES");
    end

    // ------------------------------------------------------------------
    // frontend <-> control request/response contract
    // ------------------------------------------------------------------
    logic                     fe_req_valid;
    logic [ADDR_WIDTH-1:0]    fe_req_addr;
    logic                     fe_req_we;
    logic [STRB_W-1:0]        fe_req_be;
    logic [BUS_WIDTH-1:0]     fe_req_wdata;
    logic                     ctrl_req_ready;
    logic                     ctrl_rsp_valid;
    logic [BUS_WIDTH-1:0]     ctrl_rsp_data;

    amber_cpu_frontend #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_frontend (
        .clk               (clk),
        .rst_n             (rst_n),
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
        .ctrl_rsp_valid    (ctrl_rsp_valid),
        .ctrl_rsp_data     (ctrl_rsp_data)
    );

    // ------------------------------------------------------------------
    // control <-> array / repl / partner wiring
    // ------------------------------------------------------------------
    logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_a_set;
    logic [WAYS-1:0][TAG_STATE_WIDTH-1:0]  ctrl_tag_a_tag_state;
    logic                                  ctrl_tag_a_wr_en;
    logic [WAYS-1:0]                       ctrl_tag_a_wr_way_onehot;
    logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_a_wr_set;
    logic [TAG_STATE_WIDTH-1:0]            ctrl_tag_a_wr_tag_state;
    logic                                  ctrl_tag_b_req_unused;
    logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_b_set;
    logic [WAYS-1:0][TAG_STATE_WIDTH-1:0]  ctrl_tag_b_tag_state;

    logic [MEM_ADDR_WIDTH-1:0]             ctrl_data_a_addr;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_data_a_way;
    logic [BUS_WIDTH-1:0]                  ctrl_data_a_rdata;
    logic                                  ctrl_data_a_wr_en;
    logic [WAYS-1:0]                       ctrl_data_a_wr_way_onehot;
    logic [MEM_ADDR_WIDTH-1:0]             ctrl_data_a_wr_addr;
    logic [BUS_WIDTH-1:0]                  ctrl_data_a_wr_wdata;
    logic [STRB_W-1:0]                     ctrl_data_a_wr_be;
    logic [MEM_ADDR_WIDTH-1:0]             ctrl_data_b_addr;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_data_b_way;
    logic [BUS_WIDTH-1:0]                  ctrl_data_b_rdata;

    logic                                  ctrl_repl_req;
    logic [SET_INDEX_WIDTH-1:0]            ctrl_repl_set;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_repl_way;
    logic                                  ctrl_repl_hit;
    logic                                  ctrl_repl_update;
    logic [WAY_INDEX_WIDTH-1:0]            ctrl_repl_hit_way;

    logic                                  ctrl_victim_load;
    logic [ADDR_WIDTH-1:0]                 ctrl_victim_addr_in;
    logic [LINE_BYTES*8-1:0]               ctrl_victim_data_in;

    logic                                  ctrl_fill_start;
    logic [ADDR_WIDTH-1:0]                 ctrl_fill_addr;
    logic [2:0]                            ctrl_req_class;
    logic                                  ctrl_fill_done;
    logic                                  ctrl_fill_beat_valid;
    logic [BEAT_INDEX_WIDTH-1:0]           ctrl_fill_beat_idx;
    logic [BUS_WIDTH-1:0]                  fill_beat_data;

    logic                                  ctrl_drain_start;
    logic                                  ctrl_drain_done;

    logic                                  ctrl_snoop_req;
    logic                                  ctrl_snoop_ready;
    logic [2:0]                            ctrl_snoop_type;
    logic [ADDR_WIDTH-1:0]                 ctrl_snoop_addr;
    logic [AMBER_CRRESP_WIDTH-1:0]         ctrl_crresp;
    logic [BUS_WIDTH-1:0]                  ctrl_cddata;
    logic                                  ctrl_cdlast;
    logic                                  ctrl_cdvalid;
    logic                                  ctrl_cdready;

    amber_control #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_control (
        .clk                     (clk),
        .rst_n                   (rst_n),
        .req_valid               (fe_req_valid),
        .req_addr                (fe_req_addr),
        .req_we                  (fe_req_we),
        .req_be                  (fe_req_be),
        .req_wdata               (fe_req_wdata),
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
        .ctrl_data_a_wr_en       (ctrl_data_a_wr_en),
        .ctrl_data_a_wr_way_onehot(ctrl_data_a_wr_way_onehot),
        .ctrl_data_a_wr_addr     (ctrl_data_a_wr_addr),
        .ctrl_data_a_wr_wdata    (ctrl_data_a_wr_wdata),
        .ctrl_data_a_wr_be       (ctrl_data_a_wr_be),
        .ctrl_tag_b_req          (ctrl_tag_b_req_unused),
        .ctrl_tag_b_set          (ctrl_tag_b_set),
        .ctrl_tag_b_tag_state    (ctrl_tag_b_tag_state),
        .ctrl_data_b_addr        (ctrl_data_b_addr),
        .ctrl_data_b_way         (ctrl_data_b_way),
        .ctrl_data_b_rdata       (ctrl_data_b_rdata),
        .ctrl_repl_req           (ctrl_repl_req),
        .ctrl_repl_set           (ctrl_repl_set),
        .ctrl_repl_way           (ctrl_repl_way),
        .ctrl_repl_hit           (ctrl_repl_hit),
        .ctrl_repl_update        (ctrl_repl_update),
        .ctrl_repl_hit_way       (ctrl_repl_hit_way),
        .ctrl_victim_load        (ctrl_victim_load),
        .ctrl_victim_addr_in     (ctrl_victim_addr_in),
        .ctrl_victim_data_in     (ctrl_victim_data_in),
        .ctrl_fill_start         (ctrl_fill_start),
        .ctrl_fill_addr          (ctrl_fill_addr),
        .ctrl_req_class          (ctrl_req_class),
        .ctrl_fill_done          (ctrl_fill_done),
        .ctrl_fill_beat_valid    (ctrl_fill_beat_valid),
        .ctrl_fill_beat_idx      (ctrl_fill_beat_idx),
        .ctrl_drain_start        (ctrl_drain_start),
        .ctrl_drain_done         (ctrl_drain_done),
        .ctrl_snoop_req          (ctrl_snoop_req),
        .ctrl_snoop_ready        (ctrl_snoop_ready),
        .ctrl_snoop_type         (ctrl_snoop_type),
        .ctrl_snoop_addr         (ctrl_snoop_addr),
        .ctrl_crresp             (ctrl_crresp),
        .ctrl_cddata             (ctrl_cddata),
        .ctrl_cdlast             (ctrl_cdlast),
        .ctrl_cdvalid            (ctrl_cdvalid),
        .ctrl_cdready            (ctrl_cdready),
        .ctrl_init_busy          (init_busy),
        .ctrl_init_set           (),
        .ctrl_state              (ctrl_state)
    );

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_ctrl_tap;
    assign unused_ctrl_tap = &{1'b0, ctrl_tag_b_req_unused};
    /* verilator lint_on UNUSEDSIGNAL */

    // ------------------------------------------------------------------
    // tag array: port A control-owned (CPU lookup + writes), port B
    // control-owned (snoop lookup; no integration backdoor)
    // ------------------------------------------------------------------
    amber_tag_array #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES)
    ) u_tag (
        .clk           (clk),
        .a_set         (ctrl_tag_a_set),
        .a_tag_state   (ctrl_tag_a_tag_state),
        .b_set         (ctrl_tag_b_set),
        .b_tag_state   (ctrl_tag_b_tag_state),
        .wr_en         (ctrl_tag_a_wr_en),
        .wr_way_onehot (ctrl_tag_a_wr_way_onehot),
        .wr_set        (ctrl_tag_a_wr_set),
        .wr_tag_state  (ctrl_tag_a_wr_tag_state)
    );

    // ------------------------------------------------------------------
    // data array: single write port muxed control-CPU-merge (wins) over
    // fill beats; the fill beats install into the victim way at {fill
    // set, beat idx} (never simultaneous by construction)
    // ------------------------------------------------------------------
    logic [WAYS-1:0] fill_wr_way_onehot;

    always_comb begin
        for (int w = 0; w < WAYS; w++) begin
            fill_wr_way_onehot[w] =
                (u_control.victim_way_q == WAY_INDEX_WIDTH'(w));
        end
    end

    logic                        data_wr_en;
    logic [WAYS-1:0]             data_wr_way_onehot;
    logic [MEM_ADDR_WIDTH-1:0]   data_wr_addr;
    logic [BUS_WIDTH-1:0]        data_wr_wdata;
    logic [STRB_W-1:0]           data_wr_be;

    always_comb begin
        if (ctrl_data_a_wr_en) begin
            data_wr_way_onehot = ctrl_data_a_wr_way_onehot;
            data_wr_addr       = ctrl_data_a_wr_addr;
            data_wr_wdata      = ctrl_data_a_wr_wdata;
            data_wr_be         = ctrl_data_a_wr_be;
        end else begin
            data_wr_way_onehot = fill_wr_way_onehot;
            data_wr_addr       = {ctrl_tag_a_set, ctrl_fill_beat_idx};
            data_wr_wdata      = fill_beat_data;
            data_wr_be         = {STRB_W{1'b1}};
        end
    end

    assign data_wr_en = ctrl_data_a_wr_en | ctrl_fill_beat_valid;

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

    // ------------------------------------------------------------------
    // replacement engine
    // ------------------------------------------------------------------
    amber_repl #(
        .SETS        (SETS),
        .WAYS        (WAYS),
        .REPL_POLICY (REPL_POLICY)
    ) u_repl (
        .clk             (clk),
        .rst_n           (rst_n),
        .repl_req        (ctrl_repl_req),
        .repl_set        (ctrl_repl_set),
        .repl_victim_way (ctrl_repl_way),
        .repl_hit        (ctrl_repl_hit),
        .repl_update     (ctrl_repl_update),
        .repl_hit_way    (ctrl_repl_hit_way)
    );

    // ------------------------------------------------------------------
    // fill engine (AXI4 read sequencing -> raw fub_axi_* pins; the
    // axi4_master_rd transport is a rig-top concern, DECISION D3)
    // ------------------------------------------------------------------
    amber_fill #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH)
    ) u_fill (
        .clk               (clk),
        .rst_n             (rst_n),
        .fill_start        (ctrl_fill_start),
        .fill_addr         (ctrl_fill_addr),
        .fill_req_class    (ctrl_req_class),
        .fill_done         (ctrl_fill_done),
        .fill_beat_valid   (ctrl_fill_beat_valid),
        .fill_beat_data    (fill_beat_data),
        .fill_beat_idx     (ctrl_fill_beat_idx),
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
    // drain engine (AXI4 write sequencing -> raw fub_axi_* pins)
    // ------------------------------------------------------------------
    amber_drain #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .SETS           (SETS),
        .LINE_BYTES     (LINE_BYTES),
        .BUS_WIDTH      (BUS_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH)
    ) u_drain (
        .clk              (clk),
        .rst_n            (rst_n),
        .drain_start      (ctrl_drain_start),
        .victim_addr      (ctrl_victim_addr_in),
        .victim_data      (ctrl_victim_data_in),
        .drain_done       (ctrl_drain_done),
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
    // ACE snoop responder (wraps the house axi4ace_snoop_slave transport)
    // ------------------------------------------------------------------
    amber_snoop_resp #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (BUS_WIDTH),
        .LINE_BYTES (LINE_BYTES)
    ) u_snoop (
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
        .ctrl_snoop_req    (ctrl_snoop_req),
        .ctrl_snoop_addr   (ctrl_snoop_addr),
        .ctrl_snoop_type   (ctrl_snoop_type),
        .ctrl_snoop_ready  (ctrl_snoop_ready),
        .ctrl_crresp       (ctrl_crresp),
        .ctrl_cddata       (ctrl_cddata),
        .ctrl_cdlast       (ctrl_cdlast),
        .ctrl_cdvalid      (ctrl_cdvalid),
        .ctrl_cdready      (ctrl_cdready)
    );

    // ------------------------------------------------------------------
    // Pair-rig coherence sideband (DECISION D-8): one pulse per coherence
    // request -- fill launches (class on ctrl_req_class) and dirty
    // write-back launches (WRITE_BACK, the staged victim address). Clean
    // evictions are silent. Pure observation output.
    // ------------------------------------------------------------------
    assign coh_req_valid = ctrl_fill_start | ctrl_drain_start;
    assign coh_req_addr  = ctrl_drain_start ? ctrl_victim_addr_in
                                            : ctrl_fill_addr;
    assign coh_req_type  = ctrl_drain_start ? 3'(AMBER_ACE_WRITE_BACK)
                                            : ctrl_req_class;

    // ------------------------------------------------------------------
    // MonBus observer (MAS ch04). Payload taps of control-internal
    // context use read-only hierarchical references -- the sanctioned
    // harness pattern (amber_core owns the real wiring in integration);
    // the observer drives nothing in the datapath.
    // ------------------------------------------------------------------
    logic [WAY_INDEX_WIDTH-1:0] tap_tag_wr_way;

    always_comb begin
        tap_tag_wr_way = '0;
        for (int w = 0; w < WAYS; w++) begin
            if (ctrl_tag_a_wr_way_onehot[w]) begin
                tap_tag_wr_way = WAY_INDEX_WIDTH'(w);
            end
        end
    end

    // old-state resolution per write cause (FILL_WRITE installs over an
    // Invalid line unless it is an upgrade commit, which rewrites the hit
    // way S->M; HIT_WR promotes the hit state; SNOOP rewrites the resolved
    // reference state) -- identical to the landed harness tap
    logic [2:0] tap_state_old;

    always_comb begin
        unique case (ctrl_state)
            AMBER_CTRL_SNOOP:
                tap_state_old = u_control.sn_hit_state_q;
            AMBER_CTRL_HIT_WR:
                tap_state_old = u_control.hit_state_q;
            AMBER_CTRL_FILL_WRITE:
                tap_state_old = u_control.upgr_q ? u_control.hit_state_q
                                                 : AMBER_STATE_I;
            default:
                tap_state_old = AMBER_STATE_I;
        endcase
    end

    amber_monlite #(
        .ADDR_WIDTH  (ADDR_WIDTH),
        .SETS        (SETS),
        .WAYS        (WAYS),
        .LINE_BYTES  (LINE_BYTES),
        .BUS_WIDTH   (BUS_WIDTH),
        .USE_MONITOR (USE_MONITOR)
    ) u_monlite (
        .clk                 (clk),
        .rst_n               (rst_n),
        .tap_ctrl_state      (ctrl_state),
        .tap_hit_set         (ctrl_tag_a_set),
        .tap_hit_way         (u_control.hit_way_q),
        .tap_hit_state_before(u_control.hit_state_q),
        .tap_req_we          (u_control.req_we_q),
        .tap_miss_set        (ctrl_tag_a_set),
        .tap_miss_class      (2'(AMBER_MISS_UNKNOWN)),
        .tap_snoop_fire      (ctrl_snoop_req && ctrl_snoop_ready),
        .tap_snoop_type      (ctrl_snoop_type),
        .tap_snoop_hit       (u_control.sn_hit_any),
        .tap_snoop_resp      (ctrl_crresp),
        .tap_victim_load     (ctrl_victim_load),
        .tap_victim_addr     (ctrl_victim_addr_in),
        .tap_victim_way      (u_control.victim_way_q),
        .tap_victim_state    (u_control.mv_victim_state),
        .tap_tag_wr_en       (ctrl_tag_a_wr_en),
        .tap_tag_wr_set      (ctrl_tag_a_wr_set),
        .tap_tag_wr_way      (tap_tag_wr_way),
        .tap_tag_wr_new_state(ctrl_tag_a_wr_tag_state[2:0]),
        .tap_state_old       (tap_state_old),
        .tap_fill_addr       (ctrl_fill_addr),
        .tap_drain_done      (ctrl_drain_done),
        .i_mon_time          (mon_time),
        .monbus_valid        (mon_valid),
        .monbus_ready        (mon_ready),
        .monbus_packet       (mon_packet),
        .monbus_timestamp    (mon_timestamp),
        .dropped_count       (mon_dropped)
    );

endmodule : amber_core
