// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_control
// Purpose:
//   Blocking-pipeline control FSM for the amber MESI L1 (MAS ch02_blocks/01):
//   the cache's only state machine. Owns the tag-array port-A schedule, the
//   victim-way selection handshake, the pending-fill bypass register, and
//   the start/done handshakes to amber_fill / amber_drain / amber_victim /
//   amber_snoop_resp. Exactly one CPU transaction is in flight at any time
//   (the blocking contract); snoop service on port B is Task 4 and the
//   snoop inputs are stub-tied until then.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/01_amber_control.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-07

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: amber_control
//==============================================================================
// Description:
//   One-hot FSM, one bit per pkg ctrl_state_t code; unique case decode with
//   an explicit illegal/multi-hot default into sticky CTRL_ERROR (reset is
//   the only exit, MAS ch02). Per CPU request:
//
//     IDLE        accept the frontend-latched request (single req_valid
//                 pulse; the front end holds the fields until the response)
//     LOOKUP      combinational tag/state compare on port A; hit service or
//                 miss classification (I-read -> READ_SHARED, I-write ->
//                 READ_UNIQUE, S-write -> CLEAN_UNIQUE upgrade straight to
//                 MISS_FILL -- an upgrade installs no data and evicts no
//                 victim; MAS ch02_blocks/06)
//     HIT_RD/HIT_WR  data-array port A access in the same cycle as the state
//                 check (MAS ch02 stage 2); write hit merges via be and
//                 promotes E->M (tag write suppressed when already M)
//     MISS_VICTIM repl victim way sampled on the first cycle (repl_req is a
//                 one-cycle pulse so RANDOM-policy state advances exactly
//                 once per miss); dirty (Modified) victim: gather the whole
//                 line from data-array port A into the victim-line register,
//                 then victim_load; clean victim: straight to the fill
//     MISS_DRAIN  drain_start pulse, wait drain_done
//     MISS_FILL   fill_start pulse + line address + request class, wait
//                 fill_done; the pending-fill bypass register arms here
//                 (pf_addr/pf_active; snoop-side writers arrive with Task 4)
//     FILL_WRITE  install {tag, state} at the victim way (the fill FUB has
//                 already written the raw beats into the data array); S for
//                 READ_SHARED, M otherwise; REPLAY follows
//     REPLAY      re-present the latched request; the next LOOKUP hits and
//                 the replayed write merges the CPU bytes via be (DECISION
//                 D-4: the GAXI slave sees one request, one response)
//
//   The miss-path launch decision is the workbook K-map cover, evaluated in
//   CTRL_MISS_VICTIM (hit is 0 by construction there):
//     start_drain = victim_dirty & !pending_bypass_match
//     start_fill  = !victim_dirty & !pending_bypass_match
//     replay_now  = pending_bypass_match        (defensive this task: the
//                  blocking pipeline never looks up while a bypass is armed)
//
//   INIT (DECISION D-3): post-reset walk writing STATE_I to every way of
//   every set, one set per cycle (the all-ones way select writes all ways
//   at once); ctrl_req_ready stays low until the walk completes.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / WAYS / LINE_BYTES / BUS_WIDTH:
//     Description: geometry per amber_pkg defaults (HAS Table 5.0)
//     Type: int
//
//------------------------------------------------------------------------------
// Notes:
//   - Tag/data lookups are combinational (landed array contract); a lookup
//     sees a same-set write after the clock edge.
//   - The snoop responder outputs (ctrl_snoop_ready / ctrl_crresp /
//     ctrl_cddata / ctrl_cdlast / ctrl_cdvalid) are tied off this task;
//     CTRL_SNOOP has no entering edge and decodes to CTRL_ERROR if reached.
//   - The data array receives fill beats from amber_fill directly (Task 5);
//     this module's data-array write port serves CPU merges only.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: amber_core (test harness: dv/tb/amber_control_th.sv)
//   - Package: amber_pkg (ctrl_state_t, cache_state_t, amber_ace_req_t)
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_control.py
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_control.py -v
//
//==============================================================================

module amber_control
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
    localparam int MEM_ADDR_WIDTH    = SET_INDEX_WIDTH + BEAT_INDEX_WIDTH,
    localparam int LINE_ADDR_WIDTH   = TAG_WIDTH + SET_INDEX_WIDTH
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // CPU request: single valid pulse from the frontend latch; the front
    // end holds {addr, we, be, wdata} until the response returns
    input  logic                        req_valid,
    input  logic [ADDR_WIDTH-1:0]       req_addr,
    input  logic                        req_we,
    input  logic [STRB_W-1:0]           req_be,
    input  logic [BUS_WIDTH-1:0]        req_wdata,
    output logic                        ctrl_req_ready,
    output logic                        ctrl_rsp_valid,
    output logic [BUS_WIDTH-1:0]        ctrl_rsp_data,

    // tag array port A (CPU/fill lookup + write)
    output logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_a_set,
    input  logic [WAYS-1:0][TAG_STATE_WIDTH-1:0]  ctrl_tag_a_tag_state,
    output logic                                  ctrl_tag_a_wr_en,
    output logic [WAYS-1:0]                       ctrl_tag_a_wr_way_onehot,
    output logic [SET_INDEX_WIDTH-1:0]            ctrl_tag_a_wr_set,
    output logic [TAG_STATE_WIDTH-1:0]            ctrl_tag_a_wr_tag_state,

    // data array port A (CPU hit/replay read + CPU write merge)
    output logic [MEM_ADDR_WIDTH-1:0]   ctrl_data_a_addr,
    output logic [WAY_INDEX_WIDTH-1:0]  ctrl_data_a_way,
    input  logic [BUS_WIDTH-1:0]        ctrl_data_a_rdata,
    output logic                        ctrl_data_a_wr_en,
    output logic [WAYS-1:0]             ctrl_data_a_wr_way_onehot,
    output logic [MEM_ADDR_WIDTH-1:0]   ctrl_data_a_wr_addr,
    output logic [BUS_WIDTH-1:0]        ctrl_data_a_wr_wdata,
    output logic [STRB_W-1:0]           ctrl_data_a_wr_be,

    // replacement engine
    output logic                        ctrl_repl_req,
    output logic [SET_INDEX_WIDTH-1:0]  ctrl_repl_set,
    input  logic [WAY_INDEX_WIDTH-1:0]  ctrl_repl_way,
    output logic                        ctrl_repl_hit,
    output logic                        ctrl_repl_update,
    output logic [WAY_INDEX_WIDTH-1:0]  ctrl_repl_hit_way,

    // depth-1 victim buffer
    output logic                        ctrl_victim_load,
    output logic [ADDR_WIDTH-1:0]       ctrl_victim_addr_in,
    output logic [LINE_BYTES*8-1:0]     ctrl_victim_data_in,

    // fill / drain partners
    output logic                        ctrl_fill_start,
    output logic [ADDR_WIDTH-1:0]       ctrl_fill_addr,
    output logic [2:0]                  ctrl_req_class,
    input  logic                        ctrl_fill_done,
    output logic                        ctrl_drain_start,
    input  logic                        ctrl_drain_done,

    // snoop responder interface (stub-tied this task; Task 4 services)
    input  logic                        ctrl_snoop_req,
    output logic                        ctrl_snoop_ready,
    input  logic [2:0]                  ctrl_snoop_type,
    input  logic [ADDR_WIDTH-1:0]       ctrl_snoop_addr,
    output logic [AMBER_CRRESP_WIDTH-1:0] ctrl_crresp,
    output logic [BUS_WIDTH-1:0]        ctrl_cddata,
    output logic                        ctrl_cdlast,
    output logic                        ctrl_cdvalid,
    input  logic                        ctrl_cdready,

    // init-walk status + FSM observability
    output logic                        ctrl_init_busy,
    output logic [SET_INDEX_WIDTH-1:0]  ctrl_init_set,
    output logic [3:0]                  ctrl_state
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the arrays)
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("amber_control: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("amber_control: LINE_BYTES must be a power of two");
        if ((FILL_BEATS & (FILL_BEATS - 1)) != 0)
            $error("amber_control: LINE_BYTES / BUS_WIDTH*8 must be a power of two");
        if ((BUS_WIDTH % 8) != 0)
            $error("amber_control: BUS_WIDTH must be a multiple of 8");
        if (WAYS < 2)
            $error("amber_control: WAYS must be >= 2");
    end

    // ------------------------------------------------------------------
    // One-hot FSM: bit index == pkg ctrl_state_t code; multi-hot or
    // unmapped encodings decode to sticky CTRL_ERROR.
    // ------------------------------------------------------------------
    localparam int CTRL_BITS = 12;

    localparam logic [CTRL_BITS-1:0] OH_IDLE        = 12'b0000_0000_0001;
    localparam logic [CTRL_BITS-1:0] OH_INIT        = 12'b0000_0000_0010;
    localparam logic [CTRL_BITS-1:0] OH_LOOKUP      = 12'b0000_0000_0100;
    localparam logic [CTRL_BITS-1:0] OH_HIT_RD      = 12'b0000_0000_1000;
    localparam logic [CTRL_BITS-1:0] OH_HIT_WR      = 12'b0000_0001_0000;
    localparam logic [CTRL_BITS-1:0] OH_MISS_VICTIM = 12'b0000_0010_0000;
    localparam logic [CTRL_BITS-1:0] OH_MISS_DRAIN  = 12'b0000_0100_0000;
    localparam logic [CTRL_BITS-1:0] OH_MISS_FILL   = 12'b0000_1000_0000;
    localparam logic [CTRL_BITS-1:0] OH_FILL_WRITE  = 12'b0001_0000_0000;
    localparam logic [CTRL_BITS-1:0] OH_REPLAY      = 12'b0010_0000_0000;
    localparam logic [CTRL_BITS-1:0] OH_SNOOP       = 12'b0100_0000_0000;
    localparam logic [CTRL_BITS-1:0] OH_ERROR       = 12'b1000_0000_0000;

    logic [CTRL_BITS-1:0] state_q, state_d;

    // latched request (front end presents one pulse; the request context
    // lives here through the miss/replay sequence)
    logic [ADDR_WIDTH-1:0]  req_addr_q;
    logic                   req_we_q;
    logic [STRB_W-1:0]      req_be_q;
    logic [BUS_WIDTH-1:0]   req_wdata_q;

    // LOOKUP results / miss classification
    logic [WAY_INDEX_WIDTH-1:0] hit_way_q;
    logic [2:0]                 hit_state_q;
    logic [2:0]                 req_class_q;
    logic                       upgr_q;

    // MISS_VICTIM sampling
    logic [WAY_INDEX_WIDTH-1:0] victim_way_q;
    logic [TAG_WIDTH-1:0]       victim_tag_q;
    logic [2:0]                 victim_state_q;
    logic [LINE_BYTES*8-1:0]    victim_line_q;
    logic [BEAT_INDEX_WIDTH:0]  mv_cnt_q;

    // transaction-completion handshake flags (start pulses are one cycle;
    // done may only be honoured after the start has been presented)
    logic fill_seen_q, drain_seen_q;

    // response register (one-cycle pulse, Moore: presented in IDLE)
    logic                   rsp_valid_q;
    logic [BUS_WIDTH-1:0]   rsp_data_q;

    // init walk (D-3)
    logic [SET_INDEX_WIDTH-1:0] init_cnt_q;

    // pending-fill bypass register (MAS ch02_blocks/02): armed while a fill
    // is outstanding; the snoop-side consumers/writers arrive with Task 4.
    // Only the match logic feeds the miss-path K-map this task.
    logic                        pf_active_q;
    logic [LINE_ADDR_WIDTH-1:0]  pf_addr_q;

    // ------------------------------------------------------------------
    // Request address slicing
    // ------------------------------------------------------------------
    logic [TAG_WIDTH-1:0]        req_tag;
    logic [SET_INDEX_WIDTH-1:0]  req_set;
    logic [BEAT_INDEX_WIDTH-1:0] req_beat;
    logic [LINE_ADDR_WIDTH-1:0]  req_line_addr;
    logic [ADDR_WIDTH-1:0]       req_line_base;

    assign req_tag       = req_addr_q[ADDR_WIDTH-1 -: TAG_WIDTH];
    assign req_set       = req_addr_q[LINE_OFFSET_WIDTH +: SET_INDEX_WIDTH];
    assign req_beat      = req_addr_q[LINE_OFFSET_WIDTH-1 -: BEAT_INDEX_WIDTH];
    assign req_line_addr = req_addr_q[ADDR_WIDTH-1:LINE_OFFSET_WIDTH];
    assign req_line_base = {req_line_addr, {LINE_OFFSET_WIDTH{1'b0}}};

    // ------------------------------------------------------------------
    // LOOKUP: combinational hit/miss across the ways (tag match on a
    // valid MESI state; reserved encodings never hit -- benign absorbed)
    // ------------------------------------------------------------------
    logic                       hit_any;
    logic [WAY_INDEX_WIDTH-1:0] hit_way;
    logic [2:0]                 hit_state;

    always_comb begin
        hit_any   = 1'b0;
        hit_way   = '0;
        hit_state = AMBER_STATE_I;
        for (int w = 0; w < WAYS; w++) begin
            if (!hit_any
                && (ctrl_tag_a_tag_state[w][TAG_STATE_WIDTH-1 -: TAG_WIDTH]
                        == req_tag)
                && (ctrl_tag_a_tag_state[w][2:0] == AMBER_STATE_S
                    || ctrl_tag_a_tag_state[w][2:0] == AMBER_STATE_E
                    || ctrl_tag_a_tag_state[w][2:0] == AMBER_STATE_M)) begin
                hit_any   = 1'b1;
                hit_way   = WAY_INDEX_WIDTH'(w);
                hit_state = ctrl_tag_a_tag_state[w][2:0];
            end
        end
    end

    // one-hot way selects for the array write ports
    logic [WAYS-1:0] hit_way_onehot, victim_way_onehot;

    always_comb begin
        for (int w = 0; w < WAYS; w++) begin
            hit_way_onehot[w]    = (hit_way_q    == WAY_INDEX_WIDTH'(w));
            victim_way_onehot[w] = (victim_way_q == WAY_INDEX_WIDTH'(w));
        end
    end

    // ------------------------------------------------------------------
    // Miss-path K-map (workbook "K-maps amber control"), evaluated in
    // CTRL_MISS_VICTIM where hit == 0 by construction. The bypass axis is
    // real logic; with the CPU path owning the pipeline it cannot be set
    // this task (snoop service is Task 4), making replay_now defensive.
    // ------------------------------------------------------------------
    logic [2:0] mv_victim_state;
    logic       bypass_match;
    logic       kmap_victim_dirty;
    logic       kmap_start_drain;
    logic       kmap_start_fill;
    logic       kmap_replay_now;

    assign mv_victim_state   = ctrl_tag_a_tag_state[32'(ctrl_repl_way)][2:0];
    assign bypass_match      = pf_active_q && (req_line_addr == pf_addr_q);
    assign kmap_victim_dirty = (mv_cnt_q == '0)
                               ? (mv_victim_state == AMBER_STATE_M)
                               : (victim_state_q == AMBER_STATE_M);
    assign kmap_start_drain  = kmap_victim_dirty && !bypass_match;
    assign kmap_start_fill   = !kmap_victim_dirty && !bypass_match;
    assign kmap_replay_now   = bypass_match;

    // install state at FILL_WRITE: read-shared fills install Shared, write
    // and upgrade transactions install Modified (MAS ch02_blocks/02)
    logic [2:0] install_state;

    assign install_state = (req_class_q == AMBER_ACE_READ_SHARED)
                           ? AMBER_STATE_S : AMBER_STATE_M;

    wire init_last = (init_cnt_q == SET_INDEX_WIDTH'(SETS - 1));

    // ------------------------------------------------------------------
    // Next-state logic
    // ------------------------------------------------------------------
    always_comb begin
        state_d = OH_ERROR;   // illegal / multi-hot / reserved default
        unique case (state_q)
            OH_IDLE: begin
                if (req_valid) state_d = OH_LOOKUP;
                else           state_d = OH_IDLE;
            end
            OH_INIT: begin
                if (init_last) state_d = OH_IDLE;
                else           state_d = OH_INIT;
            end
            OH_LOOKUP: begin
                if (!req_we_q && hit_any) begin
                    state_d = OH_HIT_RD;                       // read hit
                end else if (req_we_q
                             && (hit_state == AMBER_STATE_E
                                 || hit_state == AMBER_STATE_M)) begin
                    state_d = OH_HIT_WR;                       // write hit
                end else if (req_we_q && hit_state == AMBER_STATE_S) begin
                    state_d = OH_MISS_FILL;                    // upgrade
                end else begin
                    state_d = OH_MISS_VICTIM;                  // miss
                end
            end
            OH_HIT_RD: state_d = OH_IDLE;
            OH_HIT_WR: state_d = OH_IDLE;
            OH_MISS_VICTIM: begin
                if (kmap_replay_now) begin
                    state_d = OH_REPLAY;                       // defensive
                end else if (mv_cnt_q == '0 && kmap_start_fill) begin
                    state_d = OH_MISS_FILL;                    // clean victim
                end else if (mv_cnt_q == (BEAT_INDEX_WIDTH+1)'(FILL_BEATS)) begin
                    state_d = OH_MISS_DRAIN;                   // victim staged
                end else begin
                    state_d = OH_MISS_VICTIM;                  // gathering
                end
            end
            OH_MISS_DRAIN: begin
                if (drain_seen_q && ctrl_drain_done) state_d = OH_MISS_FILL;
                else                               state_d = OH_MISS_DRAIN;
            end
            OH_MISS_FILL: begin
                if (fill_seen_q && ctrl_fill_done) state_d = OH_FILL_WRITE;
                else                             state_d = OH_MISS_FILL;
            end
            OH_FILL_WRITE: state_d = OH_REPLAY;
            OH_REPLAY:     state_d = OH_LOOKUP;
            // CTRL_SNOOP service lands with Task 4; unreachable this task.
            // If it is ever entered (fault injection), fail sticky-visibly.
            OH_SNOOP: state_d = OH_ERROR;
            OH_ERROR: state_d = OH_ERROR;                      // sticky
            default:  state_d = OH_ERROR;
        endcase
    end

    // ------------------------------------------------------------------
    // State + context registers
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            state_q        <= OH_INIT;
            req_addr_q     <= '0;
            req_we_q       <= 1'b0;
            req_be_q       <= '0;
            req_wdata_q    <= '0;
            hit_way_q      <= '0;
            hit_state_q    <= AMBER_STATE_I;
            req_class_q    <= AMBER_ACE_READ_SHARED;
            upgr_q         <= 1'b0;
            victim_way_q   <= '0;
            victim_tag_q   <= '0;
            victim_state_q <= AMBER_STATE_I;
            victim_line_q  <= '0;
            mv_cnt_q       <= '0;
            fill_seen_q    <= 1'b0;
            drain_seen_q   <= 1'b0;
            rsp_valid_q    <= 1'b0;
            rsp_data_q     <= '0;
            init_cnt_q     <= '0;
            pf_active_q    <= 1'b0;
            pf_addr_q      <= '0;
        end else begin
            state_q <= state_d;

            rsp_valid_q <= 1'b0;   // one-cycle pulse; hit states re-assert

            unique case (state_q)
                OH_IDLE: begin
                    if (req_valid) begin
                        req_addr_q  <= req_addr;
                        req_we_q    <= req_we;
                        req_be_q    <= req_be;
                        req_wdata_q <= req_wdata;
                    end
                end
                OH_INIT: begin
                    if (!init_last) init_cnt_q <= init_cnt_q + 1'b1;
                end
                OH_LOOKUP: begin
                    hit_way_q   <= hit_way;
                    hit_state_q <= hit_state;
                    upgr_q      <= 1'b0;
                    if (req_we_q && hit_state == AMBER_STATE_S) begin
                        req_class_q <= AMBER_ACE_CLEAN_UNIQUE;  // upgrade
                        upgr_q      <= 1'b1;
                    end else if (!hit_any) begin
                        // true miss (I, or no tag match)
                        req_class_q <= req_we_q ? AMBER_ACE_READ_UNIQUE
                                                : AMBER_ACE_READ_SHARED;
                    end
                end
                OH_HIT_RD: begin
                    rsp_valid_q <= 1'b1;
                    rsp_data_q  <= ctrl_data_a_rdata;
                end
                OH_HIT_WR: begin
                    rsp_valid_q <= 1'b1;
                    rsp_data_q  <= req_wdata_q;
                end
                OH_MISS_VICTIM: begin
                    if (mv_cnt_q == '0) begin
                        victim_way_q   <= ctrl_repl_way;
                        victim_tag_q   <=
                            ctrl_tag_a_tag_state[32'(ctrl_repl_way)]
                                                [TAG_STATE_WIDTH-1 -: TAG_WIDTH];
                        victim_state_q <= mv_victim_state;
                        victim_line_q[0 +: BUS_WIDTH] <= ctrl_data_a_rdata;
                        mv_cnt_q       <= mv_cnt_q + 1'b1;
                    end else if (mv_cnt_q < (BEAT_INDEX_WIDTH+1)'(FILL_BEATS)) begin
                        victim_line_q[32'(mv_cnt_q) * BUS_WIDTH +: BUS_WIDTH]
                            <= ctrl_data_a_rdata;
                        mv_cnt_q <= mv_cnt_q + 1'b1;
                    end else begin
                        mv_cnt_q <= '0;
                    end
                end
                OH_MISS_FILL: begin
                    fill_seen_q <= 1'b1;
                    if (!pf_active_q) begin
                        pf_active_q <= 1'b1;
                        pf_addr_q   <= req_line_addr;
                    end
                end
                OH_MISS_DRAIN: begin
                    drain_seen_q <= 1'b1;
                end
                OH_FILL_WRITE: begin
                    mv_cnt_q     <= '0;
                    fill_seen_q  <= 1'b0;
                    drain_seen_q <= 1'b0;
                    pf_active_q  <= 1'b0;
                end
                default: ;   // ERROR / SNOOP / illegal: hold context
            endcase
        end
    )

    // ------------------------------------------------------------------
    // Outputs
    // ------------------------------------------------------------------
    always_comb begin
        // tag array port A
        ctrl_tag_a_set           = req_set;
        ctrl_tag_a_wr_en         = 1'b0;
        ctrl_tag_a_wr_way_onehot = '0;
        ctrl_tag_a_wr_set        = req_set;
        ctrl_tag_a_wr_tag_state  = '0;

        // data array port A
        ctrl_data_a_addr = {req_set, req_beat};
        ctrl_data_a_way  = hit_way_q;
        ctrl_data_a_wr_en         = 1'b0;
        ctrl_data_a_wr_way_onehot = hit_way_onehot;
        ctrl_data_a_wr_addr       = {req_set, req_beat};
        ctrl_data_a_wr_wdata      = req_wdata_q;
        ctrl_data_a_wr_be         = req_be_q;

        // replacement
        ctrl_repl_req     = 1'b0;
        ctrl_repl_set     = req_set;
        ctrl_repl_hit     = 1'b0;
        ctrl_repl_update  = 1'b0;
        ctrl_repl_hit_way = hit_way_q;

        // victim / fill / drain
        ctrl_victim_load    = 1'b0;
        ctrl_victim_addr_in = {victim_tag_q, req_set,
                               {LINE_OFFSET_WIDTH{1'b0}}};
        ctrl_victim_data_in = victim_line_q;
        ctrl_fill_start     = 1'b0;
        ctrl_fill_addr      = req_line_base;
        ctrl_drain_start    = 1'b0;

        unique case (state_q)
            OH_INIT: begin
                // The walk starts with the first cycle after reset
                // deassertion: exactly SETS writes, one per cycle, and no
                // write while reset is asserted (crisp observable contract).
                ctrl_tag_a_wr_en         = !`RST_ASSERTED(rst_n);
                ctrl_tag_a_wr_way_onehot = {WAYS{1'b1}};
                ctrl_tag_a_wr_set        = init_cnt_q;
                ctrl_tag_a_wr_tag_state  = { {TAG_WIDTH{1'b0}}, AMBER_STATE_I };
            end
            OH_HIT_WR: begin
                // byte-merge write; promote E->M (M keeps its tag entry)
                ctrl_data_a_wr_en = 1'b1;
                ctrl_tag_a_wr_en  = (hit_state_q != AMBER_STATE_M);
                ctrl_tag_a_wr_tag_state = {req_tag, AMBER_STATE_M};
                ctrl_repl_hit     = 1'b1;
            end
            OH_HIT_RD: begin
                ctrl_repl_hit = 1'b1;
            end
            OH_MISS_VICTIM: begin
                if (mv_cnt_q == '0) begin
                    ctrl_repl_req = 1'b1;
                    ctrl_data_a_addr = {req_set, {BEAT_INDEX_WIDTH{1'b0}}};
                    ctrl_data_a_way  = ctrl_repl_way;
                end else if (mv_cnt_q < (BEAT_INDEX_WIDTH+1)'(FILL_BEATS)) begin
                    ctrl_data_a_addr = {req_set, mv_cnt_q[BEAT_INDEX_WIDTH-1:0]};
                    ctrl_data_a_way  = victim_way_q;
                end else begin
                    ctrl_victim_load = 1'b1;
                end
            end
            OH_MISS_FILL: begin
                ctrl_fill_start = !fill_seen_q;
            end
            OH_MISS_DRAIN: begin
                ctrl_drain_start = !drain_seen_q;
            end
            OH_FILL_WRITE: begin
                ctrl_tag_a_wr_en         = 1'b1;
                ctrl_tag_a_wr_way_onehot = upgr_q ? hit_way_onehot
                                                  : victim_way_onehot;
                ctrl_tag_a_wr_tag_state  = {req_tag, install_state};
                if (upgr_q) begin
                    ctrl_repl_hit     = 1'b1;   // upgrade = an access
                    ctrl_repl_hit_way = hit_way_q;
                end else begin
                    ctrl_repl_update  = 1'b1;   // install into victim way
                    ctrl_repl_hit_way = victim_way_q;
                end
            end
            default: ;
        endcase
    end

    // request/response + init status
    assign ctrl_req_ready = (state_q == OH_IDLE);
    assign ctrl_rsp_valid = rsp_valid_q;
    assign ctrl_rsp_data  = rsp_data_q;
    assign ctrl_init_busy = (state_q == OH_INIT);
    assign ctrl_init_set  = init_cnt_q;

    // the request class of the in-flight miss, for amber_fill/amber_ace_issue
    assign ctrl_req_class = req_class_q;

    // snoop responder outputs: tied off until Task 4 wires the service
    assign ctrl_snoop_ready = 1'b0;
    assign ctrl_crresp      = {AMBER_CRRESP_WIDTH{1'b0}};
    assign ctrl_cddata      = {BUS_WIDTH{1'b0}};
    assign ctrl_cdlast      = 1'b0;
    assign ctrl_cdvalid     = 1'b0;

    // FSM observability: one-hot -> pkg ctrl_state_t encoding
    always_comb begin
        unique case (state_q)
            OH_IDLE:        ctrl_state = 4'(AMBER_CTRL_IDLE);
            OH_INIT:        ctrl_state = 4'(AMBER_CTRL_INIT);
            OH_LOOKUP:      ctrl_state = 4'(AMBER_CTRL_LOOKUP);
            OH_HIT_RD:      ctrl_state = 4'(AMBER_CTRL_HIT_RD);
            OH_HIT_WR:      ctrl_state = 4'(AMBER_CTRL_HIT_WR);
            OH_MISS_VICTIM: ctrl_state = 4'(AMBER_CTRL_MISS_VICTIM);
            OH_MISS_DRAIN:  ctrl_state = 4'(AMBER_CTRL_MISS_DRAIN);
            OH_MISS_FILL:   ctrl_state = 4'(AMBER_CTRL_MISS_FILL);
            OH_FILL_WRITE:  ctrl_state = 4'(AMBER_CTRL_FILL_WRITE);
            OH_REPLAY:      ctrl_state = 4'(AMBER_CTRL_REPLAY);
            OH_SNOOP:       ctrl_state = 4'(AMBER_CTRL_SNOOP);
            OH_ERROR:       ctrl_state = 4'(AMBER_CTRL_ERROR);
            default:        ctrl_state = 4'(AMBER_CTRL_ERROR);
        endcase
    end

endmodule : amber_control
