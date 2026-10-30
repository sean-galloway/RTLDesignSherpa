// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: jet_wb_buffer
// Purpose:
//   Decoupled writeback (victim) buffer for the jet MESI L1 (MAS
//   ch02_blocks/03). Holds VICTIM_DEPTH dirty eviction victims captured at
//   miss alloc and drains them oldest-first through the existing l1_drain
//   engine, independently of the fills that evicted them (J5 ruling).
//
// Documentation: projects/components/cache-ip/jet-mesi-l1/docs/jet_mas/ch02_blocks/03_jet_wb_buffer.md
// Subsystem: jet
//
// Author: sean galloway
// Created: 2026-10-28

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: jet_wb_buffer
//==============================================================================
// Description:
//   VICTIM_DEPTH-deep FIFO of dirty victims.  Capture is beat-serial from the
//   data array (port B or A-between-fills); drain presents the oldest valid
//   entry in the l1_victim shape {valid, addr, full_line} and is retired by
//   the BRESP pulse drain_done_i.  The address is held until BRESP.  Snoops
//   matching a valid entry are served from the buffer data (snarf) with the
//   post-snoop effect recorded on sn_eff_i.  The critical ships-in-the-night
//   corner is covered: a snoop landing in the entry's BRESP cycle is still
//   answered from the buffer.
//
//   The buffer head is l1_victim-compatible: drain_valid_o/drain_addr_o/
//   drain_data_o mirror victim_valid/victim_addr/victim_data, and drain_done_i
//   is the retire pulse (equivalent to victim_clear from l1_drain's side).
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   VICTIM_DEPTH:
//     Description: WB buffer rows (J5)
//     Type: int
//     Range: 1 to 4 (elaboration $error outside)
//     Default: jet_pkg.VICTIM_DEPTH (2)
//
//   LINE_W:
//     Description: Miss line-address width (snoop-compare key)
//     Type: int
//     Default: AMBER_ADDR_WIDTH - clog2(AMBER_LINE_BYTES) (26)
//
//   ADDR_WIDTH:
//     Description: Full byte address width (line address + offset bits)
//     Type: int
//     Default: l1_pkg.AMBER_ADDR_WIDTH (32)
//
//   LINE_BYTES:
//     Description: Cache line size in bytes
//     Type: int
//     Default: l1_pkg.AMBER_LINE_BYTES (64)
//
//   BUS_WIDTH:
//     Description: Data-array / AXI W channel width
//     Type: int
//     Default: l1_pkg.AMBER_BUS_WIDTH (64)
//
//------------------------------------------------------------------------------
// Notes:
//------------------------------------------------------------------------------
//   - Only one capture stream is active at a time (single data-array read
//     port).  cap_i held high opens a slot; cap_beat_i writes beats into that
//     slot; the slot closes only when the line is complete.  cap_i may deassert
//     between beats (port sharing) without aborting the capture.
//   - An entry is visible to the drain and to snarf only after all beats have
//     been captured (r_valid).
//   - sn_eff_i is recorded on the matching entry exactly once and only when a
//     non-NONE effect is presented; an invalidated snarfed victim still drains
//     to completion (fabric already took the data).
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - Instantiated by: jet_wb_buffer_th (unit DV); jet_control (Tasks 5-7)
//   - Package: jet_pkg (VICTIM_DEPTH, effect encodings), l1_pkg (geometry)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/cache-ip/jet-mesi-l1/dv/tests/test_jet_wb_buffer.py
//   Plan: dv/testplans/jet_wb_buffer_testplan.yaml
//   Run: pytest projects/components/cache-ip/jet-mesi-l1/dv/tests/test_jet_wb_buffer.py -v
//
//==============================================================================

module jet_wb_buffer
    import jet_pkg::*;
    import l1_pkg::*;
#(
    parameter int VICTIM_DEPTH = jet_pkg::VICTIM_DEPTH,
    parameter int LINE_W       = AMBER_ADDR_WIDTH - $clog2(AMBER_LINE_BYTES),
    parameter int ADDR_WIDTH   = AMBER_ADDR_WIDTH,
    parameter int LINE_BYTES   = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH    = AMBER_BUS_WIDTH,
    localparam int STRB_W         = BUS_WIDTH / 8,
    localparam int FILL_BEATS     = LINE_BYTES / STRB_W,
    localparam int BEAT_W         = $clog2(FILL_BEATS),
    localparam int LINE_WIDTH     = LINE_BYTES * 8,
    localparam int OFFSET_W       = $clog2(LINE_BYTES),
    localparam int SLOT_W         = (VICTIM_DEPTH <= 2) ? 1 : $clog2(VICTIM_DEPTH),
    localparam int OCC_W          = $clog2(VICTIM_DEPTH + 1)
)(
    input  logic                     clk,
    input  logic                     rst_n,

    // Capture: beat-serial victim load from the data array
    input  logic                     cap_i,
    input  logic [LINE_W-1:0]        cap_line_i,
    input  logic                     cap_beat_i,
    input  logic [BUS_WIDTH-1:0]     cap_beat_data_i,
    output logic                     cap_gnt_o,
    output logic [SLOT_W-1:0]        cap_slot_o,
    output logic                     wb_full_o,

    // Drain side: l1_victim-shaped head of the FIFO
    output logic                     drain_valid_o,
    output logic [ADDR_WIDTH-1:0]    drain_addr_o,
    output logic [LINE_WIDTH-1:0]    drain_data_o,
    input  logic                     drain_done_i,

    // Snarf: snoop service from the WB buffer
    input  logic [LINE_W-1:0]        sn_line_i,
    output logic                     sn_hit_o,
    output logic [LINE_WIDTH-1:0]    sn_data_o,
    output logic                     sn_bresp_cycle_o,
    input  logic [1:0]               sn_eff_i,

    // MonBus occupancy gauge (J7)
    output logic [OCC_W-1:0]         wb_occupancy_o
);

    // ------------------------------------------------------------------
    // Address-shape sanity: the default parameters keep these equal.
    // ------------------------------------------------------------------
    initial begin
        if (LINE_W + OFFSET_W != ADDR_WIDTH)
            $error("jet_wb_buffer: LINE_W + $clog2(LINE_BYTES) must equal ADDR_WIDTH");
    end

    // ------------------------------------------------------------------
    // Elaboration-time range check (house idiom, cf. l1_tag_array).
    // VICTIM_DEPTH 1-4 is the J5 range; the package carries only the
    // default because SV package parameters cannot be overridden.
    // ------------------------------------------------------------------
    initial begin
        if (VICTIM_DEPTH < 1 || VICTIM_DEPTH > 4)
            $error("jet_wb_buffer: VICTIM_DEPTH must be in 1..4 (J5)");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("jet_wb_buffer: LINE_BYTES must be a power of two");
        if ((BUS_WIDTH % 8) != 0)
            $error("jet_wb_buffer: BUS_WIDTH must be a multiple of 8");
        if (FILL_BEATS < 2)
            $error("jet_wb_buffer: LINE_BYTES / BUS_WIDTH*8 must be >= 2");
    end

    // ------------------------------------------------------------------
    // Entry storage (MAS ch02_blocks/03)
    // ------------------------------------------------------------------
    logic [VICTIM_DEPTH-1:0]       r_valid;
    logic [VICTIM_DEPTH-1:0]       r_allocated;
    logic [LINE_W-1:0]             r_line      [VICTIM_DEPTH];
    logic [LINE_WIDTH-1:0]         r_data      [VICTIM_DEPTH];
    logic [BEAT_W-1:0]             r_beats_rcvd[VICTIM_DEPTH];
    logic [1:0]                    r_eff       [VICTIM_DEPTH];

    // ------------------------------------------------------------------
    // FIFO pointers and state
    // ------------------------------------------------------------------
    logic [SLOT_W-1:0] r_head;
    logic [SLOT_W-1:0] r_tail;
    logic [SLOT_W-1:0] r_open_slot;
    logic              r_open;

    // ------------------------------------------------------------------
    // Free / full status (combinational)
    // ------------------------------------------------------------------
    logic w_any_free;

    assign w_any_free = ~(&r_allocated);
    assign wb_full_o  = ~w_any_free;
    assign cap_gnt_o  = cap_i & (r_open | w_any_free);
    assign cap_slot_o = r_open ? r_open_slot : r_tail;

    // ------------------------------------------------------------------
    // Drain head (combinational): l1_victim shape
    // ------------------------------------------------------------------
    logic [SLOT_W-1:0] w_head_idx;

    assign w_head_idx   = r_head;
    assign drain_valid_o = r_valid[w_head_idx];
    assign drain_addr_o  = ADDR_WIDTH'({r_line[w_head_idx], {OFFSET_W{1'b0}}});
    assign drain_data_o  = r_data[w_head_idx];

    // ------------------------------------------------------------------
    // Snarf CAM (combinational): search from head to tail, oldest first
    // ------------------------------------------------------------------
    logic [SLOT_W-1:0] w_sn_match_idx;
    logic              w_sn_match;

    always_comb begin
        w_sn_match     = 1'b0;
        w_sn_match_idx = '0;
        for (int offset = 0; offset < VICTIM_DEPTH; offset++) begin
            int s;
            s = (int'(r_head) + offset) % VICTIM_DEPTH;
            if (!w_sn_match && r_valid[s] && (r_line[s] == sn_line_i)) begin
                w_sn_match     = 1'b1;
                w_sn_match_idx = SLOT_W'(s);
            end
        end
    end

    assign sn_hit_o         = w_sn_match;
    assign sn_data_o        = r_data[w_sn_match_idx];
    assign sn_bresp_cycle_o = w_sn_match & drain_done_i
                              & (w_sn_match_idx == w_head_idx);

    // ------------------------------------------------------------------
    // Occupancy gauge (MonBus, J7)
    // ------------------------------------------------------------------
    always_comb begin
        wb_occupancy_o = '0;
        for (int s = 0; s < VICTIM_DEPTH; s++) begin
            wb_occupancy_o = wb_occupancy_o + OCC_W'(r_valid[s]);
        end
    end

    // ------------------------------------------------------------------
    // Sequential update
    // ------------------------------------------------------------------
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_valid      <= '0;
            r_allocated  <= '0;
            r_head       <= '0;
            r_tail       <= '0;
            r_open       <= 1'b0;
            r_open_slot  <= '0;
            for (int s = 0; s < VICTIM_DEPTH; s++) begin
                r_line[s]       <= '0;
                r_data[s]       <= '0;
                r_beats_rcvd[s] <= '0;
                r_eff[s]        <= '0;
            end
        end else begin
            // Capture allocation: cap_i opens the slot at the tail and
            // advances the tail pointer.  This keeps drain order oldest-first
            // even when entries retire out of lowest-index order.
            if (cap_i && !r_open && w_any_free) begin
                r_open                  <= 1'b1;
                r_open_slot             <= r_tail;
                r_allocated[r_tail]     <= 1'b1;
                r_valid[r_tail]         <= 1'b0;
                r_line[r_tail]          <= cap_line_i;
                r_beats_rcvd[r_tail]    <= '0;
                r_eff[r_tail]           <= JET_PEND_NONE;
                r_tail                  <= SLOT_W'((int'(r_tail) + 1) % VICTIM_DEPTH);
            end

            // Capture beat write into the open slot.  cap_i may deassert
            // between beats (data-array port sharing) without aborting; the
            // slot stays open until the last beat completes the line.
            if (r_open && cap_beat_i) begin
                logic [BEAT_W-1:0] b;
                b = r_beats_rcvd[r_open_slot];
                r_data[r_open_slot][32'(b) * BUS_WIDTH +: BUS_WIDTH]
                    <= cap_beat_data_i;
                r_beats_rcvd[r_open_slot] <= b + 1'b1;
                if (b == BEAT_W'(FILL_BEATS - 1)) begin
                    r_valid[r_open_slot] <= 1'b1;
                    r_open               <= 1'b0;
                end
            end

            // Snoop effect recording on the matching entry, gated so a
            // non-matching cycle or JET_PEND_NONE does not clobber a pending
            // effect already stored.
            if (w_sn_match && (sn_eff_i != JET_PEND_NONE)) begin
                r_eff[w_sn_match_idx] <= sn_eff_i;
            end

            // BRESP retire: free the head entry and advance.
            if (drain_done_i && r_allocated[w_head_idx]) begin
                r_valid[w_head_idx]     <= 1'b0;
                r_allocated[w_head_idx] <= 1'b0;
                r_head <= SLOT_W'((int'(r_head) + 1) % VICTIM_DEPTH);
            end
        end
    )

    // ------------------------------------------------------------------
    // Simulation-only contract checks
    // ------------------------------------------------------------------
    // pragma translate_off
    // A capture that pauses (cap_i deasserts before the line is complete)
    // must eventually resume and complete; otherwise the slot leaks.
    // We bound the pause in simulation so a stuck-open slot fails loudly.
    localparam int MAX_PAUSE_CYC = 1023;
    // Make the counter one bit wider than the maximum pause so it can
    // represent MAX_PAUSE_CYC + 1; the assertion below then has a real
    // reachable state in which it can fire.
    localparam int PAUSE_CNT_W   = $clog2(MAX_PAUSE_CYC + 2);
    logic [PAUSE_CNT_W-1:0] r_pause_cnt;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_pause_cnt <= '0;
        end else if (r_open && !cap_i) begin
            r_pause_cnt <= r_pause_cnt + 1'b1;
        end else begin
            r_pause_cnt <= '0;
        end
    end

    assert property (@(posedge clk) disable iff (!rst_n)
        (r_pause_cnt <= PAUSE_CNT_W'(MAX_PAUSE_CYC)))
        else $error("jet_wb_buffer: partial capture slot paused too long / never completed");
    // pragma translate_on

endmodule : jet_wb_buffer
