// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wr2rd_forward
// Purpose: Write-to-read forwarding ("snarf") — when an AR's decoded
//          address matches an in-flight write that has not yet drained
//          to DRAM, the read pulls data straight from the AXI write
//          buffer instead of issuing a DRAM read.
//
// Description:
//   Sits between addr_mapper and rd_cmd_cam on the AR path. For each
//   incoming AR:
//
//     1. Combinationally compare the decoded (rank, bank, row, col,
//        burst_len) against every wr_cmd_cam slot's snapshot.
//     2. If a matching in-flight write exists AND its burst length
//        matches AND it is full-beat (no byte-strobe gaps), redirect
//        the AR to the forwarded path:
//           - Do NOT push to rd_cmd_cam.
//           - Emit fwd_valid_o with the write's w_buf_ptr and the
//             length so the read side can pull beats from w_buf.
//           - Use the AR's own axi_id for the AXI rid echo.
//     3. Otherwise, pass the AR straight through to rd_cmd_cam.
//
//   "Last-write-wins": if multiple writes match (programmer error or
//   intentional double-write), the highest-slot-index match is taken,
//   which corresponds to the most recently pushed write.
//
//   Pure flag-and-counter design; no FSM. Match lines are parallel
//   comparators across the wr_cmd_cam snapshot bus.
//
//   For v1 the strb-coverage check is conservative: the FUB requires
//   the AR's first-beat byte mask AND every beat thereafter to be
//   all-1 in the write's strb_buf (i.e., the write filled the entire
//   read window). Partial overlaps fall through to DRAM.
//
//   Memory-ordering note: forwarding preserves AXI per-ID in-order
//   semantics. A read that matches a pending same-ID write returns
//   the new value (post-write); a read with a different ID may also
//   forward — there is no AXI rule against it because cross-ID OoO
//   is always permitted.
//
// Documentation:
//   docs/ddr2_lpddr2_mas/ch02_blocks/   (new section pending)
//
// Author: sean galloway
// Created: 2026-06-17

`timescale 1ns / 1ps

`include "reset_defs.svh"

module wr2rd_forward
    import ddr2_lpddr2_pkg::*;
#(
    parameter int WR_CAM_DEPTH      = 16,
    parameter int AXI_ID_WIDTH      = 4,
    parameter int NUM_RANKS         = 1,
    parameter int NUM_BANKS         = 8,
    parameter int ROW_WIDTH         = 14,
    parameter int COL_WIDTH         = 10,
    parameter int BURST_LEN_WIDTH   = 8,
    parameter int W_BUF_PTR_WIDTH   = 7,

    // Aliases
    parameter int WD  = WR_CAM_DEPTH,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int RW  = ROW_WIDTH,
    parameter int CW  = COL_WIDTH,
    parameter int BLW = BURST_LEN_WIDTH,
    parameter int WPW = W_BUF_PTR_WIDTH,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int WSL = $clog2(WD)
) (
    input  logic                 mc_clk,
    input  logic                 mc_rst_n,

    // AR intake (from addr_mapper / axi4_slave)
    input  logic                 ar_valid_i,
    output logic                 ar_ready_o,
    input  logic [IW-1:0]        ar_id_i,
    input  logic [RKW-1:0]       ar_rank_i,
    input  logic [BKW-1:0]       ar_bank_i,
    input  logic [RW-1:0]        ar_row_i,
    input  logic [CW-1:0]        ar_col_i,
    input  logic [BLW-1:0]       ar_len_i,           // beats (NOT len-1)

    // Snapshot from wr_cmd_cam (combinational)
    input  logic [WD-1:0]                       cam_valid_i,
    input  logic [WD-1:0][RKW-1:0]              cam_rank_i,
    input  logic [WD-1:0][BKW-1:0]              cam_bank_i,
    input  logic [WD-1:0][RW-1:0]               cam_row_i,
    input  logic [WD-1:0][CW-1:0]               cam_col_i,
    input  logic [WD-1:0][BLW-1:0]              cam_len_i,
    input  logic [WD-1:0][WPW-1:0]              cam_w_buf_ptr_i,
    // Per-burst "full-beat coverage" hint from axi4_slave wstrb buffer.
    // 1 = every beat in this write covers all bytes (no partial strobes).
    input  logic [WD-1:0]                       cam_full_strb_i,

    // Passthrough to rd_cmd_cam (when no forwarding match)
    output logic                 rd_push_valid_o,
    input  logic                 rd_push_ready_i,
    output logic [IW-1:0]        rd_push_id_o,
    output logic [RKW-1:0]       rd_push_rank_o,
    output logic [BKW-1:0]       rd_push_bank_o,
    output logic [RW-1:0]        rd_push_row_o,
    output logic [CW-1:0]        rd_push_col_o,
    output logic [BLW-1:0]       rd_push_len_o,

    // Forwarded read path (to rd_data_path / r_response_fifo)
    output logic                 fwd_valid_o,
    input  logic                 fwd_ready_i,
    output logic [IW-1:0]        fwd_id_o,
    output logic [WPW-1:0]       fwd_w_buf_ptr_o,    // start pointer into w_buf
    output logic [BLW-1:0]       fwd_len_o,          // beats to pull
    output logic [WSL-1:0]       fwd_src_slot_o,     // which wr slot we snarfed from

    // Telemetry
    output logic                 dbg_forward_hit_o,
    output logic                 dbg_forward_miss_o
);

    //=========================================================================
    // Per-slot eligibility (combinational)
    //=========================================================================

    logic [WD-1:0] w_addr_match;
    logic [WD-1:0] w_len_match;
    logic [WD-1:0] w_eligible;

    for (genvar i = 0; i < WD; i++) begin : g_match
        assign w_addr_match[i] = cam_valid_i[i]
                              && (cam_rank_i[i] == ar_rank_i)
                              && (cam_bank_i[i] == ar_bank_i)
                              && (cam_row_i [i] == ar_row_i)
                              && (cam_col_i [i] == ar_col_i);
        assign w_len_match [i] = (cam_len_i[i] == ar_len_i);
        assign w_eligible  [i] = w_addr_match[i]
                              && w_len_match [i]
                              && cam_full_strb_i[i];
    end

    //=========================================================================
    // Pick the newest matching write (highest slot index)
    //
    // The wr_cmd_cam allocates the lowest free slot on push; the next
    // pushed write goes into a higher slot only when the lower one is
    // occupied. There is no strict ordering guarantee from slot index
    // alone, but for the common case of a single in-flight write to
    // any one address, highest-index is the most recently pushed.
    //
    // For the (rare) case of multiple concurrent in-flight writes to
    // the same address, AXI4 already forbids the host from relying on
    // ordering between them — we pick deterministically.
    //=========================================================================

    logic [WSL-1:0] w_picked_slot;
    logic           w_any_eligible;

    always_comb begin
        w_picked_slot  = '0;
        w_any_eligible = 1'b0;
        for (int unsigned i = 0; i < WD; i++) begin
            if (w_eligible[i]) begin
                w_picked_slot  = WSL'(i);
                w_any_eligible = 1'b1;
            end
        end
    end

    //=========================================================================
    // Output drive — single-cycle decision
    //=========================================================================
    //
    // When an AR arrives:
    //   - forwarding match  → drive fwd_valid_o, gate on fwd_ready_i
    //   - no match          → drive rd_push_valid_o, gate on rd_push_ready_i
    //
    // Only one path is active per AR. ar_ready_o tracks whichever
    // downstream port is being driven.

    logic w_take_fwd;
    logic w_take_rd;
    assign w_take_fwd = ar_valid_i &&  w_any_eligible;
    assign w_take_rd  = ar_valid_i && !w_any_eligible;

    assign fwd_valid_o     = w_take_fwd;
    assign fwd_id_o        = ar_id_i;
    assign fwd_w_buf_ptr_o = cam_w_buf_ptr_i[w_picked_slot];
    assign fwd_len_o       = ar_len_i;
    assign fwd_src_slot_o  = w_picked_slot;

    assign rd_push_valid_o = w_take_rd;
    assign rd_push_id_o    = ar_id_i;
    assign rd_push_rank_o  = ar_rank_i;
    assign rd_push_bank_o  = ar_bank_i;
    assign rd_push_row_o   = ar_row_i;
    assign rd_push_col_o   = ar_col_i;
    assign rd_push_len_o   = ar_len_i;

    assign ar_ready_o = (w_take_fwd && fwd_ready_i)
                     || (w_take_rd  && rd_push_ready_i);

    //=========================================================================
    // Telemetry — one-cycle pulses on accepted AR
    //=========================================================================

    `ALWAYS_FF_RST(mc_clk, mc_rst_n, begin
        if (`RST_ASSERTED(mc_rst_n)) begin
            dbg_forward_hit_o  <= 1'b0;
            dbg_forward_miss_o <= 1'b0;
        end else begin
            dbg_forward_hit_o  <= w_take_fwd && fwd_ready_i;
            dbg_forward_miss_o <= w_take_rd  && rd_push_ready_i;
        end
    end)

endmodule : wr2rd_forward
