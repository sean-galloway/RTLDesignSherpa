// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: char_run_timer
// Purpose: The characterization harness's run timer and CRC verdict. Times
//          one DMA run in clock cycles, stamps the first and last read and
//          write beat on the same time base, and latches a pass/fail verdict
//          from the per-channel CRCs of an LFSR source and a CRC sink.
//
//          Extracted from the Genesys 2 STREAM harness so that every harness
//          built around the LFSR source / CRC sink pair (STREAM, the fabric
//          benchmark) runs the same timer and the same verdict.
//
// Run protocol
// ------------
//   CLEAR : i_clear (one-cycle pulse) zeroes every output and re-arms START.
//   START : rising edge of i_start, once per run (ignored while running, while
//           settling, and once done). The STREAM harness feeds the descriptor
//           bus AR handshake, so the run starts at the first descriptor fetch.
//   STOP  : i_wr_beat_count >= i_expected_beats -- the sink has consumed the
//           last beat. Disabled while i_expected_beats == 0, which leaves the
//           timer running so the host can read o_cycles live.
//   PASS  : o_crc_match sampled SETTLE_CYCLES after STOP. The settle window is
//           NOT counted in o_cycles, which freezes at the transfer end so
//           measured throughput stays exact.
//
// SETTLE_CYCLES must cover how far the CRC lags the beat count AT THIS
// MODULE'S INPUTS. Directly from axi4_dma_slaves the lag is dataint_crc's
// one-cycle output register, and 5 is the STREAM harness's long-standing
// value. Behind a clock crossing that delivers count and CRC as periodic
// snapshots, the CRC can still miss the last beat in the snapshot whose count
// first reaches STOP, so the window must span the next snapshot as well.
//
// Beat stamps
// -----------
//   o_r_first / o_w_first : o_cycles when the read / write count first leaves 0
//   o_r_last  / o_w_last  : o_cycles when the count first reaches the target
// They let the host separate steady-state engine throughput from the
// descriptor-fetch fill and last-burst drain. Each latches once per run.
//
// Timing: the beat counts and the target are registered once before the wide
// compare. At 8 channels the counts come out of an adder tree, and the
// unregistered path (count -> adder -> compare -> AND -> stamp CE) was 14
// levels and missed 100 MHz on the xc7a100t-1 by 1.05 ns. The flop delays the
// first/last stamps and STOP by one cycle; the host only ever sees the run
// through o_done, so nothing it reads moves.
//
// CRC verdict
// -----------
// A channel MATCHES when both its read and write CRC are valid and equal. The
// run passes when at least one channel was active (both CRCs valid) and no
// active channel mismatched; a channel that never ran has valid=0 and neither
// passes nor fails, so no channel-enable mask is needed here.
//
// EVERY channel is checked. There is no ignore mask and none may be added: a
// channel excluded from the verdict is a channel whose corruption reports PASS,
// which is worse than having no check at all. (Channel 0 was once masked for a
// harness-side aggregation bug that does not reproduce: the 8-channel cosim
// reports match_mask=0xFF, valid_mask=0xFF. A ch0 mismatch on silicon is a
// finding to debug, not to mask.)
//
// Parameters:
//   - NUM_CHANNELS : channels of the source/sink pair, >= 1, default 8
//   - CRC_WIDTH    : per-channel CRC width, default 32
//   - COUNT_WIDTH  : beat-count and target width, default 32
//   - SETTLE_CYCLES: cycles from STOP to the verdict, >= 1, default 5
// Subsystem: misc
// Author: sean galloway

`timescale 1ns / 1ps

`include "reset_defs.svh"

module char_run_timer #(
    parameter int NUM_CHANNELS  = 8,
    parameter int CRC_WIDTH     = 32,
    parameter int COUNT_WIDTH   = 32,
    parameter int SETTLE_CYCLES = 5
) (
    input  logic                                   aclk,
    input  logic                                   aresetn,

    // Control
    input  logic                                   i_clear,
    input  logic                                   i_start,
    input  logic [COUNT_WIDTH-1:0]                 i_expected_beats,

    // Source / sink status
    input  logic [COUNT_WIDTH-1:0]                 i_rd_beat_count,
    input  logic [COUNT_WIDTH-1:0]                 i_wr_beat_count,
    input  logic [NUM_CHANNELS-1:0][CRC_WIDTH-1:0] i_rd_crc_value,
    input  logic [NUM_CHANNELS-1:0]                i_rd_crc_valid,
    input  logic [NUM_CHANNELS-1:0][CRC_WIDTH-1:0] i_wr_crc_value,
    input  logic [NUM_CHANNELS-1:0]                i_wr_crc_valid,

    // CRC verdict (combinational, live)
    output logic [NUM_CHANNELS-1:0]                o_crc_valid_mask,
    output logic [NUM_CHANNELS-1:0]                o_crc_match_mask,
    output logic                                   o_crc_any_valid,
    output logic                                   o_crc_match,

    // Timer
    output logic                                   o_running,
    output logic                                   o_done,
    output logic                                   o_pass,
    output logic [63:0]                            o_cycles,
    output logic [63:0]                            o_r_first,
    output logic [63:0]                            o_r_last,
    output logic [63:0]                            o_w_first,
    output logic [63:0]                            o_w_last
);

    localparam int SW = $clog2(SETTLE_CYCLES + 1);
    localparam logic [SW-1:0] SETTLE_LAST = SW'(SETTLE_CYCLES);

    // ---- CRC verdict --------------------------------------------------------
    always_comb begin
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            o_crc_valid_mask[ch] = i_rd_crc_valid[ch] && i_wr_crc_valid[ch];
            o_crc_match_mask[ch] = o_crc_valid_mask[ch]
                                && (i_rd_crc_value[ch] == i_wr_crc_value[ch]);
        end
    end
    assign o_crc_any_valid = |o_crc_valid_mask;
    assign o_crc_match     = o_crc_any_valid && !(|(o_crc_valid_mask & ~o_crc_match_mask));

    // ---- Registered inputs (see "Timing" above) -----------------------------
    logic                   r_start_d;
    logic [COUNT_WIDTH-1:0] r_rd_beats_q;
    logic [COUNT_WIDTH-1:0] r_wr_beats_q;
    logic [COUNT_WIDTH-1:0] r_exp_beats_q;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_start_d     <= 1'b0;
            r_rd_beats_q  <= '0;
            r_wr_beats_q  <= '0;
            r_exp_beats_q <= '0;
        end else begin
            r_start_d     <= i_start;
            r_rd_beats_q  <= i_rd_beat_count;
            r_wr_beats_q  <= i_wr_beat_count;
            r_exp_beats_q <= i_expected_beats;
        end
    )

    wire w_start_rise   = i_start & ~r_start_d;
    wire w_target_armed = (r_exp_beats_q != '0);
    wire w_stop         = w_target_armed && (r_wr_beats_q >= r_exp_beats_q);

    logic r_rd_first_seen, r_wr_first_seen;
    logic r_rd_last_seen,  r_wr_last_seen;
    wire  w_rd_first_now = o_running && !r_rd_first_seen && (r_rd_beats_q != '0);
    wire  w_wr_first_now = o_running && !r_wr_first_seen && (r_wr_beats_q != '0);
    wire  w_rd_last_now  = o_running && !r_rd_last_seen && w_target_armed
                                     && (r_rd_beats_q >= r_exp_beats_q);
    wire  w_wr_last_now  = o_running && !r_wr_last_seen && w_stop;

    // ---- Timer --------------------------------------------------------------
    logic [SW-1:0] r_settle_cnt;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            o_running       <= 1'b0;
            o_done          <= 1'b0;
            o_pass          <= 1'b0;
            o_cycles        <= '0;
            r_settle_cnt    <= '0;
            o_r_first       <= '0;
            o_r_last        <= '0;
            o_w_first       <= '0;
            o_w_last        <= '0;
            r_rd_first_seen <= 1'b0;
            r_wr_first_seen <= 1'b0;
            r_rd_last_seen  <= 1'b0;
            r_wr_last_seen  <= 1'b0;
        end else if (i_clear) begin
            o_running       <= 1'b0;
            o_done          <= 1'b0;
            o_pass          <= 1'b0;
            o_cycles        <= '0;
            r_settle_cnt    <= '0;
            o_r_first       <= '0;
            o_r_last        <= '0;
            o_w_first       <= '0;
            o_w_last        <= '0;
            r_rd_first_seen <= 1'b0;
            r_wr_first_seen <= 1'b0;
            r_rd_last_seen  <= 1'b0;
            r_wr_last_seen  <= 1'b0;
        end else if (o_running) begin
            // Stamps share o_cycles' time base: cycle 1 is the start cycle.
            if (w_rd_first_now) begin
                o_r_first       <= o_cycles;
                r_rd_first_seen <= 1'b1;
            end
            if (w_wr_first_now) begin
                o_w_first       <= o_cycles;
                r_wr_first_seen <= 1'b1;
            end
            if (w_rd_last_now) begin
                o_r_last       <= o_cycles;
                r_rd_last_seen <= 1'b1;
            end
            if (w_wr_last_now) begin
                o_w_last       <= o_cycles;
                r_wr_last_seen <= 1'b1;
            end

            if (w_stop) begin
                // Freeze o_cycles at the transfer end; begin the settle window.
                o_running    <= 1'b0;
                r_settle_cnt <= SW'(1);
            end else begin
                o_cycles     <= o_cycles + 64'd1;
            end
        end else if (r_settle_cnt != '0) begin
            if (r_settle_cnt == SETTLE_LAST) begin
                r_settle_cnt <= '0;
                o_done       <= 1'b1;
                o_pass       <= o_crc_match;
            end else begin
                r_settle_cnt <= r_settle_cnt + SW'(1);
            end
        end else if (!o_done && w_start_rise) begin
            o_running <= 1'b1;
            o_cycles  <= 64'd1;  // count the start cycle
        end
    )

endmodule : char_run_timer
