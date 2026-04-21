// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cdc_open_loop
// Purpose: Open-loop multi-bit CDC using valid/data stretching.
//
// The source asserts src_valid for one cycle. The module captures the data
// and stretches the valid signal for STRETCH_CYCLES source clock cycles,
// holding data stable throughout. A multi-stage synchronizer in the
// destination domain samples the stretched valid and latches the data on
// the rising edge.
//
// The stretch duration must be long enough that the destination clock
// samples at least one cycle of the stretched valid. The guideline is:
//
//   STRETCH_CYCLES >= ceil(1.5 * T_dst / T_src) + SYNC_STAGES
//
// where T_dst and T_src are the destination and source clock periods.
// For example, a 100 MHz source crossing to a 25 MHz destination
// (ratio 4:1) needs STRETCH_CYCLES >= ceil(1.5 * 4) + 3 = 9.
//
// This is a true open-loop design: no return path, no handshake, no
// backpressure. The source is busy for exactly STRETCH_CYCLES and then
// free to send again. If the destination misses the stretched valid
// (because STRETCH_CYCLES is too short), the transfer is silently lost.
//
// Use when:
//   - Clock ratio is known and fixed (or bounded)
//   - Destination is always ready (no flow control needed)
//   - Minimum area/complexity is desired
//   - Config registers, status updates, infrequent events
//
// For unknown/variable clock ratios, use cdc_2_phase_handshake (closed-loop).
// For streaming data, use fifo_async or gaxi_fifo_async.
//
// Documentation: docs/markdown/RTLAmba/shared/cdc_open_loop.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-04-21
//
// ===========================================================================
// REQUIRED SDC CONSTRAINTS
// ---------------------------------------------------------------------------
//   # 1. Stretched valid (single-bit, synchronized by destination)
//   set_max_delay -datapath_only \
//       -from [get_pins u_cdc/r_src_valid_stretch_reg/C] \
//       -to   [get_pins u_cdc/u_valid_sync/q_reg[0]/D] \
//       <dst_period_ns>
//
//   # 2. Data bus (quasi-static, held for STRETCH_CYCLES src clocks)
//   set_max_delay -datapath_only \
//       -from [get_pins u_cdc/r_src_data_reg[*]/C] \
//       -to   [get_pins u_cdc/r_dst_data_reg[*]/D] \
//       <dst_period_ns>
//
// ===========================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cdc_open_loop #(
    parameter int DATA_WIDTH     = 8,    // Width of the data bus
    parameter int STRETCH_CYCLES = 8,    // Source clocks to hold valid+data (see formula above)
    parameter int SYNC_STAGES    = 3     // Destination synchronizer depth (2-4)
) (
    // Source clock domain
    input  logic                  clk_src,      // Source domain clock
    input  logic                  rst_src_n,    // Source domain async reset (active low)
    input  logic                  src_valid,    // Single-cycle pulse: data is valid NOW
    input  logic [DATA_WIDTH-1:0] src_data,     // Data from source domain
    output logic                  src_busy,     // High during stretch (blocks next valid)

    // Destination clock domain
    input  logic                  clk_dst,      // Destination domain clock
    input  logic                  rst_dst_n,    // Destination domain async reset (active low)
    output logic                  dst_valid,    // Single-cycle pulse: data latched
    output logic [DATA_WIDTH-1:0] dst_data      // Latched data (stable until next dst_valid)
);

    // Counter width to hold STRETCH_CYCLES
    localparam int CTR_WIDTH = $clog2(STRETCH_CYCLES + 1);

    //=========================================================================
    // Source domain: capture data and stretch valid
    //=========================================================================
    // On src_valid (when not busy), capture data and assert r_src_valid_stretch
    // for STRETCH_CYCLES. Both data and stretched valid cross to the destination
    // as quasi-static signals.

    logic [DATA_WIDTH-1:0] r_src_data;
    logic                  r_src_valid_stretch;
    logic [CTR_WIDTH-1:0]  r_stretch_count;

    assign src_busy = (r_stretch_count != '0);

    `ALWAYS_FF_RST(clk_src, rst_src_n,
        if (`RST_ASSERTED(rst_src_n)) begin
            r_src_data          <= '0;
            r_src_valid_stretch <= 1'b0;
            r_stretch_count     <= '0;
        end else begin
            if (src_valid && !src_busy) begin
                // New transfer: capture data, start stretching
                r_src_data          <= src_data;
                r_src_valid_stretch <= 1'b1;
                r_stretch_count     <= CTR_WIDTH'(STRETCH_CYCLES);
            end else if (r_stretch_count != '0) begin
                // Counting down
                r_stretch_count <= r_stretch_count - 1'b1;
                if (r_stretch_count == CTR_WIDTH'(1)) begin
                    // Last cycle -- deassert stretched valid
                    r_src_valid_stretch <= 1'b0;
                end
            end
        end
    )

    //=========================================================================
    // Destination domain: synchronize stretched valid, edge-detect, latch data
    //=========================================================================
    // The stretched valid is a level signal held for many source clocks.
    // The multi-stage synchronizer resolves metastability. We detect the
    // rising edge of the synchronized valid and latch data on that edge.

    logic w_valid_sync;

    glitch_free_n_dff_arn #(
        .FLOP_COUNT (SYNC_STAGES),
        .WIDTH      (1)
    ) u_valid_sync (
        .clk   (clk_dst),
        .rst_n (rst_dst_n),
        .d     (r_src_valid_stretch),
        .q     (w_valid_sync)
    );

    // Rising edge detect on synchronized valid
    logic r_valid_sync_prev;

    wire w_valid_rise = w_valid_sync && !r_valid_sync_prev;

    `ALWAYS_FF_RST(clk_dst, rst_dst_n,
        if (`RST_ASSERTED(rst_dst_n)) begin
            r_valid_sync_prev <= 1'b0;
            dst_data          <= '0;
            dst_valid         <= 1'b0;
        end else begin
            r_valid_sync_prev <= w_valid_sync;
            dst_valid         <= w_valid_rise;
            if (w_valid_rise) begin
                dst_data <= r_src_data;
            end
        end
    )

endmodule : cdc_open_loop
