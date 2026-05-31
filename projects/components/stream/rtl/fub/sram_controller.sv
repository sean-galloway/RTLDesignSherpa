// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: sram_controller
// Purpose: Simple SRAM Controller using per-channel FIFOs with Latency Bridge
//
// Description:
//   Replaces complex shared SRAM with segmentation logic with
//   simple per-channel gaxi_fifo_sync blocks.
//
// Architecture:
//   - Write Path: AXI Read Engine → Allocation Controller → FIFO
//   - Read Path: FIFO → Latency Bridge → AXI Write Engine
//   - Per-channel space tracking and data counting
//
// Key Features:
//   - Independent FIFO per channel (no segmentation complexity)
//   - Allocation controller tracks reserved vs. committed space
//   - Latency bridge aligns FIFO read latency (registered output)
//   - Saturating 8-bit space/count reporting
//
// Documentation: projects/components/stream/PRD.md
// Subsystem: stream_fub

`timescale 1ns / 1ps

`include "fifo_defs.svh"
`include "reset_defs.svh"

module sram_controller #(
    // Primary parameters (long names for external configuration)
    parameter int NUM_CHANNELS = 8,
    parameter int DATA_WIDTH = 512,
    parameter int SRAM_DEPTH = 512,                  // Depth per channel SRAM
    parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,  // Width of count signals

    // Short aliases (for internal use)
    parameter int NC = NUM_CHANNELS,
    parameter int DW = DATA_WIDTH,
    parameter int SD = SRAM_DEPTH,
    parameter int SCW = SEG_COUNT_WIDTH,             // Segment count width
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1    // Channel ID width (min 1 bit)
) (
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // Allocation Interface (for AXI Read Engine flow control)
    // Single request with ID - ID selects which channel's space to check
    //=========================================================================
    input  logic                        axi_rd_alloc_req,        // Allocation request
    input  logic [7:0]                  axi_rd_alloc_size,       // Number of beats to allocate
    input  logic [CIW-1:0]              axi_rd_alloc_id,         // Channel ID for allocation
    // Per-channel free-space vector. Registered at this module's output
    // boundary (see the always_ff near the bottom of this module) so
    // downstream arbiters in the read engine see a stable, 1-cycle-old
    // view rather than a combinational chain that crosses module
    // boundaries and feeds wide priority encoders. At 8 channels the
    // unregistered path could not close 100 MHz on the xc7a100t-1 and
    // false-pathing it would have violated the grant valid/ready
    // handshake. The 1-cycle latency is a no-op for AXI burst pacing.
    output logic [NC-1:0][SCW-1:0]      axi_rd_alloc_space_free, // Free space in each FIFO (registered)

    //=========================================================================
    // Write Interface (AXI Read Engine → FIFO)
    // Transaction ID-based: single valid + ID selects channel
    //=========================================================================
    input  logic                        axi_rd_sram_valid,      // Single valid
    output logic                        axi_rd_sram_ready,      // Ready (muxed from selected channel)
    input  logic [CIW-1:0]              axi_rd_sram_id,         // Channel ID select
    input  logic [DW-1:0]               axi_rd_sram_data,       // common data bus

    //=========================================================================
    // Drain Interface (Write Engine Flow Control)
    //=========================================================================
    // Registered at module boundary -- see axi_rd_alloc_space_free comment.
    output logic [NC-1:0][SCW-1:0]      axi_wr_drain_data_avail,  // Available data after reservations (registered)
    input  logic [NC-1:0]               axi_wr_drain_req,         // Per-channel drain request
    input  logic [NC-1:0][7:0]          axi_wr_drain_size,        // Per-channel drain size

    //=========================================================================
    // Read Interface (FIFO → AXI Write Engine)
    //=========================================================================
    // Also registered at module boundary -- feeds write engine arbitration.
    output logic [NC-1:0]               axi_wr_sram_valid,      // Per-channel valid (registered)
    input  logic                        axi_wr_sram_drain,      // Ready (consumer requests data)
    input  logic [CIW-1:0]              axi_wr_sram_id,         // Channel ID select
    output logic [DW-1:0]               axi_wr_sram_data,       // Data from selected channel

    //=========================================================================
    // Debug Interface (for catching bridge bugs)
    //=========================================================================
    output logic [NC-1:0]               dbg_bridge_pending,
    output logic [NC-1:0]               dbg_bridge_out_valid
);

    //=========================================================================
    // ID-to-Channel Decode Logic
    //=========================================================================
    // Decode transaction IDs to per-channel enables and mux ready signals
    //=========================================================================

    logic [NC-1:0] axi_rd_sram_valid_decoded;
    logic [NC-1:0] axi_rd_sram_ready_per_channel;
    logic [NC-1:0] axi_wr_sram_drain_decoded;
    logic [NC-1:0][DW-1:0] axi_wr_sram_data_per_channel;
    logic [NC-1:0] axi_rd_alloc_req_decoded;

    // Unregistered combinational versions of the per-channel availability
    // outputs. The wrapper flops these into the externally-visible
    // axi_{rd_alloc_space_free, wr_drain_data_avail, wr_sram_valid}
    // ports so downstream arbiters see a stable, registered view.
    logic [NC-1:0][SCW-1:0] axi_rd_alloc_space_free_comb;
    logic [NC-1:0][SCW-1:0] axi_wr_drain_data_avail_comb;
    logic [NC-1:0]          axi_wr_sram_valid_comb;

    // Write valid decode: axi_rd_sram_id selects which channel
    always_comb begin
        axi_rd_sram_valid_decoded = '0;
        /* verilator lint_off WIDTHEXPAND */
        if (axi_rd_sram_valid && axi_rd_sram_id < NC) begin
            axi_rd_sram_valid_decoded[axi_rd_sram_id] = 1'b1;
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    // Ready mux: select ready from channel indicated by axi_rd_sram_id
    always_comb begin
        /* verilator lint_off WIDTHEXPAND */
        if (axi_rd_sram_id < NC) begin
            axi_rd_sram_ready = axi_rd_sram_ready_per_channel[axi_rd_sram_id];
        end else begin
            axi_rd_sram_ready = 1'b0;  // Invalid ID → not ready
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    // Read/drain decode: axi_wr_sram_id selects which channel to drain
    always_comb begin
        axi_wr_sram_drain_decoded = '0;
        /* verilator lint_off WIDTHEXPAND */
        if (axi_wr_sram_drain && axi_wr_sram_id < NC) begin
            axi_wr_sram_drain_decoded[axi_wr_sram_id] = 1'b1;
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    // Data mux: select data from channel indicated by axi_wr_sram_id
    always_comb begin
        /* verilator lint_off WIDTHEXPAND */
        if (axi_wr_sram_id < NC) begin
            axi_wr_sram_data = axi_wr_sram_data_per_channel[axi_wr_sram_id];
        end else begin
            axi_wr_sram_data = '0;  // Invalid ID → zero data
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    // Read allocation decode: axi_rd_alloc_id selects which channel
    always_comb begin
        axi_rd_alloc_req_decoded = '0;
        /* verilator lint_off WIDTHEXPAND */
        if (axi_rd_alloc_req && axi_rd_alloc_id < NC) begin
            axi_rd_alloc_req_decoded[axi_rd_alloc_id] = 1'b1;
        end
        /* verilator lint_on WIDTHEXPAND */
    end

    //=========================================================================
    // Per-Channel Unit Instantiation
    //=========================================================================
    // Each channel has its own allocation controller, FIFO, and latency bridge
    // encapsulated in a single unit for cleaner hierarchy.
    //=========================================================================

    generate
        for (genvar i = 0; i < NC; i++) begin : gen_channel_units
            sram_controller_unit #(
                .DATA_WIDTH(DW),
                .SRAM_DEPTH(SRAM_DEPTH),
                .SEG_COUNT_WIDTH(SEG_COUNT_WIDTH)
            ) u_channel_unit (
                .clk                (clk),
                .rst_n              (rst_n),

                // Write interface (AXI Read Engine → FIFO)
                // Decoded valid from ID - only selected channel sees valid
                .axi_rd_sram_valid  (axi_rd_sram_valid_decoded[i]),
                .axi_rd_sram_ready  (axi_rd_sram_ready_per_channel[i]),
                .axi_rd_sram_data   (axi_rd_sram_data),      // SHARED - all units see same data

                // Read interface (FIFO → Latency Bridge → AXI Write Engine)
                // Decoded drain connects to ready (consumer requests data)
                .axi_wr_sram_valid  (axi_wr_sram_valid_comb[i]),  // unreg -> flopped at wrapper output
                .axi_wr_sram_ready  (axi_wr_sram_drain_decoded[i]),
                .axi_wr_sram_data   (axi_wr_sram_data_per_channel[i]),

                // Allocation interface (Read Engine Flow Control)
                // Decoded from ID - only selected channel sees req
                .axi_rd_alloc_req       (axi_rd_alloc_req_decoded[i]),
                .axi_rd_alloc_size      (axi_rd_alloc_size),                 // SHARED - all see same size
                .axi_rd_alloc_space_free(axi_rd_alloc_space_free_comb[i]),   // unreg -> flopped at wrapper output

                // Drain interface (Write Engine Flow Control)
                .axi_wr_drain_req       (axi_wr_drain_req[i]),
                .axi_wr_drain_size      (axi_wr_drain_size[i]),
                .axi_wr_drain_data_avail(axi_wr_drain_data_avail_comb[i]),   // unreg -> flopped at wrapper output

                // Debug
                .dbg_bridge_pending     (dbg_bridge_pending[i]),
                .dbg_bridge_out_valid   (dbg_bridge_out_valid[i])
            );
        end
    endgenerate

    //=========================================================================
    // Output register stage on per-channel availability vectors
    //=========================================================================
    // The unregistered combinational versions feed the per-channel
    // sram_controller_unit blocks; we flop them before they leave the
    // module. Justification:
    //
    //   * Both axi_rd_alloc_space_free and axi_wr_drain_data_avail feed
    //     wide priority-encode/arbitration trees inside the read and
    //     write engines. At 8 channels the combinational distance from
    //     the per-channel skid-buffer write pointer through the engine
    //     arbiter's grant decision exceeds 14 LUT levels -- not closable
    //     at 100 MHz on the xc7a100t-1.
    //
    //   * False-pathing the arbitration cone is unsafe because the
    //     arbiter's grant_valid + grant_id form a valid/ready handshake
    //     with the engine's grant_ack. A stale grant value would let the
    //     engine latch the wrong r_aw_channel_id and issue an AW for the
    //     wrong channel's address. So the path has to be properly closed,
    //     and pipelining the source-side "available" signals is the
    //     cleanest way to do that.
    //
    //   * Cost: 1 cycle of latency on "space free" / "data available"
    //     reporting. Since AXI bursts of 16 beats already mask
    //     single-cycle credit changes, the effect on throughput and
    //     latency is below measurement noise.
    //
    // No reset needed on these: the combinational sources self-initialize
    // from per-channel registers that DO reset, so the first valid cycle
    // after reset already presents stable values.
    always_ff @(posedge clk) begin
        axi_rd_alloc_space_free <= axi_rd_alloc_space_free_comb;
        axi_wr_drain_data_avail <= axi_wr_drain_data_avail_comb;
        axi_wr_sram_valid       <= axi_wr_sram_valid_comb;
    end

endmodule : sram_controller
