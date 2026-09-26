// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: snk_sram_controller_beats
// Purpose: SINK-side naming wrapper around STREAM's sram_controller
//
// Description:
//   This module contains NO logic. It is a pure naming adapter that maps the
//   RAPIDS sink-path signal names (fill_*/drain_*) onto STREAM's
//   sram_controller port names (axi_rd_*/axi_wr_*), which is the single
//   canonical implementation of the per-channel SRAM for both areas.
//
//   Read STREAM's naming this way -- it is counterintuitive and has already
//   caused one misunderstanding:
//
//     axi_rd_*  belongs to the AXI READ engine, and WRITES INTO the SRAM (fill)
//     axi_wr_*  belongs to the AXI WRITE engine, and READS OUT OF the SRAM (drain)
//
//   Both groups are live here: the sink path fills from the AXIS slave
//   and drains to the AXI write engine.
//
// Why a wrapper instead of a RAPIDS copy:
//   RAPIDS previously carried its own src/snk macro + unit (4 files) that were
//   byte-identical to STREAM's apart from renames and two divergences, one of
//   which was a real defect:
//
//     1. The unit added `+ SCW'(bridge_occupancy)` to drain_data_avail. STREAM
//        removed exactly that line and left a measured writeup at
//        sram_controller_unit.sv:282-305 explaining why it double-counts: a
//        beat sitting in the latency bridge's skid is STILL counted in
//        drain_data_available, so adding the occupancy lets a consumer size a
//        request against beats that do not exist, rd_ptr overshoots wr_ptr and
//        the occupancy count is permanently corrupted. That is the over-drain
//        that drain_ctrl_beats.sv's $error reports on the sink path.
//     2. MEM_STYLE was FIFO_AUTO rather than STREAM's FIFO_BRAM, which costs
//        ~9.9K LUTs of distributed RAM on the xc7a100t-1.
//
//   Duplicated RTL means a fix landed in one area silently misses the other,
//   which is precisely what happened. One implementation, two naming wrappers.
//
// Note on drain_valid vs drain_valid_comb:
//   drain_valid is REGISTERED at the SRAM boundary for timing closure and is
//   what arbitration should consume. drain_valid_comb is the unregistered tap
//   and exists ONLY to gate the outgoing data beat, so a 1-cycle-stale
//   registered valid cannot pull a beat that is not there. A consumer that
//   samples only the registered valid can pop a beat it never transmits -- see
//   STREAM axi_write_engine.sv:694-702.
//
// Subsystem: rapids_macro_beats

`timescale 1ns / 1ps

module snk_sram_controller_beats #(
    // Primary parameters
    parameter int NUM_CHANNELS = 8,
    parameter int DATA_WIDTH = 512,
    parameter int SRAM_DEPTH = 512,                  // Depth PER CHANNEL
    parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,

    // Short aliases
    parameter int NC = NUM_CHANNELS,
    parameter int DW = DATA_WIDTH,
    parameter int SD = SRAM_DEPTH,
    parameter int SCW = SEG_COUNT_WIDTH,
    // Channel ID width: supports up to 128 channels (7 bits)
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1
) (
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // Fill Allocation Interface (AXI Read Engine -> SRAM)
    //=========================================================================
    input  logic                        fill_alloc_req,
    input  logic [7:0]                  fill_alloc_size,
    input  logic [CIW-1:0]              fill_alloc_id,
    output logic [NC-1:0][SCW-1:0]      fill_space_free,   // Registered

    //=========================================================================
    // Fill Data Interface (AXI Read Engine -> FIFO)
    //=========================================================================
    input  logic                        fill_valid,
    output logic                        fill_ready,
    input  logic [CIW-1:0]              fill_id,
    input  logic [DW-1:0]               fill_data,

    //=========================================================================
    // Drain Flow Control Interface (AXI Write Engine)
    //=========================================================================
    output logic [NC-1:0][SCW-1:0]      drain_data_avail,  // Registered
    input  logic [NC-1:0]               drain_req,
    input  logic [NC-1:0][7:0]          drain_size,

    //=========================================================================
    // Drain Data Interface (FIFO -> AXI Write Engine)
    //=========================================================================
    output logic [NC-1:0]               drain_valid,       // Registered (arbitration)
    output logic [NC-1:0]               drain_valid_comb,  // Combinational (beat gate)
    input  logic                        drain_read,
    input  logic [CIW-1:0]              drain_id,
    output logic [DW-1:0]               drain_data,

    //=========================================================================
    // Debug Interface
    //=========================================================================
    output logic [NC-1:0]               dbg_bridge_pending,
    output logic [NC-1:0]               dbg_bridge_out_valid
);

    // Validate NUM_CHANNELS at elaboration time
    initial begin
        if (NC > 128) begin
            $fatal(1, "snk_sram_controller_beats: NUM_CHANNELS=%0d exceeds maximum of 128", NC);
        end
    end

    //=========================================================================
    // STREAM sram_controller -- the canonical implementation.
    // Names only; no logic is added on either side of this instance.
    //=========================================================================
    sram_controller #(
        .NUM_CHANNELS       (NC),
        .DATA_WIDTH         (DW),
        .SRAM_DEPTH         (SD),
        .SEG_COUNT_WIDTH    (SCW)
    ) u_sram_controller (
        .clk                        (clk),
        .rst_n                      (rst_n),

        // FILL: the AXI read engine writes INTO the SRAM
        .axi_rd_alloc_req           (fill_alloc_req),
        .axi_rd_alloc_size          (fill_alloc_size),
        .axi_rd_alloc_id            (fill_alloc_id),
        .axi_rd_alloc_space_free    (fill_space_free),
        .axi_rd_sram_valid          (fill_valid),
        .axi_rd_sram_ready          (fill_ready),
        .axi_rd_sram_id             (fill_id),
        .axi_rd_sram_data           (fill_data),

        // DRAIN: the consumer reads OUT OF the SRAM
        .axi_wr_drain_data_avail    (drain_data_avail),
        .axi_wr_drain_req           (drain_req),
        .axi_wr_drain_size          (drain_size),
        .axi_wr_sram_valid          (drain_valid),
        .axi_wr_sram_valid_comb     (drain_valid_comb),
        .axi_wr_sram_drain          (drain_read),
        .axi_wr_sram_id             (drain_id),
        .axi_wr_sram_data           (drain_data),

        // Debug
        .dbg_bridge_pending         (dbg_bridge_pending),
        .dbg_bridge_out_valid       (dbg_bridge_out_valid)
    );

endmodule : snk_sram_controller_beats
