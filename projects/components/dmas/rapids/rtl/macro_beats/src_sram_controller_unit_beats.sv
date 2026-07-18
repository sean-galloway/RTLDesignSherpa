// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: src_sram_controller_unit
// Purpose: Single-channel Source SRAM Controller Unit
//
// Description:
//   Single-channel SRAM controller unit for the SOURCE path containing:
//   - Allocation controller (stream_alloc_ctrl)
//   - FIFO buffer (gaxi_fifo_sync)
//   - Latency bridge (stream_latency_bridge)
//
//   Data flow: AXI Read Engine (fill) -> FIFO -> Network Master (drain)
//
//   This unit handles one channel's data flow from AXI read through
//   buffering to network egress with proper flow control.
//
// Parameters:
//   - DATA_WIDTH: Data width in bits (default: 512)
//   - SRAM_DEPTH: FIFO depth in entries (default: 512)
//   - SEG_COUNT_WIDTH: Width for count signals
//
// Interfaces:
//   - Fill side: AXI Read Engine -> FIFO (valid/ready/data)
//   - Drain side: FIFO -> Latency Bridge -> Network Master (valid/ready/data)
//   - Allocation: Flow control for producer/consumer
//
// Based on: unified_sram_controller_unit.sv
// Subsystem: rapids_macro_beats
//
// Author: RTL Design Sherpa
// Created: 2026-01-10

`timescale 1ns / 1ps

`include "fifo_defs.svh"
`include "reset_defs.svh"

module src_sram_controller_unit_beats #(
    // Primary parameters
    parameter int DATA_WIDTH = 512,
    parameter int SRAM_DEPTH = 512,
    parameter int SEG_COUNT_WIDTH = $clog2(SRAM_DEPTH) + 1,

    // Short aliases
    parameter int DW = DATA_WIDTH,
    parameter int SD = SRAM_DEPTH,
    parameter int SCW = SEG_COUNT_WIDTH
) (
    input  logic          clk,
    input  logic          rst_n,

    //=========================================================================
    // Fill Allocation Interface (AXI Read Engine -> SRAM)
    //=========================================================================
    input  logic                  fill_alloc_req,
    input  logic [7:0]            fill_alloc_size,
    output logic [SCW-1:0]        fill_space_free,

    //=========================================================================
    // Fill Data Interface (AXI Read Engine -> FIFO)
    //=========================================================================
    input  logic                  fill_valid,
    output logic                  fill_ready,
    input  logic [DW-1:0]         fill_data,

    //=========================================================================
    // Drain Flow Control Interface (Network Master)
    //=========================================================================
    output logic [SCW-1:0]        drain_data_avail,
    input  logic                  drain_req,
    input  logic [7:0]            drain_size,

    //=========================================================================
    // Drain Data Interface (FIFO -> Network Master)
    //=========================================================================
    output logic                  drain_valid,
    input  logic                  drain_ready,
    output logic [DW-1:0]         drain_data,

    //=========================================================================
    // Debug Interface
    //=========================================================================
    output logic                  dbg_bridge_pending,
    output logic                  dbg_bridge_out_valid
);

    //==========================================================================
    // Local Parameters
    //==========================================================================
    localparam int ADDR_WIDTH = $clog2(SD);

    //==========================================================================
    // Internal Signals
    //==========================================================================
    logic [ADDR_WIDTH:0] alloc_space_free;
    logic [ADDR_WIDTH:0] drain_data_available;

    // FIFO -> Latency Bridge
    logic                fifo_rd_valid_internal;
    logic                fifo_rd_ready_internal;
    logic [DW-1:0]       fifo_rd_data_internal;

    // FIFO status
    logic [ADDR_WIDTH:0] fifo_count;

    // Latency bridge status
    logic [2:0]          bridge_occupancy;

    //==========================================================================
    // Allocation Controller (Space tracking for AXI Read Engine)
    //==========================================================================
    alloc_ctrl_beats #(
        .DEPTH(SD),
        .REGISTERED(1)
    ) u_alloc_ctrl (
        .axi_aclk           (clk),
        .axi_aresetn        (rst_n),

        // Allocation request from AXI Read Engine
        .wr_valid           (fill_alloc_req),
        .wr_size            (fill_alloc_size),
        .wr_ready           (),

        // Release when data exits controller
        .rd_valid           (drain_valid && drain_ready),
        .rd_ready           (),

        // Space tracking
        .space_free         (alloc_space_free),

        // Unused status
        .wr_full            (),
        .wr_almost_full     (),
        .rd_empty           (),
        .rd_almost_empty    ()
    );

    //==========================================================================
    // Drain Controller (Data tracking for Network Master)
    //==========================================================================
    drain_ctrl_beats #(
        .DEPTH(SD),
        .REGISTERED(1)
    ) u_drain_ctrl (
        .axi_aclk           (clk),
        .axi_aresetn        (rst_n),

        // Data written to FIFO
        .wr_valid           (fill_valid && fill_ready),
        .wr_ready           (),

        // Drain request from Network Master
        .rd_valid           (drain_req),
        .rd_size            (drain_size),
        .rd_ready           (),

        // Data tracking
        .data_available     (drain_data_available),

        // Unused status
        .wr_full            (),
        .wr_almost_full     (),
        .rd_empty           (),
        .rd_almost_empty    ()
    );

    //==========================================================================
    // FIFO Buffer (Physical Data Storage)
    //==========================================================================
    gaxi_fifo_sync #(
        .MEM_STYLE(FIFO_AUTO),
        .REGISTERED(1),
        .DATA_WIDTH(DW),
        .DEPTH(SD)
    ) u_channel_fifo (
        .axi_aclk       (clk),
        .axi_aresetn    (rst_n),

        // Write port (from AXI Read Engine)
        .wr_valid       (fill_valid),
        .wr_ready       (fill_ready),
        .wr_data        (fill_data),

        // Read port (to Latency Bridge)
        .rd_valid       (fifo_rd_valid_internal),
        .rd_ready       (fifo_rd_ready_internal),
        .rd_data        (fifo_rd_data_internal),

        // Status
        .count          (fifo_count)
    );

    //==========================================================================
    // Latency Bridge (Aligns FIFO read latency)
    //==========================================================================
    latency_bridge_beats #(
        .DATA_WIDTH(DW)
    ) u_latency_bridge (
        .clk            (clk),
        .rst_n          (rst_n),

        // Slave (from FIFO)
        .s_data         (fifo_rd_data_internal),
        .s_valid        (fifo_rd_valid_internal),
        .s_ready        (fifo_rd_ready_internal),

        // Master (to Network Master)
        .m_data         (drain_data),
        .m_valid        (drain_valid),
        .m_ready        (drain_ready),

        // Status
        .occupancy      (bridge_occupancy),

        // Debug
        .dbg_r_pending      (dbg_bridge_pending),
        .dbg_r_out_valid    (dbg_bridge_out_valid)
    );

    //==========================================================================
    // Space/Count Reporting
    //==========================================================================

    // Total data available = drain controller + latency bridge
    assign drain_data_avail = drain_data_available + SCW'(bridge_occupancy);

    // Register fill_space_free to break combinatorial paths
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            fill_space_free <= SCW'(SD);
        end else begin
            fill_space_free <= alloc_space_free;
        end
    )

endmodule : src_sram_controller_unit_beats
