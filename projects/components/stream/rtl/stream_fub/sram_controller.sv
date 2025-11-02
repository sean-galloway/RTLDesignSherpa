// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: sram_controller
// Purpose: Multi-Channel SRAM Segmentation and Flow Control
//
// Description:
//   Manages monolithic SRAM by partitioning into per-channel segments.
//   Provides independent read/write pointers, flow control, and pre-allocation.
//
//   Key Features:
//   - Per-channel segmentation (SRAM_DEPTH / NUM_CHANNELS)
//   - Dual-pointer management (write from AXI RD, read to AXI WR)
//   - Pre-allocation prevents race conditions
//   - ID-based routing (AXI transaction ID selects segment)
//
// This does 90% of buffer management work so AXI engines stay simple!
//
// Documentation: projects/components/stream/docs/SRAM_CONTROLLER_SPEC.md
// Subsystem: stream_fub
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Import common STREAM and monitor packages
`include "stream_imports.svh"
`include "reset_defs.svh"


module sram_controller #(
    parameter int NUM_CHANNELS = 8,                 // Number of channels
    parameter int SRAM_DEPTH = 4096,                // Total SRAM depth
    parameter int SRAM_ADDR_WIDTH = $clog2(SRAM_DEPTH),
    parameter int DATA_WIDTH = 512,                 // Data width in bits
    parameter int ID_WIDTH = 8,                     // AXI ID width
    parameter int SEGMENT_SIZE = SRAM_DEPTH / NUM_CHANNELS,
    parameter int SEG_PTR_WIDTH = $clog2(SEGMENT_SIZE),
    parameter int SEG_COUNT_WIDTH = $clog2(SEGMENT_SIZE) + 1,
    parameter int MIN_SPACE_THRESHOLD = 8           // Minimum space for grant
) (
    // Clock and Reset
    input  logic                        clk,
    input  logic                        rst_n,

    //=========================================================================
    // AXI Read Data Interface (Write to SRAM)
    //=========================================================================
    // Data arriving from AXI read transactions
    input  logic                        axi_rd_data_valid,      // Read data valid
    input  logic [ID_WIDTH-1:0]         axi_rd_data_id,         // Transaction ID → channel
    input  logic [DATA_WIDTH-1:0]       axi_rd_data,            // Read data payload
    output logic                        axi_rd_data_ready,      // Ready to accept data

    // Pre-allocation interface (before data arrives)
    input  logic [NUM_CHANNELS-1:0]     rd_space_req,           // Channel requests space
    input  logic [NUM_CHANNELS-1:0][7:0] rd_xfer_count,        // Beats to reserve
    output logic [NUM_CHANNELS-1:0]     rd_space_grant,         // Space granted
    output logic [NUM_CHANNELS-1:0]     rd_space_valid,         // Space available

    //=========================================================================
    // AXI Write Data Interface (Read from SRAM)
    //=========================================================================
    // Read requests from AXI write engine
    input  logic [NUM_CHANNELS-1:0]     axi_wr_sram_req,        // Channel requests read
    output logic [NUM_CHANNELS-1:0]     axi_wr_sram_ack,        // Read acknowledged
    output logic [NUM_CHANNELS-1:0][DATA_WIDTH-1:0] axi_wr_sram_data,  // Read data (1-cycle latency)

    // Flow control signals
    output logic [NUM_CHANNELS-1:0]     sram_rd_valid,          // Data available to read
    output logic [NUM_CHANNELS-1:0][SEG_COUNT_WIDTH-1:0] sram_rd_count,  // Entries available

    //=========================================================================
    // SRAM Physical Interface
    //=========================================================================
    // Write port (from AXI read data)
    output logic                        sram_wr_en,
    output logic [SRAM_ADDR_WIDTH-1:0]  sram_wr_addr,
    output logic [DATA_WIDTH-1:0]       sram_wr_data,

    // Read port (to AXI write data)
    output logic                        sram_rd_en,
    output logic [SRAM_ADDR_WIDTH-1:0]  sram_rd_addr,
    input  logic [DATA_WIDTH-1:0]       sram_rd_data,
    input  logic                        sram_rd_data_valid      // SRAM read latency = 1 cycle
);

    //=========================================================================
    // Local Parameters
    //=========================================================================

    localparam int CHAN_WIDTH = $clog2(NUM_CHANNELS);

    //=========================================================================
    // Per-Channel State
    //=========================================================================

    // Pointers (local to each segment)
    logic [NUM_CHANNELS-1:0][SEG_PTR_WIDTH-1:0] r_wr_ptr;
    logic [NUM_CHANNELS-1:0][SEG_PTR_WIDTH-1:0] r_rd_ptr;

    // Occupancy tracking
    logic [NUM_CHANNELS-1:0][SEG_COUNT_WIDTH-1:0] r_wr_reserved;  // Pre-allocated space
    logic [NUM_CHANNELS-1:0][SEG_COUNT_WIDTH-1:0] w_rd_count;     // Entries available to read
    logic [NUM_CHANNELS-1:0][SEG_COUNT_WIDTH-1:0] w_space_avail;  // Space for new writes

    // Read request tracking (for 1-cycle SRAM latency)
    logic [NUM_CHANNELS-1:0] r_rd_pending;
    logic [CHAN_WIDTH-1:0] r_rd_channel;

    //=========================================================================
    // Write Path: AXI Read Data → SRAM
    //=========================================================================

    // Extract channel from transaction ID (lower bits)
    logic [CHAN_WIDTH-1:0] w_wr_channel;
    assign w_wr_channel = axi_rd_data_id[CHAN_WIDTH-1:0];

    // Calculate SRAM write address
    logic [SRAM_ADDR_WIDTH-1:0] w_sram_wr_addr;
    assign w_sram_wr_addr = SRAM_ADDR_WIDTH'((w_wr_channel * SEGMENT_SIZE)) + SRAM_ADDR_WIDTH'(r_wr_ptr[w_wr_channel]);

    // Write to SRAM when AXI read data arrives
    assign axi_rd_data_ready = 1'b1;  // Always ready (pre-allocation ensures space)
    assign sram_wr_en = axi_rd_data_valid && axi_rd_data_ready;
    assign sram_wr_addr = w_sram_wr_addr;
    assign sram_wr_data = axi_rd_data;

    // Update write pointer
    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                r_wr_ptr[i] <= '0;
            end
        end else begin
            if (sram_wr_en) begin
                // Increment write pointer (wrap within segment)
                if (r_wr_ptr[w_wr_channel] == SEG_PTR_WIDTH'(SEGMENT_SIZE - 1)) begin
                    r_wr_ptr[w_wr_channel] <= '0;
                end else begin
                    r_wr_ptr[w_wr_channel] <= r_wr_ptr[w_wr_channel] + 1'b1;
                end
            end
        end
    )


    //=========================================================================
    // Pre-Allocation Logic
    //=========================================================================
    // Reserves space before AXI read data arrives to prevent overwrites

    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                r_wr_reserved[i] <= '0;
            end
        end else begin
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                // Grant space reservation
                if (rd_space_req[i] && rd_space_grant[i]) begin
                    r_wr_reserved[i] <= r_wr_reserved[i] + SEG_COUNT_WIDTH'(rd_xfer_count[i]);
                end

                // Commit reservation when data arrives
                if (sram_wr_en && (w_wr_channel == CHAN_WIDTH'(i))) begin
                    r_wr_reserved[i] <= r_wr_reserved[i] - 1'b1;
                end
            end
        end
    )


    //=========================================================================
    // Occupancy Calculation
    //=========================================================================

    always_comb begin
        for (int i = 0; i < NUM_CHANNELS; i++) begin
            // Read count (entries available to drain)
            if (r_wr_ptr[i] >= r_rd_ptr[i]) begin
                w_rd_count[i] = r_wr_ptr[i] - r_rd_ptr[i];
            end else begin
                // Wrapped
                w_rd_count[i] = SEG_COUNT_WIDTH'(SEGMENT_SIZE) - r_rd_ptr[i] + r_wr_ptr[i];
            end

            // Space available (for new writes)
            w_space_avail[i] = SEG_COUNT_WIDTH'(SEGMENT_SIZE) - w_rd_count[i] - r_wr_reserved[i];
        end
    end

    //=========================================================================
    // Pre-Allocation Grant Logic
    //=========================================================================

    always_comb begin
        for (int i = 0; i < NUM_CHANNELS; i++) begin
            // Grant if requested space is available
            rd_space_grant[i] = rd_space_req[i] &&
                               (w_space_avail[i] >= SEG_COUNT_WIDTH'(rd_xfer_count[i]));

            // Space valid if above threshold
            rd_space_valid[i] = (w_space_avail[i] >= SEG_COUNT_WIDTH'(MIN_SPACE_THRESHOLD));
        end
    end

    //=========================================================================
    // Read Path: SRAM → AXI Write Data
    //=========================================================================

    // Simple priority arbiter for read requests (channel 0 has highest priority)
    logic [CHAN_WIDTH-1:0] w_rd_req_channel;
    logic w_rd_req_valid;

    always_comb begin
        w_rd_req_valid = 1'b0;
        w_rd_req_channel = '0;

        // Priority encoder
        for (int i = NUM_CHANNELS-1; i >= 0; i--) begin
            if (axi_wr_sram_req[i]) begin
                w_rd_req_valid = 1'b1;
                w_rd_req_channel = CHAN_WIDTH'(i);
            end
        end
    end

    // Calculate SRAM read address
    logic [SRAM_ADDR_WIDTH-1:0] w_sram_rd_addr;
    assign w_sram_rd_addr = SRAM_ADDR_WIDTH'((w_rd_req_channel * SEGMENT_SIZE)) + SRAM_ADDR_WIDTH'(r_rd_ptr[w_rd_req_channel]);

    // SRAM read control
    assign sram_rd_en = w_rd_req_valid;
    assign sram_rd_addr = w_sram_rd_addr;

    // Track pending read for 1-cycle SRAM latency
    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                r_rd_pending[i] <= 1'b0;
            end
            r_rd_channel <= '0;
        end else begin
            // Clear all pending
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                r_rd_pending[i] <= 1'b0;
            end

            // Set pending for requested channel
            if (sram_rd_en) begin
                r_rd_pending[w_rd_req_channel] <= 1'b1;
                r_rd_channel <= w_rd_req_channel;
            end
        end
    )


    // Update read pointer
    `ALWAYS_FF_RST(clk, rst_n,
if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                r_rd_ptr[i] <= '0;
            end
        end else begin
            if (sram_rd_en) begin
                // Increment read pointer (wrap within segment)
                if (r_rd_ptr[w_rd_req_channel] == SEG_PTR_WIDTH'(SEGMENT_SIZE - 1)) begin
                    r_rd_ptr[w_rd_req_channel] <= '0;
                end else begin
                    r_rd_ptr[w_rd_req_channel] <= r_rd_ptr[w_rd_req_channel] + 1'b1;
                end
            end
        end
    )


    // Read data distribution (1-cycle latency)
    always_comb begin
        for (int i = 0; i < NUM_CHANNELS; i++) begin
            axi_wr_sram_ack[i] = r_rd_pending[i] && sram_rd_data_valid;
            axi_wr_sram_data[i] = sram_rd_data;  // Broadcast to all (only ack matters)
        end
    end

    //=========================================================================
    // Flow Control Outputs
    //=========================================================================

    always_comb begin
        for (int i = 0; i < NUM_CHANNELS; i++) begin
            sram_rd_valid[i] = (w_rd_count[i] > '0);
            sram_rd_count[i] = w_rd_count[i];
        end
    end

    //=========================================================================
    // Assertions for Verification
    //=========================================================================

    `ifdef FORMAL
    // Pointer bounds
    generate
        for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_ptr_bounds
            assert property (@(posedge clk) disable iff (!rst_n)
                r_wr_ptr[i] < SEGMENT_SIZE);
            assert property (@(posedge clk) disable iff (!rst_n)
                r_rd_ptr[i] < SEGMENT_SIZE);
        end
    endgenerate

    // Occupancy invariant
    generate
        for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_occupancy
            assert property (@(posedge clk) disable iff (!rst_n)
                (w_rd_count[i] + r_wr_reserved[i]) <= SEG_COUNT_WIDTH'(SEGMENT_SIZE));
        end
    endgenerate

    // Valid signal correctness
    generate
        for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_valid
            assert property (@(posedge clk) disable iff (!rst_n)
                sram_rd_valid[i] == (w_rd_count[i] > '0));
        end
    endgenerate

    // Grant only when space available
    generate
        for (genvar i = 0; i < NUM_CHANNELS; i++) begin : gen_grant
            assert property (@(posedge clk) disable iff (!rst_n)
                rd_space_grant[i] |-> (w_space_avail[i] >= SEG_COUNT_WIDTH'(rd_xfer_count[i])));
        end
    endgenerate
    `endif

endmodule : sram_controller
