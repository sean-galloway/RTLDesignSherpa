// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: stream_alloc_ctrl
// Purpose: Allocation Control (Virtual FIFO without data path)
//
// Description:
//   Tracks space allocation and availability using FIFO pointer logic.
//   No data storage - only pointer arithmetic and flow control.
//
//   Write side: Allocation requests (reserves space)
//   Read side: Actual data writes (releases reservation)
//
//   Use Case: Pre-allocation for AXI read engines to prevent race conditions
//
// Subsystem: stream_fub
// Author: sean galloway
// Created: 2025-10-30

`timescale 1ns / 1ps

`include "reset_defs.svh"

module stream_alloc_ctrl #(
    parameter int DEPTH = 512,                      // Virtual FIFO depth
    parameter int ALMOST_WR_MARGIN = 1,             // Almost full margin
    parameter int ALMOST_RD_MARGIN = 1,             // Almost empty margin
    parameter int REGISTERED = 1,                   // Registered outputs

    // Calculated parameters
    parameter int D = DEPTH,
    parameter int AW = $clog2(D)                    // Address width
) (
    // Clock and Reset
    input  logic                axi_aclk,
    input  logic                axi_aresetn,

    // Write Interface (Allocation Requests)
    input  logic                wr_valid,           // Allocate space
    input  logic [7:0]          wr_size,            // Number of entries to allocate
    output logic                wr_ready,           // Space available

    // Read Interface (Actual Data Written)
    input  logic                rd_valid,           // Data written
    output logic                rd_ready,           // Not full

    // Status Outputs
    output logic [AW:0]         space_free,         // Available space
    output logic                wr_full,            // Full (no space)
    output logic                wr_almost_full,     // Almost full
    output logic                rd_empty,           // Empty (no allocations)
    output logic                rd_almost_empty     // Almost empty
);

    // ---------------------------------------------------------------------
    // Debug: Check parameter values
    // ---------------------------------------------------------------------
    initial begin
        $display("stream_alloc_ctrl: DEPTH=%0d, ADDR_WIDTH=%0d", D, AW);
    end

    // ---------------------------------------------------------------------
    // Local signals
    // ---------------------------------------------------------------------
    logic [AW:0]   r_wr_ptr_bin, r_rd_ptr_bin;
    logic [AW:0]   w_wr_ptr_bin_next, w_rd_ptr_bin_next;
    logic          r_wr_full, r_wr_almost_full, r_rd_empty, r_rd_almost_empty;
    logic [AW:0]   w_count;

    // ---------------------------------------------------------------------
    // Write/Read enables
    // ---------------------------------------------------------------------
    logic w_write, w_read;
    assign w_write = wr_valid && wr_ready;
    assign w_read  = rd_valid && rd_ready;

    // ---------------------------------------------------------------------
    // Write pointer (allocation pointer) - manual increment for variable size
    // ---------------------------------------------------------------------
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_wr_ptr_bin <= '0;
        end else begin
            if (w_write && !r_wr_full) begin
                r_wr_ptr_bin <= r_wr_ptr_bin + (AW+1)'(wr_size);
                // Debug: Monitor allocations
                /* verilator lint_off WIDTHEXPAND */
                $display("ALLOC @ %t: allocated %0d beats, wr_ptr: %0d -> %0d, space_free will be %0d",
                        $time, wr_size, r_wr_ptr_bin, r_wr_ptr_bin + (AW+1)'(wr_size),
                        D - (r_wr_ptr_bin + (AW+1)'(wr_size) - r_rd_ptr_bin));
                /* verilator lint_on WIDTHEXPAND */
            end
        end
    )

    assign w_wr_ptr_bin_next = r_wr_ptr_bin + (w_write && !r_wr_full ? (AW+1)'(wr_size) : '0);

    // ---------------------------------------------------------------------
    // Read pointer (actual write pointer)
    // ---------------------------------------------------------------------
    counter_bin #(
        .WIDTH (AW + 1),
        .MAX   (D)
    ) read_pointer_inst (
        .clk              (axi_aclk),
        .rst_n            (axi_aresetn),
        .enable           (w_read && !r_rd_empty),
        .counter_bin_curr (r_rd_ptr_bin),
        .counter_bin_next (w_rd_ptr_bin_next)
    );

    // Debug: Monitor drains
    always_ff @(posedge axi_aclk) begin
        if (axi_aresetn && w_read && !r_rd_empty) begin
            /* verilator lint_off WIDTHEXPAND */
            $display("DRAIN @ %t: drained 1 beat, rd_ptr: %0d -> %0d, space_free will be %0d",
                    $time, r_rd_ptr_bin, w_rd_ptr_bin_next,
                    D - (r_wr_ptr_bin - w_rd_ptr_bin_next));
            /* verilator lint_on WIDTHEXPAND */
        end
    end

    // ---------------------------------------------------------------------
    // Control block (full/empty, almost flags, count)
    // ---------------------------------------------------------------------
    fifo_control #(
        .DEPTH             (D),
        .ADDR_WIDTH        (AW),
        .ALMOST_RD_MARGIN  (ALMOST_RD_MARGIN),
        .ALMOST_WR_MARGIN  (ALMOST_WR_MARGIN),
        .REGISTERED        (REGISTERED)
    ) fifo_control_inst (
        .wr_clk           (axi_aclk),
        .wr_rst_n         (axi_aresetn),
        .rd_clk           (axi_aclk),
        .rd_rst_n         (axi_aresetn),
        .wr_ptr_bin       (w_wr_ptr_bin_next),
        .wdom_rd_ptr_bin  (w_rd_ptr_bin_next),
        .rd_ptr_bin       (w_rd_ptr_bin_next),
        .rdom_wr_ptr_bin  (w_wr_ptr_bin_next),
        .count            (w_count),
        .wr_full          (r_wr_full),
        .wr_almost_full   (r_wr_almost_full),
        .rd_empty         (r_rd_empty),
        .rd_almost_empty  (r_rd_almost_empty)
    );

    // ---------------------------------------------------------------------
    // Output Assignments
    // ---------------------------------------------------------------------
    assign wr_ready = !r_wr_full;
    assign rd_ready = !r_rd_empty;

    // Space free = total depth - current occupancy
    assign space_free = (AW+1)'(D) - w_count;

    // Status outputs
    assign wr_full = r_wr_full;
    assign wr_almost_full = r_wr_almost_full;
    assign rd_empty = r_rd_empty;
    assign rd_almost_empty = r_rd_almost_empty;

endmodule : stream_alloc_ctrl
