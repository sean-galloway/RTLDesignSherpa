// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: stream_drain_ctrl
// Purpose: Drain Control (Virtual FIFO for write engine flow control)
//
// Description:
//   Tracks space availability for write engine using FIFO pointer logic.
//   No data storage - only pointer arithmetic and flow control.
//
//   Write side: Data written to FIFO (increments occupancy)
//   Read side: Drain requests (reserves data, decrements occupancy)
//
//   Use Case: Pre-reservation for AXI write engines to prevent underflow
//
// Subsystem: stream_fub
// Author: sean galloway
// Created: 2025-11-10

`timescale 1ns / 1ps

`include "reset_defs.svh"

module stream_drain_ctrl #(
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

    // Write Interface (Data enters FIFO)
    input  logic                wr_valid,           // Data written
    output logic                wr_ready,           // Not full

    // Read Interface (Drain Requests)
    input  logic                rd_valid,           // Request to drain
    input  logic [7:0]          rd_size,            // Number of entries to drain
    output logic                rd_ready,           // Data available

    // Status Outputs
    output logic [AW:0]         data_available,     // Available data
    output logic                wr_full,            // Full (no space)
    output logic                wr_almost_full,     // Almost full
    output logic                rd_empty,           // Empty (no data)
    output logic                rd_almost_empty     // Almost empty
);

    // ---------------------------------------------------------------------
    // Debug: Check parameter values
    // ---------------------------------------------------------------------
    initial begin
    end

    // ---------------------------------------------------------------------
    // Local signals
    // ---------------------------------------------------------------------
    logic [AW:0]   r_wr_ptr_bin, r_rd_ptr_bin;
    logic [AW:0]   w_wr_ptr_bin_next, w_rd_ptr_bin_next;
    logic          r_wr_full, r_wr_almost_full, r_rd_empty, r_rd_almost_empty;
    logic [AW:0]   w_count;
    logic [AW:0]   w_available_data;  // Calculate available data independently

    // ---------------------------------------------------------------------
    // Write/Read enables
    // ---------------------------------------------------------------------
    logic w_write, w_read;
    assign w_write = wr_valid && wr_ready;
    assign w_read  = rd_valid && rd_ready;

    // ---------------------------------------------------------------------
    // Write pointer (data entry pointer) - single beat increments
    // ---------------------------------------------------------------------
    counter_bin #(
        .WIDTH (AW + 1),
        .MAX   (D)
    ) write_pointer_inst (
        .clk              (axi_aclk),
        .rst_n            (axi_aresetn),
        .enable           (w_write && !r_wr_full),
        .counter_bin_curr (r_wr_ptr_bin),
        .counter_bin_next (w_wr_ptr_bin_next)
    );

    // ---------------------------------------------------------------------
    // Read pointer (drain pointer) - variable size increments
    // ---------------------------------------------------------------------
    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_rd_ptr_bin <= '0;
        end else begin
            if (w_read && !r_rd_empty) begin
                r_rd_ptr_bin <= r_rd_ptr_bin + (AW+1)'(rd_size);
            end
        end
    )

    // Calculate available data (current write pointer - current read pointer)
    // assign w_available_data = r_wr_ptr_bin - r_rd_ptr_bin;

    // Next read pointer
    assign w_rd_ptr_bin_next = r_rd_ptr_bin + (w_read && !r_rd_empty ? (AW+1)'(rd_size) : '0);

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
    assign rd_ready = !r_rd_empty;  // Simple not-empty check (protocol uses polling, not ready handshake)

    // Data available = current occupancy (use current pointers, not next!)
    assign data_available = w_count;

    // Status outputs
    assign wr_full = r_wr_full;
    assign wr_almost_full = r_wr_almost_full;
    assign rd_empty = r_rd_empty;
    assign rd_almost_empty = r_rd_almost_empty;

    // ---------------------------------------------------------------------
    // Over-drain check (simulation only)
    // ---------------------------------------------------------------------
    // The read pointer advances by the FULL rd_size, gated only on !rd_empty.
    // If a caller ever reserves more beats than are actually present, rd_ptr
    // overshoots wr_ptr and the wrap-corrected occupancy in fifo_control
    // computes as ~DEPTH instead of a small number. Both pointers then advance
    // in lockstep, so the corruption is PERMANENT: the channel reports a nearly
    // full FIFO forever and the write engine issues bursts with no backing data,
    // stalling the shared in-order W-phase FIFO and freezing every channel.
    //
    // That silent corruption is the failure mode this assertion exists to make
    // loud -- it fires at the moment of the bad reservation rather than leaving
    // a deadlock to be diagnosed hundreds of microseconds later.
    // Written as a procedural check rather than an `assert property`: the
    // simulator here (Verilator) silently ignores SVA unless built with
    // --assert, which this flow does not pass -- a concurrent assertion would
    // be dead code. A plain always_ff + $error always executes.
    // synthesis translate_off
    always_ff @(posedge axi_aclk) begin
        // rd_size is 8-bit, data_available is (AW+1)-bit -- widen explicitly
        // (same cast idiom as the rd_ptr advance above) so the comparison does
        // not trip WIDTHEXPAND, which the FUB lint flow escalates to an error.
        if (axi_aresetn && rd_valid && !r_rd_empty && ((AW+1)'(rd_size) > data_available)) begin
            $error("stream_drain_ctrl: over-drain -- rd_size=%0d exceeds data_available=%0d; rd_ptr will overshoot wr_ptr and permanently corrupt the occupancy count",
                   rd_size, data_available);
        end
    end
    // synthesis translate_on

endmodule : stream_drain_ctrl
