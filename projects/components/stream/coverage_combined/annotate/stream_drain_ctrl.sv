//      // verilator_coverage annotation
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
 007336     input  logic                axi_aclk,
%000008     input  logic                axi_aresetn,
        
            // Write Interface (Data enters FIFO)
%000008     input  logic                wr_valid,           // Data written
%000008     output logic                wr_ready,           // Not full
        
            // Read Interface (Drain Requests)
%000000     input  logic                rd_valid,           // Request to drain
%000000     input  logic [7:0]          rd_size,            // Number of entries to drain
 000024     output logic                rd_ready,           // Data available
        
            // Status Outputs
%000000     output logic [AW:0]         data_available,     // Available data
%000000     output logic                wr_full,            // Full (no space)
%000000     output logic                wr_almost_full,     // Almost full
 000016     output logic                rd_empty,           // Empty (no data)
 000016     output logic                rd_almost_empty     // Almost empty
        );
        
            // ---------------------------------------------------------------------
            // Debug: Check parameter values
            // ---------------------------------------------------------------------
%000008     initial begin
%000008         $display("stream_drain_ctrl: DEPTH=%0d, ADDR_WIDTH=%0d", D, AW);
            end
        
            // ---------------------------------------------------------------------
            // Local signals
            // ---------------------------------------------------------------------
%000000     logic [AW:0]   r_wr_ptr_bin, r_rd_ptr_bin;
%000000     logic [AW:0]   w_wr_ptr_bin_next, w_rd_ptr_bin_next;
%000000     logic          r_wr_full, r_wr_almost_full, r_rd_empty, r_rd_almost_empty;
%000000     logic [AW:0]   w_count;
%000000     logic [AW:0]   w_available_data;  // Calculate available data independently
        
            // ---------------------------------------------------------------------
            // Write/Read enables
            // ---------------------------------------------------------------------
%000000     logic w_write, w_read;
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
        
            // Debug: Monitor FIFO writes
 003680     always_ff @(posedge axi_aclk) begin
 000056         if (axi_aresetn && w_write && !r_wr_full) begin
                    /* verilator lint_off WIDTHEXPAND */
 000056             $display("DRAIN_CTRL @ %t: data written, wr_ptr: %0d -> %0d, data_available will be %0d",
 000056                     $time, r_wr_ptr_bin, w_wr_ptr_bin_next,
 000056                     w_wr_ptr_bin_next - r_rd_ptr_bin);
                    /* verilator lint_on WIDTHEXPAND */
                end
            end
        
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
%000000     )
        
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
        
        endmodule : stream_drain_ctrl
        
