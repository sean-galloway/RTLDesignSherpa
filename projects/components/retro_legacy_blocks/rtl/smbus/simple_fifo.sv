// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: simple_fifo
// Purpose: Simple FIFO wrapper for SMBus with count output
//
// Wraps the existing fifo_sync module and adds a count tracker
// for the SMBus controller. Simplified interface with count output.

`timescale 1ns / 1ps

`include "reset_defs.svh"
`include "fifo_defs.svh"

module simple_fifo #(
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 32
) (
    input  logic                    clk,
    input  logic                    rst,        // Active-high reset
    
    // Write interface
    input  logic                    wr_en,
    input  logic [DATA_WIDTH-1:0]   wr_data,
    
    // Read interface
    input  logic                    rd_en,
    output logic [DATA_WIDTH-1:0]   rd_data,
    
    // Status
    output logic                    full,
    output logic                    empty,
    output logic [$clog2(DEPTH):0]  count
);

    //========================================================================
    // Local Parameters
    //========================================================================
    localparam int COUNT_WIDTH = $clog2(DEPTH) + 1;
    
    //========================================================================
    // Internal Signals
    //========================================================================
    logic                    w_rst_n;
    logic                    w_wr_full;
    logic                    w_rd_empty;
    logic                    w_wr_almost_full;
    logic                    w_rd_almost_empty;
    
    // Count tracking
    logic [COUNT_WIDTH-1:0]  r_count;
    
    //========================================================================
    // Reset Polarity Conversion
    //========================================================================
    assign w_rst_n = ~rst;
    
    //========================================================================
    // FIFO Instance (Using Project's fifo_sync)
    //========================================================================
    fifo_sync #(
        .MEM_STYLE(FIFO_AUTO),
        .REGISTERED(0),              // Mux mode for lowest latency
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(DEPTH),
        .ALMOST_WR_MARGIN(1),
        .ALMOST_RD_MARGIN(1),
        .INSTANCE_NAME("SMBUS_FIFO")
    ) u_fifo_sync (
        .clk             (clk),
        .rst_n           (w_rst_n),
        .write           (wr_en),
        .wr_data         (wr_data),
        .wr_full         (w_wr_full),
        .wr_almost_full  (w_wr_almost_full),
        .read            (rd_en),
        .rd_data         (rd_data),
        .rd_empty        (w_rd_empty),
        .rd_almost_empty (w_rd_almost_empty)
    );
    
    //========================================================================
    // Count Tracker
    //========================================================================
    // Track number of entries in FIFO
    always_ff @(posedge clk) begin
        if (rst) begin
            r_count <= '0;
        end else begin
            case ({wr_en && !w_wr_full, rd_en && !w_rd_empty})
                2'b10: r_count <= r_count + 1'b1;  // Write only
                2'b01: r_count <= r_count - 1'b1;  // Read only
                default: r_count <= r_count;        // Both or neither
            endcase
        end
    end
    
    //========================================================================
    // Output Assignments
    //========================================================================
    assign full = w_wr_full;
    assign empty = w_rd_empty;
    assign count = r_count;

endmodule
