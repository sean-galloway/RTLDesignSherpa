// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi_data_upsize
// Purpose: Generic Data Width Upsize (Narrow→Wide Accumulator)
//
// Description:
//   Accumulates WIDTH_RATIO narrow beats into a single wide beat.
//   Generic module used by both write and read converters:
//   - Write Converter UPSIZE: W channel (narrow slave → wide master)
//   - Read Converter DOWNSIZE: R channel (narrow master → wide slave)
//
//   Key Features:
//   - Accumulates narrow beats into wide beat buffer
//   - Configurable sideband handling (concatenate or OR together)
//   - Completes on counter reaching ratio OR narrow_last
//   - Back-pressure aware (valid/ready handshaking)
//
// Parameters:
//   NARROW_WIDTH: Input data width (32, 64, 128, 256)
//   WIDE_WIDTH: Output data width (64, 128, 256, 512)
//   NARROW_SB_WIDTH: Narrow sideband width (0=none, N/8 for WSTRB, 2 for RRESP)
//   WIDE_SB_WIDTH: Wide sideband width (calculated or explicit)
//   SB_OR_MODE: 0=concatenate sideband (WSTRB), 1=OR together (RRESP)
//
// Usage Examples:
//   Write UPSIZE (32→128):
//     NARROW_WIDTH=32, WIDE_WIDTH=128, NARROW_SB_WIDTH=4, WIDE_SB_WIDTH=16, SB_OR_MODE=0
//   Read DOWNSIZE (128→32):
//     NARROW_WIDTH=128, WIDE_WIDTH=512, NARROW_SB_WIDTH=2, WIDE_SB_WIDTH=2, SB_OR_MODE=1
//
// Author: RTL Design Sherpa
// Created: 2025-10-24

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_data_upsize #(
    // Width Configuration
    parameter int NARROW_WIDTH    = 32,
    parameter int WIDE_WIDTH      = 128,
    parameter int NARROW_SB_WIDTH = 0,        // Sideband width (0 if unused)
    parameter int WIDE_SB_WIDTH   = 0,        // Wide sideband width
    parameter int SB_OR_MODE      = 0,        // 0=concatenate, 1=OR together

    // Calculated Parameters
    localparam int WIDTH_RATIO = WIDE_WIDTH / NARROW_WIDTH,
    localparam int PTR_WIDTH   = $clog2(WIDTH_RATIO),
    // Ensure sideband widths are at least 1 for port declarations (unused if actual width is 0)
    localparam int NARROW_SB_PORT_WIDTH = (NARROW_SB_WIDTH > 0) ? NARROW_SB_WIDTH : 1,
    localparam int WIDE_SB_PORT_WIDTH = (WIDE_SB_WIDTH > 0) ? WIDE_SB_WIDTH : 1
) (
    input  logic                            aclk,
    input  logic                            aresetn,

    // Narrow Input (from slave or master)
    input  logic                            narrow_valid,
    output logic                            narrow_ready,
    input  logic [NARROW_WIDTH-1:0]         narrow_data,
    input  logic [NARROW_SB_PORT_WIDTH-1:0] narrow_sideband,  // Min width 1 to avoid [-1:0]
    input  logic                            narrow_last,

    // Wide Output (to master or slave)
    output logic                            wide_valid,
    input  logic                            wide_ready,
    output logic [WIDE_WIDTH-1:0]           wide_data,
    output logic [WIDE_SB_PORT_WIDTH-1:0]   wide_sideband,  // Min width 1 to avoid [-1:0]
    output logic                            wide_last
);

    //==========================================================================
    // Parameter Validation
    //==========================================================================

    initial begin
        if (WIDE_WIDTH <= NARROW_WIDTH)
            $error("WIDE_WIDTH (%0d) must be > NARROW_WIDTH (%0d)", WIDE_WIDTH, NARROW_WIDTH);
        if (WIDE_WIDTH % NARROW_WIDTH != 0)
            $error("WIDE_WIDTH (%0d) must be integer multiple of NARROW_WIDTH (%0d)", WIDE_WIDTH, NARROW_WIDTH);
        if (WIDTH_RATIO < 2)
            $error("WIDTH_RATIO must be >= 2");

        $display("======================================");
        $display("AXI Data Upsize (Accumulator)");
        $display("Narrow Width: %0d bits", NARROW_WIDTH);
        $display("Wide Width: %0d bits", WIDE_WIDTH);
        $display("Width Ratio: %0d", WIDTH_RATIO);
        $display("Sideband Mode: %s", (SB_OR_MODE != 0) ? "OR" : "CONCATENATE");
        $display("======================================");
    end

    //==========================================================================
    // Internal Registers
    //==========================================================================

    // Accumulator buffer
    logic [WIDE_WIDTH-1:0]          r_data_accumulator;
    logic [WIDE_SB_PORT_WIDTH-1:0]  r_sideband_accumulator;  // Use port width (min 1)
    logic [PTR_WIDTH-1:0]           r_beat_ptr;
    logic                           r_wide_valid;
    logic                           r_last_buffered;

    //==========================================================================
    // Accumulator State Machine
    //==========================================================================

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_data_accumulator <= '0;
            // r_sideband_accumulator reset handled in generate block
            r_beat_ptr <= '0;
            r_wide_valid <= 1'b0;
            r_last_buffered <= 1'b0;
        end else begin
            // Accept narrow beat
            if (narrow_valid && narrow_ready) begin
                // Accumulate data into wide buffer
                r_data_accumulator[r_beat_ptr*NARROW_WIDTH +: NARROW_WIDTH] <= narrow_data;

                // Check if accumulation complete
                if (r_beat_ptr == PTR_WIDTH'(WIDTH_RATIO-1) || narrow_last) begin
                    // Buffer full or early termination (narrow_last)
                    r_wide_valid <= 1'b1;
                    r_beat_ptr <= '0;
                    r_last_buffered <= narrow_last;
                end else begin
                    // More narrow beats needed
                    r_beat_ptr <= r_beat_ptr + 1'b1;
                end
            end

            // Wide side accepts accumulated beat
            if (r_wide_valid && wide_ready) begin
                r_wide_valid <= 1'b0;
                r_last_buffered <= 1'b0;
            end
        end
    )

    //==========================================================================
    // Sideband Accumulation Logic (only if sideband is used)
    //==========================================================================

    generate
        if (NARROW_SB_WIDTH > 0) begin : gen_sideband_accumulation
            if (SB_OR_MODE != 0) begin : gen_or_mode
                // OR mode: for RRESP error propagation
                always_ff @(posedge aclk or negedge aresetn) begin
                    if (!aresetn) begin
                        r_sideband_accumulator <= '0;
                    end else begin
                        if (narrow_valid && narrow_ready) begin
                            if (r_beat_ptr == '0) begin
                                r_sideband_accumulator <= WIDE_SB_PORT_WIDTH'(narrow_sideband);
                            end else begin
                                r_sideband_accumulator <= r_sideband_accumulator | WIDE_SB_PORT_WIDTH'(narrow_sideband);
                            end
                        end
                    end
                end
            end else begin : gen_concat_mode
                // Concatenate mode: for WSTRB accumulation
                always_ff @(posedge aclk or negedge aresetn) begin
                    if (!aresetn) begin
                        r_sideband_accumulator <= '0;
                    end else begin
                        if (narrow_valid && narrow_ready) begin
                            r_sideband_accumulator[r_beat_ptr*NARROW_SB_WIDTH +: NARROW_SB_WIDTH] <= narrow_sideband[NARROW_SB_WIDTH-1:0];
                        end
                    end
                end
            end
        end
    endgenerate

    //==========================================================================
    // Output Assignments
    //==========================================================================

    // Narrow side ready when not accumulating or wide side is ready
    assign narrow_ready = !r_wide_valid || wide_ready;

    // Wide side outputs
    assign wide_valid = r_wide_valid;
    assign wide_data = r_data_accumulator;
    assign wide_sideband = r_sideband_accumulator;
    assign wide_last = r_last_buffered && r_wide_valid;

    //==========================================================================
    // Assertions (for simulation)
    //==========================================================================

`ifdef SIMULATION
    // Check for protocol violations
    always @(posedge aclk) begin
        if (aresetn) begin
            // Valid must not drop without ready
            if ($past(narrow_valid) && !$past(narrow_ready) && !narrow_valid) begin
                $error("ERROR: narrow_valid dropped before narrow_ready asserted");
            end
        end
    end

    // Check for accumulator overflow (should never happen with correct protocol)
    always @(posedge aclk) begin
        if (aresetn && narrow_valid && narrow_ready) begin
            if (r_beat_ptr >= PTR_WIDTH'(WIDTH_RATIO)) begin
                $error("ERROR: Accumulator pointer overflow (ptr=%0d, ratio=%0d)", r_beat_ptr, WIDTH_RATIO);
            end
        end
    end
`endif

endmodule : axi_data_upsize
