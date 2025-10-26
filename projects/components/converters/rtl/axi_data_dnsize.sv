// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 RTL Design Sherpa
//
// Module: axi_data_dnsize
// Purpose: Generic Data Width Downsize (Wide→Narrow Splitter)
//
// Description:
//   Splits a single wide beat into WIDTH_RATIO narrow beats.
//   Generic module used by both write and read converters:
//   - Write Converter DOWNSIZE: W channel (wide slave → narrow master)
//   - Read Converter UPSIZE: R channel (wide master → narrow slave)
//
//   Key Features:
//   - Splits wide beat into narrow beat sequence
//   - Configurable sideband handling (broadcast or slice)
//   - Optional burst tracking for correct LAST generation
//   - Back-pressure aware (valid/ready handshaking)
//
// Parameters:
//   WIDE_WIDTH: Input data width (64, 128, 256, 512)
//   NARROW_WIDTH: Output data width (32, 64, 128, 256)
//   WIDE_SB_WIDTH: Wide sideband width (0=none, N for RRESP, N for WSTRB)
//   NARROW_SB_WIDTH: Narrow sideband width
//   SB_BROADCAST: 1=broadcast same value to all (RRESP), 0=slice (WSTRB)
//   TRACK_BURSTS: 1=track burst for LAST (read upsize), 0=simple (write dnsize)
//   BURST_LEN_WIDTH: Burst length counter width (8 for AXI4)
//
// Usage Examples:
//   Write DOWNSIZE (128→32):
//     WIDE_WIDTH=128, NARROW_WIDTH=32, SB_BROADCAST=0, TRACK_BURSTS=0
//   Read UPSIZE (128→32):
//     WIDE_WIDTH=128, NARROW_WIDTH=32, SB_BROADCAST=1, TRACK_BURSTS=1
//
// Author: RTL Design Sherpa
// Created: 2025-10-24

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_data_dnsize #(
    // Width Configuration
    parameter int WIDE_WIDTH        = 128,
    parameter int NARROW_WIDTH      = 32,
    parameter int WIDE_SB_WIDTH     = 0,        // Sideband width (0 if unused)
    parameter int NARROW_SB_WIDTH   = 0,
    parameter int SB_BROADCAST      = 1,        // 1=broadcast, 0=slice
    parameter int TRACK_BURSTS      = 0,        // 1=track bursts for LAST
    parameter int BURST_LEN_WIDTH   = 8,        // Burst length counter width
    parameter int DUAL_BUFFER       = 0,        // 1=dual buffer (100% throughput, 2x area), 0=single buffer (80% throughput)

    // Calculated Parameters
    localparam int WIDTH_RATIO = WIDE_WIDTH / NARROW_WIDTH,
    localparam int PTR_WIDTH   = $clog2(WIDTH_RATIO),
    // Ensure sideband widths are at least 1 for port declarations
    localparam int WIDE_SB_PORT_WIDTH = (WIDE_SB_WIDTH > 0) ? WIDE_SB_WIDTH : 1,
    localparam int NARROW_SB_PORT_WIDTH = (NARROW_SB_WIDTH > 0) ? NARROW_SB_WIDTH : 1
) (
    input  logic                            aclk,
    input  logic                            aresetn,

    // Burst Control (only if TRACK_BURSTS=1)
    input  logic [BURST_LEN_WIDTH-1:0]      burst_len,       // From address channel (ARLEN/AWLEN)
    input  logic                            burst_start,     // Pulse to start new burst

    // Wide Input (from slave or master)
    input  logic                            wide_valid,
    output logic                            wide_ready,
    input  logic [WIDE_WIDTH-1:0]           wide_data,
    input  logic [WIDE_SB_PORT_WIDTH-1:0]   wide_sideband,  // Min width 1 to avoid [-1:0]
    input  logic                            wide_last,

    // Narrow Output (to master or slave)
    output logic                            narrow_valid,
    input  logic                            narrow_ready,
    output logic [NARROW_WIDTH-1:0]         narrow_data,
    output logic [NARROW_SB_PORT_WIDTH-1:0] narrow_sideband,  // Min width 1 to avoid [-1:0]
    output logic                            narrow_last
);

    //==========================================================================
    // Parameter Validation
    //==========================================================================

    initial begin
        if (NARROW_WIDTH >= WIDE_WIDTH)
            $error("NARROW_WIDTH (%0d) must be < WIDE_WIDTH (%0d)", NARROW_WIDTH, WIDE_WIDTH);
        if (WIDE_WIDTH % NARROW_WIDTH != 0)
            $error("WIDE_WIDTH (%0d) must be integer multiple of NARROW_WIDTH (%0d)", WIDE_WIDTH, NARROW_WIDTH);
        if (WIDTH_RATIO < 2)
            $error("WIDTH_RATIO must be >= 2");

        $display("======================================");
        $display("AXI Data Dnsize (Splitter)");
        $display("Wide Width: %0d bits", WIDE_WIDTH);
        $display("Narrow Width: %0d bits", NARROW_WIDTH);
        $display("Width Ratio: %0d", WIDTH_RATIO);
        $display("Sideband Mode: %s", (SB_BROADCAST != 0) ? "BROADCAST" : "SLICE");
        $display("Burst Tracking: %s", (TRACK_BURSTS != 0) ? "ENABLED" : "DISABLED");
        $display("Buffer Mode: %s", (DUAL_BUFFER != 0) ? "DUAL (100%% throughput)" : "SINGLE (80%% throughput)");
        $display("======================================");
    end

    //==========================================================================
    // Internal Registers
    //==========================================================================

    // Beat pointer (shared by both modes)
    logic [PTR_WIDTH-1:0] r_beat_ptr;

    // Burst tracking (if enabled, shared by both modes)
    logic [BURST_LEN_WIDTH-1:0] r_slave_beat_count;
    logic [BURST_LEN_WIDTH-1:0] r_slave_total_beats;
    logic                       r_burst_active;

    // Single-buffer mode registers
    generate
        if (DUAL_BUFFER == 0) begin : gen_single_buffer
            logic [WIDE_WIDTH-1:0]          r_data_buffer;
            logic [WIDE_SB_PORT_WIDTH-1:0]  r_sideband_buffer;
            logic                           r_wide_buffered;
            logic                           r_last_buffered;
        end else begin : gen_dual_buffer
            // Dual-buffer mode registers
            logic [WIDE_WIDTH-1:0]          r_buffer_0;
            logic [WIDE_WIDTH-1:0]          r_buffer_1;
            logic [WIDE_SB_PORT_WIDTH-1:0]  r_sb_buffer_0;
            logic [WIDE_SB_PORT_WIDTH-1:0]  r_sb_buffer_1;
            logic                           r_last_buffer_0;
            logic                           r_last_buffer_1;
            logic                           r_buffer_0_valid;
            logic                           r_buffer_1_valid;
            logic                           r_read_buffer;  // 0=reading buf0, 1=reading buf1
        end
    endgenerate

    //==========================================================================
    // Splitter State Machine
    //==========================================================================

    generate
        if (DUAL_BUFFER == 0) begin : gen_single_buffer_sm
            // SINGLE-BUFFER MODE: Original implementation
            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    gen_single_buffer.r_data_buffer <= '0;
                    r_beat_ptr <= '0;
                    gen_single_buffer.r_wide_buffered <= 1'b0;
                    gen_single_buffer.r_last_buffered <= 1'b0;

                    if (TRACK_BURSTS != 0) begin
                        r_slave_beat_count <= '0;
                        r_slave_total_beats <= '0;
                        r_burst_active <= 1'b0;
                    end
                end else begin
                    // Burst tracking logic
                    if (TRACK_BURSTS != 0 && burst_start && !r_burst_active) begin
                        r_slave_total_beats <= burst_len + 1'b1;
                        r_slave_beat_count <= '0;
                        r_burst_active <= 1'b1;
                    end

                    // Accept wide beat
                    if (wide_valid && wide_ready && !gen_single_buffer.r_wide_buffered) begin
                        gen_single_buffer.r_data_buffer <= wide_data;
                        gen_single_buffer.r_last_buffered <= wide_last;
                        gen_single_buffer.r_wide_buffered <= 1'b1;
                        r_beat_ptr <= '0;
                    end

                    // Send narrow beat
                    if (gen_single_buffer.r_wide_buffered && narrow_ready) begin
                        if (TRACK_BURSTS != 0 && r_burst_active) begin
                            // With burst tracking
                            if ((r_slave_beat_count + 1'b1) >= r_slave_total_beats) begin
                                gen_single_buffer.r_wide_buffered <= 1'b0;
                                r_beat_ptr <= '0;
                                r_slave_beat_count <= '0;
                                r_burst_active <= 1'b0;
                            end else if (r_beat_ptr == PTR_WIDTH'(WIDTH_RATIO-1)) begin
                                gen_single_buffer.r_wide_buffered <= 1'b0;
                                r_beat_ptr <= '0;
                                r_slave_beat_count <= r_slave_beat_count + 1'b1;
                            end else begin
                                r_beat_ptr <= r_beat_ptr + 1'b1;
                                r_slave_beat_count <= r_slave_beat_count + 1'b1;
                            end
                        end else begin
                            // Simple mode (no burst tracking)
                            if (r_beat_ptr == PTR_WIDTH'(WIDTH_RATIO-1)) begin
                                gen_single_buffer.r_wide_buffered <= 1'b0;
                                r_beat_ptr <= '0;
                            end else begin
                                r_beat_ptr <= r_beat_ptr + 1'b1;
                            end
                        end
                    end
                end
            )
        end else begin : gen_dual_buffer_sm
            // DUAL-BUFFER MODE: Enhanced throughput implementation
            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    gen_dual_buffer.r_buffer_0 <= '0;
                    gen_dual_buffer.r_buffer_1 <= '0;
                    gen_dual_buffer.r_last_buffer_0 <= 1'b0;
                    gen_dual_buffer.r_last_buffer_1 <= 1'b0;
                    gen_dual_buffer.r_buffer_0_valid <= 1'b0;
                    gen_dual_buffer.r_buffer_1_valid <= 1'b0;
                    gen_dual_buffer.r_read_buffer <= 1'b0;
                    r_beat_ptr <= '0;

                    if (TRACK_BURSTS != 0) begin
                        r_slave_beat_count <= '0;
                        r_slave_total_beats <= '0;
                        r_burst_active <= 1'b0;
                    end
                end else begin
                    // Burst tracking logic
                    if (TRACK_BURSTS != 0 && burst_start && !r_burst_active) begin
                        r_slave_total_beats <= burst_len + 1'b1;
                        r_slave_beat_count <= '0;
                        r_burst_active <= 1'b1;
                    end

                    // WRITE PATH: Accept wide beat into empty buffer
                    if (wide_valid && wide_ready) begin
                        if (!gen_dual_buffer.r_buffer_0_valid) begin
                            // Write to buffer 0
                            gen_dual_buffer.r_buffer_0 <= wide_data;
                            gen_dual_buffer.r_last_buffer_0 <= wide_last;
                            gen_dual_buffer.r_buffer_0_valid <= 1'b1;
                        end else begin
                            // Write to buffer 1 (must be empty if wide_ready=1)
                            gen_dual_buffer.r_buffer_1 <= wide_data;
                            gen_dual_buffer.r_last_buffer_1 <= wide_last;
                            gen_dual_buffer.r_buffer_1_valid <= 1'b1;
                        end
                    end

                    // READ PATH: Send narrow beats from current buffer
                    if ((gen_dual_buffer.r_read_buffer ? gen_dual_buffer.r_buffer_1_valid : gen_dual_buffer.r_buffer_0_valid) && narrow_ready) begin
                        // Check if this is the last narrow beat from current wide beat
                        // Check if this is the last beat of entire burst

                        if (TRACK_BURSTS != 0 && r_burst_active) begin
                            // Burst tracking mode
                            if (((r_slave_beat_count + 1'b1) >= r_slave_total_beats)) begin
                                // Last narrow beat of entire burst - clear current buffer
                                if (gen_dual_buffer.r_read_buffer) begin
                                    gen_dual_buffer.r_buffer_1_valid <= 1'b0;
                                end else begin
                                    gen_dual_buffer.r_buffer_0_valid <= 1'b0;
                                end
                                r_beat_ptr <= '0;
                                r_slave_beat_count <= '0;
                                r_burst_active <= 1'b0;

                                // Swap to other buffer if it has data
                                if (gen_dual_buffer.r_read_buffer ? gen_dual_buffer.r_buffer_0_valid :
                                    gen_dual_buffer.r_buffer_1_valid) begin
                                    gen_dual_buffer.r_read_buffer <= ~gen_dual_buffer.r_read_buffer;
                                end
                            end else if (r_beat_ptr == PTR_WIDTH'(WIDTH_RATIO-1)) begin
                                // Last narrow beat from this wide beat, but more beats in burst
                                if (gen_dual_buffer.r_read_buffer) begin
                                    gen_dual_buffer.r_buffer_1_valid <= 1'b0;
                                end else begin
                                    gen_dual_buffer.r_buffer_0_valid <= 1'b0;
                                end
                                r_beat_ptr <= '0;
                                r_slave_beat_count <= r_slave_beat_count + 1'b1;

                                // Swap to other buffer if it has data
                                if (gen_dual_buffer.r_read_buffer ? gen_dual_buffer.r_buffer_0_valid :
                                    gen_dual_buffer.r_buffer_1_valid) begin
                                    gen_dual_buffer.r_read_buffer <= ~gen_dual_buffer.r_read_buffer;
                                end
                            end else begin
                                // More narrow beats from this wide beat
                                r_beat_ptr <= r_beat_ptr + 1'b1;
                                r_slave_beat_count <= r_slave_beat_count + 1'b1;
                            end
                        end else begin
                            // Simple mode (no burst tracking)
                            if (r_beat_ptr == PTR_WIDTH'(WIDTH_RATIO-1)) begin
                                // Last narrow beat - clear current buffer
                                if (gen_dual_buffer.r_read_buffer) begin
                                    gen_dual_buffer.r_buffer_1_valid <= 1'b0;
                                end else begin
                                    gen_dual_buffer.r_buffer_0_valid <= 1'b0;
                                end
                                r_beat_ptr <= '0;

                                // Swap to other buffer if it has data
                                if (gen_dual_buffer.r_read_buffer ? gen_dual_buffer.r_buffer_0_valid :
                                    gen_dual_buffer.r_buffer_1_valid) begin
                                    gen_dual_buffer.r_read_buffer <= ~gen_dual_buffer.r_read_buffer;
                                end
                            end else begin
                                // More narrow beats from this wide beat
                                r_beat_ptr <= r_beat_ptr + 1'b1;
                            end
                        end
                    end
                end
            )
        end
    endgenerate

    //==========================================================================
    // Sideband Buffer Logic (only if sideband is used)
    //==========================================================================

    generate
        if (WIDE_SB_WIDTH > 0) begin : gen_sideband_buffer_logic
            if (DUAL_BUFFER == 0) begin : gen_single_sb
                // Single-buffer sideband logic
                always_ff @(posedge aclk or negedge aresetn) begin
                    if (!aresetn) begin
                        gen_single_buffer.r_sideband_buffer <= '0;
                    end else begin
                        if (wide_valid && wide_ready && !gen_single_buffer.r_wide_buffered) begin
                            gen_single_buffer.r_sideband_buffer <= wide_sideband;
                        end
                    end
                end
            end else begin : gen_dual_sb
                // Dual-buffer sideband logic
                always_ff @(posedge aclk or negedge aresetn) begin
                    if (!aresetn) begin
                        gen_dual_buffer.r_sb_buffer_0 <= '0;
                        gen_dual_buffer.r_sb_buffer_1 <= '0;
                    end else begin
                        // Write sideband to same buffer as data
                        if (wide_valid && wide_ready) begin
                            if (!gen_dual_buffer.r_buffer_0_valid) begin
                                gen_dual_buffer.r_sb_buffer_0 <= wide_sideband;
                            end else begin
                                gen_dual_buffer.r_sb_buffer_1 <= wide_sideband;
                            end
                        end
                    end
                end
            end
        end
    endgenerate

    //==========================================================================
    // Output Assignments
    //==========================================================================

    // Common signal for last narrow beat detection
    logic w_last_narrow_beat;
    assign w_last_narrow_beat = (r_beat_ptr == PTR_WIDTH'(WIDTH_RATIO-1));

    generate
        if (DUAL_BUFFER == 0) begin : gen_single_buffer_outputs
            // SINGLE-BUFFER MODE OUTPUTS

            // Extract narrow data slice from wide buffer
            assign narrow_data = gen_single_buffer.r_data_buffer[r_beat_ptr*NARROW_WIDTH +: NARROW_WIDTH];

            // Handle sideband signal extraction
            if (NARROW_SB_WIDTH > 0) begin : gen_sideband
                if (SB_BROADCAST != 0) begin : gen_broadcast
                    // Broadcast mode: all narrow beats get same sideband value (RRESP)
                    assign narrow_sideband = gen_single_buffer.r_sideband_buffer[NARROW_SB_WIDTH-1:0];
                end else begin : gen_slice
                    // Slice mode: extract appropriate slice of sideband (WSTRB)
                    assign narrow_sideband = gen_single_buffer.r_sideband_buffer[r_beat_ptr*NARROW_SB_WIDTH +: NARROW_SB_WIDTH];
                end
            end else begin : gen_no_sideband
                assign narrow_sideband = '0;
            end

            // Generate LAST signal
            if (TRACK_BURSTS != 0) begin : gen_tracked_last
                // With burst tracking: LAST on final beat of entire burst
                assign narrow_last = gen_single_buffer.r_wide_buffered && r_burst_active &&
                                     (r_slave_beat_count + 1'b1 >= r_slave_total_beats);
            end else begin : gen_simple_last
                // Simple mode: LAST when we finish splitting the wide beat AND wide_last was set
                assign narrow_last = gen_single_buffer.r_wide_buffered && gen_single_buffer.r_last_buffered && w_last_narrow_beat;
            end

            // Narrow side valid when buffer has data
            assign narrow_valid = gen_single_buffer.r_wide_buffered;

            // Wide side ready when buffer empty OR sending last narrow beat
            assign wide_ready = !gen_single_buffer.r_wide_buffered || (narrow_ready && w_last_narrow_beat);

        end else begin : gen_dual_buffer_outputs
            // DUAL-BUFFER MODE OUTPUTS

            // Select current buffer based on read pointer
            logic [WIDE_WIDTH-1:0] current_buffer_data;
            logic [WIDE_SB_PORT_WIDTH-1:0] current_buffer_sideband;
            logic current_buffer_last;
            logic current_buffer_valid;

            assign current_buffer_data = gen_dual_buffer.r_read_buffer ?
                gen_dual_buffer.r_buffer_1 : gen_dual_buffer.r_buffer_0;
            assign current_buffer_sideband = gen_dual_buffer.r_read_buffer ?
                gen_dual_buffer.r_sb_buffer_1 : gen_dual_buffer.r_sb_buffer_0;
            assign current_buffer_last = gen_dual_buffer.r_read_buffer ?
                gen_dual_buffer.r_last_buffer_1 : gen_dual_buffer.r_last_buffer_0;
            assign current_buffer_valid = gen_dual_buffer.r_read_buffer ?
                gen_dual_buffer.r_buffer_1_valid : gen_dual_buffer.r_buffer_0_valid;

            // Extract narrow data slice from current buffer
            assign narrow_data = current_buffer_data[r_beat_ptr*NARROW_WIDTH +: NARROW_WIDTH];

            // Handle sideband signal extraction
            if (NARROW_SB_WIDTH > 0) begin : gen_sideband
                if (SB_BROADCAST != 0) begin : gen_broadcast
                    // Broadcast mode
                    assign narrow_sideband = current_buffer_sideband[NARROW_SB_WIDTH-1:0];
                end else begin : gen_slice
                    // Slice mode
                    assign narrow_sideband = current_buffer_sideband[r_beat_ptr*NARROW_SB_WIDTH +: NARROW_SB_WIDTH];
                end
            end else begin : gen_no_sideband
                assign narrow_sideband = '0;
            end

            // Generate LAST signal
            if (TRACK_BURSTS != 0) begin : gen_tracked_last
                // With burst tracking: LAST on final beat of entire burst
                assign narrow_last = current_buffer_valid && r_burst_active &&
                                     (r_slave_beat_count + 1'b1 >= r_slave_total_beats);
            end else begin : gen_simple_last
                // Simple mode: LAST when we finish splitting AND wide_last was set
                assign narrow_last = current_buffer_valid && current_buffer_last && w_last_narrow_beat;
            end

            // Narrow side valid when current buffer has data
            assign narrow_valid = current_buffer_valid;

            // Wide side ready when at least one buffer is empty
            assign wide_ready = !gen_dual_buffer.r_buffer_0_valid || !gen_dual_buffer.r_buffer_1_valid;

        end
    endgenerate

    //==========================================================================
    // Assertions (for simulation)
    //==========================================================================

`ifdef SIMULATION
    // Check for protocol violations
    always @(posedge aclk) begin
        if (aresetn) begin
            // Valid must not drop without ready
            if ($past(wide_valid) && !$past(wide_ready) && !wide_valid) begin
                $error("ERROR: wide_valid dropped before wide_ready asserted");
            end
        end
    end

    // Check for pointer overflow
    always @(posedge aclk) begin
        if (aresetn && r_wide_buffered && narrow_ready) begin
            if (r_beat_ptr >= PTR_WIDTH'(WIDTH_RATIO)) begin
                $error("ERROR: Splitter pointer overflow (ptr=%0d, ratio=%0d)", r_beat_ptr, WIDTH_RATIO);
            end
        end
    end

    // Check burst tracking consistency (if enabled)
    generate
        if (TRACK_BURSTS) begin : gen_burst_assertions
            always @(posedge aclk) begin
                if (aresetn && r_burst_active) begin
                    if (r_slave_beat_count > r_slave_total_beats) begin
                        $error("ERROR: Beat count (%0d) exceeded total beats (%0d)",
                               r_slave_beat_count, r_slave_total_beats);
                    end
                end
            end
        end
    endgenerate
`endif

endmodule : axi_data_dnsize
