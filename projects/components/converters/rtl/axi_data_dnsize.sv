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
    // Lane of the burst's FIRST narrow beat inside the first wide word
    // (addr % wide_bytes / narrow_bytes). Sampled on the burst's first
    // wide beat; later wide beats slice from lane 0. Tie '0 for the
    // historical aligned-only behavior. TRACK_BURSTS=1 only.
    input  logic [PTR_WIDTH-1:0]            start_lane,

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
    // The next wide beat accepted is the FIRST of its burst -- its slice
    // pointer starts at start_lane instead of 0 (mid-word burst start).
    logic                       r_first_wide_of_burst;
    logic                       w_burst_opening;
    assign w_burst_opening = (TRACK_BURSTS != 0) && burst_start && !r_burst_active;

    // Single-buffer mode registers
    generate
        begin : gen_single_buffer
            logic [WIDE_WIDTH-1:0]          r_data_buffer;
            logic [WIDE_SB_PORT_WIDTH-1:0]  r_sideband_buffer;
            logic                           r_wide_buffered;
            logic                           r_last_buffered;
        end
    endgenerate

    //==========================================================================
    // Splitter State Machine
    //==========================================================================

    generate
        begin : gen_single_buffer_sm
            // SINGLE-BUFFER MODE
            //
            // Send/accept ordering note:
            //   `wide_ready` (combinational, defined below) asserts in two
            //   cases: buffer empty, OR we're on the last-narrow-beat
            //   cycle that frees the buffer this cycle. The latter
            //   enables back-to-back wide beats with no bubble.
            //
            //   For the atomic-replace case to work, the accept FF must
            //   fire even when `r_wide_buffered=1` at the start of the
            //   cycle (since the same cycle's send branch is clearing
            //   it). We rely on SystemVerilog's "last NBA wins"
            //   semantics within a single always_ff: the accept block
            //   is textually AFTER the send block, so its
            //   `r_wide_buffered <= 1'b1` overrides any `<= 1'b0` from
            //   the send branch.
            //
            //   The previous implementation gated accept on
            //   `!r_wide_buffered`, which silently dropped back-to-back
            //   wide beats — the producer saw wide_ready=1 and
            //   handshaked, but the FF didn't capture the data.
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
                        r_first_wide_of_burst <= 1'b0;
                    end
                end else begin
                    // Burst tracking logic
                    if (w_burst_opening) begin
                        r_slave_total_beats <= burst_len + 1'b1;
                        r_slave_beat_count <= '0;
                        r_burst_active <= 1'b1;
                        r_first_wide_of_burst <= 1'b1;
                    end

                    // Send narrow beat (may clear r_wide_buffered)
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

                    // Accept wide beat (textually after send so its NBA to
                    // r_wide_buffered/r_beat_ptr takes priority on the
                    // atomic-replace cycle). wide_ready already encodes
                    // when accept is safe (see wide_ready assign below).
                    if (wide_valid && wide_ready) begin
                        gen_single_buffer.r_data_buffer <= wide_data;
                        gen_single_buffer.r_last_buffered <= wide_last;
                        gen_single_buffer.r_wide_buffered <= 1'b1;
                        // The burst's first wide word is sliced from
                        // start_lane (mid-word burst start); every later
                        // wide word from lane 0. w_burst_opening covers
                        // the burst-start-and-first-wide-same-cycle case
                        // (this NBA is textually after the opening branch,
                        // so the flag clear wins -- the lane is consumed).
                        if (TRACK_BURSTS != 0 &&
                            (r_first_wide_of_burst || w_burst_opening)) begin
                            r_beat_ptr <= start_lane;
                            r_first_wide_of_burst <= 1'b0;
                        end else begin
                            r_beat_ptr <= '0;
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
            begin : gen_single_sb
                // Single-buffer sideband logic — same accept criterion
                // as the data-path FF above (drops the !r_wide_buffered
                // predicate so back-to-back atomic-replace captures the
                // new wide beat's sideband too).
                always_ff @(posedge aclk or negedge aresetn) begin
                    if (!aresetn) begin
                        gen_single_buffer.r_sideband_buffer <= '0;
                    end else begin
                        if (wide_valid && wide_ready) begin
                            gen_single_buffer.r_sideband_buffer <= wide_sideband;
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
        begin : gen_single_buffer_outputs
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

            // Wide side ready: buffer empty, OR sending the last narrow
            // beat of the current wide group AND the burst (if tracked)
            // needs another wide beat after this one.
            //
            // The "atomic replace" case lets the producer deliver a new
            // wide beat in the same cycle the last narrow beat goes out,
            // which the FF above handles via NBA last-write-wins. For
            // TRACK_BURSTS=1, exclude end-of-burst — accepting a new wide
            // there would land it in the buffer without burst context
            // (the send branch is also clearing r_burst_active), leaving
            // the new data stranded.
            if (TRACK_BURSTS != 0) begin : gen_wide_ready_tracked
                wire mid_burst_replace = r_burst_active &&
                                         (r_beat_ptr == PTR_WIDTH'(WIDTH_RATIO-1)) &&
                                         ((r_slave_beat_count + 1'b1) < r_slave_total_beats);
                assign wide_ready = !gen_single_buffer.r_wide_buffered ||
                                    (narrow_ready && mid_burst_replace);
            end else begin : gen_wide_ready_simple
                assign wide_ready = !gen_single_buffer.r_wide_buffered ||
                                    (narrow_ready && w_last_narrow_beat);
            end

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
        if (aresetn && gen_single_buffer.r_wide_buffered && narrow_ready) begin
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
