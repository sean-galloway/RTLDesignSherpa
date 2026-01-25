//      // verilator_coverage annotation
        // SPDX-License-Identifier: MIT
        // SPDX-FileCopyrightText: 2024-2025 sean galloway
        //
        // RTL Design Sherpa - Industry-Standard RTL Design and Verification
        // https://github.com/sean-galloway/RTLDesignSherpa
        //
        // Module: perf_profiler
        // Purpose: Performance profiling for STREAM channels
        //
        // Description:
        //   Captures timing information for channel activity to enable performance
        //   analysis and bottleneck identification. Supports two profiling modes:
        //
        //   Mode 0 (TIMESTAMP_MODE): Captures timestamps on idle signal edges
        //     - Records timestamp when channel transitions idle → active (start)
        //     - Records timestamp when channel transitions active → idle (end)
        //     - Software calculates elapsed time from timestamp pairs
        //     - Simpler hardware, more flexible analysis
        //
        //   Mode 1 (ELAPSED_MODE): Captures elapsed time directly
        //     - Measures time from idle deassert to idle assert
        //     - Records elapsed time when channel returns to idle
        //     - Hardware calculates duration, simpler software
        //
        //   Features:
        //     - Per-channel profiling with 32-bit free-running counter
        //     - 256-entry FIFO for buffering performance data
        //     - Configurable profiling mode via APB register
        //     - Channel ID tagging for multi-channel identification
        //     - FIFO status monitoring (empty, full, count)
        //     - Readable via APB configuration space
        //
        // Usage:
        //   1. Enable profiling: cfg_enable = 1, cfg_mode = 0 (timestamp) or 1 (elapsed)
        //   2. Connect channel_idle signals from schedulers
        //   3. Monitor transitions and FIFO fills
        //   4. Read FIFO via two-register sequence:
        //      a. Read PERF_FIFO_DATA_LOW (asserts perf_fifo_rd):
        //         - Returns timestamp or elapsed time [31:0]
        //         - Pops FIFO and latches both registers
        //      b. Read PERF_FIFO_DATA_HIGH:
        //         - Returns {28'b0, event_type, channel_id[2:0]}
        //         - No FIFO pop, reads latched data
        //   5. Parse data:
        //      - timestamp/elapsed = perf_fifo_data_low[31:0]
        //      - channel_id = perf_fifo_data_high[2:0]
        //      - event_type = perf_fifo_data_high[3] (timestamp mode only)
        //                     0 = idle→active (start), 1 = active→idle (end)
        //   6. Software processes FIFO data to analyze performance
        //
        // Integration:
        //   - Add to stream_top alongside schedulers
        //   - Map to two APB registers (PERF_FIFO_DATA_LOW, PERF_FIFO_DATA_HIGH)
        //   - Reading LOW register triggers perf_fifo_rd strobe
        //   - Add cfg registers for enable/mode/clear control
        //
        // Documentation: projects/components/stream/PRD.md
        // Subsystem: stream_fub
        //
        // Author: sean galloway
        // Created: 2025-10-20
        
        `timescale 1ns / 1ps
        
        `include "reset_defs.svh"
        
        module perf_profiler #(
            parameter int NUM_CHANNELS = 8,
            parameter int CHANNEL_WIDTH = $clog2(NUM_CHANNELS),
            parameter int TIMESTAMP_WIDTH = 32,
            parameter int FIFO_DEPTH = 256,
            parameter int FIFO_ADDR_WIDTH = $clog2(FIFO_DEPTH)
        ) (
            // Clock and Reset
 002210     input  logic                        clk,
%000002     input  logic                        rst_n,
        
            // Channel idle signals (from schedulers)
%000002     input  logic [NUM_CHANNELS-1:0]     channel_idle,
        
            // Configuration Interface
%000000     input  logic                        cfg_enable,      // Enable profiling
%000000     input  logic                        cfg_mode,        // 0=timestamp, 1=elapsed
%000000     input  logic                        cfg_clear,       // Clear FIFO and counters
        
            // FIFO Read Interface (to APB/AXI config space)
            // Two-register read sequence:
            //   1. Read PERF_FIFO_DATA_LOW  -> Pops FIFO, latches both registers
            //   2. Read PERF_FIFO_DATA_HIGH -> Returns latched metadata
%000000     input  logic                        perf_fifo_rd,         // Read strobe (single cycle, pops FIFO)
%000000     output logic [31:0]                 perf_fifo_data_low,   // Timestamp or elapsed time [31:0]
%000000     output logic [31:0]                 perf_fifo_data_high,  // {28'b0, event_type, channel_id[2:0]}
%000002     output logic                        perf_fifo_empty,
%000000     output logic                        perf_fifo_full,
%000000     output logic [15:0]                 perf_fifo_count       // Number of entries in FIFO
        );
        
            //=========================================================================
            // Local Parameters
            //=========================================================================
        
            // Profiling modes
            localparam logic MODE_TIMESTAMP = 1'b0;  // Capture timestamps on edges
            localparam logic MODE_ELAPSED   = 1'b1;  // Capture elapsed time
        
            // Event types (for timestamp mode)
            localparam logic EVENT_START = 1'b0;  // idle → active (start of activity)
            localparam logic EVENT_END   = 1'b1;  // active → idle (end of activity)
        
            //=========================================================================
            // Internal Signals
            //=========================================================================
        
            // Free-running timestamp counter
            // Increments every clock cycle when profiling enabled
            // Provides timing reference for all measurements
%000000     logic [TIMESTAMP_WIDTH-1:0] r_timestamp_counter;
        
            // Per-channel idle tracking
            // Registers previous state of idle signals for edge detection
%000002     logic [NUM_CHANNELS-1:0] r_idle_prev;
%000000     logic [NUM_CHANNELS-1:0] w_idle_rising;   // active → idle (channel stops)
%000000     logic [NUM_CHANNELS-1:0] w_idle_falling;  // idle → active (channel starts)
        
            // Per-channel elapsed time tracking (MODE_ELAPSED only)
            // Captures timestamp when channel becomes active
            // Computes elapsed = current_timestamp - start_timestamp when channel becomes idle
%000000     logic [TIMESTAMP_WIDTH-1:0] r_start_time [NUM_CHANNELS];
%000000     logic [NUM_CHANNELS-1:0] r_channel_active;  // Track active state per channel
        
            // FIFO write interface
%000000     logic                       w_fifo_wr;
%000000     logic [35:0]                w_fifo_wr_data;
%000002     logic                       w_fifo_wr_ready_internal;  // FIFO ready to accept writes
%000000     logic                       w_fifo_full_internal;      // Derived from !wr_ready
        
            // FIFO read interface
%000004     logic                       w_fifo_rd_valid_internal;  // FIFO has data available
%000000     logic [35:0]                w_fifo_rd_data;            // Direct FIFO output
%000000     logic [35:0]                r_fifo_data_latched;       // Latched on perf_fifo_rd
%000000     logic [FIFO_ADDR_WIDTH:0]   w_fifo_count_internal;    // FIFO count (9 bits for 256-entry)
        
            // Priority encoder for handling multiple channels changing simultaneously
            // When multiple channels transition on same cycle, process them in priority order
%000000     logic [CHANNEL_WIDTH-1:0]   w_active_channel;
%000004     logic                       w_channel_event;  // Any channel has event to record
        
            // Elapsed time calculation (for MODE_ELAPSED)
%000000     logic [TIMESTAMP_WIDTH-1:0] w_elapsed_time;
        
            //=========================================================================
            // Free-Running Timestamp Counter
            //=========================================================================
            // Provides global timing reference
            // Increments every cycle when profiling enabled
            // Wraps around at 2^32 - 1 (software must handle rollover)
        
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_timestamp_counter <= '0;
                end else if (cfg_clear) begin
                    r_timestamp_counter <= '0;
                end else if (cfg_enable) begin
                    r_timestamp_counter <= r_timestamp_counter + 1'b1;
                end
%000000     )
        
        
            //=========================================================================
            // Edge Detection
            //=========================================================================
            // Detect transitions on channel idle signals
            // Rising edge (active → idle): Channel completes operation, becomes idle
            // Falling edge (idle → active): Channel starts operation
        
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_idle_prev <= '1;  // Initialize to all idle
                end else if (cfg_enable) begin
                    r_idle_prev <= channel_idle;
                end
%000000     )
        
        
            assign w_idle_rising  = channel_idle & ~r_idle_prev;  // 0→1: Active → Idle
            assign w_idle_falling = ~channel_idle & r_idle_prev;  // 1→0: Idle → Active
        
            //=========================================================================
            // Per-Channel Activity Tracking (MODE_ELAPSED)
            //=========================================================================
            // Tracks start time when channel becomes active
            // Computes elapsed time when channel returns to idle
            //
            // Example timeline:
            //   T=100: Channel 0 becomes active (idle falls)
            //          → r_start_time[0] = 100
            //   T=150: Channel 0 returns to idle (idle rises)
            //          → elapsed = 150 - 100 = 50
            //          → Push (elapsed=50, channel=0) to FIFO
        
            genvar ch;
            generate
%000000         for (ch = 0; ch < NUM_CHANNELS; ch++) begin : gen_channel_tracking
                    `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                            r_start_time[ch] <= '0;
                            r_channel_active[ch] <= 1'b0;
                        end else if (cfg_clear) begin
                            r_start_time[ch] <= '0;
                            r_channel_active[ch] <= 1'b0;
                        end else if (cfg_enable && cfg_mode == MODE_ELAPSED) begin
                            // Channel becomes active: Record start time
                            if (w_idle_falling[ch]) begin
                                r_start_time[ch] <= r_timestamp_counter;
                                r_channel_active[ch] <= 1'b1;
                            end
                            // Channel returns to idle: Clear active flag
                            // (Elapsed time computed combinationally and pushed to FIFO)
                            else if (w_idle_rising[ch]) begin
                                r_channel_active[ch] <= 1'b0;
                            end
                        end
%000000             )
        
                end
            endgenerate
        
            //=========================================================================
            // Priority Encoder for Multi-Channel Event Handling
            //=========================================================================
            // When multiple channels have events simultaneously, process one per cycle
            // Priority: Lower channel number = higher priority
            // Remaining events captured in subsequent cycles
            //
            // Example: If channels 0, 3, 5 all transition on same cycle:
            //   Cycle N:   Process channel 0
            //   Cycle N+1: Process channel 3
            //   Cycle N+2: Process channel 5
            //
            // Note: For typical workloads, simultaneous events are rare
        
 006577     always_comb begin
 006577         w_active_channel = '0;
 006577         w_channel_event = 1'b0;
        
                // MODE_TIMESTAMP: Event occurs on either edge (start or end)
%000000         if (cfg_mode == MODE_TIMESTAMP) begin
 004676             for (int i = 0; i < NUM_CHANNELS; i++) begin
%000000                 if (w_idle_rising[i] || w_idle_falling[i]) begin
%000000                     w_active_channel = i[CHANNEL_WIDTH-1:0];
%000000                     w_channel_event = 1'b1;
%000000                     break;  // Priority to lowest channel number
                        end
                    end
                end
                // MODE_ELAPSED: Event occurs on rising edge only (end of activity)
%000000         else begin
%000000             for (int i = 0; i < NUM_CHANNELS; i++) begin
%000000                 if (w_idle_rising[i]) begin
%000000                     w_active_channel = i[CHANNEL_WIDTH-1:0];
%000000                     w_channel_event = 1'b1;
%000000                     break;  // Priority to lowest channel number
                        end
                    end
                end
            end
        
            //=========================================================================
            // FIFO Write Data Generation
            //=========================================================================
            // Package event data into 36-bit FIFO entry:
            //   Bits [31:0]:  Timestamp or elapsed time
            //   Bits [34:32]: Channel ID (0-7 for 8 channels)
            //   Bit  [35]:    Event type (timestamp mode only):
            //                 0 = idle→active (start)
            //                 1 = active→idle (end)
            //
            // MODE_TIMESTAMP: Record timestamp on both edges
            //   - Falling edge: timestamp + channel + EVENT_START
            //   - Rising edge:  timestamp + channel + EVENT_END
            //   - Software calculates: elapsed = timestamp_end - timestamp_start
            //
            // MODE_ELAPSED: Record elapsed time on rising edge only
            //   - Rising edge: elapsed_time + channel + EVENT_END
            //   - elapsed_time = current_timestamp - start_timestamp
            //   - No software calculation needed
        
            // Compute elapsed time for MODE_ELAPSED (combinational)
            assign w_elapsed_time = r_timestamp_counter - r_start_time[w_active_channel];
        
 006577     always_comb begin
 006577         w_fifo_wr = 1'b0;
 006577         w_fifo_wr_data = '0;
        
%000000         if (cfg_enable && w_channel_event && !w_fifo_full_internal) begin
%000000             w_fifo_wr = 1'b1;
        
%000000             if (cfg_mode == MODE_TIMESTAMP) begin
                        // Timestamp mode: Record current timestamp with event type
%000000                 w_fifo_wr_data = {
%000000                     w_idle_rising[w_active_channel] ? EVENT_END : EVENT_START,  // [35]: Event type
%000000                     w_active_channel[2:0],                                       // [34:32]: Channel ID
%000000                     r_timestamp_counter                                          // [31:0]: Timestamp
                        };
%000000             end else begin
                        // Elapsed mode: Record pre-computed elapsed time
%000000                 w_fifo_wr_data = {
%000000                     EVENT_END,                  // [35]: Always end event for elapsed mode
%000000                     w_active_channel[2:0],      // [34:32]: Channel ID
%000000                     w_elapsed_time              // [31:0]: Elapsed time in clock cycles
                        };
                    end
                end
            end
        
            //=========================================================================
            // Performance Data FIFO
            //=========================================================================
            // Buffers performance events for later retrieval via APB
            // Depth: 256 entries (configurable via FIFO_DEPTH parameter)
            // Width: 36 bits (timestamp/elapsed + channel_id + event_type)
            //
            // Software reads FIFO via APB (two-register sequence):
            //   1. Check perf_fifo_empty == 0 (data available)
            //   2. Read PERF_FIFO_DATA_LOW:
            //      - APB slave asserts perf_fifo_rd for one cycle
            //      - FIFO pops and latches 36-bit entry
            //      - Returns timestamp/elapsed [31:0]
            //   3. Read PERF_FIFO_DATA_HIGH:
            //      - Returns latched {28'b0, event_type, channel_id[2:0]}
            //      - No FIFO pop occurs
            //   4. Parse data:
            //      - timestamp/elapsed = PERF_FIFO_DATA_LOW[31:0]
            //      - channel_id = PERF_FIFO_DATA_HIGH[2:0]
            //      - event_type = PERF_FIFO_DATA_HIGH[3] (timestamp mode only)
            //
            // FIFO full handling:
            //   - When full, new events are DROPPED (no backpressure to schedulers)
            //   - Software should poll frequently to prevent loss
            //   - Alternative: Interrupt on FIFO half-full threshold
        
            gaxi_fifo_sync #(
                .DATA_WIDTH(36),
                .DEPTH(FIFO_DEPTH)
            ) u_perf_fifo (
                .axi_aclk      (clk),
                .axi_aresetn   (rst_n && !cfg_clear),  // Clear on cfg_clear
        
                // Write interface (from profiler logic)
                .wr_valid      (w_fifo_wr),
                .wr_data       (w_fifo_wr_data),
                .wr_ready      (w_fifo_wr_ready_internal),  // FIFO ready for write
        
                // Read interface (to APB config space)
                .rd_valid      (w_fifo_rd_valid_internal),  // Data available
                .rd_data       (w_fifo_rd_data),            // 36-bit FIFO output
                .rd_ready      (perf_fifo_rd),              // Pop FIFO on read strobe
        
                // Status
                .count         (w_fifo_count_internal)      // Internal count signal
            );
        
            // Derive empty/full from FIFO interface signals
            assign w_fifo_full_internal = !w_fifo_wr_ready_internal;  // Full when FIFO can't accept writes
            assign perf_fifo_empty = !w_fifo_rd_valid_internal;       // Empty when no data available
            assign perf_fifo_full = w_fifo_full_internal;             // Full status to output
        
            // Zero-extend FIFO count to 16-bit output
            assign perf_fifo_count = {{(16-FIFO_ADDR_WIDTH-1){1'b0}}, w_fifo_count_internal};
        
            //=========================================================================
            // FIFO Data Latching and Splitting
            //=========================================================================
            // Two-register read sequence for 36-bit data over 32-bit APB bus:
            //
            // 1. Software reads PERF_FIFO_DATA_LOW (APB address 0xXXX):
            //    - APB slave asserts perf_fifo_rd for one cycle
            //    - FIFO pops and provides 36-bit data on w_fifo_rd_data
            //    - Data is latched into r_fifo_data_latched
            //    - APB returns lower 32 bits (timestamp/elapsed)
            //
            // 2. Software reads PERF_FIFO_DATA_HIGH (APB address 0xXXX+4):
            //    - APB returns upper 4 bits from latched data
            //    - No FIFO pop occurs
            //
            // This ensures atomic access to 36-bit FIFO entries across two 32-bit reads.
        
            `ALWAYS_FF_RST(clk, rst_n,
                if (`RST_ASSERTED(rst_n)) begin
                    r_fifo_data_latched <= '0;
                end else if (cfg_clear) begin
                    r_fifo_data_latched <= '0;
                end else if (perf_fifo_rd && !perf_fifo_empty) begin
                    // Latch FIFO data when read strobe asserted
                    r_fifo_data_latched <= w_fifo_rd_data;
                end
%000000     )
        
        
            // Split 36-bit latched data into two 32-bit outputs
            assign perf_fifo_data_low  = r_fifo_data_latched[31:0];   // Timestamp or elapsed time
            assign perf_fifo_data_high = {28'b0, r_fifo_data_latched[35:32]}; // {28'b0, event_type, channel_id[2:0]}
        
            //=========================================================================
            // Assertions for Verification
            //=========================================================================
        
            `ifdef FORMAL
            // Timestamp counter never decrements (unless clear or rollover)
            property timestamp_monotonic;
                @(posedge clk) disable iff (!rst_n || cfg_clear)
                cfg_enable && (r_timestamp_counter != '1) |->
                    ##1 (r_timestamp_counter == $past(r_timestamp_counter) + 1);
            endproperty
            assert property (timestamp_monotonic);
        
            // In elapsed mode, channel must be active before recording elapsed time
            property elapsed_requires_active;
                @(posedge clk) disable iff (!rst_n)
                (cfg_mode == MODE_ELAPSED) && w_fifo_wr |->
                    r_channel_active[w_active_channel];
            endproperty
            assert property (elapsed_requires_active);
        
            // FIFO write only when enabled and event detected
            property fifo_write_conditions;
                @(posedge clk) disable iff (!rst_n)
                w_fifo_wr |-> (cfg_enable && w_channel_event);
            endproperty
            assert property (fifo_write_conditions);
            `endif
        
        endmodule : perf_profiler
        
