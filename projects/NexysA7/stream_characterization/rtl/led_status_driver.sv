// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: led_status_driver
// Purpose: Drive the Nexys A7 LED bank from a properly-isolated slow clock
//          domain so that LED outputs do NOT appear as endpoints of any
//          high-speed datapath in the rest of the design.
//
// Subsystem: NexysA7/stream_characterization
//
// Author: sean galloway
// Created: 2026-04-26
//
// ---------------------------------------------------------------------------
// WHY
// ---------------------------------------------------------------------------
// LEDs are human-visible — anything faster than ~100 Hz is invisible. Letting
// `assign LED = some_fast_flop` puts LED OBUFs at the end of a 10 ns timing
// path that has no engineering reason to close. In the stream_char build the
// raw LED drivers were three of the worst post-route endpoints (-0.9 to
// -1.3 ns), and each one was a different fast-domain status flop driving
// straight into an LED OBUF.
//
// This module fixes that the right way:
//
//   1. Generate a slow clock (~LED_UPDATE_HZ) by dividing aclk and routing
//      the result through a BUFG so it can clock real flops.
//   2. Synchronise aresetn into the slow clock domain.
//   3. Cross the status word from the fast (aclk) domain into the slow
//      domain via cdc_2_phase_handshake — proper CDC, no shortcuts.
//   4. Drive LEDs from a slow-domain register only.
//
// After this, the LED OBUF endpoint clock is the slow generated clock, not
// sys_clk_pin, so its timing budget is the slow period (5 ms at 200 Hz)
// rather than 10 ns. The set_false_path -to [get_ports {LED[*]}] in the
// XDC becomes a debugging convenience rather than a load-bearing fix.
//
// ---------------------------------------------------------------------------
// REQUIRED SDC CONSTRAINTS (must be in the project XDC)
// ---------------------------------------------------------------------------
//   # 1) Declare the divided clock so Vivado treats it as its own domain.
//   create_generated_clock -name led_slow_clk \
//       -source [get_pins -hier -filter {NAME =~ *u_led_status_driver/r_div_count_reg[0]/C}] \
//       -divide_by <2 * (FPGA_CLK_HZ / LED_UPDATE_HZ)> \
//       [get_pins -hier -filter {NAME =~ *u_led_status_driver/u_slow_bufg/O}]
//
//   # 2) cdc_2_phase_handshake CDC datapath constraints (see that module's
//   #    header for the canonical pattern). Apply at the parent (XDC) level:
//   set_max_delay -datapath_only \
//       -from [get_pins -hier -filter {NAME =~ *u_led_status_driver/u_hs/r_req_tog_reg/C}] \
//       -to   [get_pins -hier -filter {NAME =~ *u_led_status_driver/u_hs/r_req_sync_reg[0]/D}] \
//       <slow_period_ns>
//   set_max_delay -datapath_only \
//       -from [get_pins -hier -filter {NAME =~ *u_led_status_driver/u_hs/r_ack_tog_reg/C}] \
//       -to   [get_pins -hier -filter {NAME =~ *u_led_status_driver/u_hs/r_ack_sync_reg[0]/D}] \
//       <fast_period_ns>
//   set_max_delay -datapath_only \
//       -from [get_pins -hier -filter {NAME =~ *u_led_status_driver/u_hs/r_src_data_hold_reg[*]/C}] \
//       -to   [get_pins -hier -filter {NAME =~ *u_led_status_driver/u_hs/r_dst_data_reg[*]/D}] \
//       <slow_period_ns>
// ---------------------------------------------------------------------------

`timescale 1ns / 1ps

`include "reset_defs.svh"

module led_status_driver #(
    parameter int FPGA_CLK_HZ   = 100_000_000,  // aclk frequency
    parameter int LED_UPDATE_HZ = 200,          // slow clock frequency
    parameter int NUM_LEDS      = 16,           // status / LED bus width
    parameter int SYNC_STAGES   = 3             // CDC synchroniser depth
) (
    // Fast (source) domain
    input  logic                  aclk,
    input  logic                  aresetn,
    input  logic [NUM_LEDS-1:0]   i_status,

    // LED bank (driven from slow domain register)
    output logic [NUM_LEDS-1:0]   o_led
);

    // -----------------------------------------------------------------------
    // Slow clock generation
    // -----------------------------------------------------------------------
    // Toggle a flop every DIV_HALF_PERIOD aclk cycles. Resulting square wave
    // has frequency LED_UPDATE_HZ. For 100 MHz / 200 Hz that's a divide-by
    // 250000, so r_div_count is 18 bits.
    localparam int DIV_HALF_PERIOD = FPGA_CLK_HZ / (2 * LED_UPDATE_HZ);
    localparam int DIV_WIDTH       = (DIV_HALF_PERIOD <= 1) ? 1 :
                                     $clog2(DIV_HALF_PERIOD);

    logic [DIV_WIDTH-1:0] r_div_count;
    logic                 r_slow_clk_raw;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_div_count    <= '0;
            r_slow_clk_raw <= 1'b0;
        end else if (r_div_count == DIV_WIDTH'(DIV_HALF_PERIOD - 1)) begin
            r_div_count    <= '0;
            r_slow_clk_raw <= ~r_slow_clk_raw;
        end else begin
            r_div_count    <= r_div_count + 1'b1;
        end
    )

    // Route the divided clock through a BUFG so it lands on the global
    // clock network and can drive real flops. Without this, Vivado will
    // either route the slow clock on local fabric (bad skew, sometimes
    // illegal) or refuse to use it as a clock at all.
    logic slow_clk;
    BUFG u_slow_bufg (
        .I (r_slow_clk_raw),
        .O (slow_clk)
    );

    // -----------------------------------------------------------------------
    // Reset synchroniser for the slow domain
    // -----------------------------------------------------------------------
    // Standard 2-flop async-assert / sync-deassert. Tagged ASYNC_REG so
    // Vivado keeps them packed and back-annotates for MTBF reporting.
    (* ASYNC_REG = "TRUE" *) logic r_slow_rst_meta;
    (* ASYNC_REG = "TRUE" *) logic r_slow_rst_sync;

    always_ff @(posedge slow_clk or negedge aresetn) begin
        if (!aresetn) begin
            r_slow_rst_meta <= 1'b0;
            r_slow_rst_sync <= 1'b0;
        end else begin
            r_slow_rst_meta <= 1'b1;
            r_slow_rst_sync <= r_slow_rst_meta;
        end
    end

    wire slow_aresetn = r_slow_rst_sync;

    // -----------------------------------------------------------------------
    // CDC: send i_status across via 2-phase handshake
    // -----------------------------------------------------------------------
    // The source side asserts src_valid continuously with the current
    // status word. Each handshake round-trip (~2 + 2*SYNC_STAGES *
    // max(src,dst) periods, dominated by the slow clock here) latches a
    // new sample into the destination register. With SYNC_STAGES=3 and a
    // 200 Hz slow clock that's roughly 30 ms per update — ample for any
    // human-visible status display.
    //
    // src_ready is intentionally unused: we don't need backpressure
    // because we are not throttling the producer; we're merely sampling
    // its current state.
    logic                w_dst_valid;
    logic [NUM_LEDS-1:0] w_dst_data;

    cdc_2_phase_handshake #(
        .DATA_WIDTH    (NUM_LEDS),
        .SYNC_STAGES   (SYNC_STAGES),
        .TIMEOUT_CYCLES(0)
    ) u_hs (
        .clk_src     (aclk),
        .rst_src_n   (aresetn),
        .src_valid   (1'b1),
        .src_ready   (/* unused */),
        .src_data    (i_status),
        .src_timeout (/* unused */),

        .clk_dst     (slow_clk),
        .rst_dst_n   (slow_aresetn),
        .dst_valid   (w_dst_valid),
        .dst_ready   (1'b1),
        .dst_data    (w_dst_data)
    );

    // -----------------------------------------------------------------------
    // Slow-domain LED register — single source of LED bus
    // -----------------------------------------------------------------------
    logic [NUM_LEDS-1:0] r_led;

    always_ff @(posedge slow_clk or negedge slow_aresetn) begin
        if (!slow_aresetn) begin
            r_led <= '0;
        end else if (w_dst_valid) begin
            r_led <= w_dst_data;
        end
    end

    assign o_led = r_led;

endmodule : led_status_driver
