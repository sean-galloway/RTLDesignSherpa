// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: stream_mon_genesys2_top
// Purpose: Genesys 2 (Kintex-7 XC7K325T-2) board top for the STREAM
//          characterization harness -- the monitor board-validation
//          coverage/rate-matching build (see
//          vault/handbook/fpga/monitor-board-coverage.md).
//
// Differences vs the Nexys A7 top (stream_char_top.sv):
//   - Board clocking: the Genesys 2 provides a 200 MHz LVDS system clock, so
//     this top adds IBUFDS + MMCM (patterned on rapids_char_genesys2_top.sv)
//     to derive the harness clock. VCO = 200 MHz x 6 = 1200 MHz; the harness
//     clock is 1200 / CLKOUT0_DIVIDE (12 -> 100 MHz, 15 -> 80 MHz,
//     20 -> 60 MHz). FPGA_CLK_HZ for the UART divisor / heartbeat / timer is
//     derived from the same parameter so it can never disagree.
//   - NUM_CHANNELS = 4 (owner: 2-4 channels is the interesting config;
//     8-channel builds are also supported).
//   - USE_AXI_MONITORS = 1: the in-core rd/wr AXI monitors are BUILT on this
//     bitstream. Their CAM tables size at stream_core's parametric default
//     (RD/WR_MON_MAX_TRANS = NUM_CHANNELS * AR/AW_MAX_OUTSTANDING + 4 = 36
//     at 4 channels) -- the no-backpressure bound from the plan.
//   - LEDs: the Genesys 2 has 8 user LEDs (no 7-segment display), so the
//     status bank is 8 bits and the PASS/FAIL patterns are one byte.
//
// Board I/O (pins fixed by stream_char_genesys2_top.xdc):
//   sysclk_p/n  - 200 MHz LVDS system clock (AD12/AD11)
//   cpu_resetn  - red CPU reset button (R19, active-low)
//   uart_tx_in  - host -> FPGA UART RX (Y20)
//   uart_rx_out - FPGA -> host UART TX (Y23)
//   led[7:0]    - user LEDs

`timescale 1ns / 1ps

`include "reset_defs.svh"

module stream_mon_genesys2_top #(
    // Harness clock = 1200 MHz VCO / CLKOUT0_DIVIDE.
    //   12 -> 100 MHz, 15 -> 80 MHz, 20 -> 60 MHz.
    parameter int CLKOUT0_DIVIDE = 12,
    // Owner-specified geometry for the monitor validation campaign.
    parameter int NUM_CHANNELS     = 4,
    parameter int USE_AXI_MONITORS = 1,
    parameter int UART_BAUD        = 115_200
) (
    input  logic       sysclk_p,      // 200 MHz LVDS (+)
    input  logic       sysclk_n,      // 200 MHz LVDS (-)
    input  logic       cpu_resetn,    // active-low pushbutton (R19)

    input  logic       uart_tx_in,    // host -> FPGA
    output logic       uart_rx_out,   // FPGA -> host

    output logic [7:0] led
);

    // Derived harness clock frequency; single source of truth for the UART
    // divisor, heartbeat, LED update rate and characterization timer.
    localparam int FPGA_CLK_HZ = 1_200_000_000 / CLKOUT0_DIVIDE;

    // =========================================================================
    // 200 MHz LVDS -> single-ended -> MMCM -> harness clock.
    // VCO = 200 MHz * 6 = 1200 MHz (inside the -2 Kintex 600-1440 MHz range).
    // =========================================================================
    logic sysclk_ib, clk_unbuf, aclk, clkfb, clkfb_buf, mmcm_locked;

    IBUFDS u_ibufds (.I(sysclk_p), .IB(sysclk_n), .O(sysclk_ib));

    MMCME2_BASE #(
        .BANDWIDTH        ("OPTIMIZED"),
        .CLKIN1_PERIOD    (5.000),                // 200 MHz
        .DIVCLK_DIVIDE    (1),
        .CLKFBOUT_MULT_F  (6.000),                // VCO = 1200 MHz
        .CLKOUT0_DIVIDE_F (CLKOUT0_DIVIDE),        // int -> real conversion
        .CLKOUT0_DUTY_CYCLE(0.500),
        .CLKOUT0_PHASE    (0.000),
        .STARTUP_WAIT     ("FALSE")
    ) u_mmcm (
        .CLKIN1   (sysclk_ib),
        .CLKFBIN  (clkfb_buf),
        .CLKFBOUT (clkfb),
        .CLKFBOUTB(),
        .CLKOUT0  (clk_unbuf),
        .CLKOUT0B (), .CLKOUT1 (), .CLKOUT1B(), .CLKOUT2 (), .CLKOUT2B(),
        .CLKOUT3  (), .CLKOUT3B(), .CLKOUT4 (), .CLKOUT5 (), .CLKOUT6 (),
        .LOCKED   (mmcm_locked),
        .RST      (1'b0),
        .PWRDWN   (1'b0)
    );
    BUFG u_bufg_fb (.I(clkfb),     .O(clkfb_buf));
    BUFG u_bufg_c0 (.I(clk_unbuf), .O(aclk));

    // =========================================================================
    // Reset synchronization -- async assert, sync deassert. Held asserted
    // until the MMCM locks (OR of the button and lock loss). Same two-flop
    // ASYNC_REG structure as stream_char_top so the XDC false paths match.
    // =========================================================================
    logic rst_n_raw;
    assign rst_n_raw = cpu_resetn & mmcm_locked;

    (* ASYNC_REG = "TRUE" *) logic r_rst_meta;
    (* ASYNC_REG = "TRUE" *) logic r_rst_sync;
    always_ff @(posedge aclk or negedge rst_n_raw) begin
        if (!rst_n_raw) begin
            r_rst_meta <= 1'b0;
            r_rst_sync <= 1'b0;
        end else begin
            r_rst_meta <= 1'b1;
            r_rst_sync <= r_rst_meta;
        end
    end

    wire aresetn = r_rst_sync;

    // =========================================================================
    // Harness. Memory sizing carried over unchanged from the proven Nexys A7
    // build (DESC_RAM_ENTRIES=256 covers 8ch x 16 desc/ch, so 4ch trivially;
    // DEBUG_SRAM_WORDS=4096 trace ring). The only deltas vs the A7 build are
    // NUM_CHANNELS=4 and USE_AXI_MONITORS=1 -- this bitstream exists to put
    // the rd/wr AXI monitors on silicon (properly sized tables).
    // =========================================================================
    logic       w_stream_irq;
    logic       w_any_error;
    logic       w_trace_overflow;
    logic [3:0] w_heartbeat;
    logic       w_timer_done;
    logic       w_timer_pass;

    stream_mon_harness #(
        .FPGA_CLK_HZ           (FPGA_CLK_HZ),
        .UART_BAUD             (UART_BAUD),
        .DATA_WIDTH            (128),
        .ADDR_WIDTH            (32),
        .SRAM_DEPTH            (256),
        .NUM_CHANNELS          (NUM_CHANNELS),
        .DESC_RAM_ENTRIES      ( 256),   //  256 x 256 b =   8 KB (LUTRAM)
        .DEBUG_SRAM_WORDS      (4096),   // 4096 x  32 b =  16 KB (~4 BRAM tiles)
        // In-core rd/wr AXI monitors ON (the point of this bitstream).
        // stream_core sizes their CAMs at RD/WR_MON_MAX_TRANS =
        // NUM_CHANNELS * AR/AW_MAX_OUTSTANDING + 4 (= 36 here) by default.
        .USE_AXI_MONITORS      (USE_AXI_MONITORS),
        // Characterization knobs from the same per-build config package the
        // A7 flow uses (AR/AW outstanding = 8, delay queue capacities).
        .AR_MAX_OUTSTANDING    (stream_char_cfg_pkg::CFG_AR_MAX_OUTSTANDING),
        .AW_MAX_OUTSTANDING    (stream_char_cfg_pkg::CFG_AW_MAX_OUTSTANDING),
        .RESP_DELAY_R_CAPACITY (stream_char_cfg_pkg::CFG_RESP_DELAY_R_CAPACITY),
        .RESP_DELAY_B_CAPACITY (stream_char_cfg_pkg::CFG_RESP_DELAY_B_CAPACITY),
        // Match the A7 board build: per-channel completion/error MonBus
        // emitters stay off (the harness hard-wires them off toward
        // stream_top_ch8 regardless; kept explicit for documentation).
        .GEN_MON               (1'b0),
        // TASK-101 extended addressing on, same as the A7 bitstream, so this
        // build runs both legacy contiguous and extended descriptors.
        .USE_ROW_COL_MAJOR_ADDRESSING (1)
    ) u_harness (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .i_uart_rx       (uart_tx_in),
        .o_uart_tx       (uart_rx_out),
        .o_stream_irq    (w_stream_irq),
        .o_any_error     (w_any_error),
        .o_trace_overflow(w_trace_overflow),
        .o_heartbeat     (w_heartbeat),
        .o_timer_done    (w_timer_done),
        .o_timer_pass    (w_timer_pass)
    );

    // =========================================================================
    // LEDs -- same slow-domain CDC driver as the A7 top, 8 LEDs wide.
    // Idle:   [0] stream_irq, [1] any_error, [2] trace_overflow,
    //         [3] ~1 Hz heartbeat, [7:4] zero.
    // Result: PASS = 0x23 (low byte of the A7 ladder pattern; heartbeat
    //         keeps blinking on bit 3), FAIL = 0x99.
    // =========================================================================
    logic [7:0] w_led_status;
    logic [7:0] w_led_status_idle;
    localparam logic [7:0] LED_PATTERN_PASS = 8'h23;
    localparam logic [7:0] LED_PATTERN_FAIL = 8'h99;

    assign w_led_status_idle = {4'h0,
                                w_heartbeat[3],     // [3] ~1 Hz blink
                                w_trace_overflow,   // [2]
                                w_any_error,        // [1]
                                w_stream_irq};      // [0]

    assign w_led_status = w_timer_done
        ? (w_timer_pass ? LED_PATTERN_PASS : LED_PATTERN_FAIL)
        : w_led_status_idle;

    led_status_driver #(
        .FPGA_CLK_HZ  (FPGA_CLK_HZ),
        .LED_UPDATE_HZ(200),
        .NUM_LEDS     (8),
        .SYNC_STAGES  (3)
    ) u_led_status_driver (
        .aclk     (aclk),
        .aresetn  (aresetn),
        .i_status (w_led_status),
        .o_led    (led)
    );

endmodule : stream_char_genesys2_top
