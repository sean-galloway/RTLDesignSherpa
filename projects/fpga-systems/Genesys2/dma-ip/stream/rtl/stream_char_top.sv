// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: stream_char_top
// Purpose: Nexys A7-100T (Artix-7 XC7A100T-1) board top for the STREAM
//          characterization harness. Pins + reset sync + LED/7-seg only; the
//          whole host path (UART -> AXIL -> CSRs + kick) lives inside
//          stream_harness, so simulating the harness exercises the board's own
//          launch mechanism.
//
// Differences vs the Genesys 2 top (stream_genesys2_top.sv):
//   - Board clocking: the Nexys A7 provides a 100 MHz single-ended oscillator
//     (E3), so aclk = CLK100MHZ directly -- no IBUFDS/MMCM. FPGA_CLK_HZ is a
//     parameter solely so the UART divisor / heartbeat / timer stay derived.
//   - NUM_CHANNELS defaults to 4: the -1 100T fabric does not close the
//     instrumented 8-channel geometry (see build-mon/Makefile); 4 is the
//     board's design point. Override via the STREAM_NUM_CHANNELS generic.
//   - LEDs: 16 user LEDs plus an 8-digit 7-segment display. The display shows
//     "0123" on PASS / "9999" on FAIL once the characterization timer latches;
//     until then it is blank. LED bit 3 keeps blinking with the heartbeat even
//     in the result state (the "A7 ladder pattern" the Genesys 2 top's
//     PASS/FAIL bytes are the low byte of).
//
// Board I/O (pins fixed by stream_char_top.xdc):
//   CLK100MHZ   - 100 MHz oscillator (E3)
//   CPU_RESETN  - center pushbutton (C12, active-low)
//   UART_TXD_IN - FTDI -> FPGA RX (C4)
//   UART_RXD_OUT- FPGA -> FTDI TX (D4)
//   LED[15:0]   - status bank / PASS-FAIL ladder
//   AN[7:0], CA..CG, DP - 7-segment display (AN[3:0] used, AN[7:4] blanked)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module stream_char_top #(
    // Single source of truth for the UART divisor, heartbeat, LED update rate
    // and characterization timer. The Nexys A7 oscillator is 100 MHz.
    parameter int FPGA_CLK_HZ      = 100_000_000,
    // The -1 100T closes 4 channels with the monitors built; 8 is the Genesys 2
    // geometry. Same power-of-2 set the DUT supports (1/2/4/8).
    parameter int NUM_CHANNELS     = 4,
    // Same instrument knobs as the Genesys 2 top -- see stream_genesys2_top.sv
    // for the long version. Generic names must match fpga/tcl/create_project.tcl.
    parameter int USE_AXI_MONITORS = stream_char_cfg_pkg::CFG_USE_AXI_MONITORS,
    parameter bit OBS_ENABLE_MON_TAPS = stream_char_cfg_pkg::CFG_OBS_ENABLE_MON_TAPS,
    parameter int MON_NUM_BANKS    = stream_char_cfg_pkg::CFG_MON_NUM_BANKS,
    // Agent-resolved tally legal-set size (both tally memories).
    parameter int MON_N_PROFILE          = 64,
    // Observer transaction-table sizing, forwarded to stream_harness.
    parameter int OBS_MAX_TRANSACTIONS   = 64,
    parameter int OBS_NUM_BANKS          = 4,
    parameter bit OBS_USE_WDATA_ORDER_Q  = 1'b1,
    // Datapath-monitor cone set: 0 = all-except-error, 1 = error only, 2 = ALL.
    parameter int MON_ERROR_FLAVOR = 2,
    parameter int UART_BAUD        = 115_200
) (
    input  logic        CLK100MHZ,     // 100 MHz board clock
    input  logic        CPU_RESETN,    // active-low pushbutton

    input  logic        UART_TXD_IN,   // host -> FPGA
    output logic        UART_RXD_OUT,  // FPGA -> host

    output logic [15:0] LED,

    // 7-segment display (rightmost 4 digits used; AN[7:4] blanked)
    output logic [7:0]  AN,            // anodes, active low
    output logic        CA, CB, CC, CD, // cathode segments, active low
    output logic        CE, CF, CG,
    output logic        DP             // decimal point, active low
);

    // Elaboration guard: catch an invalid cone mode at compile time rather
    // than as a silently-different bitstream.
    initial begin
        if (MON_ERROR_FLAVOR < 0 || MON_ERROR_FLAVOR > 2)
            $error("MON_ERROR_FLAVOR=%0d invalid (0=all-except-error, 1=error-only, 2=all cones)",
                   MON_ERROR_FLAVOR);
    end

    wire aclk    = CLK100MHZ;

    // =========================================================================
    // Reset synchronization -- async assert, sync deassert. ASYNC_REG keeps the
    // flops adjacent for MTBF. False paths to r_rst_meta/D and the reset
    // distribution network are set in stream_char_top.xdc.
    // =========================================================================
    (* ASYNC_REG = "TRUE" *) logic r_rst_meta;
    (* ASYNC_REG = "TRUE" *) logic r_rst_sync;
    `ALWAYS_FF_RST(CLK100MHZ, CPU_RESETN,
        if (`RST_ASSERTED(CPU_RESETN)) begin
            r_rst_meta <= 1'b0;
            r_rst_sync <= 1'b0;
        end else begin
            r_rst_meta <= 1'b1;
            r_rst_sync <= r_rst_meta;
        end
    )

    wire aresetn = r_rst_sync;

    // =========================================================================
    // Harness. Geometry (DATA/ADDR_WIDTH, SRAM_DEPTH, DESC_RAM_ENTRIES,
    // DEBUG_SRAM_WORDS, AR/AW_MAX_OUTSTANDING, RESP_DELAY_*, GEN_MON,
    // USE_ROW_COL_MAJOR_ADDRESSING) defaults from stream_char_cfg_pkg via
    // stream_harness -- do not restate it here (see the note in
    // stream_genesys2_top.sv: three hand-written answers, no single source).
    // =========================================================================
    logic       w_stream_irq;
    logic       w_any_error;
    logic       w_trace_overflow;
    logic [3:0] w_heartbeat;
    logic       w_timer_done;
    logic       w_timer_pass;

    stream_harness #(
        .FPGA_CLK_HZ           (FPGA_CLK_HZ),
        .UART_BAUD             (UART_BAUD),
        .NUM_CHANNELS          (NUM_CHANNELS),
        .OBS_MAX_TRANSACTIONS  (OBS_MAX_TRANSACTIONS),
        .OBS_NUM_BANKS         (OBS_NUM_BANKS),
        .OBS_USE_WDATA_ORDER_Q (OBS_USE_WDATA_ORDER_Q),
        .USE_AXI_MONITORS      (USE_AXI_MONITORS),
        .OBS_ENABLE_MON_TAPS   (OBS_ENABLE_MON_TAPS),
        .MON_NUM_BANKS         (MON_NUM_BANKS),
        .MON_N_PROFILE         (MON_N_PROFILE),
        .DATA_MON_CONE_MODE    (MON_ERROR_FLAVOR)
    ) u_harness (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .i_uart_rx       (UART_TXD_IN),
        .o_uart_tx       (UART_RXD_OUT),
        .o_stream_irq    (w_stream_irq),
        .o_any_error     (w_any_error),
        .o_trace_overflow(w_trace_overflow),
        .o_heartbeat     (w_heartbeat),
        .o_timer_done    (w_timer_done),
        .o_timer_pass    (w_timer_pass)
    );

    // =========================================================================
    // LEDs -- 16-bit slow-domain CDC driver (same as the Genesys 2 top, 8 bits
    // wider). Idle: [0] stream_irq, [1] any_error, [2] trace_overflow,
    //             [3] ~1 Hz heartbeat, [15:4] zero.
    // Result: PASS = 0x0123, FAIL = 0x9999, with bit 3 left as the live
    //         heartbeat so something keeps blinking after the timer latches.
    // =========================================================================
    logic [15:0] w_led_status;
    logic [15:0] w_led_status_idle;
    logic [15:0] w_led_status_result;
    localparam logic [15:0] LED_PATTERN_PASS = 16'h0123;
    localparam logic [15:0] LED_PATTERN_FAIL = 16'h9999;
    localparam logic [15:0] LED_HEART_BIT    = 16'h0008;

    assign w_led_status_idle = {12'h0,
                                w_heartbeat[3],     // [3] ~1 Hz blink
                                w_trace_overflow,   // [2]
                                w_any_error,        // [1]
                                w_stream_irq};      // [0]

    // One always_comb: bit 3 is the live heartbeat overriding the pattern
    // bit. Two overlapping continuous assigns (whole vector + bit select)
    // multiply-drive the net -- Vivado synth rewires that into neighboring
    // cones (caught as DRC MDRV-1 on u_harness/o_heartbeat).
    always_comb begin
        w_led_status_result = w_timer_pass ? LED_PATTERN_PASS : LED_PATTERN_FAIL;
        w_led_status_result[3] = w_heartbeat[3];
    end

    assign w_led_status = w_timer_done ? w_led_status_result : w_led_status_idle;

    led_status_driver #(
        .FPGA_CLK_HZ  (FPGA_CLK_HZ),
        .LED_UPDATE_HZ(200),
        .NUM_LEDS     (16),
        .SYNC_STAGES  (3)
    ) u_led_status_driver (
        .aclk     (aclk),
        .aresetn  (aresetn),
        .i_status (w_led_status),
        .o_led    (LED)
    );

    // =========================================================================
    // 7-segment: "0123" on PASS, "9999" on FAIL, blank until the timer latches.
    // =========================================================================
    logic [15:0] w_seg_value;
    logic [6:0]  w_seg_bus;
    assign w_seg_value = w_timer_pass ? 16'h0123 : 16'h9999;

    seven_seg_4digit #(
        .FPGA_CLK_HZ(FPGA_CLK_HZ),
        .REFRESH_HZ (1000)
    ) u_seven_seg (
        .aclk    (aclk),
        .aresetn (aresetn),
        .i_hex   (w_seg_value),
        .i_enable(w_timer_done),
        .o_an    (AN),
        .o_seg   (w_seg_bus),
        .o_dp    (DP)
    );

    // Cathode bus split into named board pins: w_seg_bus = {g,f,e,d,c,b,a}
    assign CA = w_seg_bus[0];
    assign CB = w_seg_bus[1];
    assign CC = w_seg_bus[2];
    assign CD = w_seg_bus[3];
    assign CE = w_seg_bus[4];
    assign CF = w_seg_bus[5];
    assign CG = w_seg_bus[6];

endmodule : stream_char_top
