// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// Module: stream_char_top
// Purpose: FPGA pin-level top for the STREAM characterization harness.
//
// Target board: Digilent Nexys A7-100T (xc7a100tcsg324-1)
//
// Pin mapping (typical; final pins fixed by XDC):
//   CLK100MHZ       - 100 MHz system clock (E3)
//   CPU_RESETN      - Center pushbutton (C12, active-low)
//   UART_TXD_IN     - FTDI -> FPGA RX     (C4)
//   UART_RXD_OUT    - FPGA -> FTDI TX     (D4)
//   LED[0]          - stream_irq
//   LED[1]          - any_error (sticky)
//   LED[2]          - trace_overflow
//   LED[3]          - 1 Hz heartbeat
//   LED[15:4]       - (unused / reserved for scratch debug)
//
// This module intentionally does nothing beyond pin I/O and instantiating
// stream_char_harness. All interesting logic lives in the harness.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module stream_char_top (
    input  logic        CLK100MHZ,       // 100 MHz board clock
    input  logic        CPU_RESETN,      // active-low pushbutton

    input  logic        UART_TXD_IN,     // FTDI->FPGA
    output logic        UART_RXD_OUT,    // FPGA->FTDI

    output logic [15:0] LED,

    // 7-segment display (rightmost 4 digits used; AN[7:4] blanked)
    output logic [7:0]  AN,              // anodes, active low
    output logic        CA, CB, CC, CD,  // cathode segments, active low
    output logic        CE, CF, CG,
    output logic        DP               // decimal point, active low
);

    // =========================================================================
    // Reset synchronization — async assert, sync deassert. ASYNC_REG tells
    // Vivado to keep these flops adjacent and to annotate them for MTBF
    // analysis. The false path to r_rst_meta's D input is set in the XDC.
    (* ASYNC_REG = "TRUE" *) logic r_rst_meta;
    (* ASYNC_REG = "TRUE" *) logic r_rst_sync;
    always_ff @(posedge CLK100MHZ or negedge CPU_RESETN) begin
        if (!CPU_RESETN) begin
            r_rst_meta <= 1'b0;
            r_rst_sync <= 1'b0;
        end else begin
            r_rst_meta <= 1'b1;
            r_rst_sync <= r_rst_meta;
        end
    end

    wire aclk    = CLK100MHZ;
    wire aresetn = r_rst_sync;

    // =========================================================================
    // Harness
    // =========================================================================
    logic       w_stream_irq;
    logic       w_any_error;
    logic       w_trace_overflow;
    logic [3:0] w_heartbeat;
    logic       w_timer_done;
    logic       w_timer_pass;

    // Per-build characterization knobs — see stream_char_cfg_pkg.sv. Swap
    // which cfg package is in the filelist to change side-Q / delay-queue
    // sizing without editing this file.
    stream_char_harness #(
        .FPGA_CLK_HZ           (100_000_000),
        .UART_BAUD             (115_200),
        .DATA_WIDTH            (128),
        .ADDR_WIDTH            (32),
        .SRAM_DEPTH            (256),
        // 8 channels with the widened false-path constraint covering all
        // arbiter state flops (see stream_char_top.xdc, "scheduler beats-
        // remaining counter into read-arbiter"). Prior attempt failed
        // timing because the existing false_path only covered
        // r_pending_client_reg; at 8 channels grant_reg/grant_id_reg also
        // land in the same cone and need the same exception.
        // Keep in lockstep with dv/tests/test_stream_char.py rtl_params.
        .NUM_CHANNELS          (8),
        // First-synth BRAM budget was 192 tiles / 135. Dominant consumers were
        // the harness's descriptor RAM (2048 × 256 b → 128 tiles) and monitor
        // trace buffer (64K × 32 b → 64 tiles), neither proportional to the
        // channel count. Shrunk here to fit the 100T. Bump either when the
        // characterization campaign needs deeper descriptor chains or longer
        // trace captures — at the expense of BRAM headroom.
        // DESC_RAM_ENTRIES = 256 covers 8 channels × 16 desc/channel with the
        // DESC_INDEX_OFFSET = 1 reserved slot (max in-use index = 128). Was 128
        // entries, which only covered up to ch=3 at 16 desc/ch; the host's
        // descriptor_builder packs channel N at byte N * MAX_DESC_PER_CH * 32,
        // so any 16-desc test with >= 4 channels wrapped ch4-7's descriptors
        // on top of ch0-3's and the engine then read garbage chains. desc_ram
        // is LUTRAM (Xilinx auto-infers distributed), so doubling adds ~800
        // LUTs (was 814) and zero BRAM -- fits comfortably in the 100T.
        .DESC_RAM_ENTRIES      ( 256),   //  256 × 256 b =   8 KB → ~0 BRAM (LUTRAM)
        .DEBUG_SRAM_WORDS      (4096),   // 4096 ×  32 b =  16 KB → ~4 tiles
        // Characterization knobs sourced from stream_char_cfg_pkg so a single
        // file controls the build's configuration (no module edits per sweep).
        .AR_MAX_OUTSTANDING    (stream_char_cfg_pkg::CFG_AR_MAX_OUTSTANDING),
        .AW_MAX_OUTSTANDING    (stream_char_cfg_pkg::CFG_AW_MAX_OUTSTANDING),
        .RESP_DELAY_R_CAPACITY (stream_char_cfg_pkg::CFG_RESP_DELAY_R_CAPACITY),
        .RESP_DELAY_B_CAPACITY (stream_char_cfg_pkg::CFG_RESP_DELAY_B_CAPACITY)
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
    // LEDs — driven from a slow (~200 Hz) clock domain via a 2-phase CDC
    // handshake. See led_status_driver.sv for the full rationale; in short,
    // LEDs are human-visible and have no business sitting on 10 ns
    // sys_clk_pin paths in the heart of the design.
    //
    // When the characterization timer has completed, override the per-bit
    // status display with one of two distinctive patterns so the board
    // shows the result at a glance (no need to read it over UART):
    //   PASS = 0x0123  (low-bit "ladder" — bits 0,1,5,8 lit)
    //   FAIL = 0x9999  (every nibble = 1001, very obviously NOT 0x0123)
    // Heartbeat continues blinking on bit [3] in the PASS pattern (bit 3
    // of 0x0123 is 0, so the heartbeat doesn't disturb the pattern).
    // =========================================================================
    logic [15:0] w_led_status;
    logic [15:0] w_led_status_idle;
    localparam logic [15:0] LED_PATTERN_PASS = 16'h0123;
    localparam logic [15:0] LED_PATTERN_FAIL = 16'h9999;

    assign w_led_status_idle = {12'h000,
                                w_heartbeat[3],     // [3] ~1 Hz blink
                                w_trace_overflow,   // [2]
                                w_any_error,        // [1]
                                w_stream_irq};      // [0]

    assign w_led_status = w_timer_done
        ? (w_timer_pass ? LED_PATTERN_PASS : LED_PATTERN_FAIL)
        : w_led_status_idle;

    led_status_driver #(
        .FPGA_CLK_HZ  (100_000_000),
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
    // 7-segment display: show "0123" on PASS, "9999" on FAIL, blank when idle.
    // Same w_timer_done / w_timer_pass signals that drive the LED override.
    // =========================================================================
    logic [15:0] w_seg_value;
    logic [6:0]  w_seg_bus;

    assign w_seg_value = w_timer_pass ? 16'h0123 : 16'h9999;

    seven_seg_4digit #(
        .FPGA_CLK_HZ(100_000_000),
        .REFRESH_HZ (1000)
    ) u_seven_seg (
        .aclk    (aclk),
        .aresetn (aresetn),
        .i_hex   (w_seg_value),
        .i_enable(w_timer_done),  // blanked until a result is latched
        .o_an    (AN),
        .o_seg   (w_seg_bus),
        .o_dp    (DP)
    );

    // Cathode bus split into named board pins. Bit order matches hex_to_7seg:
    //   w_seg_bus = {g, f, e, d, c, b, a}
    assign CA = w_seg_bus[0];
    assign CB = w_seg_bus[1];
    assign CC = w_seg_bus[2];
    assign CD = w_seg_bus[3];
    assign CE = w_seg_bus[4];
    assign CF = w_seg_bus[5];
    assign CG = w_seg_bus[6];

endmodule : stream_char_top
