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
//   - Board clocking: default is the BYPASS -- aclk = CLK100MHZ direct at
//     100 MHz, no MMCM. VCO_MHZ/CLKOUT0_DIVIDE derate the harness clock for
//     builds that miss timing on the -1 fabric (750/10 -> 75 MHz, 600/10 ->
//     60 MHz, 1000/20 -> 50 MHz); VCO = 100 MHz x MULT_F must stay on the
//     0.125 grid (VCO multiple of 12.5) inside the Artix-7 -1 range
//     600..1200 MHz, enforced by the elaboration guards below.
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
    // Harness clock. VCO_MHZ=0 (default) BYPASSES the MMCM: aclk = CLK100MHZ
    // direct at 100 MHz. Derate with VCO_MHZ/CLKOUT0_DIVIDE when a build
    // misses timing on the -1 fabric: 750/10 -> 75 MHz, 600/10 -> 60 MHz,
    // 1000/20 -> 50 MHz. MULT_F = VCO_MHZ/100 must stay on the MMCM 0.125
    // grid and inside the Artix-7 -1 VCO range (guards below).
    parameter int VCO_MHZ        = 0,
    parameter int CLKOUT0_DIVIDE = 10,
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

    // Elaboration guard: catch an invalid cone mode or an unbuildable clock
    // pair at compile time rather than as a silently-wrong bitstream.
    initial begin
        if (MON_ERROR_FLAVOR < 0 || MON_ERROR_FLAVOR > 2)
            $error("MON_ERROR_FLAVOR=%0d invalid (0=all-except-error, 1=error-only, 2=all cones)",
                   MON_ERROR_FLAVOR);
        if (VCO_MHZ != 0) begin
            if ((VCO_MHZ * 8) % 100 != 0)
                $error("VCO_MHZ=%0d is not a multiple of 12.5: MULT_F=%0f is off the MMCM 0.125 grid",
                       VCO_MHZ, real'(VCO_MHZ) / 100.0);
            if (VCO_MHZ < 600 || VCO_MHZ > 1200)
                $error("VCO_MHZ=%0d outside the Artix-7 -1 MMCM range 600..1200", VCO_MHZ);
            if ((VCO_MHZ * 1_000_000) % CLKOUT0_DIVIDE != 0)
                $error("VCO_MHZ=%0d / CLKOUT0_DIVIDE=%0d is not an integer Hz frequency",
                       VCO_MHZ, CLKOUT0_DIVIDE);
        end
    end

    // Derived harness clock frequency; single source of truth for the UART
    // divisor, heartbeat, LED update rate and characterization timer.
    localparam int FPGA_CLK_HZ = (VCO_MHZ == 0) ? 100_000_000
                                                : (VCO_MHZ * 1_000_000) / CLKOUT0_DIVIDE;

    // =========================================================================
    // Harness clock. BYPASS (default): aclk = CLK100MHZ. Derated: 100 MHz ->
    // IBUF -> MMCM (VCO = 100 MHz x MULT_F) -> BUFG. Reset is held asserted
    // until the MMCM locks (bypass ties locked high). Vivado auto-derives the
    // MMCM output clock from sys_clk_pin, so the XDC needs no generated-clock
    // declaration for it.
    // =========================================================================
    logic clk_ib, clk_unbuf, aclk, clkfb, clkfb_buf, mmcm_locked;

    generate
    if (VCO_MHZ == 0) begin : g_clk_bypass
        assign aclk        = CLK100MHZ;
        assign mmcm_locked = 1'b1;
    end else begin : g_clk_mmcm
        localparam real CLKFBOUT_MULT = real'(VCO_MHZ) / 100.0;

        IBUF u_ibuf (.I(CLK100MHZ), .O(clk_ib));

        MMCME2_BASE #(
            .BANDWIDTH        ("OPTIMIZED"),
            .CLKIN1_PERIOD    (10.000),               // 100 MHz
            .DIVCLK_DIVIDE    (1),
            .CLKFBOUT_MULT_F  (CLKFBOUT_MULT),        // VCO = 100 MHz * MULT
            .CLKOUT0_DIVIDE_F (CLKOUT0_DIVIDE),
            .CLKOUT0_DUTY_CYCLE(0.500),
            .CLKOUT0_PHASE    (0.000),
            .STARTUP_WAIT     ("FALSE")
        ) u_mmcm (
            .CLKIN1   (clk_ib),
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
    end
    endgenerate

    logic rst_n_raw;
    assign rst_n_raw = CPU_RESETN & mmcm_locked;

    // =========================================================================
    // Reset synchronization -- async assert, sync deassert. ASYNC_REG keeps the
    // flops adjacent for MTBF. False paths to r_rst_meta/D and the reset
    // distribution network are set in stream_char_top.xdc.
    // =========================================================================
    (* ASYNC_REG = "TRUE" *) logic r_rst_meta;
    (* ASYNC_REG = "TRUE" *) logic r_rst_sync;
    `ALWAYS_FF_RST(aclk, rst_n_raw,
        if (`RST_ASSERTED(rst_n_raw)) begin
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
