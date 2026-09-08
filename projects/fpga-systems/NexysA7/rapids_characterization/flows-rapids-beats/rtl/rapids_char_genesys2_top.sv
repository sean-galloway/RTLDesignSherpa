// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: rapids_char_genesys2_top
// Purpose: Genesys 2 (Kintex-7 XC7K325T-2) board wrapper for the RAPIDS beats
//          characterization harness. Thin shim over the board-agnostic
//          rapids_char_top: it turns the Genesys 2's 200 MHz LVDS system clock
//          into the 100 MHz single-ended clock rapids_char_top expects (via an
//          MMCM) and maps the Genesys 2 pins. Everything downstream (UART bridge,
//          AXIL/CSR decode, the harness + DUT) is reused UNCHANGED from the
//          Nexys A7 flow.
//
// Why Genesys 2: the Artix-7 100T (-1) is at its timing limit for RAPIDS beats
// at >4 channels (512-bit datapath). The Kintex-7 325T (-2) has ~3.2x the LUTs
// and a faster speed grade, so the full 8-channel geometry closes 100 MHz with
// large margin (monitors may be left on).
//
// Board I/O (pins fixed by rapids_char_genesys2_top.xdc):
//   sysclk_p/n  - 200 MHz LVDS system clock (AD12/AD11)
//   cpu_resetn  - red CPU reset button (R19, active-low)
//   uart_tx_in  - host -> FPGA UART RX (Y20)
//   uart_rx_out - FPGA -> host UART TX (Y23)
//   led[7:0]    - user LEDs (low 8 of the harness status bank)

`timescale 1ns / 1ps

module rapids_char_genesys2_top #(
    parameter int NUM_CHANNELS     = 8,   // Kintex closes 8ch; override via generic
    parameter int DATA_WIDTH       = 512,
    parameter int ADDR_WIDTH       = 64,
    parameter int AXI_ID_WIDTH     = 8,
    parameter int AXIS_DEST_WIDTH  = 4,
    parameter int DESC_DATA_WIDTH  = 256,
    parameter int SRAM_DEPTH       = 256,
    parameter int DESC_RAM_ENTRIES = 256,
    parameter int APB_ADDR_WIDTH   = 13,
    parameter int APB_DATA_WIDTH   = 32,
    parameter int UART_BAUD        = 115_200
) (
    input  logic        sysclk_p,      // 200 MHz LVDS (+)
    input  logic        sysclk_n,      // 200 MHz LVDS (-)
    input  logic        cpu_resetn,    // active-low pushbutton (R19)

    input  logic        uart_tx_in,    // host -> FPGA
    output logic        uart_rx_out,   // FPGA -> host

    output logic [7:0]  led
);

    // -------------------------------------------------------------------------
    // 200 MHz LVDS -> single-ended -> MMCM -> 100 MHz
    // VCO = 200 MHz * 6 = 1200 MHz (in the -2 Kintex 600-1600 MHz range);
    // CLKOUT0 = 1200 / 12 = 100 MHz.
    // -------------------------------------------------------------------------
    logic sysclk_ib, clk100_unbuf, clk100, clkfb, clkfb_buf, mmcm_locked;

    IBUFDS u_ibufds (.I(sysclk_p), .IB(sysclk_n), .O(sysclk_ib));

    MMCME2_BASE #(
        .BANDWIDTH        ("OPTIMIZED"),
        .CLKIN1_PERIOD    (5.000),        // 200 MHz
        .DIVCLK_DIVIDE    (1),
        .CLKFBOUT_MULT_F  (6.000),        // VCO = 1200 MHz
        .CLKOUT0_DIVIDE_F (12.000),       // 100 MHz
        .CLKOUT0_DUTY_CYCLE(0.500),
        .CLKOUT0_PHASE    (0.000),
        .STARTUP_WAIT     ("FALSE")
    ) u_mmcm (
        .CLKIN1   (sysclk_ib),
        .CLKFBIN  (clkfb_buf),
        .CLKFBOUT (clkfb),
        .CLKFBOUTB(),
        .CLKOUT0  (clk100_unbuf),
        .CLKOUT0B (), .CLKOUT1 (), .CLKOUT1B(), .CLKOUT2 (), .CLKOUT2B(),
        .CLKOUT3  (), .CLKOUT3B(), .CLKOUT4 (), .CLKOUT5 (), .CLKOUT6 (),
        .LOCKED   (mmcm_locked),
        .RST      (1'b0),
        .PWRDWN   (1'b0)
    );
    BUFG u_bufg_fb (.I(clkfb),        .O(clkfb_buf));
    BUFG u_bufg_c0 (.I(clk100_unbuf), .O(clk100));

    // Hold the DUT in reset (active-low) until the MMCM locks; OR in the button.
    logic dut_resetn;
    assign dut_resetn = cpu_resetn & mmcm_locked;

    // -------------------------------------------------------------------------
    // Board-agnostic char top (reused unchanged). 7-segment outputs are left
    // open (Genesys 2 has no 7-seg); LED bank is truncated to the board's 8.
    // -------------------------------------------------------------------------
    logic [15:0] led16;
    assign led = led16[7:0];

    rapids_char_top #(
        .FPGA_CLK_HZ      (100_000_000),
        .UART_BAUD        (UART_BAUD),
        .NUM_CHANNELS     (NUM_CHANNELS),
        .DATA_WIDTH       (DATA_WIDTH),
        .ADDR_WIDTH       (ADDR_WIDTH),
        .AXI_ID_WIDTH     (AXI_ID_WIDTH),
        .AXIS_DEST_WIDTH  (AXIS_DEST_WIDTH),
        .DESC_DATA_WIDTH  (DESC_DATA_WIDTH),
        .SRAM_DEPTH       (SRAM_DEPTH),
        .DESC_RAM_ENTRIES (DESC_RAM_ENTRIES),
        .APB_ADDR_WIDTH   (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH   (APB_DATA_WIDTH)
    ) u_char_top (
        .CLK100MHZ    (clk100),
        .CPU_RESETN   (dut_resetn),
        .UART_TXD_IN  (uart_tx_in),
        .UART_RXD_OUT (uart_rx_out),
        .LED          (led16),
        // 7-segment display: unused on Genesys 2.
        .AN (), .CA (), .CB (), .CC (), .CD (), .CE (), .CF (), .CG (), .DP ()
    );

endmodule : rapids_char_genesys2_top
