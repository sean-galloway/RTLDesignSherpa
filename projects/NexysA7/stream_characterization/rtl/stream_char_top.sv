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

    output logic [15:0] LED
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

    stream_char_harness #(
        .FPGA_CLK_HZ  (100_000_000),
        .UART_BAUD    (115_200),
        .DATA_WIDTH   (128),
        .ADDR_WIDTH   (32),
        .SRAM_DEPTH   (256),
        // NUM_CHANNELS shrunk from 8 to 4 to fit the Artix-7 100T BRAM budget.
        // Keep in lockstep with dv/tests/test_stream_char.py rtl_params.
        .NUM_CHANNELS (4)
    ) u_harness (
        .aclk            (aclk),
        .aresetn         (aresetn),
        .i_uart_rx       (UART_TXD_IN),
        .o_uart_tx       (UART_RXD_OUT),
        .o_stream_irq    (w_stream_irq),
        .o_any_error     (w_any_error),
        .o_trace_overflow(w_trace_overflow),
        .o_heartbeat     (w_heartbeat)
    );

    // =========================================================================
    // LEDs
    // =========================================================================
    assign LED[0]     = w_stream_irq;
    assign LED[1]     = w_any_error;
    assign LED[2]     = w_trace_overflow;
    assign LED[3]     = w_heartbeat[3];   // ~1 Hz blink
    assign LED[15:4]  = 12'h000;

endmodule : stream_char_top
