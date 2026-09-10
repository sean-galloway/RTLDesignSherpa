// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: uart_16550_intr
// Purpose: UART 16550 interrupt conditions, IER gating and IIR priority
//
// Description:
//   Turns the four raw conditions into the four IER-gated interrupts, encodes
//   the IIR priority, applies the read-IIR clear of the THR-empty interrupt,
//   and gates irq with OUT2.
//
//   Split out of uart_16550_core to keep that file under the 800-line cap.
//
// Notes:
//   - The character timeout shares the received-data-available priority
//     slot and is distinguished by IIR[3], so IIR reads 0x0C for it and
//     0x04 for a plain trigger-level interrupt. It is gated by IER[0] like
//     the source it shares with, and exists only in FIFO mode.
//   - No assertions live in this module; properties belong in formal/.
//
// Documentation: projects/components/retro_legacy_blocks/rtl/uart_16550/README.md
// Created: 2026-09-10

`timescale 1ns / 1ps

`include "reset_defs.svh"

module uart_16550_intr #(
    parameter int FIFO_DEPTH = 16
) (
    input  logic clk,
    input  logic rst_n,

    // Raw conditions from the datapath
    input  logic overrun_error,
    input  logic parity_error,
    input  logic framing_error,
    input  logic break_interrupt,
    input  logic rx_fifo_empty,
    input  logic [$clog2(FIFO_DEPTH):0] rx_fifo_count,
    input  logic tx_fifo_empty,
    input  logic delta_cts,
    input  logic delta_dsr,
    input  logic trailing_ri,
    input  logic delta_dcd,

    // Configuration
    input  logic       cfg_fifo_enable,
    input  logic [1:0] cfg_rx_trigger,
    input  logic       cfg_out2,
    input  logic       cfg_rx_data_ie,
    input  logic       cfg_tx_empty_ie,
    input  logic       cfg_line_status_ie,
    input  logic       cfg_modem_ie,

    // Character timeout level from the receiver (four character times with
    // a non-empty FIFO and no activity), gated here by IER[0] like the
    // received-data source it shares a priority slot with.
    input  logic rx_timeout,

    // Read strobe for IIR
    input  logic iir_read,

    // Interrupt outputs
    output logic       int_not_pending,
    output logic [1:0] int_id,
    output logic       int_timeout,
    // The RX FIFO is at or above the trigger level. Exported so auto flow
    // control drives RTS from the same condition the interrupt uses,
    // rather than a second copy of the comparison.
    output logic       rx_trigger_reached,
    output logic       irq
);

    localparam int FIFO_ADDR_WIDTH = $clog2(FIFO_DEPTH);

    // RX Trigger levels (1, 4, 8, 14 bytes)
    localparam logic [3:0] RX_TRIGGER_1  = 4'd1;
    localparam logic [3:0] RX_TRIGGER_4  = 4'd4;
    localparam logic [3:0] RX_TRIGGER_8  = 4'd8;
    localparam logic [3:0] RX_TRIGGER_14 = 4'd14;

    logic w_rx_trigger_reached;
    assign rx_trigger_reached = w_rx_trigger_reached;
    logic [3:0] w_rx_trigger_level;

    always_comb begin
        unique case (cfg_rx_trigger)
            2'b00: w_rx_trigger_level = RX_TRIGGER_1;
            2'b01: w_rx_trigger_level = RX_TRIGGER_4;
            2'b10: w_rx_trigger_level = RX_TRIGGER_8;
            2'b11: w_rx_trigger_level = RX_TRIGGER_14;
        endcase
    end

    // Sized from FIFO_ADDR_WIDTH, not a fixed 5-bit concat: the count is
    // [FIFO_ADDR_WIDTH:0], so at FIFO_DEPTH 32 or 64 a {1'b0, [3:0]} RHS is
    // narrower than the LHS and -Wall reports WIDTHEXPAND.
    assign w_rx_trigger_reached =
        (rx_fifo_count >= (FIFO_ADDR_WIDTH+1)'(w_rx_trigger_level));

    // Interrupt priority (highest to lowest):
    // 1. RX Line Status (LSR[1:4] - errors)
    // 2. RX Data Available / Character Timeout
    // 3. TX Holding Register Empty
    // 4. Modem Status

    logic w_cond_rx_error, w_cond_rx_data, w_cond_tx_empty, w_cond_modem;
    logic w_int_rx_error, w_int_rx_data, w_int_tx_empty, w_int_modem;
    logic w_cond_timeout, w_int_timeout;
    logic r_thre_int_masked;

    // The raw CONDITIONS, independent of whether anyone asked to hear about
    // them. LSR and MSR report these whatever IER says.
    assign w_cond_rx_error = overrun_error | parity_error |
                             framing_error | break_interrupt;
    assign w_cond_rx_data  = cfg_fifo_enable ? w_rx_trigger_reached : !rx_fifo_empty;
    assign w_cond_tx_empty = tx_fifo_empty;
    assign w_cond_modem    = delta_cts | delta_dsr |
                             trailing_ri | delta_dcd;

    // EACH SOURCE IS GATED INDEPENDENTLY BY ITS OWN IER BIT. A disabled
    // source stays true in LSR/MSR and is simply not an interrupt: it does
    // not raise irq and IIR does not report it. IER used to have no port on
    // this module at all - irq was `~int_not_pending && cfg_out2` regardless -
    // so IER was decorative.
    //
    // READING IIR CLEARS THE THR-EMPTY INTERRUPT when THR empty is the source
    // being reported (16550 rule). The condition itself stays true - the FIFO
    // really is empty - so the mask is what clears, and it re-arms the moment
    // the condition goes away, i.e. when something is written to THR.
    assign w_int_rx_error = w_cond_rx_error && cfg_line_status_ie;
    assign w_int_rx_data  = w_cond_rx_data  && cfg_rx_data_ie;
    // The timeout only exists in FIFO mode: in character mode a single
    // unread byte is already the received-data condition.
    assign w_cond_timeout = cfg_fifo_enable && rx_timeout && !rx_fifo_empty;
    assign w_int_timeout  = w_cond_timeout && cfg_rx_data_ie;
    assign w_int_tx_empty = w_cond_tx_empty && cfg_tx_empty_ie && !r_thre_int_masked;
    assign w_int_modem    = w_cond_modem    && cfg_modem_ie;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_thre_int_masked <= 1'b0;
        end else if (!w_cond_tx_empty) begin
            // The condition went away; the next one is a fresh interrupt.
            r_thre_int_masked <= 1'b0;
        end else if (iir_read && !w_int_rx_error && !w_int_rx_data &&
                     !w_int_timeout && w_int_tx_empty) begin
            // IIR was read while THR empty was the source it reported.
            r_thre_int_masked <= 1'b1;
        end
    )

    // Priority, highest first: RX line status, RX data available or the
    // character timeout, THR empty, modem status. Only ENABLED sources take
    // part, so a disabled higher source never hides an enabled lower one.
    // The timeout shares the received-data slot and is distinguished by
    // IIR[3], which is what makes IIR read 0x0C rather than 0x04.
    always_comb begin
        if (w_int_rx_error) begin
            int_not_pending = 1'b0;
            int_id = 2'b11;
        end else if (w_int_rx_data || w_int_timeout) begin
            int_not_pending = 1'b0;
            int_id = 2'b10;
        end else if (w_int_tx_empty) begin
            int_not_pending = 1'b0;
            int_id = 2'b01;
        end else if (w_int_modem) begin
            int_not_pending = 1'b0;
            int_id = 2'b00;
        end else begin
            int_not_pending = 1'b1;
            int_id = 2'b00;
        end
    end

    // IIR[3] distinguishes the timeout from plain received-data-available
    // within the same priority slot, which is how PC16550D encodes 0x0C.
    assign int_timeout = w_int_timeout;

    assign irq = ~int_not_pending && cfg_out2;  // OUT2 gates interrupt

endmodule : uart_16550_intr
