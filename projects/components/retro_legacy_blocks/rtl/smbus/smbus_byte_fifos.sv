// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: smbus_byte_fifos
// Purpose: The TX and RX byte buffers, and their reset policy.
//
// The two FIFOs are here together because what is worth stating about them is
// the thing they share: THREE DIFFERENT THINGS CAN EMPTY THEM, and all three
// have to mean the same thing to both.
//
//   rst_n            power-on / bus reset
//   soft_reset       SMBUS_CONTROL.soft_reset - the engine restarts, and a
//                    half-drained transmit buffer is not something the next
//                    transaction should inherit
//   fifo_reset       SMBUS_CONTROL.fifo_reset - software clearing the buffers
//                    on their own, without disturbing the engine
//
// Splitting that across two instantiations in the sequencer is how one of
// them ends up honouring two of the three.

`timescale 1ns / 1ps

module smbus_byte_fifos #(
    parameter int FIFO_DEPTH = 32
) (
    input  wire       clk,
    input  wire       rst_n,        // active-low (house convention)
    input  wire       soft_reset,
    input  wire       fifo_reset,

    // TX: software writes, the sequencer pops
    input  wire [7:0] tx_wdata,
    input  wire       tx_wr,
    input  wire       tx_rd,
    output wire [7:0] tx_rdata,
    output wire [5:0] tx_level,
    output wire       tx_full,
    output wire       tx_empty,

    // RX: the sequencer pushes, software reads
    input  wire [7:0] rx_wdata,
    input  wire       rx_wr,
    input  wire       rx_rd,
    output wire [7:0] rx_rdata,
    output wire [5:0] rx_level,
    output wire       rx_full,
    output wire       rx_empty
);

    // Matching guard: this module has its own filelist and can be elaborated
    // on its own, so the range cannot live only in apb4_smbus.
    initial begin : param_check
        if (FIFO_DEPTH < 2 || FIFO_DEPTH > 63) begin
            $fatal(1, "smbus_byte_fifos: FIFO_DEPTH must be 2..63, got %0d", FIFO_DEPTH);
        end
    end

    wire w_clear;

    // rst_n goes to the FIFOs UNTOUCHED and the two software strobes are a
    // SYNCHRONOUS clear. Composing them into the reset by hand -
    // `rst_n && !soft_reset && !fifo_reset` - inverts under
    // RESET_ACTIVE_HIGH: asserting fifo_reset DE-asserted the reset and the
    // buffers kept their contents, and it put a decoded register bit
    // combinationally onto an asynchronous reset pin besides.
    assign w_clear = soft_reset || fifo_reset;

    simple_fifo #(
        .DATA_WIDTH (8),
        .DEPTH      (FIFO_DEPTH)
    ) u_tx_fifo (
        .clk        (clk),
        .rst_n      (rst_n),
        .clear      (w_clear),
        .wr_en      (tx_wr),
        .wr_data    (tx_wdata),
        .rd_en      (tx_rd),
        .rd_data    (tx_rdata),
        .full       (tx_full),
        .empty      (tx_empty),
        .count      (tx_level)
    );

    simple_fifo #(
        .DATA_WIDTH (8),
        .DEPTH      (FIFO_DEPTH)
    ) u_rx_fifo (
        .clk        (clk),
        .rst_n      (rst_n),
        .clear      (w_clear),
        .wr_en      (rx_wr),
        .wr_data    (rx_wdata),
        .rd_en      (rx_rd),
        .rd_data    (rx_rdata),
        .full       (rx_full),
        .empty      (rx_empty),
        .count      (rx_level)
    );

endmodule
