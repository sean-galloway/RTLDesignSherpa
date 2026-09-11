// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: smbus_int_status
// Purpose: The sticky SMBUS_INT_STATUS bits, owned in hardware.
//
// EVERY BIT IS SET BY THE RISING EDGE OF ITS CONDITION AND CLEARED ONLY BY A
// DECODED W1C WRITE. That includes the two FIFO threshold bits: their RDL
// description says "(W1C)", and a W1C bit that is really a level is not a W1C
// bit at all. Wiring a live level straight into the register field - what
// this block used to do with tx_fifo_empty and !rx_fifo_empty - re-asserts
// the bit on the clock after software clears it, which makes the whole
// register decorative and the interrupt impossible to deassert.
//
// SET WINS over a simultaneous clear. Software clearing bit N in the same
// cycle a new event sets bit N must keep the event: losing it means an
// interrupt that never comes back, which is a hang, whereas an extra
// interrupt is a wasted read.
//
// This is a separate module because "sticky, edge-set, W1C-cleared" is the
// contract, not an implementation detail of the SMBus FSM, and because the
// register block's own field is only a live MIRROR of what lives here.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module smbus_int_status (
    input  wire       clk,
    input  wire       rst_n,
    // Synchronous clear (SMBUS_CONTROL.soft_reset). A decoded register bit
    // must not be ANDed into the reset: the polarity is build-defined, so a
    // hand-composed `rst_n && !clear` DE-asserts reset under
    // RESET_ACTIVE_HIGH and the sticky bits survive the soft reset they were
    // supposed to be cleared by.
    input  wire       clear,

    // Conditions, in SMBUS_INT_STATUS bit order
    input  wire       cond_complete,     // bit 0: transaction complete
    input  wire       cond_error,        // bit 1: bus/timeout/PEC error
    input  wire       cond_tx_thresh,    // bit 2: TX FIFO below threshold
    input  wire       cond_rx_thresh,    // bit 3: RX FIFO above threshold
    input  wire       cond_slave_addr,   // bit 4: addressed as slave
    input  wire       cond_slave_rx,     // bit 5: slave took a byte off the bus
    input  wire       cond_slave_tx,     // bit 6: slave needs a byte to send
    input  wire       cond_slave_done,   // bit 7: slave transfer ended at STOP

    input  wire [7:0] sw_clr,            // decoded W1C mask, one cycle
    output wire [7:0] int_status
);

    logic [7:0] r_status;
    logic [7:0] r_cond_d;
    logic       r_armed;
    logic [7:0] w_cond;
    logic [7:0] w_set;

    assign w_cond = {cond_slave_done, cond_slave_tx, cond_slave_rx,
                     cond_slave_addr, cond_rx_thresh, cond_tx_thresh,
                     cond_error, cond_complete};

    // The edge detector is ARMED one cycle after reset. r_cond_d resets to
    // zero, but a condition can be TRUE at time zero - tx_fifo_empty always
    // is, because an empty FIFO is empty - and the first comparison would
    // then see a rising edge that never happened and set the bit with no
    // access having taken place. INT_STATUS must read 0 out of reset.
    assign w_set = r_armed ? (w_cond & ~r_cond_d) : 8'h00;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n) || clear) begin
            r_status <= 8'h00;
            r_cond_d <= 8'h00;
            r_armed  <= 1'b0;
        end else begin
            r_cond_d <= w_cond;
            r_armed  <= 1'b1;
            r_status <= (r_status & ~sw_clr) | w_set;
        end
    )

    assign int_status = r_status;

endmodule
