// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: smbus_flow_rules
// Purpose: Given where the master sequencer is, what happens next.
//
// Every combinational rule the sequencer consults - which states are byte
// states, when a byte is finished, whether a received byte is ACKed or NAKed,
// when the TX FIFO is popped, and when either FIFO has run out. They are here
// rather than inline because they are a CONTRACT, not an implementation
// detail, and because three of the four defects they encode were invisible
// while they were scattered through a 900-line FSM.
//
// THE TX LOAD/POP DISCIPLINE is the one worth reading twice. simple_fifo is
// fifo_sync REGISTERED(0), so its read data is the COMBINATIONAL head: the
// value captured on the edge that also asserts rd_en is the pre-pop head -
// exactly the byte being loaded. So every FIFO-sourced byte load pops in its
// OWN cycle, and nothing else pops. Loading without popping sends the same
// byte twice (Write Word did, for both its bytes). Popping a cycle later than
// the load puts every load one pop behind the pointer (Block Write repeated
// its first payload byte and dropped its last). There is no third option.
//
// It is deliberately NOT "always the FIFO": a Write Byte has no FIFO traffic
// at all, and a Block Write's first transmitted byte is the count.
//
// THE FIFO EXHAUSTION RULES:
//   TX UNDERRUN - more bytes claimed than staged. Fabricating one would put a
//   value on the wire nobody asked to send, so the transfer is abandoned.
//   RX OVERRUN is checked in smbus_core, at the point the byte would be
//   stored, because "is there room" has to be asked BEFORE the store and for
//   EVERY data byte including the last - a full fifo_sync drops the write
//   silently, so a terminal byte with no room simply vanished.

`timescale 1ns / 1ps

module smbus_flow_rules #(
    parameter int FIFO_DEPTH = 32
) (
    // Where the sequencer is
    input  wire [3:0] master_state,
    input  wire [3:0] bit_counter,
    // Only [6:0] is read: bit 7 is the bit already on the wire.
    /* verilator lint_off UNUSEDSIGNAL */
    input  wire [7:0] shift_reg,
    /* verilator lint_on UNUSEDSIGNAL */
    input  wire       phy_rx_bit,
    input  wire [5:0] byte_counter,
    input  wire [5:0] bytes_total,
    input  wire       ack_valid,
    input  wire       ack_bit,
    input  wire       pec_en,
    input  wire       pec_phase,
    input  wire       count_sent,

    // What kind of transaction it is (from smbus_trans_decode)
    input  wire       sends_count,
    input  wire       needs_restart,
    input  wire       tx_from_fifo,

    // What the FIFOs say
    input  wire       tx_fifo_empty,

    // What happens next
    output wire       byte_tx_state,
    output wire       byte_rx_state,
    output wire       ack_state,
    output wire [3:0] tx_ack_state,
    output wire       byte_last_bit,
    output wire [7:0] rx_byte,
    output wire [7:0] next_tx_byte,
    output wire [5:0] rx_count_clamped,
    output wire       more_data,
    output wire       send_ack,
    output wire       tx_underrun,
    output wire       tx_fifo_rd
);

    // Mirrors smbus_core's master_state_t. The encoding is ABI - it is what
    // SMBUS_STATUS.fsm_state exposes - so naming it twice is safe; deriving
    // it from something else would not be.
    localparam logic [3:0] M_ADDR = 4'h2, M_ADDR_ACK = 4'h3;
    localparam logic [3:0] M_CMD  = 4'h4, M_CMD_ACK  = 4'h5;
    localparam logic [3:0] M_DATA_WR = 4'h6, M_DATA_WR_ACK = 4'h7;
    localparam logic [3:0] M_DATA_RD = 4'h8;
    localparam logic [3:0] M_PEC_WR  = 4'hA, M_PEC_WR_ACK = 4'hB;
    localparam logic [3:0] M_PEC_RD  = 4'hC;

    logic [3:0] w_tx_ack_state;
    logic       w_tx_load_now;

    assign byte_tx_state = (master_state == M_ADDR)    || (master_state == M_CMD) ||
                           (master_state == M_DATA_WR) || (master_state == M_PEC_WR);

    assign byte_rx_state = (master_state == M_DATA_RD) || (master_state == M_PEC_RD);

    assign ack_state     = (master_state == M_ADDR_ACK)    ||
                           (master_state == M_CMD_ACK)     ||
                           (master_state == M_DATA_WR_ACK) ||
                           (master_state == M_PEC_WR_ACK);

    // Which ACK state each transmit-a-byte state waits in.
    always_comb begin
        unique case (master_state)
            M_ADDR:    w_tx_ack_state = M_ADDR_ACK;
            M_CMD:     w_tx_ack_state = M_CMD_ACK;
            M_DATA_WR: w_tx_ack_state = M_DATA_WR_ACK;
            default:   w_tx_ack_state = M_PEC_WR_ACK;
        endcase
    end
    assign tx_ack_state = w_tx_ack_state;

    assign byte_last_bit = (bit_counter == 4'd7);
    assign rx_byte       = {shift_reg[6:0], phy_rx_bit};
    assign next_tx_byte  = {shift_reg[6:0], 1'b0};

    // A slave-supplied length of 0 or > the FIFO depth cannot be honoured.
    // The >DEPTH test comes FIRST and looks at the WHOLE byte: a count of
    // 0x40 has all-zero low six bits, so testing the truncated field first
    // read 64 as 0 and clamped a too-long block to one byte.
    assign rx_count_clamped = (rx_byte > 8'(FIFO_DEPTH)) ? 6'(FIFO_DEPTH) :
                              (rx_byte[5:0] == 6'd0)     ? 6'd1 :
                                                           rx_byte[5:0];

    assign more_data = (byte_counter + 6'd1) < bytes_total;

    // ACK a received byte if another follows; NAK the last one.
    assign send_ack  = more_data || (pec_en && !pec_phase);

    assign w_tx_load_now = ((master_state == M_CMD_ACK) && ack_valid && !ack_bit &&
                          !needs_restart && !sends_count) ||
                         ((master_state == M_DATA_WR_ACK) && ack_valid && !ack_bit &&
                          ((sends_count && !count_sent) || more_data));

    assign tx_underrun = w_tx_load_now && tx_from_fifo && tx_fifo_empty;
    assign tx_fifo_rd  = w_tx_load_now && tx_from_fifo && !tx_underrun;

endmodule
