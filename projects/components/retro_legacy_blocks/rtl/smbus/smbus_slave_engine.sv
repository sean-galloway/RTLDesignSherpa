// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: smbus_slave_engine
// Purpose: Bit-level SMBus/I2C target engine - the half that ANSWERS.
//
// Documentation: projects/components/retro_legacy_blocks/rtl/smbus/README.md
// Created: 2026-09-10
//
//==============================================================================
// WHY THIS IS NOT smbus_bit_phy
//==============================================================================
//   The master PHY OWNS the clock: it decides when SCL falls and how long each
//   phase lasts, and every primitive is a request it schedules. A target owns
//   none of that. It is a passenger on somebody else's clock, so its whole
//   structure is different: everything happens on an observed edge of SCL, and
//   the only thing it can impose on the bus is a pull-down - SDA to answer,
//   SCL to ask for time.
//
//   Trying to express that as another operation in the master PHY would mean a
//   module that is sometimes a clock source and sometimes not. Two engines,
//   one wire, is the honest shape.
//
//==============================================================================
// WHAT IT DRIVES, AND WHEN
//==============================================================================
//   Open-drain, exactly as the master PHY: this module never drives a 1. It
//   emits two PULL-DOWN requests, and smbus_core wired-ANDs them with the
//   master's. sda_drive_low answers (ACK, or a transmitted 0); scl_drive_low
//   stretches the clock.
//
//   SDA ONLY EVER CHANGES WHILE SCL IS LOW. Every drive decision in here is
//   taken on a falling edge of the synchronized SCL and held until the next
//   one, because a transition while SCL is high is a START or a STOP, not
//   data. That rule is what makes the engine safe to read: if a line movement
//   is not on a falling edge, it is a bug.
//
//==============================================================================
// OWNERSHIP
//==============================================================================
//   One engine on the wire at a time. While the block's own master engine is
//   running, this one is inhibited - it would otherwise see its master's START
//   and, if the master happened to address this block's own address, answer
//   itself. The other direction is enforced in smbus_core: a master START is
//   refused while this engine is mid-transaction.
//
//==============================================================================
// PEC WITHOUT KNOWING THE LENGTH
//==============================================================================
//   A target does not know how long a transfer is; the protocol does, and the
//   protocol lives in software. The CRC-8 property removes the need to know:
//
//     WRITES - the running CRC covers the address byte and every data byte,
//     and a correct trailing PEC byte drives it to ZERO. So "PEC good" is
//     "the running value is 0 at the STOP", with no byte counting anywhere.
//
//     READS - when the TX FIFO runs dry and PEC is enabled, the byte sent is
//     the running CRC itself, which is exactly the PEC the master expects.
//     Software decides the length by how many bytes it queues.
//
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module smbus_slave_engine (
    input  wire       clk,
    input  wire       rst_n,             // Active-low reset (house convention)

    //--- Synchronized bus, from smbus_bit_phy. One synchronizer per line for
    //--- the whole block: a second pair here could resolve the same edge a
    //--- cycle apart from the master's and the two engines would disagree
    //--- about when a START happened.
    input  wire       sda_sync,
    input  wire       scl_sync,

    //--- Open-drain pull-down requests, wired-AND'd in smbus_core
    output wire       sda_drive_low,
    output wire       scl_drive_low,

    //--- Configuration
    input  wire       cfg_slave_en,
    input  wire [6:0] cfg_own_addr,
    input  wire       cfg_own_addr_en,
    input  wire       cfg_gc_en,         // answer the general call (0x00)
    input  wire       cfg_nack_all,      // software is busy: NAK my address
    input  wire       cfg_pec_en,        // maintain, check and append the PEC
    input  wire       cfg_stretch_en,    // hold SCL while the TX FIFO is dry
    input  wire       cfg_soft_reset,

    //--- Ownership
    input  wire       master_active,     // the master engine owns the wire

    //--- RX path (shared RX FIFO)
    output wire [7:0] rx_wdata,
    output wire       rx_wr,
    input  wire       rx_full,

    //--- TX path (shared TX FIFO)
    input  wire [7:0] tx_rdata,
    input  wire       tx_empty,
    output wire       tx_rd,

    //--- Status
    // ADDRESSED is also the ownership claim smbus_core arbitrates on: see
    // the note at the assign below for why it is not "a transfer is in
    // progress on the wire".
    output wire       addressed,         // currently addressed, level
    output wire       rd_not_wr,         // direction of the current transfer
    output wire       stretching,        // holding SCL, waiting for software
    output wire       done,              // one cycle, at the closing STOP
    output wire       pec_error,         // sticky until the next START
    output wire [7:0] pec_value
);

    //=========================================================================
    // Bus edges
    //=========================================================================
    // START and STOP are the two transitions of SDA that happen while SCL is
    // HIGH; everything else is data. Both are decoded from the synchronized
    // lines, so they are late by the synchronizer depth and not by anything
    // else - the master PHY sees them at the same instant this does.

    logic r_scl_d;
    logic r_sda_d;
    logic w_scl_rise;
    logic w_scl_fall;
    logic w_start;
    logic w_stop;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_scl_d <= 1'b1;        // idle bus is released = high
            r_sda_d <= 1'b1;
        end else begin
            r_scl_d <= scl_sync;
            r_sda_d <= sda_sync;
        end
    )

    assign w_scl_rise = scl_sync && !r_scl_d;
    assign w_scl_fall = !scl_sync && r_scl_d;
    assign w_start    = scl_sync && r_scl_d &&  r_sda_d && !sda_sync;
    assign w_stop     = scl_sync && r_scl_d && !r_sda_d &&  sda_sync;

    //=========================================================================
    // State
    //=========================================================================

    typedef enum logic [3:0] {
        S_IDLE     = 4'd0,   // no transfer in progress
        S_ADDR     = 4'd1,   // receiving the address byte
        S_ADDR_ACK = 4'd2,   // driving the answer to the address
        S_RX       = 4'd3,   // receiving a data byte
        S_RX_ACK   = 4'd4,   // driving the answer to a data byte
        S_TX_LOAD  = 4'd5,   // fetching a byte to send; may stretch here
        S_TX       = 4'd6,   // shifting a byte out
        S_TX_ACK   = 4'd7,   // reading the master's answer
        S_IGNORE   = 4'd8    // somebody else's transfer, or we NAK'd
    } slave_state_t;

    slave_state_t r_state;
    logic [3:0]   r_bit_cnt;
    logic [7:0]   r_shift;
    logic [7:0]   r_tx_shift;
    logic         r_sda_low;
    logic         r_scl_low;
    logic         r_ack_addr;
    logic         r_ack_data;
    logic         r_rd_not_wr;
    logic         r_sent_any;      // at least one byte transmitted this read
    logic         r_pec_error;
    logic         r_rx_wr;
    logic [7:0]   r_rx_wdata;
    logic         r_tx_rd;
    logic         r_done;

    logic [7:0]   w_addr_byte;
    logic [7:0]   w_rx_byte;
    logic         w_addr_hit;
    logic         w_enabled;
    logic         w_pec_clear;
    logic         w_pec_valid;
    logic [7:0]   w_pec_data;
    logic [7:0]   w_pec;
    logic         w_tx_have_byte;
    logic [7:0]   w_tx_next;

    // The byte the current SCL rise completes. On the eighth rise the first
    // seven bits are in r_shift and the eighth is still on the wire, so the
    // comparison has to be made against the concatenation rather than against
    // r_shift, which does not hold the whole byte until a cycle later.
    assign w_rx_byte   = {r_shift[6:0], sda_sync};
    assign w_addr_byte = w_rx_byte;

    // ADDRESS MATCH. Own address when enabled, plus the general call at 0x00
    // when software asks for it. The general call is a WRITE address by
    // definition, so a read to 0x00 is not a hit.
    assign w_enabled = cfg_slave_en && !cfg_soft_reset;
    assign w_addr_hit =
        (cfg_own_addr_en && (w_addr_byte[7:1] == cfg_own_addr)) ||
        (cfg_gc_en && (w_addr_byte[7:0] == 8'h00));

    //=========================================================================
    // PEC
    //=========================================================================
    // Cleared when a transfer BEGINS, not at every START: a repeated START is
    // inside one transfer and its address byte is covered too, which is what
    // makes a block read's PEC match the master's.

    assign w_pec_clear = cfg_soft_reset ||
                         (w_start && (r_state == S_IDLE || r_state == S_IGNORE));

    smbus_pec u_slave_pec (
        .clk        (clk),
        .rst_n      (rst_n),
        .enable     (cfg_pec_en),
        .clear      (w_pec_clear),
        .data_in    (w_pec_data),
        .data_valid (w_pec_valid),
        .crc_out    (w_pec)
    );

    //=========================================================================
    // Transmit source
    //=========================================================================
    // A queued byte first. With the FIFO dry and PEC on, the running CRC IS
    // the byte the master is waiting for, so send it rather than stretching
    // for a byte software cannot know how to compute. r_sent_any keeps that
    // from firing on the FIRST byte of a read, where an empty FIFO means
    // software has not filled it yet, not that the data is finished.

    assign w_tx_have_byte = !tx_empty || (cfg_pec_en && r_sent_any);
    assign w_tx_next      = !tx_empty ? tx_rdata : w_pec;

    //=========================================================================
    // The engine
    //=========================================================================

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n) || cfg_soft_reset) begin
            r_state      <= S_IDLE;
            r_bit_cnt    <= 4'd0;
            r_shift      <= 8'h00;
            r_tx_shift   <= 8'h00;
            r_sda_low    <= 1'b0;
            r_scl_low    <= 1'b0;
            r_ack_addr   <= 1'b0;
            r_ack_data   <= 1'b0;
            r_rd_not_wr  <= 1'b0;
            r_sent_any   <= 1'b0;
            r_pec_error  <= 1'b0;
            r_rx_wr      <= 1'b0;
            r_rx_wdata   <= 8'h00;
            r_tx_rd      <= 1'b0;
            r_done       <= 1'b0;
        end else begin
            // One-cycle pulses default off; the branches below raise them.
            r_rx_wr      <= 1'b0;
            r_tx_rd      <= 1'b0;
            r_done       <= 1'b0;

            if (w_stop) begin
                // END OF TRANSFER. The PEC verdict is taken here because this
                // is the only moment a target knows the transfer is over: a
                // correct trailing PEC byte has driven the running CRC to
                // zero by now.
                if (r_state != S_IDLE && r_state != S_IGNORE) begin
                    r_done <= 1'b1;
                    if (cfg_pec_en && !r_rd_not_wr) begin
                        r_pec_error <= (w_pec != 8'h00);
                    end
                end
                r_state   <= S_IDLE;
                r_sda_low <= 1'b0;
                r_scl_low <= 1'b0;
            end else if (w_start) begin
                // START or repeated START. Inhibited while our own master
                // engine owns the wire - it would be this block answering
                // itself.
                r_sda_low <= 1'b0;
                r_scl_low <= 1'b0;
                r_bit_cnt <= 4'd0;
                if (w_enabled && !master_active) begin
                    r_state <= S_ADDR;
                    if (r_state == S_IDLE || r_state == S_IGNORE) begin
                        r_pec_error <= 1'b0;
                        r_sent_any  <= 1'b0;
                    end
                end else begin
                    r_state <= S_IGNORE;
                end
            end else begin
                unique case (r_state)
                    // Two labels, not one `S_IDLE, S_IGNORE:` item: a
                    // comma at the top level of an ALWAYS_FF_RST body is a
                    // macro argument separator, not SystemVerilog.
                    S_IDLE: begin
                        r_sda_low <= 1'b0;
                        r_scl_low <= 1'b0;
                    end

                    S_IGNORE: begin
                        r_sda_low <= 1'b0;
                        r_scl_low <= 1'b0;
                    end

                    S_ADDR: begin
                        if (w_scl_rise) begin
                            r_shift   <= w_rx_byte;
                            r_bit_cnt <= r_bit_cnt + 4'd1;
                            if (r_bit_cnt == 4'd7) begin
                                // ACK POLICY. We answer our own address unless
                                // software has said it is busy. A NAK here is
                                // the target's only way to say "not now"
                                // without holding the bus.
                                r_ack_addr  <= w_addr_hit && !cfg_nack_all;
                                // The general call is address 0x00, whose
                                // direction bit is already 0, so this needs
                                // no special case.
                                r_rd_not_wr <= w_addr_byte[0];
                            end
                        end else if (w_scl_fall && (r_bit_cnt == 4'd8)) begin
                            r_sda_low <= r_ack_addr;
                            r_state   <= S_ADDR_ACK;
                        end
                    end

                    S_ADDR_ACK: begin
                        if (w_scl_fall) begin
                            r_sda_low <= 1'b0;
                            r_bit_cnt <= 4'd0;
                            if (!r_ack_addr) begin
                                r_state <= S_IGNORE;
                            end else if (r_rd_not_wr) begin
                                r_state <= S_TX_LOAD;
                            end else begin
                                r_state <= S_RX;
                            end
                        end
                    end

                    S_RX: begin
                        if (w_scl_rise) begin
                            r_shift   <= w_rx_byte;
                            r_bit_cnt <= r_bit_cnt + 4'd1;
                            if (r_bit_cnt == 4'd7) begin
                                // A full FIFO is answered with a NAK rather
                                // than a silently dropped byte: the master
                                // has to be told, or it writes into a target
                                // that is not listening.
                                r_ack_data <= !rx_full;
                                if (!rx_full) begin
                                    r_rx_wr    <= 1'b1;
                                    r_rx_wdata <= w_rx_byte;
                                end
                            end
                        end else if (w_scl_fall && (r_bit_cnt == 4'd8)) begin
                            r_sda_low <= r_ack_data;
                            r_state   <= S_RX_ACK;
                        end
                    end

                    S_RX_ACK: begin
                        if (w_scl_fall) begin
                            r_sda_low <= 1'b0;
                            r_bit_cnt <= 4'd0;
                            r_state   <= r_ack_data ? S_RX : S_IGNORE;
                        end
                    end

                    S_TX_LOAD: begin
                        // SCL is low here in every path that reaches this
                        // state, so pulling it low is a legal stretch rather
                        // than a line movement.
                        if (w_tx_have_byte) begin
                            r_tx_shift <= {w_tx_next[6:0], 1'b0};
                            r_sda_low  <= !w_tx_next[7];
                            r_tx_rd    <= !tx_empty;
                            r_sent_any <= 1'b1;
                            r_scl_low  <= 1'b0;
                            r_bit_cnt  <= 4'd1;
                            r_state    <= S_TX;
                        end else if (cfg_stretch_en) begin
                            r_scl_low <= 1'b1;
                        end else begin
                            // No stretch allowed and nothing to send: all
                            // ones, which is what an unprogrammed target on a
                            // real bus looks like.
                            r_tx_shift <= 8'hFE;
                            r_sda_low  <= 1'b0;
                            r_sent_any <= 1'b1;
                            r_bit_cnt  <= 4'd1;
                            r_state    <= S_TX;
                        end
                    end

                    S_TX: begin
                        if (w_scl_fall) begin
                            if (r_bit_cnt == 4'd8) begin
                                r_sda_low <= 1'b0;   // release for the ACK bit
                                r_state   <= S_TX_ACK;
                            end else begin
                                r_sda_low  <= !r_tx_shift[7];
                                r_tx_shift <= {r_tx_shift[6:0], 1'b0};
                                r_bit_cnt  <= r_bit_cnt + 4'd1;
                            end
                        end
                    end

                    S_TX_ACK: begin
                        if (w_scl_rise) begin
                            // The master's answer. A NAK means it has all it
                            // wanted, and the next thing on the bus is its
                            // STOP or repeated START.
                            r_ack_data <= !sda_sync;
                        end else if (w_scl_fall) begin
                            r_bit_cnt <= 4'd0;
                            r_state   <= r_ack_data ? S_TX_LOAD : S_IGNORE;
                        end
                    end

                    default: r_state <= S_IDLE;
                endcase
            end
        end
    )

    //=========================================================================
    // PEC feed
    //=========================================================================
    // Every byte that crosses the wire in either direction, address bytes
    // included. The address is fed at the same edge the match is decided, and
    // a transmitted byte as it is loaded.

    always_comb begin
        w_pec_valid = 1'b0;
        w_pec_data  = 8'h00;
        if (r_rx_wr) begin
            w_pec_valid = 1'b1;
            w_pec_data  = r_rx_wdata;
        end else if ((r_state == S_ADDR) && w_scl_rise && (r_bit_cnt == 4'd7)
                     && w_addr_hit && !cfg_nack_all) begin
            w_pec_valid = 1'b1;
            w_pec_data  = w_addr_byte;
        end else if ((r_state == S_TX_LOAD) && w_tx_have_byte) begin
            w_pec_valid = 1'b1;
            w_pec_data  = w_tx_next;
        end
    end

    //=========================================================================
    // Outputs
    //=========================================================================

    assign sda_drive_low = r_sda_low;
    assign scl_drive_low = r_scl_low;
    // ADDRESSED means THIS target answered, so the ACK bit of an address we
    // did not match does not count even though the engine is still walking
    // through it.
    //
    // It is deliberately NOT "a transfer is in progress on the wire". The
    // ownership question smbus_core asks is whether the two halves of THIS
    // block would collide, and they only can when this half is actually
    // answering. Claiming the wire for any observed START also claims it for
    // a STUCK one -- SDA pulled low under a high SCL looks exactly like a
    // START that never ends -- and the master could then never run the bus
    // recovery that exists to clear precisely that condition. Whether the bus
    // is busy is the master PHY's own question, and it answers it with the
    // bus-free wait in front of every START.
    assign addressed     = r_ack_addr && (r_state != S_IDLE) &&
                           (r_state != S_IGNORE) && (r_state != S_ADDR);
    assign rd_not_wr     = r_rd_not_wr;
    assign stretching    = r_scl_low;
    assign done          = r_done;
    assign pec_error     = r_pec_error;
    assign pec_value     = w_pec;
    assign rx_wdata      = r_rx_wdata;
    assign rx_wr         = r_rx_wr;
    assign tx_rd         = r_tx_rd;

endmodule : smbus_slave_engine
