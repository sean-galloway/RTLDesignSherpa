// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: uart_16550_core
// Purpose: UART 16550 Core - TX/RX with FIFOs
//
// Description:
//   Core UART logic implementing NS16550-compatible serial communication:
//   the baud generator, the TX FIFO and transmitter, the RX FIFO and
//   receiver, and the per-character line status. Modem control lives in
//   uart_16550_modem and the interrupt logic in uart_16550_intr; both are
//   instantiated here.
//
// Features:
//   - 16-byte TX and RX FIFOs
//   - Programmable baud rate via 16-bit divisor
//   - 5/6/7/8 data bits
//   - 1, 1.5 (5-bit words) or 2 stop bits
//   - None/Odd/Even/Mark/Space parity
//   - Modem control signals (uart_16550_modem)
//   - Loopback mode
//   - FCR[0]=0 is real 16450 character mode: one holding register per side
//   - LSR[4:2] are the tags of the character being handed to the CPU
//   - A continuous break loads exactly one character
//   - Character timeout interrupt: NOT implemented (int_timeout tied 0)
//
// Documentation: projects/components/retro_legacy_blocks/rtl/uart_16550/README.md
// Created: 2025-11-29

`timescale 1ns / 1ps

`include "reset_defs.svh"

module uart_16550_core #(
    parameter int FIFO_DEPTH = 16,   // FIFO depth (16 for 16550)
    parameter int SYNC_STAGES = 2    // RX synchronizer stages
) (
    // Clock and Reset
    input  logic        clk,
    input  logic        rst_n,

    // Serial Interface
    input  logic        uart_rx,      // UART RX input
    output logic        uart_tx,      // UART TX output

    // Modem Control Inputs (directly from pins, active low on physical pins)
    input  logic        cts_n,        // Clear To Send (active low)
    input  logic        dsr_n,        // Data Set Ready (active low)
    input  logic        ri_n,         // Ring Indicator (active low)
    input  logic        dcd_n,        // Data Carrier Detect (active low)

    // Modem Control Outputs
    output logic        dtr_n,        // Data Terminal Ready (active low)
    output logic        rts_n,        // Request To Send (active low)
    output logic        out1_n,       // User output 1 (active low)
    output logic        out2_n,       // User output 2 / INT gate (active low)

    // Configuration from registers
    input  logic [15:0] cfg_divisor,           // Baud rate divisor
    input  logic [1:0]  cfg_word_length,       // 00=5, 01=6, 10=7, 11=8
    input  logic        cfg_stop_bits,         // 0=1, 1=1.5/2
    input  logic        cfg_parity_enable,
    input  logic        cfg_even_parity,
    input  logic        cfg_stick_parity,
    input  logic        cfg_set_break,
    input  logic        cfg_fifo_enable,
    input  logic [1:0]  cfg_rx_trigger,        // RX FIFO trigger level
    input  logic        cfg_dtr,
    input  logic        cfg_rts,
    input  logic        cfg_out1,
    input  logic        cfg_out2,
    input  logic        cfg_loopback,
    input  logic        cfg_afe,
    input  logic        cfg_dma_mode,   // FCR[3]: 0=single, 1=multi

    // 16550 interrupt enables (IER). Each source is gated independently: a
    // disabled source may be true in LSR/MSR and still not raise irq or be
    // reported by IIR.
    input  logic        cfg_rx_data_ie,
    input  logic        cfg_tx_empty_ie,
    input  logic        cfg_line_status_ie,
    input  logic        cfg_modem_ie,

    // Reading IIR clears the THR-empty interrupt when THR empty is the source
    // being reported (16550 rule).
    input  logic        iir_read,

    // FIFO Reset Commands (active high, self-clearing)
    input  logic        cmd_rx_fifo_reset,
    input  logic        cmd_tx_fifo_reset,

    // TX Data Interface
    input  logic [7:0]  tx_data,
    input  logic        tx_write,              // Write strobe to TX FIFO

    // RX Data Interface
    output logic [7:0]  rx_data,
    input  logic        rx_read,               // Read strobe from RX FIFO

    // Status to Registers
    output logic        sts_data_ready,        // RX data available
    output logic        sts_overrun_error,     // RX overrun
    output logic        sts_parity_error,      // Parity error
    output logic        sts_framing_error,     // Stop bit error
    output logic        sts_break_interrupt,   // Break detected
    output logic        sts_tx_holding_empty,  // TX holding register empty
    output logic        sts_tx_empty,          // TX completely empty
    output logic        sts_rx_fifo_error,     // Error in RX FIFO
    output logic        sts_delta_cts,         // CTS changed
    output logic        sts_delta_dsr,         // DSR changed
    output logic        sts_trailing_ri,       // RI trailing edge
    output logic        sts_delta_dcd,         // DCD changed
    output logic        sts_cts,               // Current CTS
    output logic        sts_dsr,               // Current DSR
    output logic        sts_ri,                // Current RI
    output logic        sts_dcd,               // Current DCD
    output logic [1:0]  sts_fifo_status,       // FIFO enabled status

    // Status clear commands
    input  logic        clr_overrun_error,
    input  logic        clr_parity_error,
    input  logic        clr_framing_error,
    input  logic        clr_break_interrupt,
    input  logic        clr_delta_cts,
    input  logic        clr_delta_dsr,
    input  logic        clr_trailing_ri,
    input  logic        clr_delta_dcd,

    // Interrupt Identification
    output logic        int_not_pending,       // 0 = interrupt pending
    output logic [1:0]  int_id,                // Interrupt ID
    output logic        int_timeout,           // Character timeout
    output logic        rxrdy_n,               // DMA receive request
    output logic        txrdy_n,               // DMA transmit request

    // Aggregate Interrupt
    output logic        irq
);

    // ========================================================================
    // Local Parameters
    // ========================================================================
    localparam int FIFO_ADDR_WIDTH = $clog2(FIFO_DEPTH);

    // The pointer/count arithmetic is modulo 2^(FIFO_ADDR_WIDTH+1) and the
    // memory indices take [FIFO_ADDR_WIDTH-1:0], which is only the same thing
    // when the depth is a power of two - at any other depth the pointers wrap
    // somewhere the memory does not. The RX trigger constants go up to 14, so
    // a depth under 16 cannot express the levels FCR advertises.
    initial begin : param_check
        if (FIFO_DEPTH < 16) begin
            // RX trigger levels go up to 14.
            $fatal(1, "uart_16550_core: FIFO_DEPTH must be >= 16, got %0d", FIFO_DEPTH);
        end
        if ((FIFO_DEPTH & (FIFO_DEPTH - 1)) != 0) begin
            $fatal(1, "uart_16550_core: FIFO_DEPTH must be a power of two, got %0d",
                   FIFO_DEPTH);
        end
    end

    // ========================================================================
    // Modem Control and Status
    // ========================================================================
    // Synchronizers, the loopback substitution, the four MSR deltas and the
    // active-low outputs all live in uart_16550_modem. The delta flags leave
    // on this module's own sts_* ports and the interrupt block reads them
    // from there, so nothing in this file needs a local copy.

    // End of the current transmit bit time. Declared here because the TX
    // state machine above the RX section uses it; it is assigned with the
    // other bit-timing terms further down.
    logic       w_tx_phase_end;

    // Declared here because the modem instance below consumes it and the
    // interrupt block that produces it is instantiated further down.
    logic       w_rx_trigger_reached;

    uart_16550_modem #(
        .SYNC_STAGES     (SYNC_STAGES)
    ) u_modem (
        .clk             (clk),
        .rst_n           (rst_n),
        .cts_n           (cts_n),
        .dsr_n           (dsr_n),
        .ri_n            (ri_n),
        .dcd_n           (dcd_n),
        .dtr_n           (dtr_n),
        .rts_n           (rts_n),
        .out1_n          (out1_n),
        .out2_n          (out2_n),
        .cfg_dtr         (cfg_dtr),
        .cfg_rts         (cfg_rts),
        .cfg_out1        (cfg_out1),
        .cfg_out2        (cfg_out2),
        .cfg_loopback    (cfg_loopback),
        .cfg_afe         (cfg_afe),
        .rx_hold_off     (w_rx_trigger_reached),
        .clr_delta_cts   (clr_delta_cts),
        .clr_delta_dsr   (clr_delta_dsr),
        .clr_trailing_ri (clr_trailing_ri),
        .clr_delta_dcd   (clr_delta_dcd),
        .sts_cts         (sts_cts),
        .sts_dsr         (sts_dsr),
        .sts_ri          (sts_ri),
        .sts_dcd         (sts_dcd),
        .sts_delta_cts   (sts_delta_cts),
        .sts_delta_dsr   (sts_delta_dsr),
        .sts_trailing_ri (sts_trailing_ri),
        .sts_delta_dcd   (sts_delta_dcd)
    );

    // ========================================================================
    // Baud Rate Generator
    // ========================================================================
    logic [15:0] r_baud_count;
    logic        w_baud_tick;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_baud_count <= '0;
        end else begin
            if (cfg_divisor == '0 || r_baud_count >= cfg_divisor - 1) begin
                r_baud_count <= '0;
            end else begin
                r_baud_count <= r_baud_count + 1'b1;
            end
        end
    )

    assign w_baud_tick = (r_baud_count == '0);

    // ========================================================================
    // TX FIFO and Transmitter
    // ========================================================================
    // FPGA memory attributes are mandatory on every memory array (component
    // rule #0.2). "auto" because the depth is a parameter: at 16 the vendor
    // picks distributed RAM, at 64+ it can pick a block.
`ifdef XILINX
    (* ram_style = "auto" *)
`elsif INTEL
    /* synthesis ramstyle = "AUTO" */
`endif
    logic [7:0] r_tx_fifo [FIFO_DEPTH];
    logic [FIFO_ADDR_WIDTH:0] r_tx_wr_ptr, r_tx_rd_ptr;
    logic w_tx_fifo_empty, w_tx_fifo_full;
    logic [FIFO_ADDR_WIDTH:0] w_tx_fifo_count;
    logic [FIFO_ADDR_WIDTH:0] w_tx_depth;

    // FCR[0]=0 IS 16450 CHARACTER MODE, NOT A COSMETIC BIT. cfg_fifo_enable
    // used to have two consumers - sts_fifo_status and the RX trigger - and
    // the datapath never looked at it, so both FIFOs stayed 16 deep whatever
    // FCR[0] said and character mode did not exist. With FIFOs off the depth
    // is one holding register on each side.
    assign w_tx_depth      = cfg_fifo_enable ? (FIFO_ADDR_WIDTH+1)'(FIFO_DEPTH)
                                             : (FIFO_ADDR_WIDTH+1)'(1);
    assign w_tx_fifo_count = r_tx_wr_ptr - r_tx_rd_ptr;
    assign w_tx_fifo_empty = (w_tx_fifo_count == 0);
    assign w_tx_fifo_full  = (w_tx_fifo_count >= w_tx_depth);

    // TX FIFO write
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_tx_wr_ptr <= '0;
        end else if (cmd_tx_fifo_reset) begin
            r_tx_wr_ptr <= '0;
        end else if (tx_write) begin
            if (!w_tx_fifo_full) begin
                r_tx_fifo[r_tx_wr_ptr[FIFO_ADDR_WIDTH-1:0]] <= tx_data;
                r_tx_wr_ptr <= r_tx_wr_ptr + 1'b1;
            end else if (!cfg_fifo_enable) begin
                // Character mode: THR is a single holding register, so a
                // second write OVERWRITES the byte still waiting to be
                // loaded into the shifter. It does not queue (there is
                // nowhere to queue it) and it is not silently dropped.
                r_tx_fifo[r_tx_rd_ptr[FIFO_ADDR_WIDTH-1:0]] <= tx_data;
            end
        end
    )

    // TX State Machine
    typedef enum logic [2:0] {
        TX_IDLE,
        TX_START,
        TX_DATA,
        TX_PARITY,
        TX_STOP1,
        TX_STOP2
    } tx_state_t;

    tx_state_t r_tx_state;
    logic [7:0] r_tx_shift;
    logic [2:0] r_tx_bit_idx;
    logic [3:0] r_tx_baud_cnt;   // 16x oversample counter
    logic       r_tx_parity;
    logic [2:0] w_tx_last_bit;

    // Number of data bits based on word length
    always_comb begin
        unique case (cfg_word_length)
            2'b00: w_tx_last_bit = 3'd4;  // 5 bits
            2'b01: w_tx_last_bit = 3'd5;  // 6 bits
            2'b10: w_tx_last_bit = 3'd6;  // 7 bits
            2'b11: w_tx_last_bit = 3'd7;  // 8 bits
        endcase
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_tx_state    <= TX_IDLE;
            r_tx_shift    <= '0;
            r_tx_bit_idx  <= '0;
            r_tx_baud_cnt <= '0;
            r_tx_parity   <= 1'b0;
            r_tx_rd_ptr   <= '0;
        end else begin
            // FCR[2] RESETS THE FIFO, NOT THE TRANSMITTER. This branch used
            // to force r_tx_state <= TX_IDLE, which cut whatever character
            // was on the wire in half. The datasheet clears the FIFO
            // counter and pointers only; the character already in the shift
            // register finishes, and the transmitter then finds the FIFO
            // empty and stops. Placed after the state machine so the
            // pointer reset wins over a same-cycle FIFO load without
            // freezing the shifter for the duration of the strobe.
            if (w_baud_tick) begin
                // 16x oversample: every bit time is 16 ticks, except the
                // second stop bit of a 5-bit word, which is half a bit time
                // (1.5 stop bits, PC16550D). Zeroing the counter on the phase
                // end rather than letting it wrap is what keeps the next
                // start bit aligned after a half-length phase.
                if (w_tx_phase_end) begin
                    r_tx_baud_cnt <= '0;
                    case (r_tx_state)
                        TX_IDLE: begin
                            // Auto flow control: do not start a character
                            // while the far end is holding CTS off. The
                            // character already in the shifter always
                            // finishes; AFE gates the START, not the frame.
                            if (!w_tx_fifo_empty && (!cfg_afe || sts_cts)) begin
                                r_tx_shift  <= r_tx_fifo[r_tx_rd_ptr[FIFO_ADDR_WIDTH-1:0]];
                                r_tx_rd_ptr <= r_tx_rd_ptr + 1'b1;
                                r_tx_state  <= TX_START;
                                r_tx_parity <= cfg_even_parity ? 1'b0 : 1'b1;
                            end
                        end

                        TX_START: begin
                            r_tx_state   <= TX_DATA;
                            r_tx_bit_idx <= '0;
                        end

                        TX_DATA: begin
                            r_tx_parity <= r_tx_parity ^ r_tx_shift[0];
                            r_tx_shift  <= {1'b0, r_tx_shift[7:1]};

                            if (r_tx_bit_idx == w_tx_last_bit) begin
                                if (cfg_parity_enable)
                                    r_tx_state <= TX_PARITY;
                                else
                                    r_tx_state <= TX_STOP1;
                            end else begin
                                r_tx_bit_idx <= r_tx_bit_idx + 1'b1;
                            end
                        end

                        TX_PARITY: begin
                            r_tx_state <= TX_STOP1;
                        end

                        TX_STOP1: begin
                            if (cfg_stop_bits) begin
                                // Two stop bits for 6/7/8-bit words, and the
                                // half-length second one for a 5-bit word.
                                r_tx_state <= TX_STOP2;
                            end else begin
                                r_tx_state <= TX_IDLE;
                            end
                        end

                        TX_STOP2: begin
                            r_tx_state <= TX_IDLE;
                        end

                        default: r_tx_state <= TX_IDLE;
                    endcase
                end else begin
                    r_tx_baud_cnt <= r_tx_baud_cnt + 1'b1;
                end
            end

            if (cmd_tx_fifo_reset) begin
                r_tx_rd_ptr <= '0;
            end
        end
    )

    // TX output
    logic w_tx_bit;
    always_comb begin
        if (cfg_set_break) begin
            w_tx_bit = 1'b0;  // Break condition
        end else begin
            case (r_tx_state)
                TX_IDLE:   w_tx_bit = 1'b1;  // Idle high
                TX_START:  w_tx_bit = 1'b0;  // Start bit
                TX_DATA:   w_tx_bit = r_tx_shift[0];
                TX_PARITY: w_tx_bit = cfg_stick_parity ? ~cfg_even_parity : r_tx_parity;
                TX_STOP1:  w_tx_bit = 1'b1;  // Stop bit
                TX_STOP2:  w_tx_bit = 1'b1;  // Stop bit
                default:   w_tx_bit = 1'b1;
            endcase
        end
    end

    assign uart_tx = cfg_loopback ? 1'b1 : w_tx_bit;

    // TX status
    assign sts_tx_holding_empty = w_tx_fifo_empty;
    assign sts_tx_empty = w_tx_fifo_empty && (r_tx_state == TX_IDLE);

    // ========================================================================
    // RX Synchronizer and Receiver
    // ========================================================================
    logic r_rx_sync [SYNC_STAGES];
    logic w_rx_in;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < SYNC_STAGES; i++) begin
                r_rx_sync[i] <= 1'b1;
            end
        end else begin
            r_rx_sync[0] <= uart_rx;
            for (int i = 1; i < SYNC_STAGES; i++) begin
                r_rx_sync[i] <= r_rx_sync[i-1];
            end
        end
    )

    assign w_rx_in = cfg_loopback ? w_tx_bit : r_rx_sync[SYNC_STAGES-1];

    // RX FIFO
`ifdef XILINX
    (* ram_style = "auto" *)
`elsif INTEL
    /* synthesis ramstyle = "AUTO" */
`endif
    logic [10:0] r_rx_fifo [FIFO_DEPTH];  // 8 data + parity_err + frame_err + break
    logic [FIFO_ADDR_WIDTH:0] r_rx_wr_ptr, r_rx_rd_ptr;
    // Count of FIFO entries carrying a PE/FE/BI tag. LSR[7] is an
    // aggregate over the WHOLE FIFO (PC16550D: "at least one parity
    // error, framing error or break indication in the FIFO"), so it
    // cannot be read off the entry at the read pointer - that entry
    // is clean whenever a tagged character is queued behind one.
    logic [FIFO_ADDR_WIDTH:0] r_rx_err_count;
    logic w_rx_fifo_empty, w_rx_fifo_full;
    logic [FIFO_ADDR_WIDTH:0] w_rx_fifo_count;
    logic [FIFO_ADDR_WIDTH:0] w_rx_depth;

    // Character mode (FCR[0]=0) is one receive holding register: a second
    // character arriving before the first is read is an overrun, which is
    // the whole point of the mode.
    assign w_rx_depth      = cfg_fifo_enable ? (FIFO_ADDR_WIDTH+1)'(FIFO_DEPTH)
                                             : (FIFO_ADDR_WIDTH+1)'(1);
    assign w_rx_fifo_count = r_rx_wr_ptr - r_rx_rd_ptr;
    assign w_rx_fifo_empty = (w_rx_fifo_count == 0);
    assign w_rx_fifo_full  = (w_rx_fifo_count >= w_rx_depth);

    // RX State Machine
    typedef enum logic [2:0] {
        RX_IDLE,
        RX_START,
        RX_DATA,
        RX_PARITY,
        RX_STOP
    } rx_state_t;

    rx_state_t r_rx_state;
    logic [7:0] r_rx_shift;
    logic [2:0] r_rx_bit_idx;
    logic [3:0] r_rx_baud_cnt;
    logic       r_rx_parity;
    logic       r_rx_parity_err;

    // FRAMING AND BREAK ARE COMBINATIONAL, not flops. They used to be
    // assigned in the RX_STOP branch and read back three lines later by the
    // FIFO write and the sticky sets - non-blocking, so every reader saw the
    // PRE-EDGE value, still 0, and LSR[3]/LSR[4], the FIFO entry error bits
    // and the line-status interrupt could never assert at all.
    logic       w_rx_frame_err;
    logic       w_rx_break;

    // RIGHT-JUSTIFIED, ZERO-FILLED. The receiver shifts LSB-first by
    // inserting at bit 7 and shifting right, so after N bits the character
    // sits in [7:8-N] - correct only at N=8. A 16550 right-justifies into
    // [N-1:0] and zero-fills above, which is what this block's own
    // transmitter already sends, so before this the two disagreed in loopback
    // at 5, 6 and 7 bits. Zero-filling also keeps the break test (all data
    // bits zero) working at every word length.
    logic [7:0] w_rx_char;
    logic       r_overrun_error;
    logic       r_parity_error;
    logic       r_framing_error;
    logic       r_break_interrupt;
    logic [2:0] w_rx_last_bit;
    logic       w_rx_expected_parity;

    // A CONTINUOUS BREAK IS ONE CHARACTER, NOT A STREAM OF THEM. RX_IDLE
    // re-arms on a still-low line, so a break held for N character times
    // framed N zero characters and eventually overran the FIFO. After a
    // break character is loaded this holds the receiver off until the line
    // returns to marking and a genuine new start bit arrives.
    logic       r_rx_break_hold;

    // Per-character error reporting. w_rx_char_done is the stop-bit sample
    // point; the push happens there when there is room, and in character
    // mode a character arriving with no room OVERWRITES the one still
    // sitting in RBR and destroys it (PC16550D, Overrun Error).
    logic       w_rx_char_done;
    logic       w_rx_push;
    // Character timeout (PC16550D): with the RX FIFO non-empty and neither a
    // new character nor a read for four character times, the timeout fires.
    // Counted in baud ticks, which are the 16x oversampling ticks, so one bit
    // time is 16 of them.
    logic [4:0]  w_char_bits;      // start + data + optional parity + stop(s)
    logic [12:0] w_timeout_target; // 4 character times, in baud ticks
    logic [12:0] r_timeout_cnt;
    logic        r_timeout_flag;
    logic       w_rx_overwrite;
    logic       w_rx_pop;
    logic       w_rx_new_top;
    logic [2:0] w_rx_new_tags;
    logic [2:0] w_rx_pop_tags;
    logic       w_rx_err_push;
    logic       w_rx_err_pop;

    always_comb begin
        unique case (cfg_word_length)
            2'b00:   w_rx_char = {3'b000, r_rx_shift[7:3]};   // 5 data bits
            2'b01:   w_rx_char = {2'b00,  r_rx_shift[7:2]};   // 6
            2'b10:   w_rx_char = {1'b0,   r_rx_shift[7:1]};   // 7
            default: w_rx_char = r_rx_shift;                  // 8
        endcase
    end

    assign w_rx_frame_err = !w_rx_in;                       // stop bit not high
    assign w_rx_break     = (w_rx_char == 8'h00) && !w_rx_in;

    assign w_rx_char_done = w_baud_tick && (r_rx_state == RX_STOP) &&
                            (r_rx_baud_cnt == 4'd15);
    assign w_rx_push      = w_rx_char_done && !w_rx_fifo_full;

    // 1 start + N data + optional parity + 1 or 2 stop. A 5-bit word with
    // two stop bits actually sends 1.5, and this rounds up: the timeout is a
    // "no activity for at least four character times" guard, so erring long
    // is the safe direction.
    assign w_tx_phase_end = ((r_tx_state == TX_STOP2) && (cfg_word_length == 2'b00))
                          ? (r_tx_baud_cnt == 4'd7)    // half a bit time
                          : (r_tx_baud_cnt == 4'd15);

    assign w_char_bits = 5'd1
                       + 5'({3'b0, cfg_word_length}) + 5'd5
                       + (cfg_parity_enable ? 5'd1 : 5'd0)
                       + (cfg_stop_bits ? 5'd2 : 5'd1);
    // 4 character times x 16 baud ticks per bit.
    assign w_timeout_target = 13'({w_char_bits, 6'b0});

    // The counter runs only while there is something to time out on, and any
    // activity on the FIFO restarts it: a character arriving, a character read
    // out, or software resetting the FIFO. Once the flag is set it stays set
    // until one of those happens, which is what makes it a level the interrupt
    // logic can gate rather than a pulse it has to catch.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_timeout_cnt  <= '0;
            r_timeout_flag <= 1'b0;
        end else if (cmd_rx_fifo_reset || w_rx_fifo_empty ||
                     w_rx_push || w_rx_pop) begin
            r_timeout_cnt  <= '0;
            r_timeout_flag <= 1'b0;
        end else if (!r_timeout_flag && w_baud_tick) begin
            if (r_timeout_cnt >= (w_timeout_target - 13'd1))
                r_timeout_flag <= 1'b1;
            else
                r_timeout_cnt <= r_timeout_cnt + 13'd1;
        end
    )
    assign w_rx_overwrite = w_rx_char_done && w_rx_fifo_full && !cfg_fifo_enable;
    assign w_rx_pop       = rx_read && !w_rx_fifo_empty;
    assign w_rx_new_tags  = {w_rx_break, w_rx_frame_err, r_rx_parity_err};
    assign w_rx_pop_tags  = r_rx_fifo[r_rx_rd_ptr[FIFO_ADDR_WIDTH-1:0]][10:8];
    // A tagged character entering or leaving the FIFO. The push term
    // repeats the RX_STOP store condition below; the character-mode
    // overwrite is deliberately not counted, because LSR[7] is
    // defined only in FIFO mode and the counter is held clear there.
    assign w_rx_err_push  = w_baud_tick && (r_rx_state == RX_STOP) &&
                            (r_rx_baud_cnt == 4'd15) && !w_rx_fifo_full &&
                            (w_rx_new_tags != 3'b000);
    assign w_rx_err_pop   = w_rx_pop && (w_rx_pop_tags != 3'b000);

    // The character the CPU is about to be handed changed: either one
    // arrived into an empty receiver, or a character-mode overwrite
    // replaced the one that was there.
    assign w_rx_new_top   = (w_rx_push && w_rx_fifo_empty) || w_rx_overwrite;

    // Number of data bits based on word length (for RX)
    always_comb begin
        unique case (cfg_word_length)
            2'b00: w_rx_last_bit = 3'd4;  // 5 bits
            2'b01: w_rx_last_bit = 3'd5;  // 6 bits
            2'b10: w_rx_last_bit = 3'd6;  // 7 bits
            2'b11: w_rx_last_bit = 3'd7;  // 8 bits
        endcase
    end

    // Expected parity calculation
    always_comb begin
        if (cfg_stick_parity)
            w_rx_expected_parity = ~cfg_even_parity;
        else
            w_rx_expected_parity = r_rx_parity;
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rx_state      <= RX_IDLE;
            r_rx_shift      <= '0;
            r_rx_bit_idx    <= '0;
            r_rx_baud_cnt   <= '0;
            r_rx_parity     <= 1'b0;
            r_rx_parity_err <= 1'b0;
            r_rx_wr_ptr     <= '0;
            r_rx_rd_ptr     <= '0;
            r_rx_err_count  <= '0;
            r_overrun_error <= 1'b0;
            r_parity_error  <= 1'b0;
            r_framing_error <= 1'b0;
            r_break_interrupt <= 1'b0;
            r_rx_break_hold <= 1'b0;
        end else if (cmd_rx_fifo_reset) begin
            r_rx_state  <= RX_IDLE;
            r_rx_wr_ptr <= '0;
            r_rx_rd_ptr <= '0;
            r_rx_err_count <= '0;
        end else begin
            // One update, after the state machine below, so a push and a pop
            // in the same cycle net out instead of one overwriting the other.
            // Held clear in character mode: LSR[7] is a FIFO-mode bit, and
            // the character-mode overwrite path does not move the pointers,
            // so a count kept across the mode change could not be trusted.
            if (!cfg_fifo_enable)
                r_rx_err_count <= '0;
            else if (w_rx_err_push && !w_rx_err_pop)
                r_rx_err_count <= r_rx_err_count + 1'b1;
            else if (w_rx_err_pop && !w_rx_err_push)
                r_rx_err_count <= r_rx_err_count - 1'b1;

            // Clear on read of LSR (16550 read-clear, see the wrapper).
            if (clr_overrun_error)   r_overrun_error   <= 1'b0;
            if (clr_parity_error)    r_parity_error    <= 1'b0;
            if (clr_framing_error)   r_framing_error   <= 1'b0;
            if (clr_break_interrupt) r_break_interrupt <= 1'b0;

            // RX FIFO read
            if (w_rx_pop) begin
                r_rx_rd_ptr <= r_rx_rd_ptr + 1'b1;
            end

            // LSR[4:2] ARE THE TAGS OF THE CHARACTER THE CPU IS BEING
            // HANDED, not a global running OR of everything ever received.
            // The per-character tags were already stored in the FIFO entry's
            // [10:8] and only LSR[7] used them; PE/FE/BI were separate
            // sticky flops, so one bad byte poisoned the status of every
            // clean byte behind it until software happened to read LSR.
            // A read of RBR hands over a character and its tags; before any
            // read, the tags are those of the character waiting at the top.
            // These assignments come after the clears above so a tag
            // arriving in the same cycle as a read of LSR is not lost.
            if (w_rx_pop) begin
                r_parity_error    <= w_rx_pop_tags[0];
                r_framing_error   <= w_rx_pop_tags[1];
                r_break_interrupt <= w_rx_pop_tags[2];
            end else if (w_rx_new_top) begin
                r_parity_error    <= w_rx_new_tags[0];
                r_framing_error   <= w_rx_new_tags[1];
                r_break_interrupt <= w_rx_new_tags[2];
            end

            if (w_baud_tick) begin
                case (r_rx_state)
                    RX_IDLE: begin
                        r_rx_baud_cnt <= '0;
                        if (w_rx_in) begin
                            // Line back to marking - a break, if one was
                            // being held off, is over.
                            r_rx_break_hold <= 1'b0;
                        end else if (!r_rx_break_hold) begin
                            r_rx_state <= RX_START;  // Start bit detected
                        end
                    end

                    RX_START: begin
                        r_rx_baud_cnt <= r_rx_baud_cnt + 1'b1;
                        if (r_rx_baud_cnt == 4'd7) begin  // Sample at midpoint
                            if (!w_rx_in) begin  // Confirm start bit
                                r_rx_state   <= RX_DATA;
                                r_rx_bit_idx <= '0;
                                r_rx_parity  <= cfg_even_parity ? 1'b0 : 1'b1;
                                r_rx_baud_cnt <= '0;
                            end else begin
                                r_rx_state <= RX_IDLE;  // False start
                            end
                        end
                    end

                    RX_DATA: begin
                        r_rx_baud_cnt <= r_rx_baud_cnt + 1'b1;
                        if (r_rx_baud_cnt == 4'd15) begin
                            r_rx_shift  <= {w_rx_in, r_rx_shift[7:1]};
                            r_rx_parity <= r_rx_parity ^ w_rx_in;

                            if (r_rx_bit_idx == w_rx_last_bit) begin
                                if (cfg_parity_enable)
                                    r_rx_state <= RX_PARITY;
                                else
                                    r_rx_state <= RX_STOP;
                            end else begin
                                r_rx_bit_idx <= r_rx_bit_idx + 1'b1;
                            end
                        end
                    end

                    RX_PARITY: begin
                        r_rx_baud_cnt <= r_rx_baud_cnt + 1'b1;
                        if (r_rx_baud_cnt == 4'd15) begin
                            r_rx_parity_err <= (w_rx_in != w_rx_expected_parity);
                            r_rx_state <= RX_STOP;
                        end
                    end

                    RX_STOP: begin
                        r_rx_baud_cnt <= r_rx_baud_cnt + 1'b1;
                        if (r_rx_baud_cnt == 4'd15) begin
                            if (!w_rx_fifo_full) begin
                                r_rx_fifo[r_rx_wr_ptr[FIFO_ADDR_WIDTH-1:0]] <=
                                    {w_rx_new_tags, w_rx_char};
                                r_rx_wr_ptr <= r_rx_wr_ptr + 1'b1;
                            end else begin
                                // Overrun. In character mode the arriving
                                // character overwrites and destroys the one
                                // still in RBR; in FIFO mode it is lost.
                                if (!cfg_fifo_enable) begin
                                    r_rx_fifo[r_rx_rd_ptr[FIFO_ADDR_WIDTH-1:0]] <=
                                        {w_rx_new_tags, w_rx_char};
                                end
                                r_overrun_error <= 1'b1;
                            end

                            // One character per break: hold the receiver off
                            // until the line goes back to marking.
                            if (w_rx_break) begin
                                r_rx_break_hold <= 1'b1;
                            end

                            r_rx_state <= RX_IDLE;
                            r_rx_parity_err <= 1'b0;
                        end
                    end

                    default: r_rx_state <= RX_IDLE;
                endcase
            end
        end
    )

    // RX data output
    assign rx_data = r_rx_fifo[r_rx_rd_ptr[FIFO_ADDR_WIDTH-1:0]][7:0];

    // DMA handshake, PC16550D FCR[3]. Mode 0 is one character at a time:
    // receive is requested as soon as anything is in the RX FIFO, and
    // transmit while the TX FIFO is completely empty. Mode 1 is block: the
    // receive request waits for the trigger level (or the character timeout,
    // which is what stops a partial block stalling forever) and the transmit
    // request stands while there is any room at all.
    assign rxrdy_n = cfg_dma_mode ? ~(w_rx_trigger_reached || r_timeout_flag)
                                  : ~(!w_rx_fifo_empty);
    assign txrdy_n = cfg_dma_mode ? ~(w_tx_fifo_count < w_tx_depth)
                                  : ~w_tx_fifo_empty;

    // RX status
    assign sts_data_ready     = !w_rx_fifo_empty;
    assign sts_overrun_error  = r_overrun_error;
    assign sts_parity_error   = r_parity_error;
    assign sts_framing_error  = r_framing_error;
    assign sts_break_interrupt = r_break_interrupt;
    // LSR[7] is defined only in FIFO mode and reads 0 in 16450 mode.
    assign sts_rx_fifo_error  = cfg_fifo_enable && (r_rx_err_count != 0);

    // FIFO status
    assign sts_fifo_status = cfg_fifo_enable ? 2'b11 : 2'b00;

    // ========================================================================
    // Interrupts
    // ========================================================================
    // Conditions -> IER gating -> IIR priority -> irq lives in
    // uart_16550_intr. The FCR trigger comparison lives there too, because
    // the RX-data-available condition is the only thing that uses it.
    uart_16550_intr #(
        .FIFO_DEPTH         (FIFO_DEPTH)
    ) u_intr (
        .clk                (clk),
        .rst_n              (rst_n),
        .overrun_error      (r_overrun_error),
        .parity_error       (r_parity_error),
        .framing_error      (r_framing_error),
        .break_interrupt    (r_break_interrupt),
        .rx_fifo_empty      (w_rx_fifo_empty),
        .rx_fifo_count      (w_rx_fifo_count),
        .tx_fifo_empty      (w_tx_fifo_empty),
        .delta_cts          (sts_delta_cts),
        .delta_dsr          (sts_delta_dsr),
        .trailing_ri        (sts_trailing_ri),
        .delta_dcd          (sts_delta_dcd),
        .cfg_fifo_enable    (cfg_fifo_enable),
        .cfg_rx_trigger     (cfg_rx_trigger),
        .cfg_out2           (cfg_out2),
        .cfg_rx_data_ie     (cfg_rx_data_ie),
        .cfg_tx_empty_ie    (cfg_tx_empty_ie),
        .cfg_line_status_ie (cfg_line_status_ie),
        .cfg_modem_ie       (cfg_modem_ie),
        .rx_timeout         (r_timeout_flag),
        .iir_read           (iir_read),
        .int_not_pending    (int_not_pending),
        .int_id             (int_id),
        .int_timeout        (int_timeout),
        .rx_trigger_reached (w_rx_trigger_reached),
        .irq                (irq)
    );

endmodule : uart_16550_core
