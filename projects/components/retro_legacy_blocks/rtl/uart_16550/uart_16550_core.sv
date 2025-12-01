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
//   Core UART logic implementing NS16550-compatible serial communication.
//   Includes 16-byte TX and RX FIFOs, baud rate generator, and
//   interrupt generation.
//
// Features:
//   - 16-byte TX and RX FIFOs
//   - Programmable baud rate via 16-bit divisor
//   - 5/6/7/8 data bits
//   - 1/1.5/2 stop bits
//   - None/Odd/Even/Mark/Space parity
//   - Modem control signals
//   - Loopback mode
//   - Character timeout interrupt
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

    // Aggregate Interrupt
    output logic        irq
);

    // ========================================================================
    // Local Parameters
    // ========================================================================
    localparam int FIFO_ADDR_WIDTH = $clog2(FIFO_DEPTH);

    // RX Trigger levels (1, 4, 8, 14 bytes)
    localparam logic [3:0] RX_TRIGGER_1  = 4'd1;
    localparam logic [3:0] RX_TRIGGER_4  = 4'd4;
    localparam logic [3:0] RX_TRIGGER_8  = 4'd8;
    localparam logic [3:0] RX_TRIGGER_14 = 4'd14;

    // ========================================================================
    // Modem Control Logic
    // ========================================================================
    // Modem inputs synchronized
    logic r_cts_sync [SYNC_STAGES-1:0];
    logic r_dsr_sync [SYNC_STAGES-1:0];
    logic r_ri_sync  [SYNC_STAGES-1:0];
    logic r_dcd_sync [SYNC_STAGES-1:0];

    logic w_cts, w_dsr, w_ri, w_dcd;
    logic r_cts_prev, r_dsr_prev, r_ri_prev, r_dcd_prev;
    logic r_delta_cts, r_delta_dsr, r_trailing_ri, r_delta_dcd;

    // Synchronize modem inputs
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < SYNC_STAGES; i++) begin
                r_cts_sync[i] <= 1'b0;
                r_dsr_sync[i] <= 1'b0;
                r_ri_sync[i]  <= 1'b0;
                r_dcd_sync[i] <= 1'b0;
            end
        end else begin
            r_cts_sync[0] <= ~cts_n;  // Invert active-low inputs
            r_dsr_sync[0] <= ~dsr_n;
            r_ri_sync[0]  <= ~ri_n;
            r_dcd_sync[0] <= ~dcd_n;
            for (int i = 1; i < SYNC_STAGES; i++) begin
                r_cts_sync[i] <= r_cts_sync[i-1];
                r_dsr_sync[i] <= r_dsr_sync[i-1];
                r_ri_sync[i]  <= r_ri_sync[i-1];
                r_dcd_sync[i] <= r_dcd_sync[i-1];
            end
        end
    )

    assign w_cts = cfg_loopback ? cfg_rts : r_cts_sync[SYNC_STAGES-1];
    assign w_dsr = cfg_loopback ? cfg_dtr : r_dsr_sync[SYNC_STAGES-1];
    assign w_ri  = cfg_loopback ? cfg_out1 : r_ri_sync[SYNC_STAGES-1];
    assign w_dcd = cfg_loopback ? cfg_out2 : r_dcd_sync[SYNC_STAGES-1];

    // Delta detection
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_cts_prev    <= 1'b0;
            r_dsr_prev    <= 1'b0;
            r_ri_prev     <= 1'b0;
            r_dcd_prev    <= 1'b0;
            r_delta_cts   <= 1'b0;
            r_delta_dsr   <= 1'b0;
            r_trailing_ri <= 1'b0;
            r_delta_dcd   <= 1'b0;
        end else begin
            r_cts_prev <= w_cts;
            r_dsr_prev <= w_dsr;
            r_ri_prev  <= w_ri;
            r_dcd_prev <= w_dcd;

            // Set on change, clear on register read
            if (clr_delta_cts) r_delta_cts <= 1'b0;
            else if (w_cts != r_cts_prev) r_delta_cts <= 1'b1;

            if (clr_delta_dsr) r_delta_dsr <= 1'b0;
            else if (w_dsr != r_dsr_prev) r_delta_dsr <= 1'b1;

            if (clr_trailing_ri) r_trailing_ri <= 1'b0;
            else if (~w_ri && r_ri_prev) r_trailing_ri <= 1'b1;  // RI trailing edge

            if (clr_delta_dcd) r_delta_dcd <= 1'b0;
            else if (w_dcd != r_dcd_prev) r_delta_dcd <= 1'b1;
        end
    )

    // Modem outputs
    assign dtr_n  = ~cfg_dtr;
    assign rts_n  = ~cfg_rts;
    assign out1_n = ~cfg_out1;
    assign out2_n = ~cfg_out2;

    // Modem status outputs
    assign sts_cts = w_cts;
    assign sts_dsr = w_dsr;
    assign sts_ri  = w_ri;
    assign sts_dcd = w_dcd;
    assign sts_delta_cts   = r_delta_cts;
    assign sts_delta_dsr   = r_delta_dsr;
    assign sts_trailing_ri = r_trailing_ri;
    assign sts_delta_dcd   = r_delta_dcd;

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
    logic [7:0] r_tx_fifo [FIFO_DEPTH-1:0];
    logic [FIFO_ADDR_WIDTH:0] r_tx_wr_ptr, r_tx_rd_ptr;
    logic w_tx_fifo_empty, w_tx_fifo_full;
    logic [FIFO_ADDR_WIDTH:0] w_tx_fifo_count;

    assign w_tx_fifo_count = r_tx_wr_ptr - r_tx_rd_ptr;
    assign w_tx_fifo_empty = (w_tx_fifo_count == 0);
    assign w_tx_fifo_full  = (w_tx_fifo_count == FIFO_DEPTH);

    // TX FIFO write
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_tx_wr_ptr <= '0;
        end else if (cmd_tx_fifo_reset) begin
            r_tx_wr_ptr <= '0;
        end else if (tx_write && !w_tx_fifo_full) begin
            r_tx_fifo[r_tx_wr_ptr[FIFO_ADDR_WIDTH-1:0]] <= tx_data;
            r_tx_wr_ptr <= r_tx_wr_ptr + 1'b1;
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
    logic       r_tx_active;
    logic [2:0] w_tx_last_bit;

    // Number of data bits based on word length
    always_comb begin
        case (cfg_word_length)
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
            r_tx_active   <= 1'b0;
        end else if (cmd_tx_fifo_reset) begin
            r_tx_state    <= TX_IDLE;
            r_tx_rd_ptr   <= '0;
            r_tx_active   <= 1'b0;
        end else if (w_baud_tick) begin
            r_tx_baud_cnt <= r_tx_baud_cnt + 1'b1;

            // 16x oversample - transition every 16 baud ticks
            if (r_tx_baud_cnt == 4'd15) begin
                case (r_tx_state)
                    TX_IDLE: begin
                        r_tx_active <= 1'b0;
                        if (!w_tx_fifo_empty) begin
                            r_tx_shift  <= r_tx_fifo[r_tx_rd_ptr[FIFO_ADDR_WIDTH-1:0]];
                            r_tx_rd_ptr <= r_tx_rd_ptr + 1'b1;
                            r_tx_state  <= TX_START;
                            r_tx_parity <= cfg_even_parity ? 1'b0 : 1'b1;
                            r_tx_active <= 1'b1;
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
                        if (cfg_stop_bits && cfg_word_length != 2'b00) begin
                            r_tx_state <= TX_STOP2;  // 2 stop bits for 6/7/8 bit words
                        end else begin
                            r_tx_state <= TX_IDLE;
                        end
                    end

                    TX_STOP2: begin
                        r_tx_state <= TX_IDLE;
                    end

                    default: r_tx_state <= TX_IDLE;
                endcase
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
    logic r_rx_sync [SYNC_STAGES-1:0];
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
    logic [10:0] r_rx_fifo [FIFO_DEPTH-1:0];  // 8 data + parity_err + frame_err + break
    logic [FIFO_ADDR_WIDTH:0] r_rx_wr_ptr, r_rx_rd_ptr;
    logic w_rx_fifo_empty, w_rx_fifo_full;
    logic [FIFO_ADDR_WIDTH:0] w_rx_fifo_count;

    assign w_rx_fifo_count = r_rx_wr_ptr - r_rx_rd_ptr;
    assign w_rx_fifo_empty = (w_rx_fifo_count == 0);
    assign w_rx_fifo_full  = (w_rx_fifo_count == FIFO_DEPTH);

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
    logic       r_rx_frame_err;
    logic       r_rx_break;
    logic       r_overrun_error;
    logic       r_parity_error;
    logic       r_framing_error;
    logic       r_break_interrupt;
    logic [2:0] w_rx_last_bit;
    logic       w_rx_expected_parity;

    // Number of data bits based on word length (for RX)
    always_comb begin
        case (cfg_word_length)
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
            r_rx_frame_err  <= 1'b0;
            r_rx_break      <= 1'b0;
            r_rx_wr_ptr     <= '0;
            r_rx_rd_ptr     <= '0;
            r_overrun_error <= 1'b0;
            r_parity_error  <= 1'b0;
            r_framing_error <= 1'b0;
            r_break_interrupt <= 1'b0;
        end else if (cmd_rx_fifo_reset) begin
            r_rx_state  <= RX_IDLE;
            r_rx_wr_ptr <= '0;
            r_rx_rd_ptr <= '0;
        end else begin
            // Clear errors on W1C
            if (clr_overrun_error)   r_overrun_error   <= 1'b0;
            if (clr_parity_error)    r_parity_error    <= 1'b0;
            if (clr_framing_error)   r_framing_error   <= 1'b0;
            if (clr_break_interrupt) r_break_interrupt <= 1'b0;

            // RX FIFO read
            if (rx_read && !w_rx_fifo_empty) begin
                r_rx_rd_ptr <= r_rx_rd_ptr + 1'b1;
            end

            if (w_baud_tick) begin
                case (r_rx_state)
                    RX_IDLE: begin
                        r_rx_baud_cnt <= '0;
                        if (!w_rx_in) begin  // Start bit detected
                            r_rx_state <= RX_START;
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
                            r_rx_frame_err <= !w_rx_in;  // Missing stop bit
                            r_rx_break <= (r_rx_shift == 8'h00 && !w_rx_in);

                            // Write to FIFO
                            if (!w_rx_fifo_full) begin
                                r_rx_fifo[r_rx_wr_ptr[FIFO_ADDR_WIDTH-1:0]] <=
                                    {r_rx_break, r_rx_frame_err, r_rx_parity_err, r_rx_shift};
                                r_rx_wr_ptr <= r_rx_wr_ptr + 1'b1;

                                // Set error flags
                                if (r_rx_parity_err) r_parity_error <= 1'b1;
                                if (r_rx_frame_err)  r_framing_error <= 1'b1;
                                if (r_rx_break)      r_break_interrupt <= 1'b1;
                            end else begin
                                r_overrun_error <= 1'b1;
                            end

                            r_rx_state <= RX_IDLE;
                            r_rx_parity_err <= 1'b0;
                            r_rx_frame_err  <= 1'b0;
                            r_rx_break      <= 1'b0;
                        end
                    end

                    default: r_rx_state <= RX_IDLE;
                endcase
            end
        end
    )

    // RX data output
    assign rx_data = r_rx_fifo[r_rx_rd_ptr[FIFO_ADDR_WIDTH-1:0]][7:0];

    // RX status
    assign sts_data_ready     = !w_rx_fifo_empty;
    assign sts_overrun_error  = r_overrun_error;
    assign sts_parity_error   = r_parity_error;
    assign sts_framing_error  = r_framing_error;
    assign sts_break_interrupt = r_break_interrupt;
    assign sts_rx_fifo_error  = (r_rx_fifo[r_rx_rd_ptr[FIFO_ADDR_WIDTH-1:0]][10:8] != 3'b000) && !w_rx_fifo_empty;

    // FIFO status
    assign sts_fifo_status = cfg_fifo_enable ? 2'b11 : 2'b00;

    // ========================================================================
    // Interrupt Generation
    // ========================================================================
    // TODO: Add interrupt enable inputs and implement priority logic
    // For now, simplified interrupt generation
    logic w_rx_trigger_reached;
    logic [3:0] w_rx_trigger_level;

    always_comb begin
        case (cfg_rx_trigger)
            2'b00: w_rx_trigger_level = RX_TRIGGER_1;
            2'b01: w_rx_trigger_level = RX_TRIGGER_4;
            2'b10: w_rx_trigger_level = RX_TRIGGER_8;
            2'b11: w_rx_trigger_level = RX_TRIGGER_14;
        endcase
    end

    assign w_rx_trigger_reached = (w_rx_fifo_count >= {1'b0, w_rx_trigger_level});

    // Interrupt priority (highest to lowest):
    // 1. RX Line Status (LSR[1:4] - errors)
    // 2. RX Data Available / Character Timeout
    // 3. TX Holding Register Empty
    // 4. Modem Status

    logic w_int_rx_error, w_int_rx_data, w_int_tx_empty, w_int_modem;

    assign w_int_rx_error = r_overrun_error | r_parity_error | r_framing_error | r_break_interrupt;
    assign w_int_rx_data  = cfg_fifo_enable ? w_rx_trigger_reached : !w_rx_fifo_empty;
    assign w_int_tx_empty = w_tx_fifo_empty;
    assign w_int_modem    = r_delta_cts | r_delta_dsr | r_trailing_ri | r_delta_dcd;

    always_comb begin
        if (w_int_rx_error) begin
            int_not_pending = 1'b0;
            int_id = 2'b11;  // Highest priority
        end else if (w_int_rx_data) begin
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

    assign int_timeout = 1'b0;  // TODO: Implement character timeout

    assign irq = ~int_not_pending && cfg_out2;  // OUT2 gates interrupt

endmodule : uart_16550_core
