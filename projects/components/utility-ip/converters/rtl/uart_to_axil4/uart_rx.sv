// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: uart_rx
// Purpose: UART Receiver Module
//
// Receives 8-bit data over UART with configurable baud rate

`timescale 1ns / 1ps

`include "reset_defs.svh"

module uart_rx #(
    parameter int CLKS_PER_BIT = 868  // 100MHz / 115200 baud
)(
    input  logic       i_clk,
    input  logic       i_rst_n,
    input  logic       i_rx,
    output logic [7:0] o_rx_data,
    output logic       o_rx_valid,
    input  logic       i_rx_ready
);

    typedef enum logic [2:0] {
        IDLE,
        START,
        DATA,
        STOP,
        CLEANUP
    } state_t;

    localparam int COUNT_WIDTH = $clog2(CLKS_PER_BIT);

    state_t r_state, w_next_state;
    logic [COUNT_WIDTH-1:0] r_clk_count, w_clk_count_next;
    logic [2:0]  r_bit_index, w_bit_index_next;
    logic [7:0]  r_rx_data_reg, w_rx_data_next;
    logic        r_rx_valid_reg;

    // Synchronize RX input (2-FF synchronizer for CDC)
    logic r_rx_sync1, r_rx_sync2;

    `ALWAYS_FF_RST(i_clk, i_rst_n,
        if (`RST_ASSERTED(i_rst_n)) begin
            r_rx_sync1 <= 1'b1;  // UART idle is high
            r_rx_sync2 <= 1'b1;
        end else begin
            r_rx_sync1 <= i_rx;
            r_rx_sync2 <= r_rx_sync1;
        end
    )

    // State machine registers
    `ALWAYS_FF_RST(i_clk, i_rst_n,
        if (`RST_ASSERTED(i_rst_n)) begin
            r_state      <= IDLE;
            r_clk_count  <= '0;
            r_bit_index  <= '0;
            r_rx_data_reg <= '0;
            r_rx_valid_reg <= 1'b0;
        end else begin
            r_state      <= w_next_state;
            r_clk_count  <= w_clk_count_next;
            r_bit_index  <= w_bit_index_next;
            r_rx_data_reg <= w_rx_data_next;
            r_rx_valid_reg <= (w_next_state == CLEANUP);
        end
    )

    // State machine combinational logic
    always_comb begin
        w_next_state = r_state;
        w_clk_count_next = r_clk_count;
        w_bit_index_next = r_bit_index;
        w_rx_data_next = r_rx_data_reg;

        case (r_state)
            IDLE: begin
                w_clk_count_next = '0;
                w_bit_index_next = '0;
                if (r_rx_sync2 == 1'b0) begin  // Start bit detected
                    w_next_state = START;
                end
            end

            START: begin
                if (r_clk_count == COUNT_WIDTH'((CLKS_PER_BIT-1)/2)) begin
                    if (r_rx_sync2 == 1'b0) begin  // Verify start bit at midpoint
                        w_clk_count_next = '0;
                        w_next_state = DATA;
                    end else begin
                        w_next_state = IDLE;  // False start bit
                    end
                end else begin
                    w_clk_count_next = r_clk_count + 1'b1;
                end
            end

            DATA: begin
                if (r_clk_count == COUNT_WIDTH'(CLKS_PER_BIT-1)) begin
                    w_clk_count_next = '0;
                    w_rx_data_next[r_bit_index] = r_rx_sync2;

                    if (r_bit_index == 3'd7) begin
                        w_next_state = STOP;
                    end else begin
                        w_bit_index_next = r_bit_index + 1'b1;
                    end
                end else begin
                    w_clk_count_next = r_clk_count + 1'b1;
                end
            end

            STOP: begin
                if (r_clk_count == COUNT_WIDTH'(CLKS_PER_BIT-1)) begin
                    w_clk_count_next = '0;
                    w_next_state = CLEANUP;
                end else begin
                    w_clk_count_next = r_clk_count + 1'b1;
                end
            end

            CLEANUP: begin
                if (i_rx_ready) begin
                    w_next_state = IDLE;
                end
            end

            default: w_next_state = IDLE;
        endcase
    end

    assign o_rx_data = r_rx_data_reg;
    assign o_rx_valid = r_rx_valid_reg;

endmodule : uart_rx
