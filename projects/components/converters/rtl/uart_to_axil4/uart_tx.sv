// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: uart_tx
// Purpose: UART Transmitter Module
//
// Transmits 8-bit data over UART with configurable baud rate

`timescale 1ns / 1ps

`include "reset_defs.svh"

module uart_tx #(
    parameter int CLKS_PER_BIT = 868  // 100MHz / 115200 baud
)(
    input  logic       i_clk,
    input  logic       i_rst_n,
    output logic       o_tx,
    input  logic [7:0] i_tx_data,
    input  logic       i_tx_valid,
    output logic       o_tx_ready
);

    typedef enum logic [2:0] {
        IDLE,
        START,
        DATA,
        STOP
    } state_t;

    localparam int COUNT_WIDTH = $clog2(CLKS_PER_BIT);

    state_t r_state, w_next_state;
    logic [COUNT_WIDTH-1:0] r_clk_count, w_clk_count_next;
    logic [2:0]  r_bit_index, w_bit_index_next;
    logic [7:0]  r_tx_data_reg, w_tx_data_next;
    logic        r_tx_reg;

    // State machine registers
    `ALWAYS_FF_RST(i_clk, i_rst_n,
        if (`RST_ASSERTED(i_rst_n)) begin
            r_state      <= IDLE;
            r_clk_count  <= '0;
            r_bit_index  <= '0;
            r_tx_data_reg <= '0;
            r_tx_reg     <= 1'b1;  // UART idle is high
        end else begin
            r_state      <= w_next_state;
            r_clk_count  <= w_clk_count_next;
            r_bit_index  <= w_bit_index_next;
            r_tx_data_reg <= w_tx_data_next;

            // TX output assignment based on state
            case (w_next_state)
                IDLE:  r_tx_reg <= 1'b1;
                START: r_tx_reg <= 1'b0;
                DATA:  r_tx_reg <= r_tx_data_reg[r_bit_index];
                STOP:  r_tx_reg <= 1'b1;
                default: r_tx_reg <= 1'b1;
            endcase
        end
    )

    // State machine combinational logic
    always_comb begin
        w_next_state = r_state;
        w_clk_count_next = r_clk_count;
        w_bit_index_next = r_bit_index;
        w_tx_data_next = r_tx_data_reg;

        case (r_state)
            IDLE: begin
                w_clk_count_next = '0;
                w_bit_index_next = '0;
                if (i_tx_valid) begin
                    w_tx_data_next = i_tx_data;
                    w_next_state = START;
                end
            end

            START: begin
                if (r_clk_count == COUNT_WIDTH'(CLKS_PER_BIT-1)) begin
                    w_clk_count_next = '0;
                    w_next_state = DATA;
                end else begin
                    w_clk_count_next = r_clk_count + 1'b1;
                end
            end

            DATA: begin
                if (r_clk_count == COUNT_WIDTH'(CLKS_PER_BIT-1)) begin
                    w_clk_count_next = '0;

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
                    w_next_state = IDLE;
                end else begin
                    w_clk_count_next = r_clk_count + 1'b1;
                end
            end

            default: w_next_state = IDLE;
        endcase
    end

    assign o_tx = r_tx_reg;
    assign o_tx_ready = (r_state == IDLE);

endmodule : uart_tx
