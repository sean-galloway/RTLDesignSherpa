// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: traffic_counter
// Purpose: Router tap synchronizer + 32-bit wrapping counter bank
//
// Documentation: projects/components/compute-eng-ip/hive-serv/docs/hive_mas/ch02_blocks/03_serv_monitor.md
// Subsystem: hive-serv
//
// Author: sean galloway
// Created: 2026-10-13

`timescale 1ns / 1ps

module traffic_counter #(
    parameter int IBUF_DEPTH = 8
)(
    input  logic        clk,
    input  logic        rst_n,

    // --- router tap (source domain is the tile router / delta_clk)
    input  logic [3:0]  tap_rx_stb,
    input  logic [3:0]  tap_tx_stb,
    input  logic [3:0]  tap_local_inject_stb,
    input  logic [3:0]  tap_local_consume_stb,
    input  logic [31:0] tap_occupancy,
    input  logic        tap_stall_stb,
    input  logic        tap_parity_err_stb,
    input  logic        tap_protocol_err_stb,
    input  logic        tap_overflow_stb,

    // --- counter bank outputs (serv_clk domain)
    output logic [31:0] pkt_rx_count [4],
    output logic [31:0] pkt_tx_count [4],
    output logic [31:0] pkt_local_inject,
    output logic [31:0] pkt_local_consume,
    output logic [31:0] buffer_overflow_count,
    output logic [31:0] stall_cycles,
    output logic [7:0]  buffer_occupancy [4],

    // --- synchronized error pulses (one cycle in serv_clk)
    output logic        parity_err_pulse,
    output logic        protocol_err_pulse,
    output logic        overflow_err_pulse,

    // --- control
    input  logic        clear_stats
);

    //--------------------------------------------------------------------------
    // Dual-flop synchronizers for all tap signals (2026-10-13 decision)
    //--------------------------------------------------------------------------
    logic [3:0] rx_stb_sync;
    logic [3:0] tx_stb_sync;
    logic [3:0] local_inject_stb_sync;
    logic [3:0] local_consume_stb_sync;
    logic [31:0] occupancy_sync;
    logic        stall_stb_sync;
    logic        parity_err_sync;
    logic        protocol_err_sync;
    logic        overflow_stb_sync;

    cdc_synchronizer #(.WIDTH(4),  .FLOP_COUNT(2)) u_rx_sync          (.clk, .rst_n, .async_in(tap_rx_stb),          .sync_out(rx_stb_sync));
    cdc_synchronizer #(.WIDTH(4),  .FLOP_COUNT(2)) u_tx_sync          (.clk, .rst_n, .async_in(tap_tx_stb),          .sync_out(tx_stb_sync));
    cdc_synchronizer #(.WIDTH(4),  .FLOP_COUNT(2)) u_local_inject_sync (.clk, .rst_n, .async_in(tap_local_inject_stb), .sync_out(local_inject_stb_sync));
    cdc_synchronizer #(.WIDTH(4),  .FLOP_COUNT(2)) u_local_consume_sync(.clk, .rst_n, .async_in(tap_local_consume_stb), .sync_out(local_consume_stb_sync));
    cdc_synchronizer #(.WIDTH(32), .FLOP_COUNT(2)) u_occupancy_sync   (.clk, .rst_n, .async_in(tap_occupancy),       .sync_out(occupancy_sync));
    cdc_synchronizer #(.WIDTH(1),  .FLOP_COUNT(2)) u_stall_sync       (.clk, .rst_n, .async_in(tap_stall_stb),       .sync_out(stall_stb_sync));
    cdc_synchronizer #(.WIDTH(1),  .FLOP_COUNT(2)) u_parity_sync      (.clk, .rst_n, .async_in(tap_parity_err_stb),  .sync_out(parity_err_sync));
    cdc_synchronizer #(.WIDTH(1),  .FLOP_COUNT(2)) u_protocol_sync    (.clk, .rst_n, .async_in(tap_protocol_err_stb), .sync_out(protocol_err_sync));
    cdc_synchronizer #(.WIDTH(1),  .FLOP_COUNT(2)) u_overflow_sync    (.clk, .rst_n, .async_in(tap_overflow_stb),    .sync_out(overflow_stb_sync));

    //--------------------------------------------------------------------------
    // Occupancy decode (8 bits per direction)
    //--------------------------------------------------------------------------
    genvar d;
    generate
        for (d = 0; d < 4; d++) begin : gen_occ
            assign buffer_occupancy[d] = occupancy_sync[d*8 +: 8];
        end
    endgenerate

    //--------------------------------------------------------------------------
    // Edge-detect counters for per-direction packet strobes
    //--------------------------------------------------------------------------
    logic [3:0] rx_stb_prev;
    logic [3:0] tx_stb_prev;
    logic [3:0] local_inject_stb_prev;
    logic [3:0] local_consume_stb_prev;
    logic       overflow_stb_prev;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_stb_prev           <= '0;
            tx_stb_prev           <= '0;
            local_inject_stb_prev <= '0;
            local_consume_stb_prev<= '0;
            overflow_stb_prev     <= '0;
            for (int i = 0; i < 4; i++) begin
                pkt_rx_count[i]   <= '0;
                pkt_tx_count[i]   <= '0;
            end
            pkt_local_inject      <= '0;
            pkt_local_consume     <= '0;
            buffer_overflow_count <= '0;
            stall_cycles          <= '0;
        end else begin
            rx_stb_prev           <= rx_stb_sync;
            tx_stb_prev           <= tx_stb_sync;
            local_inject_stb_prev <= local_inject_stb_sync;
            local_consume_stb_prev<= local_consume_stb_sync;
            overflow_stb_prev     <= overflow_stb_sync;

            if (clear_stats) begin
                for (int i = 0; i < 4; i++) begin
                    pkt_rx_count[i]   <= '0;
                    pkt_tx_count[i]   <= '0;
                end
                pkt_local_inject      <= '0;
                pkt_local_consume     <= '0;
                buffer_overflow_count <= '0;
                stall_cycles          <= '0;
            end else begin
                for (int i = 0; i < 4; i++) begin
                    if (rx_stb_sync[i] && !rx_stb_prev[i])
                        pkt_rx_count[i] <= pkt_rx_count[i] + 32'd1;
                    if (tx_stb_sync[i] && !tx_stb_prev[i])
                        pkt_tx_count[i] <= pkt_tx_count[i] + 32'd1;
                end
                if (local_inject_stb_sync[0] && !local_inject_stb_prev[0])
                    pkt_local_inject <= pkt_local_inject + 32'd1;
                if (local_consume_stb_sync[0] && !local_consume_stb_prev[0])
                    pkt_local_consume <= pkt_local_consume + 32'd1;
                if (overflow_stb_sync && !overflow_stb_prev)
                    buffer_overflow_count <= buffer_overflow_count + 32'd1;
                if (stall_stb_sync)
                    stall_cycles <= stall_cycles + 32'd1;
            end
        end
    end

    //--------------------------------------------------------------------------
    // Synchronized error pulses
    //--------------------------------------------------------------------------
    logic parity_err_prev;
    logic protocol_err_prev;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            parity_err_prev   <= '0;
            protocol_err_prev <= '0;
        end else begin
            parity_err_prev   <= parity_err_sync;
            protocol_err_prev <= protocol_err_sync;
        end
    end

    assign parity_err_pulse   = parity_err_sync   && !parity_err_prev;
    assign protocol_err_pulse = protocol_err_sync && !protocol_err_prev;
    assign overflow_err_pulse = overflow_stb_sync && !overflow_stb_prev;

endmodule : traffic_counter
