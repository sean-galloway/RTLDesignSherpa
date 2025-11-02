// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cdc_handshake
// Purpose: Cdc Handshake module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cdc_handshake #(
    parameter int DATA_WIDTH = 8  // Width of the data bus for transfer
) (
    // Source clock domain signals
    input  logic                  clk_src,     // Source domain clock
    input  logic                  rst_src_n,   // Source domain async reset (active low)
    input  logic                  src_valid,   // Source indicates data valid
    output logic                  src_ready,   // Handshake ready back to source
    input  logic [DATA_WIDTH-1:0] src_data,    // Data from source domain

    // Destination clock domain signals
    input  logic                  clk_dst,     // Destination domain clock
    input  logic                  rst_dst_n,   // Destination domain async reset (active low)
    output logic                  dst_valid,   // Destination indicates data valid to receiver
    input  logic                  dst_ready,   // Receiver ready in destination domain
    output logic [DATA_WIDTH-1:0] dst_data     // Data transferred to destination domain
);

    //-------------------------------------------------------------------------
    // Internal Signals for CDC Handshake
    //-------------------------------------------------------------------------

    // Handshake request/acknowledge signals (cross-domain)
    logic r_req_src;    // Request flag (source domain) - asserted when a new data transfer starts
    logic r_ack_dst;    // Acknowledge flag (destination domain) - asserted when transfer is accepted

    // Data storage for crossing
    logic [DATA_WIDTH-1:0] r_async_data;  // Holds the data word during transfer (latched in source domain)
    logic [DATA_WIDTH-1:0] r_dst_data;    // Latched data in destination domain (to drive dst_data)

    // Multi-stage synchronizer registers (3-stage) for CDC
    logic [2:0] r_req_sync;  // Synchronizer for r_req_src -> clk_dst domain
    logic [2:0] r_ack_sync;  // Synchronizer for r_ack_dst -> clk_src domain

    // Synchronized signals after CDC
    logic w_req_sync;  // Synchronized request in clk_dst domain (after 3-stage sync)
    logic w_ack_sync;  // Synchronized ack in clk_src domain (after 3-stage sync)

    // State encoding for source and destination domain state machines
    typedef enum logic [1:0] {
        S_IDLE,         // Source idle (ready for new data)
        S_WAIT_ACK,     // Waiting for destination ack (data in flight)
        S_WAIT_ACK_CLR  // Waiting for ack to clear (handshake completion)
    } src_state_t;

    typedef enum logic [1:0] {
        D_IDLE,         // Destination idle (waiting for request)
        D_WAIT_READY,   // Received request, waiting for dest ready
        D_WAIT_REQ_CLR  // Ack sent, waiting for request to clear
    } dst_state_t;

    src_state_t r_src_state;
    dst_state_t r_dst_state;

    //-------------------------------------------------------------------------
    // Source Domain Synchronizer (Dest -> Source Ack)
    //-------------------------------------------------------------------------
    // Synchronize the destination ack signal (r_ack_dst) into the source clock domain (clk_src).
    // This uses a 3-stage shift register to safely transfer the asynchronous r_ack_dst signal.
    `ALWAYS_FF_RST(clk_src, rst_src_n,
if (`RST_ASSERTED(rst_src_n)) begin
            r_ack_sync <= 3'b000;
        end else begin
            r_ack_sync <= {r_ack_sync[1:0], r_ack_dst};
        end
    )


    assign w_ack_sync = r_ack_sync[2];  // Synchronized ack signal in clk_src domain

    //-------------------------------------------------------------------------
    // Source Domain Handshake FSM (clk_src)
    //-------------------------------------------------------------------------
    // Handles incoming src_valid/src_data, drives request and generates src_ready after handshake completes.
    `ALWAYS_FF_RST(clk_src, rst_src_n,
if (`RST_ASSERTED(rst_src_n)) begin
            // Asynchronous reset (active low)
            r_src_state   <= S_IDLE;
            r_req_src     <= 1'b0;
            src_ready     <= 1'b0;
            r_async_data  <= {DATA_WIDTH{1'b0}};
        end else begin
            case (r_src_state)
                S_IDLE: begin
                    src_ready <= 1'b1;      // Module is ready for a new transfer
                    r_req_src <= 1'b0;      // Ensure request is low when idle
                    if (src_valid) begin
                        // New valid data detected, latch data and raise request
                        r_async_data <= src_data;   // Capture the data word for transfer
                        r_req_src    <= 1'b1;       // Assert request to destination
                        src_ready    <= 1'b0;       // Not ready for new data until current handshake completes
                        r_src_state  <= S_WAIT_ACK;
                    end
                end

                S_WAIT_ACK: begin
                    src_ready <= 1'b0;      // Busy waiting for ack, hold src_ready low
                    if (w_ack_sync) begin
                        // Destination acknowledged the transfer (ack received)
                        r_req_src    <= 1'b0;     // Drop the request now that ack is seen
                        r_src_state  <= S_WAIT_ACK_CLR;
                        // Note: Keep src_ready low until ack is fully cleared in next state
                    end else begin
                        // No ack yet, keep waiting
                        r_req_src    <= 1'b1;     // Maintain request signal
                        r_src_state  <= S_WAIT_ACK;
                    end
                end

                S_WAIT_ACK_CLR: begin
                    src_ready <= 1'b0;      // Still busy until ack is cleared
                    r_req_src <= 1'b0;      // Ensure request remains deasserted
                    if (!w_ack_sync) begin
                        // Ack has returned to 0 in source domain -> handshake cycle complete
                        src_ready    <= 1'b1;     // Now ready for the next data (handshake done)
                        r_src_state  <= S_IDLE;
                    end else begin
                        // Ack still asserted, wait for it to clear
                        r_src_state  <= S_WAIT_ACK_CLR;
                    end
                end
                default: begin
                    r_src_state   <= S_IDLE;
                    src_ready <= 1'b1;      // Module is ready for a new transfer
                    r_req_src <= 1'b0;      // Ensure request is low when idle
                end
            endcase
        end
    )


    //-------------------------------------------------------------------------
    // Destination Domain Synchronizer (Source -> Destination Req)
    //-------------------------------------------------------------------------
    // Synchronize the source request signal (r_req_src) into the destination clock domain (clk_dst).
    // Also using a 3-stage shift register for metastability protection.
    `ALWAYS_FF_RST(clk_dst, rst_dst_n,
if (`RST_ASSERTED(rst_dst_n)) begin
            r_req_sync <= 3'b000;
        end else begin
            r_req_sync <= {r_req_sync[1:0], r_req_src};
        end
    )


    assign w_req_sync = r_req_sync[2];  // Synchronized request signal in clk_dst domain

    //-------------------------------------------------------------------------
    // Destination Domain Handshake FSM (clk_dst)
    //-------------------------------------------------------------------------
    // Waits for synchronized request, then, if the local receiver is ready, latches data and asserts dst_valid and ack.
    // Holds dst_valid high until dst_ready is asserted by the receiver, and waits for source to drop request (acknowledged back).
    `ALWAYS_FF_RST(clk_dst, rst_dst_n,
if (`RST_ASSERTED(rst_dst_n)) begin
            // Asynchronous reset (active low)
            r_dst_state <= D_IDLE;
            r_ack_dst   <= 1'b0;
            dst_valid   <= 1'b0;
            r_dst_data  <= {DATA_WIDTH{1'b0}};
        end else begin
            case (r_dst_state)
                D_IDLE: begin
                    r_ack_dst <= 1'b0;
                    if (w_req_sync) begin
                        r_dst_data   <= r_async_data;
                        dst_valid    <= 1'b1;
                        r_dst_state  <= D_WAIT_READY;      // Always go to WAIT_READY first
                    end else begin
                        dst_valid <= 1'b0;
                    end
                end
                D_WAIT_READY: begin
                    // Keep dst_valid high while waiting for dst_ready
                    dst_valid <= 1'b1;
                    if (dst_ready) begin
                        // Now receiver is ready, acknowledge the transfer
                        r_ack_dst    <= 1'b1;
                        dst_valid    <= 1'b0;  // Drop dst_valid as soon as dst_ready is sampled high
                        r_dst_state  <= D_WAIT_REQ_CLR;
                    end else if (!w_req_sync) begin
                        // Source withdrew the request
                        dst_valid    <= 1'b0;
                        r_dst_state  <= D_IDLE;
                    end
                end

                D_WAIT_REQ_CLR: begin
                    // At this point, ack is high but dst_valid is now low
                    dst_valid <= 1'b0;  // Keep dst_valid low in this state
                    if (!w_req_sync) begin
                        // Source has dropped the request (received our ack and completed its cycle)
                        r_ack_dst    <= 1'b0;   // Drop acknowledge signal
                        r_dst_state  <= D_IDLE; // Return to idle, ready for next request
                    end else begin
                        // Source request still asserted, keep waiting
                        r_ack_dst    <= 1'b1;   // Keep ack asserted
                    end
                end
                default: begin
                    r_dst_state <= D_IDLE;
                    r_ack_dst   <= 1'b0;
                    dst_valid   <= 1'b0;
                end
            endcase
        end
    )


    // Drive the output data bus in destination domain from the latched register
    assign dst_data = r_dst_data;

endmodule : cdc_handshake
