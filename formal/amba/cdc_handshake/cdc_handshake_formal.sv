// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Yosys-compatible copy of cdc_handshake.sv for formal verification.
// Changes from original:
//   - Replaced `include "reset_defs.svh" macros with explicit always_ff blocks
//   - Everything else identical to rtl/amba/shared/cdc_handshake.sv

`timescale 1ns / 1ps

module cdc_handshake #(
    parameter int DATA_WIDTH = 8
) (
    input  logic                  clk_src,
    input  logic                  rst_src_n,
    input  logic                  src_valid,
    output logic                  src_ready,
    input  logic [DATA_WIDTH-1:0] src_data,

    input  logic                  clk_dst,
    input  logic                  rst_dst_n,
    output logic                  dst_valid,
    input  logic                  dst_ready,
    output logic [DATA_WIDTH-1:0] dst_data
);

    logic r_req_src;
    logic r_ack_dst;
    logic [DATA_WIDTH-1:0] r_async_data;
    logic [DATA_WIDTH-1:0] r_dst_data;
    logic [2:0] r_req_sync;
    logic [2:0] r_ack_sync;
    logic w_req_sync;
    logic w_ack_sync;

    typedef enum logic [1:0] {
        S_IDLE,
        S_WAIT_ACK,
        S_WAIT_ACK_CLR
    } src_state_t;

    typedef enum logic [1:0] {
        D_IDLE,
        D_WAIT_READY,
        D_WAIT_REQ_CLR
    } dst_state_t;

    src_state_t r_src_state;
    dst_state_t r_dst_state;

    // Source Domain Synchronizer (Dest -> Source Ack)
    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n) begin
            r_ack_sync <= 3'b000;
        end else begin
            r_ack_sync <= {r_ack_sync[1:0], r_ack_dst};
        end
    end

    assign w_ack_sync = r_ack_sync[2];

    // Source Domain Handshake FSM
    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n) begin
            r_src_state   <= S_IDLE;
            r_req_src     <= 1'b0;
            src_ready     <= 1'b0;
            r_async_data  <= {DATA_WIDTH{1'b0}};
        end else begin
            case (r_src_state)
                S_IDLE: begin
                    src_ready <= 1'b1;
                    r_req_src <= 1'b0;
                    if (src_valid) begin
                        r_async_data <= src_data;
                        r_req_src    <= 1'b1;
                        src_ready    <= 1'b0;
                        r_src_state  <= S_WAIT_ACK;
                    end
                end
                S_WAIT_ACK: begin
                    src_ready <= 1'b0;
                    if (w_ack_sync) begin
                        r_req_src    <= 1'b0;
                        r_src_state  <= S_WAIT_ACK_CLR;
                    end else begin
                        r_req_src    <= 1'b1;
                        r_src_state  <= S_WAIT_ACK;
                    end
                end
                S_WAIT_ACK_CLR: begin
                    src_ready <= 1'b0;
                    r_req_src <= 1'b0;
                    if (!w_ack_sync) begin
                        src_ready    <= 1'b1;
                        r_src_state  <= S_IDLE;
                    end else begin
                        r_src_state  <= S_WAIT_ACK_CLR;
                    end
                end
                default: begin
                    r_src_state <= S_IDLE;
                    src_ready   <= 1'b1;
                    r_req_src   <= 1'b0;
                end
            endcase
        end
    end

    // Destination Domain Synchronizer (Source -> Dest Req)
    always_ff @(posedge clk_dst or negedge rst_dst_n) begin
        if (!rst_dst_n) begin
            r_req_sync <= 3'b000;
        end else begin
            r_req_sync <= {r_req_sync[1:0], r_req_src};
        end
    end

    assign w_req_sync = r_req_sync[2];

    // Destination Domain Handshake FSM
    always_ff @(posedge clk_dst or negedge rst_dst_n) begin
        if (!rst_dst_n) begin
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
                        r_dst_state  <= D_WAIT_READY;
                    end else begin
                        dst_valid <= 1'b0;
                    end
                end
                D_WAIT_READY: begin
                    dst_valid <= 1'b1;
                    if (dst_ready) begin
                        r_ack_dst    <= 1'b1;
                        dst_valid    <= 1'b0;
                        r_dst_state  <= D_WAIT_REQ_CLR;
                    end else if (!w_req_sync) begin
                        dst_valid    <= 1'b0;
                        r_dst_state  <= D_IDLE;
                    end
                end
                D_WAIT_REQ_CLR: begin
                    dst_valid <= 1'b0;
                    if (!w_req_sync) begin
                        r_ack_dst    <= 1'b0;
                        r_dst_state  <= D_IDLE;
                    end else begin
                        r_ack_dst    <= 1'b1;
                    end
                end
                default: begin
                    r_dst_state <= D_IDLE;
                    r_ack_dst   <= 1'b0;
                    dst_valid   <= 1'b0;
                end
            endcase
        end
    end

    assign dst_data = r_dst_data;

endmodule : cdc_handshake
