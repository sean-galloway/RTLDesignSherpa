// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cdc_4_phase_handshake
// Purpose: Four-phase (req/ack/req-clr/ack-clr) CDC handshake with data
//          transfer. Source-domain valid/ready + destination-domain
//          valid/ready wrapper around a classic 4-phase request/acknowledge
//          CDC with data latched in the source domain and sampled in the
//          destination domain.
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18
// Renamed: 2026-04-18 (was cdc_handshake.sv)
//
// ===========================================================================
// PORT NAMING
// ---------------------------------------------------------------------------
// This module deliberately uses raw handshake names (src_valid / src_ready
// / src_data, dst_valid / dst_ready / dst_data) rather than the repository's
// i_*/o_* convention. This is required because the GAXI cocotb factory
// discovers signals by matching `{bus}_valid`, `{bus}_ready`, `{bus}_data`
// patterns. Changing to i_/o_ prefixes would break both the verification
// environment and every existing consumer (apb_slave_cdc, apb5_slave_cdc,
// apb_slave_cdc_cg).
//
// ===========================================================================
// REQUIRED SDC CONSTRAINTS (MUST be provided by the user)
// ---------------------------------------------------------------------------
// This block crosses clock domains. Timing constraints are NOT optional.
// The verification of functional correctness in simulation says nothing about
// STA closure: provide the following constraints or metastability-induced
// failures WILL occur in silicon.
//
//   # 1. Req / Ack single-bit crossings (control handshake)
//   set_max_delay -datapath_only -from [get_pins u_hs/r_req_src_reg/C] \
//                                 -to   [get_pins u_hs/r_req_sync_reg[0]/D] \
//                                 <dst_period_ns>
//   set_max_delay -datapath_only -from [get_pins u_hs/r_ack_dst_reg/C] \
//                                 -to   [get_pins u_hs/r_ack_sync_reg[0]/D] \
//                                 <src_period_ns>
//
//   # 2. Data bus (quasi-static, protected by the req/ack handshake)
//   set_max_delay -datapath_only -from [get_pins u_hs/r_src_data_hold_reg[*]/C] \
//                                 -to   [get_pins u_hs/r_dst_data_reg[*]/D] \
//                                 <dst_period_ns>
//
// Do NOT use a blanket `set_false_path` — the data bus relies on a BOUNDED
// crossing window (roughly three destination clocks) for correctness.
//
// ===========================================================================
// ASYNC_REG ATTRIBUTES
// ---------------------------------------------------------------------------
// Synchronizer flops are marked (* ASYNC_REG = "TRUE" *) so Xilinx Vivado
// keeps them in the same slice and back-annotates them for MTBF analysis.
// Altera/Intel uses the equivalent /* synthesis preserve = 1 */ attribute -
// both are applied below.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cdc_4_phase_handshake #(
    parameter int DATA_WIDTH     = 8,   // Width of the data bus for transfer
    parameter int SYNC_STAGES    = 3,   // Synchronizer depth for req/ack (2 or 3)
    parameter int TIMEOUT_CYCLES = 0,   // 0 = disabled; >0 asserts src_timeout
    parameter bit FAST_PATH      = 1'b0 // 1 = dst fast-path when dst_ready is already high
) (
    // Source clock domain signals
    input  logic                  clk_src,     // Source domain clock
    input  logic                  rst_src_n,   // Source domain async reset (active low)
    input  logic                  src_valid,   // Source indicates data valid
    output logic                  src_ready,   // Handshake ready back to source
    input  logic [DATA_WIDTH-1:0] src_data,    // Data from source domain
    output logic                  src_timeout, // Asserted (source domain) when TIMEOUT_CYCLES>0 and handshake stalls

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

    // Data storage for crossing. r_src_data_hold is a plain synchronous
    // source-domain register; "hold" indicates that it is held stable across
    // the CDC window by the req/ack protocol, NOT that it is async logic.
    logic [DATA_WIDTH-1:0] r_src_data_hold;
    (* ASYNC_REG = "TRUE" *)
    logic [DATA_WIDTH-1:0] r_dst_data;    // Latched data in destination domain

    // Multi-stage synchronizer registers for CDC.
    (* ASYNC_REG = "TRUE" *)
    logic [SYNC_STAGES-1:0] r_req_sync;  // r_req_src -> clk_dst domain
    (* ASYNC_REG = "TRUE" *)
    logic [SYNC_STAGES-1:0] r_ack_sync;  // r_ack_dst -> clk_src domain

    // Synchronized signals after CDC
    logic w_req_sync;  // Synchronized request in clk_dst domain
    logic w_ack_sync;  // Synchronized ack in clk_src domain

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

    // Optional timeout counter (source domain)
    localparam int TIMEOUT_CW = (TIMEOUT_CYCLES > 1) ? $clog2(TIMEOUT_CYCLES+1) : 1;
    logic [TIMEOUT_CW-1:0] r_timeout_cnt;

    //-------------------------------------------------------------------------
    // Source Domain Synchronizer (Dest -> Source Ack)
    //-------------------------------------------------------------------------
    // Synchronize r_ack_dst into clk_src domain using a SYNC_STAGES shift reg.
    `ALWAYS_FF_RST(clk_src, rst_src_n,
        if (`RST_ASSERTED(rst_src_n)) begin
            r_ack_sync <= '0;
        end else begin
            r_ack_sync <= {r_ack_sync[SYNC_STAGES-2:0], r_ack_dst};
        end
    )

    assign w_ack_sync = r_ack_sync[SYNC_STAGES-1];

    //-------------------------------------------------------------------------
    // Source Domain Handshake FSM (clk_src)
    //-------------------------------------------------------------------------
    `ALWAYS_FF_RST(clk_src, rst_src_n,
        if (`RST_ASSERTED(rst_src_n)) begin
            r_src_state     <= S_IDLE;
            r_req_src       <= 1'b0;
            src_ready       <= 1'b0;
            r_src_data_hold <= '0;
        end else begin
            unique case (r_src_state)
                S_IDLE: begin
                    src_ready <= 1'b1;
                    r_req_src <= 1'b0;
                    if (src_valid) begin
                        r_src_data_hold <= src_data;
                        r_req_src       <= 1'b1;
                        src_ready       <= 1'b0;
                        r_src_state     <= S_WAIT_ACK;
                    end
                end

                S_WAIT_ACK: begin
                    src_ready <= 1'b0;
                    if (w_ack_sync) begin
                        r_req_src   <= 1'b0;
                        r_src_state <= S_WAIT_ACK_CLR;
                    end
                    // else: keep r_req_src high (no self-assignment needed)
                end

                S_WAIT_ACK_CLR: begin
                    src_ready <= 1'b0;
                    r_req_src <= 1'b0;
                    if (!w_ack_sync) begin
                        src_ready   <= 1'b1;
                        r_src_state <= S_IDLE;
                    end
                end

                default: begin
                    r_src_state <= S_IDLE;
                    src_ready   <= 1'b1;
                    r_req_src   <= 1'b0;
                end
            endcase
        end
    )

    //-------------------------------------------------------------------------
    // Optional Timeout (source domain)
    //-------------------------------------------------------------------------
    generate
        if (TIMEOUT_CYCLES > 0) begin : g_timeout
            `ALWAYS_FF_RST(clk_src, rst_src_n,
                if (`RST_ASSERTED(rst_src_n)) begin
                    r_timeout_cnt <= '0;
                    src_timeout   <= 1'b0;
                end else begin
                    if (r_src_state == S_IDLE) begin
                        r_timeout_cnt <= '0;
                        src_timeout   <= 1'b0;
                    end else if (r_timeout_cnt == TIMEOUT_CYCLES[TIMEOUT_CW-1:0]) begin
                        src_timeout   <= 1'b1;
                    end else begin
                        r_timeout_cnt <= r_timeout_cnt + 1'b1;
                    end
                end
            )
        end else begin : g_no_timeout
            assign src_timeout   = 1'b0;
            // Keep counter reg declared but unused; tie off to avoid X propagation.
            always_comb r_timeout_cnt = '0;
        end
    endgenerate

    //-------------------------------------------------------------------------
    // Destination Domain Synchronizer (Source -> Destination Req)
    //-------------------------------------------------------------------------
    `ALWAYS_FF_RST(clk_dst, rst_dst_n,
        if (`RST_ASSERTED(rst_dst_n)) begin
            r_req_sync <= '0;
        end else begin
            r_req_sync <= {r_req_sync[SYNC_STAGES-2:0], r_req_src};
        end
    )

    assign w_req_sync = r_req_sync[SYNC_STAGES-1];

    //-------------------------------------------------------------------------
    // Destination Domain Handshake FSM (clk_dst)
    //-------------------------------------------------------------------------
    `ALWAYS_FF_RST(clk_dst, rst_dst_n,
        if (`RST_ASSERTED(rst_dst_n)) begin
            r_dst_state <= D_IDLE;
            r_ack_dst   <= 1'b0;
            dst_valid   <= 1'b0;
            r_dst_data  <= '0;
        end else begin
            unique case (r_dst_state)
                D_IDLE: begin
                    r_ack_dst <= 1'b0;
                    if (w_req_sync) begin
                        r_dst_data <= r_src_data_hold;
                        if (FAST_PATH && dst_ready) begin
                            // Receiver already ready: ack immediately, skip
                            // D_WAIT_READY to save one dst clock.
                            dst_valid   <= 1'b1;
                            r_ack_dst   <= 1'b1;
                            r_dst_state <= D_WAIT_REQ_CLR;
                        end else begin
                            dst_valid   <= 1'b1;
                            r_dst_state <= D_WAIT_READY;
                        end
                    end else begin
                        dst_valid <= 1'b0;
                    end
                end

                D_WAIT_READY: begin
                    dst_valid <= 1'b1;
                    if (dst_ready) begin
                        r_ack_dst   <= 1'b1;
                        dst_valid   <= 1'b0;
                        r_dst_state <= D_WAIT_REQ_CLR;
                    end else if (!w_req_sync) begin
                        dst_valid   <= 1'b0;
                        r_dst_state <= D_IDLE;
                    end
                end

                D_WAIT_REQ_CLR: begin
                    dst_valid <= 1'b0;
                    if (!w_req_sync) begin
                        r_ack_dst   <= 1'b0;
                        r_dst_state <= D_IDLE;
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

    assign dst_data = r_dst_data;

    //-------------------------------------------------------------------------
    // SVA (simulation-only) handshake protocol assertions
    //-------------------------------------------------------------------------
`ifndef SYNTHESIS
`ifndef VERILATOR
    // src_valid must not drop while src_ready is low (stalled transfer).
    a_src_stable: assert property (
        @(posedge clk_src) disable iff (`RST_ASSERTED(rst_src_n))
        (src_valid && !src_ready) |=> src_valid
    ) else $error("cdc_4_phase_handshake: src_valid dropped while src_ready=0");

    // dst_valid must remain high until dst_ready samples it.
    a_dst_stable: assert property (
        @(posedge clk_dst) disable iff (`RST_ASSERTED(rst_dst_n))
        (dst_valid && !dst_ready) |=> dst_valid || (r_dst_state == D_IDLE)
    ) else $error("cdc_4_phase_handshake: dst_valid dropped before dst_ready");

    // Request must not be asserted while source claims ready.
    a_no_req_in_idle_ready: assert property (
        @(posedge clk_src) disable iff (`RST_ASSERTED(rst_src_n))
        (r_src_state == S_IDLE) |-> !r_req_src
    );
`endif
`endif

endmodule : cdc_4_phase_handshake
