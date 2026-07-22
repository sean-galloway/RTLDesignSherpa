// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: cdc_2_phase_handshake
// Purpose: Two-phase (toggle / NRZ) CDC handshake with data transfer.
//          Source-domain valid/ready + destination-domain valid/ready wrapper
//          around a toggle-based request/acknowledge CDC. On each new
//          transfer the source toggles its request bit; the destination
//          detects the toggle edge (XOR with a one-cycle-delayed synchronized
//          copy), latches the data, and toggles its acknowledge bit. The
//          source sees the ack toggle and releases the handshake.
//
//          Versus the 4-phase variant this halves the control-path round
//          trip (two synchronizer crossings per transfer instead of four)
//          at the cost of slightly trickier reasoning because the "event"
//          is a TRANSITION of the signal, not a level.
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-04-18
//
// ===========================================================================
// PORT NAMING
// ---------------------------------------------------------------------------
// Raw handshake names (src_valid/src_ready/src_data, dst_valid/dst_ready/
// dst_data) match the cdc_4_phase_handshake contract so the two modules are
// drop-in interchangeable at the interface level. The GAXI cocotb factory
// discovers signals by matching `{bus}_valid`, `{bus}_ready`, `{bus}_data`
// patterns and would break if i_/o_ prefixes were added.
//
// ===========================================================================
// REQUIRED SDC CONSTRAINTS (MUST be provided by the user)
// ---------------------------------------------------------------------------
// This block crosses clock domains. Timing constraints are NOT optional.
//
//   # 1. Req / Ack single-bit toggle crossings
//   set_max_delay -datapath_only -from [get_pins u_hs/r_req_tog_reg/C] \
//                                 -to   [get_pins u_hs/r_req_sync_reg[0]/D] \
//                                 <dst_period_ns>
//   set_max_delay -datapath_only -from [get_pins u_hs/r_ack_tog_reg/C] \
//                                 -to   [get_pins u_hs/r_ack_sync_reg[0]/D] \
//                                 <src_period_ns>
//
//   # 2. Data bus (quasi-static, protected by the toggle handshake)
//   set_max_delay -datapath_only -from [get_pins u_hs/r_src_data_hold_reg[*]/C] \
//                                 -to   [get_pins u_hs/r_dst_data_reg[*]/D] \
//                                 <dst_period_ns>
//
// Do NOT use a blanket `set_false_path` — the data bus relies on a BOUNDED
// crossing window (roughly SYNC_STAGES destination clocks) for correctness.
//
// ===========================================================================
// ASYNC_REG ATTRIBUTES
// ---------------------------------------------------------------------------
// Synchronizer flops are marked (* ASYNC_REG = "TRUE" *) so Xilinx Vivado
// keeps them together and back-annotates them for MTBF analysis.
//
// ===========================================================================
// THEORY OF OPERATION
// ---------------------------------------------------------------------------
//   Source domain (clk_src):
//     S_IDLE      src_ready=1. On src_valid: latch data into r_src_data_hold,
//                 toggle r_req_tog, drop src_ready, go to S_WAIT_ACK.
//     S_WAIT_ACK  wait for ack edge (w_ack_event). On edge: src_ready=1,
//                 return to S_IDLE.
//
//   Destination domain (clk_dst):
//     D_IDLE      wait for req edge (w_req_event). On edge: copy
//                 r_src_data_hold into r_dst_data, raise dst_valid, go to
//                 D_WAIT_READY.
//     D_WAIT_READY  hold dst_valid. On dst_ready: drop dst_valid, toggle
//                 r_ack_tog, return to D_IDLE.
//
//   Edge detection:
//     event = current_sync_output ^ previous_sync_output
//   where previous_sync_output is a one-cycle-delayed register in the
//   receiving domain — so the edge-detect cost is one flop per direction.
//
// ===========================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cdc_2_phase_handshake #(
    parameter int DATA_WIDTH     = 8,   // Width of the data bus for transfer
    parameter int SYNC_STAGES    = 3,   // Synchronizer depth for req/ack (2 or 3)
    parameter int TIMEOUT_CYCLES = 0    // 0 = disabled; >0 asserts src_timeout
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
    // Toggle bits (one per direction, crossed as NRZ)
    //-------------------------------------------------------------------------
    logic r_req_tog;    // Source-domain request toggle (flips on each new xfer)
    logic r_ack_tog;    // Destination-domain ack toggle (flips on each accept)

    // Data storage. r_src_data_hold is a plain synchronous source-domain
    // register; "hold" indicates that it is held stable across the CDC window
    // by the toggle handshake, NOT that it is async logic.
    logic [DATA_WIDTH-1:0] r_src_data_hold;
    (* ASYNC_REG = "TRUE" *)
    logic [DATA_WIDTH-1:0] r_dst_data;

    //-------------------------------------------------------------------------
    // Multi-stage synchronizer registers
    //-------------------------------------------------------------------------
    (* ASYNC_REG = "TRUE" *)
    logic [SYNC_STAGES-1:0] r_req_sync;  // r_req_tog -> clk_dst
    (* ASYNC_REG = "TRUE" *)
    logic [SYNC_STAGES-1:0] r_ack_sync;  // r_ack_tog -> clk_src

    // One-cycle-delayed copies of the synchronizer outputs, used for
    // edge-detect. Held in the RECEIVING domain so they are synchronous there.
    logic r_req_sync_d;
    logic r_ack_sync_d;

    logic w_req_sync;   // Final synchronized request (clk_dst domain)
    logic w_ack_sync;   // Final synchronized ack    (clk_src domain)
    logic w_req_event;  // Request toggle observed in clk_dst domain
    logic w_ack_event;  // Ack     toggle observed in clk_src domain

    //-------------------------------------------------------------------------
    // Source FSM
    //-------------------------------------------------------------------------
    typedef enum logic {
        S_IDLE,        // Ready for a new data beat
        S_WAIT_ACK     // Req toggled, waiting for ack toggle to return
    } src_state_t;

    src_state_t r_src_state;

    //-------------------------------------------------------------------------
    // Destination FSM
    //-------------------------------------------------------------------------
    typedef enum logic {
        D_IDLE,        // Waiting for a new req toggle
        D_WAIT_READY   // dst_valid asserted, waiting for dst_ready
    } dst_state_t;

    dst_state_t r_dst_state;

    //-------------------------------------------------------------------------
    // Optional timeout counter (source domain)
    //-------------------------------------------------------------------------
    localparam int TIMEOUT_CW = (TIMEOUT_CYCLES > 1) ? $clog2(TIMEOUT_CYCLES+1) : 1;
    logic [TIMEOUT_CW-1:0] r_timeout_cnt;

    //-------------------------------------------------------------------------
    // Source Domain Synchronizer (Dest ack toggle -> Source)
    //-------------------------------------------------------------------------
    `ALWAYS_FF_RST(clk_src, rst_src_n,
        if (`RST_ASSERTED(rst_src_n)) begin
            r_ack_sync   <= '0;
            r_ack_sync_d <= 1'b0;
        end else begin
            r_ack_sync   <= {r_ack_sync[SYNC_STAGES-2:0], r_ack_tog};
            r_ack_sync_d <= r_ack_sync[SYNC_STAGES-1];
        end
    )

    assign w_ack_sync  = r_ack_sync[SYNC_STAGES-1];
    assign w_ack_event = w_ack_sync ^ r_ack_sync_d;

    //-------------------------------------------------------------------------
    // Source Domain Handshake FSM (clk_src)
    //-------------------------------------------------------------------------
    `ALWAYS_FF_RST(clk_src, rst_src_n,
        if (`RST_ASSERTED(rst_src_n)) begin
            r_src_state     <= S_IDLE;
            r_req_tog       <= 1'b0;
            src_ready       <= 1'b0;
            r_src_data_hold <= '0;
        end else begin
            unique case (r_src_state)
                S_IDLE: begin
                    src_ready <= 1'b1;
                    if (src_valid) begin
                        r_src_data_hold <= src_data;
                        r_req_tog       <= ~r_req_tog;   // Toggle = "new xfer"
                        src_ready       <= 1'b0;
                        r_src_state     <= S_WAIT_ACK;
                    end
                end

                S_WAIT_ACK: begin
                    src_ready <= 1'b0;
                    if (w_ack_event) begin
                        src_ready   <= 1'b1;
                        r_src_state <= S_IDLE;
                    end
                end

                default: begin
                    r_src_state <= S_IDLE;
                    src_ready   <= 1'b1;
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
            assign src_timeout = 1'b0;
            always_comb r_timeout_cnt = '0;
        end
    endgenerate

    //-------------------------------------------------------------------------
    // Destination Domain Synchronizer (Source req toggle -> Dest)
    //-------------------------------------------------------------------------
    `ALWAYS_FF_RST(clk_dst, rst_dst_n,
        if (`RST_ASSERTED(rst_dst_n)) begin
            r_req_sync   <= '0;
            r_req_sync_d <= 1'b0;
        end else begin
            r_req_sync   <= {r_req_sync[SYNC_STAGES-2:0], r_req_tog};
            r_req_sync_d <= r_req_sync[SYNC_STAGES-1];
        end
    )

    assign w_req_sync  = r_req_sync[SYNC_STAGES-1];
    assign w_req_event = w_req_sync ^ r_req_sync_d;

    //-------------------------------------------------------------------------
    // Destination Domain Handshake FSM (clk_dst)
    //-------------------------------------------------------------------------
    `ALWAYS_FF_RST(clk_dst, rst_dst_n,
        if (`RST_ASSERTED(rst_dst_n)) begin
            r_dst_state <= D_IDLE;
            r_ack_tog   <= 1'b0;
            dst_valid   <= 1'b0;
            r_dst_data  <= '0;
        end else begin
            unique case (r_dst_state)
                D_IDLE: begin
                    if (w_req_event) begin
                        r_dst_data  <= r_src_data_hold;
                        dst_valid   <= 1'b1;
                        r_dst_state <= D_WAIT_READY;
                    end else begin
                        dst_valid <= 1'b0;
                    end
                end

                D_WAIT_READY: begin
                    dst_valid <= 1'b1;
                    if (dst_ready) begin
                        r_ack_tog   <= ~r_ack_tog;   // Toggle = "accepted"
                        dst_valid   <= 1'b0;
                        r_dst_state <= D_IDLE;
                    end
                end

                default: begin
                    r_dst_state <= D_IDLE;
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
    ) else $error("cdc_2_phase_handshake: src_valid dropped while src_ready=0");

    // dst_valid must remain high until dst_ready samples it.
    a_dst_stable: assert property (
        @(posedge clk_dst) disable iff (`RST_ASSERTED(rst_dst_n))
        (dst_valid && !dst_ready) |=> dst_valid || (r_dst_state == D_IDLE)
    ) else $error("cdc_2_phase_handshake: dst_valid dropped before dst_ready");

    // At most one toggle event per direction per cycle (implicit in a 1-bit
    // toggle + synchronous flop pair, but asserted to catch corrupted sync
    // registers in simulation).
    a_single_req_event: assert property (
        @(posedge clk_dst) disable iff (`RST_ASSERTED(rst_dst_n))
        w_req_event |-> !$isunknown(r_src_data_hold)
    );
`endif
`endif

endmodule : cdc_2_phase_handshake
