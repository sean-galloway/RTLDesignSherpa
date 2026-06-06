// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/github/RTLDesignSherpa
//
// Module: axi_monitor_reporter_debug
// Purpose: Per-transaction state-change emitter for the 0.9 monitor
//          reporter. Sixth sub-block alongside error/timeout/compl/
//          threshold/perf. Gives integrators (and compression analysis)
//          a packet stream that mirrors the live trans_table FSM:
//          one PktTypeDebug packet per (slot, state_change) event.
//
// Holds a per-slot prev_state vector (3 bits × MAX_TRANSACTIONS) and
// compares against the live state each cycle. When any slot transitions
// to a new state, priority-encode the first match and emit a packet
// carrying the slot's address plus the (prev_state, new_state) tuple
// in the high nibbles of the data field.
//
// Drops entirely when ENABLE_DEBUG_LOGIC=0. cfg_debug_enable acts as a
// runtime mask (logic still synthesizes, but emissions are gated).
//
// Sequential. Author: sean galloway. Created: 2026-06-06.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_monitor_reporter_debug
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter int MAX_TRANSACTIONS = 16,
    parameter int IDX_W            = $clog2(MAX_TRANSACTIONS)
)(
    input  logic                        aclk,
    input  logic                        aresetn,

    input  bus_transaction_t            trans_table[MAX_TRANSACTIONS],
    input  logic                        cfg_debug_enable,

    // Top reporter tells us when the output bus is free. Debug packets
    // bypass the FIFO (like threshold/perf) and inject directly, so we
    // need the same "is monbus free?" gate to avoid overwriting an
    // in-flight packet.
    input  logic                        output_busy,
    input  logic                        pkt_taken,   // pulsed when our packet was accepted

    output logic                        pkt_valid,
    output logic [3:0]                  pkt_type,
    output logic [7:0]                  pkt_event_code,
    output logic [8:0]                  pkt_channel,
    output logic [63:0]                 pkt_data
);

    function automatic logic [63:0] pad_address(input logic [31:0] addr);
        return 64'(addr);
    endfunction

    // Per-slot previous state — flopped so we can detect changes.
    transaction_state_t r_prev_state [MAX_TRANSACTIONS];

    // Per-slot change-detected vector (combinational).
    logic [MAX_TRANSACTIONS-1:0] w_changed;
    logic [IDX_W-1:0]            w_sel;
    logic                        w_has_event;

    always_comb begin
        w_changed   = '0;
        w_sel       = '0;
        w_has_event = 1'b0;

        if (cfg_debug_enable) begin
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                // Slot must be valid and its state must differ from the
                // previously captured one. Detecting valid_falling/rising
                // is implicit: when a slot is freed, r_prev_state will
                // reset to IDLE next cycle (see ALWAYS_FF below) so the
                // transition IDLE→IDLE doesn't fire.
                if (trans_table[idx].valid &&
                    trans_table[idx].state != r_prev_state[idx]) begin
                    w_changed[idx] = 1'b1;
                end
            end
            // First-match priority encoder.
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (w_changed[idx] && !w_has_event) begin
                    /* verilator lint_off WIDTHTRUNC */
                    w_sel       = idx[IDX_W-1:0];
                    /* verilator lint_on WIDTHTRUNC */
                    w_has_event = 1'b1;
                end
            end
        end
    end

    // Prev-state update: snapshot the trans_table each cycle. When a
    // slot becomes invalid we reset its prev_state to IDLE so the next
    // allocation triggers a fresh IDLE→ADDR_PHASE transition.
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                r_prev_state[idx] <= TRANS_IDLE;
            end
        end else begin
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (!trans_table[idx].valid) begin
                    r_prev_state[idx] <= TRANS_IDLE;
                end else begin
                    r_prev_state[idx] <= trans_table[idx].state;
                end
            end
        end
    )

    // Output: encode the (prev, new) state tuple into the high bits of
    // the 64-bit data field, address in the low bits. event_code is
    // AXI_DEBUG_STATE_CHANGE; channel comes from the slot. The
    // compression analysis can pull either the tuple OR the address as
    // its dictionary key depending on which carries more entropy.
    //
    // Data layout: {prev_state[2:0], new_state[2:0], 26'h0, addr[31:0]}
    always_comb begin
        pkt_valid      = 1'b0;
        pkt_type       = PktTypeDebug;
        pkt_event_code = AXI_DEBUG_STATE_CHANGE;
        pkt_channel    = '0;
        pkt_data       = '0;

        if (w_has_event && !output_busy) begin
            pkt_valid      = 1'b1;
            pkt_event_code = AXI_DEBUG_STATE_CHANGE;
            pkt_channel    = {3'b0, trans_table[w_sel].channel[5:0]};
            pkt_data       = {
                3'(r_prev_state[w_sel]),
                3'(trans_table[w_sel].state),
                26'h0,
                trans_table[w_sel].addr
            };
        end
    end

    // pkt_taken is unused today — the prev_state flop updates every
    // cycle regardless of whether the packet was emitted, so a missed
    // transition just gets aliased into the next change. Kept on the
    // port list for symmetry with threshold/perf and future hooks
    // (e.g. backpressure on debug packet bursts).
    /* verilator lint_off UNUSED */
    logic unused_pkt_taken;
    assign unused_pkt_taken = pkt_taken;
    /* verilator lint_on UNUSED */

endmodule : axi_monitor_reporter_debug
