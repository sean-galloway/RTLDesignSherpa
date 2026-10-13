// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_reporter_error
// Purpose: Error-packet detection cone (split out of axi_monitor_reporter
//          so integrators can drop it with ENABLE_ERROR_LOGIC=0 and pay
//          zero LUT cost for the per-slot scan + priority encoder).
//
// Scans the transaction table for unreported ERROR (non-timeout) and
// ORPHANED transactions, priority-encodes the first match, and emits the
// packet fields for the top reporter to push into the shared monbus FIFO.
//
// Pure combinational. Threshold flags + event_reported feedback stay in
// the top reporter (shared state).
//
// Author: sean galloway
// Created: 2026-06-06

`timescale 1ns / 1ps

module axi_monitor_reporter_error
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter int MAX_TRANSACTIONS = 16,
    parameter int IDX_W            = $clog2(MAX_TRANSACTIONS)
)(
    input  bus_transaction_t            trans_table[MAX_TRANSACTIONS],
    input  logic [MAX_TRANSACTIONS-1:0] event_reported,
    input  logic [MAX_TRANSACTIONS-1:0] timeout_detected,
    input  logic                        cfg_error_enable,

    output logic                        pkt_valid,
    output logic [3:0]                  pkt_type,
    output logic [7:0]                  pkt_event_code,
    output logic [8:0]                  pkt_channel,
    output logic [63:0]                 pkt_data,
    output logic [IDX_W-1:0]            sel_idx
);

    function automatic logic [63:0] pad_address(input logic [31:0] addr);
        return 64'(addr);
    endfunction

    logic [MAX_TRANSACTIONS-1:0] w_events;
    logic [IDX_W-1:0]            w_sel;
    logic                        w_has_event;

    always_comb begin
        w_events    = '0;
        w_sel       = '0;
        w_has_event = 1'b0;

        // Scan: ERROR-but-not-timeout, or ORPHANED.
        // timeout_detected lets us separate genuine errors from timeouts
        // so the timeout sub-block can claim the latter without aliasing.
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (trans_table[idx].valid && !event_reported[idx] && cfg_error_enable &&
                    ((trans_table[idx].state == TRANS_ERROR && !timeout_detected[idx]) ||
                     (trans_table[idx].state == TRANS_ORPHANED))) begin
                w_events[idx] = 1'b1;
            end
        end

        // First-match priority encoder.
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (w_events[idx] && !w_has_event) begin
                /* verilator lint_off WIDTHTRUNC */
                w_sel       = idx[IDX_W-1:0];
                /* verilator lint_on WIDTHTRUNC */
                w_has_event = 1'b1;
            end
        end
    end

    assign pkt_valid      = w_has_event;
    assign sel_idx        = w_sel;
    assign pkt_type       = PktTypeError;
    assign pkt_event_code = trans_table[w_sel].event_code.raw_code;
    assign pkt_channel    = {3'b0, trans_table[w_sel].channel[5:0]};
    assign pkt_data       = pad_address(trans_table[w_sel].addr);

endmodule : axi_monitor_reporter_error
