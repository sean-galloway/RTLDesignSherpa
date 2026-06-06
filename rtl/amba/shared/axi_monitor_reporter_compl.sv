// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_reporter_compl
// Purpose: Completion-packet detection cone (split out of axi_monitor_reporter
//          so integrators can drop it with ENABLE_COMPL_LOGIC=0).
//
// Scans for unreported TRANS_COMPLETE slots, priority-encodes the first
// match, and emits the packet fields.
//
// Pure combinational. Author: sean galloway. Created: 2026-06-06.

`timescale 1ns / 1ps

module axi_monitor_reporter_compl
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter int MAX_TRANSACTIONS = 16,
    parameter int IDX_W            = $clog2(MAX_TRANSACTIONS)
)(
    input  bus_transaction_t            trans_table[MAX_TRANSACTIONS],
    input  logic [MAX_TRANSACTIONS-1:0] event_reported,
    input  logic                        cfg_compl_enable,

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

        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (trans_table[idx].valid && !event_reported[idx] &&
                trans_table[idx].state == TRANS_COMPLETE && cfg_compl_enable) begin
                w_events[idx] = 1'b1;
            end
        end

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
    assign pkt_type       = PktTypeCompletion;
    assign pkt_event_code = EVT_TRANS_COMPLETE;
    assign pkt_channel    = {3'b0, trans_table[w_sel].channel[5:0]};
    assign pkt_data       = pad_address(trans_table[w_sel].addr);

endmodule : axi_monitor_reporter_compl
