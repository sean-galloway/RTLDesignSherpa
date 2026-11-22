// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: onyx_counters
// Purpose:
//   Exact event counters beside the MonBus observer (D9): six 32-bit
//   saturating counters on onyx_ccu's event taps -- transactions granted,
//   lines a peer supplied, memory reads issued, reads wasted (issued, then
//   the line was supplied), absorptions, write-backs.  Cleared by a pulse,
//   held by a level (the harness CSR's tally_clear and tally_freeze, so one
//   host protocol snapshots the tally bins and these together).
//
//   Why both: the MonBus carries every event with its payload and timing,
//   at one packet a cycle through a bounded queue, and reports what it
//   drops; the counts the D6 measurement is made of (reads issued against
//   reads wasted) have to be exact under any burst, and a counter is the
//   honest instrument for a count.
//
// Documentation: projects/components/cache-ip/onyx-ace-ccu/docs/onyx_has/ch04_interfaces/04_observation_monbus.md
// Subsystem: onyx (cache-ip)
//
// Author: sean galloway
// Created: 2026-11-21
`timescale 1ns / 1ps
`include "reset_defs.svh"

module onyx_counters #(
    parameter int N_PORTS = 2
) (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        clear_i,        // one-cycle pulse: all counters to zero
    input  logic        freeze_i,       // level: hold
    input  logic                evt_grant_i,
    input  logic [N_PORTS-1:0]  evt_gather_i,       // per answering port
    input  logic [N_PORTS-1:0]  evt_gather_dt_i,
    input  logic                evt_mem_ar_i,
    input  logic [N_PORTS-1:0]  evt_read_wasted_i,  // per answering port
    input  logic        evt_absorb_i,
    input  logic        evt_wb_i,
    output logic [31:0] cnt_txn_o,
    output logic [31:0] cnt_supplied_o,
    output logic [31:0] cnt_mem_read_o,
    output logic [31:0] cnt_read_wasted_o,
    output logic [31:0] cnt_absorb_o,
    output logic [31:0] cnt_wb_o
);
    // the per-port events can fire on several ports in one cycle: count them
    localparam int PC_W = $clog2(N_PORTS + 1);
    logic [31:0]     r_cnt [6];
    logic [PC_W-1:0] w_inc [6];
    always_comb begin
        w_inc[0] = PC_W'(evt_grant_i);
        w_inc[1] = '0;
        w_inc[2] = PC_W'(evt_mem_ar_i);
        w_inc[3] = '0;
        w_inc[4] = PC_W'(evt_absorb_i);
        w_inc[5] = PC_W'(evt_wb_i);
        for (int p = 0; p < N_PORTS; p++) begin
            w_inc[1] = w_inc[1] + PC_W'(evt_gather_i[p] & evt_gather_dt_i[p]);
            w_inc[3] = w_inc[3] + PC_W'(evt_read_wasted_i[p]);
        end
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int k = 0; k < 6; k++) r_cnt[k] <= '0;
        end else if (clear_i) begin
            for (int k = 0; k < 6; k++) r_cnt[k] <= '0;
        end else if (!freeze_i) begin
            for (int k = 0; k < 6; k++)
                if (r_cnt[k] <= 32'hFFFF_FFFF - 32'(N_PORTS)) r_cnt[k] <= r_cnt[k] + 32'(w_inc[k]);
        end
    )
    assign cnt_txn_o         = r_cnt[0];
    assign cnt_supplied_o    = r_cnt[1];
    assign cnt_mem_read_o    = r_cnt[2];
    assign cnt_read_wasted_o = r_cnt[3];
    assign cnt_absorb_o      = r_cnt[4];
    assign cnt_wb_o          = r_cnt[5];
endmodule : onyx_counters
