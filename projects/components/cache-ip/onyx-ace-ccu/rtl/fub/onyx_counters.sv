// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: onyx_counters
// Purpose:
//   Exact event counters beside the MonBus observer (D9): eight 32-bit
//   saturating counters on onyx_ccu's event taps -- transactions granted,
//   lines a peer supplied, memory reads issued, reads wasted (issued, then
//   the line was supplied), absorptions, write-backs, and two corner
//   counts:
//     cu_dt   CleanUnique slots whose gather ended with data (a killed
//             upgrade's peer passed the line dirty -- onyx BUG-001's case)
//     old_wb  cache writes first presented on a line a slot still gathers
//             (the write is OLDER than that slot's verdict: a victim drain
//             the snoop passed on, jet-prime BUG-002; the order onyx
//             BUG-003 fixed).  It mirrors onyx_ccu's r_aw_old from the
//             grant and gather taps: per slot, its line and "still
//             gathering" (set at the grant, cleared by the slot's last CR
//             or when the slot frees), so onyx_ccu needs no extra port.
//   Cleared by a pulse,
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
    parameter int N_PORTS    = 2,
    parameter int SLOTS      = 18,
    parameter int ADDR_WIDTH = 32,
    parameter int LINE_BYTES = 64,
    localparam int SLOT_W = (SLOTS > 1) ? $clog2(SLOTS) : 1,
    localparam int OFF_W  = $clog2(LINE_BYTES)
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
    // the corner counts' taps
    input  logic [SLOT_W-1:0]      evt_grant_slot_i,
    /* verilator lint_off UNUSEDSIGNAL */      // the line offset bits
    input  logic [ADDR_WIDTH-1:0]  evt_grant_addr_i,
    /* verilator lint_on UNUSEDSIGNAL */
    input  logic                   evt_grant_cu_i,      // the grant is a CleanUnique
    input  logic [SLOT_W-1:0]      evt_gather_slot_i [N_PORTS],
    input  logic [SLOTS-1:0]       slot_vld_i,
    input  logic [N_PORTS-1:0]     c_awvalid_i,
    input  logic [N_PORTS-1:0]     c_awready_i,
    /* verilator lint_off UNUSEDSIGNAL */
    input  logic [ADDR_WIDTH-1:0]  c_awaddr_i [N_PORTS],
    /* verilator lint_on UNUSEDSIGNAL */
    output logic [31:0] cnt_txn_o,
    output logic [31:0] cnt_supplied_o,
    output logic [31:0] cnt_mem_read_o,
    output logic [31:0] cnt_read_wasted_o,
    output logic [31:0] cnt_absorb_o,
    output logic [31:0] cnt_wb_o,
    output logic [31:0] cnt_cu_dt_o,
    output logic [31:0] cnt_old_wb_o
);
    localparam int NC = 8;
    localparam int LW = ADDR_WIDTH - OFF_W;

    // per-slot mirror: the granted line, CleanUnique, still gathering
    logic [LW-1:0]      r_sl_line [SLOTS];
    logic [SLOTS-1:0]   r_sl_cu, r_sl_gath;
    logic [N_PORTS-1:0] r_aw_old;           // onyx_ccu's r_aw_old, mirrored
    logic [N_PORTS-1:0] w_aw_gblk;          // a slot on the write's line still gathers
    logic [SLOTS-1:0]   w_gath_done;
    logic [N_PORTS-1:0] w_cu_dt, w_old_wb;  // the two corner events, per port
    always_comb begin
        w_gath_done = '0;
        for (int p = 0; p < N_PORTS; p++)
            if (evt_gather_i[p]) w_gath_done[evt_gather_slot_i[p]] = 1'b1;
        for (int p = 0; p < N_PORTS; p++) begin
            w_aw_gblk[p] = 1'b0;
            for (int s = 0; s < SLOTS; s++)
                if (slot_vld_i[s] && r_sl_gath[s]
                        && (r_sl_line[s] == c_awaddr_i[p][ADDR_WIDTH-1:OFF_W]))
                    w_aw_gblk[p] = 1'b1;
            w_cu_dt[p]  = evt_gather_i[p] & evt_gather_dt_i[p] & r_sl_cu[evt_gather_slot_i[p]];
            // not in its accepting cycle: a write the port selected before
            // the slot's grant completes its AW then, ahead of the slot on
            // the one write port, and is not old (onyx_ccu's r_aw_old
            // excludes it the same way)
            w_old_wb[p] = c_awvalid_i[p] & ~c_awready_i[p] & w_aw_gblk[p] & ~r_aw_old[p];
        end
    end
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_sl_cu   <= '0;
            r_sl_gath <= '0;
            r_aw_old  <= '0;
        end else begin
            r_sl_gath <= r_sl_gath & slot_vld_i & ~w_gath_done;
            if (evt_grant_i) begin
                r_sl_gath[evt_grant_slot_i] <= 1'b1;
                r_sl_cu[evt_grant_slot_i]   <= evt_grant_cu_i;
            end
            r_aw_old <= c_awvalid_i & ~c_awready_i & (r_aw_old | w_aw_gblk);
        end
    )
    // the line store carries no reset (it is read only under r_sl_gath)
    always_ff @(posedge clk) begin
        if (evt_grant_i) r_sl_line[evt_grant_slot_i] <= evt_grant_addr_i[ADDR_WIDTH-1:OFF_W];
    end

    // the per-port events can fire on several ports in one cycle: count them
    localparam int PC_W = $clog2(N_PORTS + 1);
    logic [31:0]     r_cnt [NC];
    logic [PC_W-1:0] w_inc [NC];
    always_comb begin
        w_inc[0] = PC_W'(evt_grant_i);
        w_inc[1] = '0;
        w_inc[2] = PC_W'(evt_mem_ar_i);
        w_inc[3] = '0;
        w_inc[4] = PC_W'(evt_absorb_i);
        w_inc[5] = PC_W'(evt_wb_i);
        w_inc[6] = '0;
        w_inc[7] = '0;
        for (int p = 0; p < N_PORTS; p++) begin
            w_inc[1] = w_inc[1] + PC_W'(evt_gather_i[p] & evt_gather_dt_i[p]);
            w_inc[3] = w_inc[3] + PC_W'(evt_read_wasted_i[p]);
            w_inc[6] = w_inc[6] + PC_W'(w_cu_dt[p]);
            w_inc[7] = w_inc[7] + PC_W'(w_old_wb[p]);
        end
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int k = 0; k < NC; k++) r_cnt[k] <= '0;
        end else if (clear_i) begin
            for (int k = 0; k < NC; k++) r_cnt[k] <= '0;
        end else if (!freeze_i) begin
            for (int k = 0; k < NC; k++)
                if (r_cnt[k] <= 32'hFFFF_FFFF - 32'(N_PORTS)) r_cnt[k] <= r_cnt[k] + 32'(w_inc[k]);
        end
    )
    assign cnt_txn_o         = r_cnt[0];
    assign cnt_supplied_o    = r_cnt[1];
    assign cnt_mem_read_o    = r_cnt[2];
    assign cnt_read_wasted_o = r_cnt[3];
    assign cnt_absorb_o      = r_cnt[4];
    assign cnt_wb_o          = r_cnt[5];
    assign cnt_cu_dt_o       = r_cnt[6];
    assign cnt_old_wb_o      = r_cnt[7];
endmodule : onyx_counters
