// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_pktgen_dut
// Purpose: Directed-stimulus harness for the monitor PACKET GENERATION path:
//          axi_monitor_timeout -> axi_monitor_reporter (+ its error / timeout /
//          completion / threshold / perf sub-blocks).
//
// Why a harness at all: both DUTs take the transaction table as an unpacked
// array of `bus_transaction_t`, which a testbench cannot drive directly. This
// module flattens the table into packed vectors so a test can place the table
// in any state it likes -- including states that are hard or impossible to
// reach by driving AXI traffic at a full monitor wrapper, e.g. three slots
// reaching a terminal state in the SAME cycle.
//
// That reachability is the point. The defects this harness covers (per-index
// event marking, cfg_*_enable gating, FIFO pop/load agreement, timeout timer
// accumulation) were all invisible to the full-stack monitor tests because
// those tests cannot construct the exact table + backpressure combinations
// that expose them.
//
// The test plays the role of axi_monitor_trans_mgr: it owns the table and
// updates it in response to event_reported_flags / timeout_detected, exactly
// as trans_mgr does.
//
// Used by: val/amba/test_axi_monitor_pktgen.py
// Author: sean galloway
// Created: 2026-07-20

`timescale 1ns / 1ps

module axi_monitor_pktgen_dut
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter int MAX_TRANSACTIONS = 4,
    parameter int INTR_FIFO_DEPTH  = 8,
    parameter bit IS_READ          = 1'b1
)(
    input  logic                              aclk,
    input  logic                              aresetn,

    // ---------------------------------------------------------------------
    // Flattened transaction table. Slot i occupies bit i (1-bit fields) or
    // [i*W +: W] (wide fields).
    // ---------------------------------------------------------------------
    input  logic [MAX_TRANSACTIONS-1:0]       slot_valid,
    input  logic [(MAX_TRANSACTIONS*3)-1:0]   slot_state,
    input  logic [MAX_TRANSACTIONS-1:0]       slot_cmd_received,
    input  logic [MAX_TRANSACTIONS-1:0]       slot_data_started,
    input  logic [MAX_TRANSACTIONS-1:0]       slot_data_completed,
    input  logic [MAX_TRANSACTIONS-1:0]       slot_resp_received,
    input  logic [(MAX_TRANSACTIONS*32)-1:0]  slot_addr,
    input  logic [(MAX_TRANSACTIONS*8)-1:0]   slot_event_code,
    input  logic [(MAX_TRANSACTIONS*6)-1:0]   slot_channel,
    input  logic [(MAX_TRANSACTIONS*32)-1:0]  slot_addr_timestamp,
    input  logic [(MAX_TRANSACTIONS*32)-1:0]  slot_data_timestamp,

    // ---------------------------------------------------------------------
    // Timeout detector
    // ---------------------------------------------------------------------
    input  logic                              timer_tick,
    input  logic [3:0]                        cfg_addr_cnt,
    input  logic [3:0]                        cfg_data_cnt,
    input  logic [3:0]                        cfg_resp_cnt,
    output logic [MAX_TRANSACTIONS-1:0]       timeout_detected,

    // ---------------------------------------------------------------------
    // Reporter configuration
    // ---------------------------------------------------------------------
    input  logic                              cfg_error_enable,
    input  logic                              cfg_compl_enable,
    input  logic                              cfg_threshold_enable,
    input  logic                              cfg_timeout_enable,
    input  logic                              cfg_perf_enable,
    input  logic                              cfg_debug_enable,
    input  logic [15:0]                       active_trans_threshold,
    input  logic [31:0]                       latency_threshold,

    // ---------------------------------------------------------------------
    // Monitor bus + feedback
    // ---------------------------------------------------------------------
    input  logic                              monbus_ready,
    output logic                              monbus_valid,
    output monitor_packet_t                   monbus_packet,
    output logic [15:0]                       event_count,
    output logic [15:0]                       perf_completed_count,
    output logic [15:0]                       perf_error_count,
    output logic [MAX_TRANSACTIONS-1:0]       event_reported_flags
);

    // -------------------------------------------------------------------------
    // Rebuild the unpacked transaction table from the flattened drive vectors.
    // -------------------------------------------------------------------------
    bus_transaction_t w_trans_table [MAX_TRANSACTIONS];

    always_comb begin
        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            w_trans_table[i]                 = '0;
            w_trans_table[i].valid           = slot_valid[i];
            w_trans_table[i].state            = transaction_state_t'(slot_state[i*3 +: 3]);
            w_trans_table[i].cmd_received     = slot_cmd_received[i];
            w_trans_table[i].data_started     = slot_data_started[i];
            w_trans_table[i].data_completed   = slot_data_completed[i];
            w_trans_table[i].resp_received    = slot_resp_received[i];
            w_trans_table[i].addr             = slot_addr[i*32 +: 32];
            w_trans_table[i].channel          = slot_channel[i*6 +: 6];
            w_trans_table[i].event_code.raw_code = slot_event_code[i*8 +: 8];
            w_trans_table[i].addr_timestamp   = slot_addr_timestamp[i*32 +: 32];
            w_trans_table[i].data_timestamp   = slot_data_timestamp[i*32 +: 32];
            w_trans_table[i].resp_timestamp   = slot_data_timestamp[i*32 +: 32];
        end
    end

    // -------------------------------------------------------------------------
    // DUT 1: timeout detector. Its timeout_detected feeds the reporter exactly
    // as it does inside axi_monitor_base.
    // -------------------------------------------------------------------------
    axi_monitor_timeout #(
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .ADDR_WIDTH       (32),
        .IS_READ          (IS_READ)
    ) u_timeout (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .trans_table        (w_trans_table),
        .timer_tick         (timer_tick),
        .cfg_addr_cnt       (cfg_addr_cnt),
        .cfg_data_cnt       (cfg_data_cnt),
        .cfg_resp_cnt       (cfg_resp_cnt),
        .cfg_timeout_enable (cfg_timeout_enable),
        .timeout_detected   (timeout_detected)
    );

    // -------------------------------------------------------------------------
    // DUT 2: reporter dispatcher + all six packet-type sub-blocks.
    // -------------------------------------------------------------------------
    axi_monitor_reporter #(
        .MAX_TRANSACTIONS      (MAX_TRANSACTIONS),
        .ADDR_WIDTH            (32),
        .UNIT_ID               (8'h09),
        .AGENT_ID              (16'h0063),
        .IS_READ               (IS_READ),
        .INTR_FIFO_DEPTH       (INTR_FIFO_DEPTH),
        .ENABLE_ERROR_LOGIC    (1'b1),
        .ENABLE_TIMEOUT_LOGIC  (1'b1),
        .ENABLE_COMPL_LOGIC    (1'b1),
        .ENABLE_THRESHOLD_LOGIC(1'b1),
        .ENABLE_PERF_LOGIC     (1'b1),
        .ENABLE_DEBUG_LOGIC    (1'b0)
    ) u_reporter (
        .aclk                  (aclk),
        .aresetn               (aresetn),
        .trans_table           (w_trans_table),
        .timeout_detected      (timeout_detected),
        // This DUT drives trans_table itself and exercises no address filter,
        // so no slot is suppressed. Tied off explicitly rather than left
        // unconnected: an omitted input reads as 0 and gives the same answer
        // by accident, which is how this pin went missing unnoticed.
        .filtered_mask         ('0),
        .cfg_error_enable      (cfg_error_enable),
        .cfg_compl_enable      (cfg_compl_enable),
        .cfg_threshold_enable  (cfg_threshold_enable),
        .cfg_timeout_enable    (cfg_timeout_enable),
        .cfg_perf_enable       (cfg_perf_enable),
        .cfg_debug_enable      (cfg_debug_enable),
        .monbus_ready          (monbus_ready),
        .monbus_valid          (monbus_valid),
        .monbus_packet         (monbus_packet),
        .event_count           (event_count),
        .perf_completed_count  (perf_completed_count),
        .perf_error_count      (perf_error_count),
        .active_trans_threshold(active_trans_threshold),
        .latency_threshold     (latency_threshold),
        .event_reported_flags  (event_reported_flags)
    );

endmodule : axi_monitor_pktgen_dut
