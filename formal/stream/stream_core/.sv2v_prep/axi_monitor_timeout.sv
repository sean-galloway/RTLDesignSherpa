// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_timeout
// Purpose: Axi Monitor Timeout module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

/**
 * AXI Monitor Bus Timeout Detector
 *
 * This module monitors the transaction tracking table for potential timeout
 * conditions in each phase of AXI transactions (address, data, response).
 * It uses the timer tick from the frequency invariant timer and the
 * configurable timeout thresholds.
 */

`include "reset_defs.svh"
module axi_monitor_timeout
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
    // NOTE: `import monitor_common_pkg::*; import monitor_amba4_pkg::*; import monitor_amba5_pkg::*; import monitor_arbiter_pkg::*;` intentionally omitted -- its helper
    // functions (get_packet_type etc.) duplicate monitor_common_pkg's, and
    // Vivado flags the duplicates as ambiguous under wildcard imports.
#(
    parameter int MAX_TRANSACTIONS   = 16,   // Maximum outstanding transactions
    parameter int ADDR_WIDTH         = 32,   // Width of address bus
    parameter bit IS_READ            = 1     // 1 for read, 0 for write
)
(
    // Global Clock and Reset
    input  logic                     aclk,
    input  logic                     aresetn,

    // Transaction table (read-modify access) - Fixed: Use unpacked array
    input  bus_transaction_t         trans_table[MAX_TRANSACTIONS],

    // Timer inputs
    input  logic                     timer_tick,    // From frequency invariant timer

    // Timeout configuration
    input  logic [15:0]              cfg_addr_cnt,  // Address phase timeout threshold
    input  logic [15:0]              cfg_data_cnt,  // Data phase timeout threshold
    input  logic [15:0]              cfg_resp_cnt,  // Response phase timeout threshold

    // Packet type configuration
    input  logic                     cfg_timeout_enable, // Enable dedicated timeout packets

    // Output signals
    output logic [MAX_TRANSACTIONS-1:0] timeout_detected   // Indicates which transactions had timeouts
);

    // -------------------------------------------------------------------------
    // Timer accumulators.
    //
    // These used to live inside a private copy of the whole transaction struct
    // that was re-copied from `trans_table` every single cycle. The copy
    // overwrote the accumulators on the cycles between timer ticks, so every
    // timer was pinned at 1 and no threshold above 1 could ever be reached.
    // The timers are now dedicated state, owned solely by this module, and the
    // rest of the transaction record is read live off `trans_table`.
    //
    // cfg_*_cnt counts MICROSECONDS (timer_tick is the 1 us frequency-invariant
    // tick from counter_freq_invariant, which is the whole point of using that
    // counter: a timeout expressed in real time, not in clocks, so it means the
    // same thing at any aclk. 16 bits => up to 65535 us ~= 65 ms, which is long
    // enough that expiry is unambiguously a real timeout rather than a slow bus.
    //
    // These were 4 bits, and every wrapper squashed the host's 16-bit
    // cfg_timeout_cycles down to them with a saturating truncation -- so ANY
    // value >= 16 became 15, and the entire configurable range collapsed onto
    // 1..15 us. A host asking for 50 and a host asking for 100000 got the same
    // hardware.
    // of unused counter per slot.
    // -------------------------------------------------------------------------
    localparam int TIMER_W = 16;   // must hold the full us threshold

    logic [TIMER_W-1:0] r_addr_timer [MAX_TRANSACTIONS];
    logic [TIMER_W-1:0] r_data_timer [MAX_TRANSACTIONS];
    logic [TIMER_W-1:0] r_resp_timer [MAX_TRANSACTIONS];

    // Flag to track if timeouts have been detected for each transaction (flopped)
    logic [MAX_TRANSACTIONS-1:0] r_timeout_detected;

    // cfg_timeout_enable now actually gates detection (it was declared and
    // never referenced — detection ran unconditionally).
    assign timeout_detected = cfg_timeout_enable ? r_timeout_detected
                                                 : {MAX_TRANSACTIONS{1'b0}};

    // -------------------------------------------------------------------------
    // Per-phase "still waiting" conditions, read straight off the live table.
    // -------------------------------------------------------------------------
    logic [MAX_TRANSACTIONS-1:0] w_addr_pending;
    logic [MAX_TRANSACTIONS-1:0] w_data_pending;
    logic [MAX_TRANSACTIONS-1:0] w_resp_pending;
    logic [MAX_TRANSACTIONS-1:0] w_slot_retired;

    always_comb begin
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            // Address phase: command issued but not yet accepted.
            w_addr_pending[idx] = trans_table[idx].valid &&
                                  (trans_table[idx].state == TRANS_ADDR_PHASE) &&
                                  !trans_table[idx].cmd_received;

            // Data phase: command accepted but data not finished.
            //
            // Deliberately does NOT require data_started: "command accepted,
            // first beat never arrives" is precisely the stall a data
            // timeout exists to catch, and with the data_started term it
            // could NEVER fire -- the entry sat in TRANS_ADDR_PHASE for
            // ever, pinned a table slot, and (once enough slots were
            // pinned) held block_ready low permanently. The data timer only
            // runs while this term is true, so a transaction whose command
            // just handshook still gets the full cfg_data_cnt window for
            // its first beat, same as every later beat.
            w_data_pending[idx] = trans_table[idx].valid &&
                                  ((trans_table[idx].state == TRANS_ADDR_PHASE) ||
                                   (trans_table[idx].state == TRANS_DATA_PHASE)) &&
                                  trans_table[idx].cmd_received &&
                                  !trans_table[idx].data_completed;

            // Response phase: write only, data done, B beat outstanding.
            w_resp_pending[idx] = !IS_READ && trans_table[idx].valid &&
                                  (trans_table[idx].state == TRANS_DATA_PHASE) &&
                                  trans_table[idx].data_completed &&
                                  !trans_table[idx].resp_received;

            // Slot no longer in flight — rearm detection for its next occupant.
            //
            // Deliberately NOT cleared on TRANS_ERROR: that is the state a
            // detected timeout puts the transaction into, so clearing on it
            // erases the flag exactly when the reporter needs it. The reporter
            // splits genuine errors from timeouts on this vector
            // (axi_monitor_reporter_error masks slots where it is set,
            // axi_monitor_reporter_timeout claims them), so dropping it here
            // would emit PktTypeError for every timeout and make
            // PktTypeTimeout unreachable.
            //
            // TRANS_COMPLETE still clears it: a transaction that recovered and
            // completed is no longer timing out and should report normally.
            w_slot_retired[idx] = !trans_table[idx].valid ||
                                  (trans_table[idx].state == TRANS_COMPLETE) ||
                                  (trans_table[idx].state == TRANS_IDLE);
        end
    end

    // -------------------------------------------------------------------------
    // Timeout detection logic
    //
    // Each timer counts timer_tick events while its phase is pending and is
    // held at 0 whenever the phase is not pending. Firing on
    // (timer >= cfg_*_cnt) preserves the original threshold semantics.
    // -------------------------------------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                r_addr_timer[idx] <= '0;
                r_data_timer[idx] <= '0;
                r_resp_timer[idx] <= '0;
            end
            r_timeout_detected <= '0;
        end else if (!cfg_timeout_enable) begin
            // Runtime-disabled: flush state, do not just mask the output.
            // Holding detections registered while disabled means a stale bit
            // computed against old timer state resurfaces the instant the
            // enable comes back -- a "detection" with no tick, which formal
            // ap_no_set_without_tick rightly rejects. Disable means inert.
            r_timeout_detected <= '0;
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                r_addr_timer[idx] <= '0;
                r_data_timer[idx] <= '0;
                r_resp_timer[idx] <= '0;
            end
        end else begin
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin

                // Retired slots drop the sticky flag.
                if (w_slot_retired[idx]) begin
                    r_timeout_detected[idx] <= 1'b0;
                end

                // Idle phases hold their timer at zero.
                if (!w_addr_pending[idx]) r_addr_timer[idx] <= '0;
                if (!w_data_pending[idx]) r_data_timer[idx] <= '0;
                if (!w_resp_pending[idx]) r_resp_timer[idx] <= '0;

                if (cfg_timeout_enable && timer_tick && !r_timeout_detected[idx]) begin
                    /* verilator lint_off WIDTHEXPAND */

                    // Address phase timeout detection
                    if (w_addr_pending[idx]) begin
                        if (r_addr_timer[idx] >= cfg_addr_cnt) begin
                            r_timeout_detected[idx] <= 1'b1;
                        end else begin
                            r_addr_timer[idx] <= r_addr_timer[idx] + 1'b1;
                        end
                    end

                    // Data phase timeout detection
                    if (w_data_pending[idx]) begin
                        if (r_data_timer[idx] >= cfg_data_cnt) begin
                            r_timeout_detected[idx] <= 1'b1;
                        end else begin
                            r_data_timer[idx] <= r_data_timer[idx] + 1'b1;
                        end
                    end

                    // Response phase timeout detection (write only)
                    if (w_resp_pending[idx]) begin
                        if (r_resp_timer[idx] >= cfg_resp_cnt) begin
                            r_timeout_detected[idx] <= 1'b1;
                        end else begin
                            r_resp_timer[idx] <= r_resp_timer[idx] + 1'b1;
                        end
                    end

                    /* verilator lint_on WIDTHEXPAND */
                end
            end
        end
    )


endmodule : axi_monitor_timeout
