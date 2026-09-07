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
    // NOTE: `import monitor_pkg::*;` intentionally omitted -- its helper
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
    // TODO(MON-TIMEOUT-CAP): Timeout packets saturate at a couple of dozen per
    // reset; every other class reports thousands from the same traffic.
    //
    // MEASURED (Genesys 2 build-obs, 4ch, 60 MHz, 2026-09-07, three reps over
    // both observers, slave response delayed 2048 cycles so transactions
    // genuinely expire):
    //
    //     compl 13470   perf 1138364   addrmatch 13230   error 13206
    //     threshold 13206   debug 13212   TIMEOUT 21
    //
    // 21 is the odd one out by three orders of magnitude, and it is close to
    // the table depth -- which is the shape of "each slot reports at most once
    // and is then never reusable for another timeout", not of a stimulus or
    // keying problem. The stimulus is known good: the same run produced 13206
    // threshold packets from the identical delayed traffic.
    //
    // DO NOT "fix" this by adding TRANS_ERROR to w_slot_retired above. That is
    // deliberate and the comment there explains it: a detected timeout is what
    // puts the entry INTO TRANS_ERROR, the error reporter masks slots whose
    // r_timeout_detected is set and the timeout reporter claims them, so
    // clearing on TRANS_ERROR erases the flag exactly when the reporter needs
    // it and makes PktTypeTimeout unreachable entirely. That trade was already
    // made once; do not re-make it.
    //
    // The intended lifecycle, which is what to instrument:
    //     phase timer expires -> r_timeout_detected[idx] sticky
    //     -> trans_mgr moves the entry to TRANS_ERROR
    //     -> axi_monitor_reporter_timeout claims it (state == TRANS_ERROR &&
    //        cfg_timeout_enable && timeout_detected[idx])
    //     -> axi_monitor_reporter marks event_reported, but ONLY on
    //        w_fifo_wr_accept (an ACCEPTED monbus FIFO write)
    //     -> trans_mgr's w_can_cleanup frees the slot (TRANS_ERROR is in that
    //        set, gated on event_reported)
    //     -> w_slot_retired clears r_timeout_detected and the slot is reusable.
    //
    // Every link exists, so the loop should recycle indefinitely. Find which
    // link does not close before changing anything. Prime suspects, cheapest
    // first:
    //   1. Reporter arbitration starvation. Priority in axi_monitor_reporter is
    //      error > timeout > compl, and only ONE slot is marked per accepted
    //      FIFO write. Under heavy completion traffic the timeout sub-block may
    //      simply never win, leaving slots stuck in TRANS_ERROR unreported and
    //      therefore unfreeable.
    //   2. FIFO backpressure. event_reported is produced ONLY by
    //      w_fifo_wr_accept, so a full monbus FIFO stalls retirement as well as
    //      reporting; the entry stays terminal-but-unreported.
    //   3. A genuinely stuck phase-pending: if w_addr/data/resp_pending never
    //      drops for an expired entry, the slot is consumed even after report.
    //
    // Instrument, do not guess: the cosim harness can count reporter grants per
    // class and sample active_count. If (1), the fix is a fairness/aging term in
    // the reporter's priority mux, NOT a change to the retire policy here.
    //
    // Board-visible consequence today: timeout is the one class the obs
    // campaign cannot drive above its 1000-packet floor, so host_obs_matrix.py
    // exits 1 on an otherwise clean 6/7 run. Coverage of the class is proven
    // (packets DO arrive, just not many); throughput of the class is not.
    //
    // Scope note: this file is shared rtl/amba, consumed by every *_mon variant
    // and by pumice. Any change here needs the full monitor formal set plus the
    // val/amba monitor subset, not just the Genesys 2 campaign.
    // -------------------------------------------------------------------------

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
