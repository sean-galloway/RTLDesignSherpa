// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_reporter_perf
// Purpose: Perf packet generator (split out of axi_monitor_reporter so
//          integrators can drop it with ENABLE_PERF_LOGIC=0). Owns the
//          completion/error counters and the 5-state cycle FSM that
//          decides when to publish a count-rollup packet.
//
// Counters are driven from the top reporter via error_marked_mask and
// compl_marked_mask (set whenever the top accepts that event into the
// FIFO). Output emits ONE packet at a time via pkt_valid; the top
// strobes pkt_taken when accepted.
//
// NOTE: This sub-block runs in parallel with Stage A/B perfmon counters
// in axi_monitor_base; those are window-buckets emitted via PktTypePerfWin/
// PerfHist, while this one emits the legacy PktTypePerf packets that
// roll up completion/error counts over the lifetime of the monitor.
//
// Sequential. Author: sean galloway. Created: 2026-06-06.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_monitor_reporter_perf
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    parameter int MAX_TRANSACTIONS = 16
)(
    input  logic                        aclk,
    input  logic                        aresetn,

    input  logic                        cfg_perf_enable,
    input  logic                        output_busy,        // FIFO has data or monbus_valid
    input  logic                        pkt_taken,          // our packet was accepted
    input  logic [MAX_TRANSACTIONS-1:0] error_marked_mask,  // events marked-reported this cycle
    input  logic [MAX_TRANSACTIONS-1:0] compl_marked_mask,

    output logic                        pkt_valid,
    output logic [3:0]                  pkt_type,
    output logic [7:0]                  pkt_event_code,
    output logic [8:0]                  pkt_channel,
    output logic [63:0]                 pkt_data,

    // Lifetime counters — exposed for status / debug.
    output logic [15:0]                 perf_completed_count,
    output logic [15:0]                 perf_error_count
);

    // Lifetime counters.
    logic [15:0] r_completed_count;
    logic [15:0] r_error_count;
    assign perf_completed_count = r_completed_count;
    assign perf_error_count     = r_error_count;

    // 5-state cycle FSM (matches the original reporter behavior 1:1).
    logic [2:0] r_state;
    logic [2:0] w_next_state;
    logic       w_gen_completed;
    logic       w_gen_errors;

    always_comb begin
        w_next_state    = r_state;
        w_gen_completed = 1'b0;
        w_gen_errors    = 1'b0;

        if (cfg_perf_enable && !output_busy) begin
            case (r_state)
                3'h0: w_next_state = 3'h1;  // ADDR_LATENCY  (no packet — addr/data/total
                3'h1: w_next_state = 3'h2;  // DATA_LATENCY   latency states were placeholders)
                3'h2: w_next_state = 3'h3;  // TOTAL_LATENCY
                3'h3: begin                 // COMPLETED_COUNT
                    w_next_state = 3'h4;
                    if (r_completed_count > 0) w_gen_completed = 1'b1;
                end
                3'h4: begin                 // ERROR_COUNT
                    w_next_state = 3'h0;
                    if (r_error_count > 0)     w_gen_errors    = 1'b1;
                end
                default: w_next_state = 3'h0;
            endcase
        end
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_completed_count <= '0;
            r_error_count     <= '0;
            r_state           <= 3'h0;
        end else begin
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (error_marked_mask[idx]) r_error_count     <= r_error_count     + 1'b1;
                if (compl_marked_mask[idx]) r_completed_count <= r_completed_count + 1'b1;
            end
            r_state <= w_next_state;
        end
    )

    // Output mux: completion-count first, then error-count.
    always_comb begin
        pkt_valid      = 1'b0;
        pkt_type       = PktTypePerf;
        pkt_event_code = AXI_PERF_COMPLETED_COUNT;
        pkt_channel    = '0;
        pkt_data       = '0;

        if (w_gen_completed) begin
            pkt_valid      = 1'b1;
            pkt_event_code = AXI_PERF_COMPLETED_COUNT;
            pkt_data       = 64'(r_completed_count);
        end else if (w_gen_errors) begin
            pkt_valid      = 1'b1;
            pkt_event_code = AXI_PERF_ERROR_COUNT;
            pkt_data       = 64'(r_error_count);
        end
    end

    // pkt_taken is unused here today — counters update from masks regardless
    // of whether the top emits. Kept on the port list for future hooks
    // (e.g., back-pressure on packet bursts).
    /* verilator lint_off UNUSED */
    logic unused_pkt_taken;
    assign unused_pkt_taken = pkt_taken;
    /* verilator lint_on UNUSED */

endmodule : axi_monitor_reporter_perf
