// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_monitor_timeout
// Purpose: Axi Monitor Timeout module
//
// Documentation: rtl/amba/PRD.md
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
    import monitor_pkg::*;
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
    input  logic [3:0]               cfg_addr_cnt,  // Address phase timeout threshold
    input  logic [3:0]               cfg_data_cnt,  // Data phase timeout threshold
    input  logic [3:0]               cfg_resp_cnt,  // Response phase timeout threshold

    // Packet type configuration
    input  logic                     cfg_timeout_enable, // Enable dedicated timeout packets

    // Output signals
    output logic [MAX_TRANSACTIONS-1:0] timeout_detected   // Indicates which transactions had timeouts
);

    // Local copy of transaction table for modifications (flopped) - use unpacked array
    bus_transaction_t r_trans_table_local[MAX_TRANSACTIONS];

    // Flag to track if timeouts have been detected for each transaction (flopped)
    logic [MAX_TRANSACTIONS-1:0] r_timeout_detected;
    assign timeout_detected = r_timeout_detected;

    // Timeout detection logic
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            // Reset local table
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                r_trans_table_local[idx] <= '0;
            end
            r_timeout_detected <= '0;
        end else begin
            // Update local table from input and process individually
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                r_trans_table_local[idx] <= trans_table[idx];

                // If this transaction has a state change to non-active, mark it as no longer timing out
                if (trans_table[idx].state == TRANS_COMPLETE ||
                    trans_table[idx].state == TRANS_ERROR ||
                    trans_table[idx].state == TRANS_IDLE) begin
                    r_timeout_detected[idx] <= 1'b0;
                end
            end

            // If timer tick, check for timeouts
            if (timer_tick) begin
                for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                    if (r_trans_table_local[idx].valid && !r_timeout_detected[idx]) begin

                        // Address phase timeout detection
                        if (r_trans_table_local[idx].state == TRANS_ADDR_PHASE &&
                            !r_trans_table_local[idx].cmd_received) begin

                            // Increment address timer
                            r_trans_table_local[idx].addr_timer <= r_trans_table_local[idx].addr_timer + 1'b1;

                            // Check for timeout
                            /* verilator lint_off WIDTHEXPAND */
                            if (r_trans_table_local[idx].addr_timer >= {12'h0, cfg_addr_cnt}) begin
                            /* verilator lint_on WIDTHEXPAND */
                                r_trans_table_local[idx].state <= TRANS_ERROR;
                                r_trans_table_local[idx].event_code.axi_timeout <= EVT_CMD_TIMEOUT;
                                r_timeout_detected[idx] <= 1'b1;
                            end
                        end

                        // Data phase timeout detection
                        if ((r_trans_table_local[idx].state == TRANS_ADDR_PHASE ||
                                r_trans_table_local[idx].state == TRANS_DATA_PHASE) &&
                                r_trans_table_local[idx].cmd_received &&
                                r_trans_table_local[idx].data_started &&
                                !r_trans_table_local[idx].data_completed) begin

                            // Increment data timer
                            r_trans_table_local[idx].data_timer <= r_trans_table_local[idx].data_timer + 1'b1;

                            // Check for timeout
                            /* verilator lint_off WIDTHEXPAND */
                            if (r_trans_table_local[idx].data_timer >= {12'h0, cfg_data_cnt}) begin
                            /* verilator lint_on WIDTHEXPAND */
                                r_trans_table_local[idx].state <= TRANS_ERROR;
                                r_trans_table_local[idx].event_code.axi_timeout <= EVT_DATA_TIMEOUT;
                                r_timeout_detected[idx] <= 1'b1;
                            end
                        end

                        // Response phase timeout detection (write only)
                        if (!IS_READ &&
                            r_trans_table_local[idx].state == TRANS_DATA_PHASE &&
                            r_trans_table_local[idx].data_completed &&
                            !r_trans_table_local[idx].resp_received) begin

                            // Increment response timer
                            r_trans_table_local[idx].resp_timer <= r_trans_table_local[idx].resp_timer + 1'b1;

                            // Check for timeout
                            /* verilator lint_off WIDTHEXPAND */
                            if (r_trans_table_local[idx].resp_timer >= {12'h0, cfg_resp_cnt}) begin
                            /* verilator lint_on WIDTHEXPAND */
                                r_trans_table_local[idx].state <= TRANS_ERROR;
                                r_trans_table_local[idx].event_code.axi_timeout <= EVT_RESP_TIMEOUT;
                                r_timeout_detected[idx] <= 1'b1;
                            end
                        end
                    end
                end
            end
        end
    )


endmodule : axi_monitor_timeout
