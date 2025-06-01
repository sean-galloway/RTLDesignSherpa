`timescale 1ns / 1ps

/**
 * AXI Interrupt Bus Timeout Detector
 *
 * This module monitors the transaction tracking table for potential timeout
 * conditions in each phase of AXI transactions (address, data, response).
 * It uses the timer tick from the frequency invariant timer and the
 * configurable timeout thresholds.
 *
 * Updated to support dedicated timeout packet types.
 * Updated with proper naming conventions: w_ for combo, r_ for flopped
 * Fixed for Verilator compatibility and consistent array declarations
 */
module axi_errmon_timeout
    import axi_errmon_types::*;
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
    input  axi_transaction_t         i_trans_table[MAX_TRANSACTIONS],

    // Timer inputs
    input  logic                     i_timer_tick,    // From frequency invariant timer

    // Timeout configuration
    input  logic [3:0]               i_cfg_addr_cnt,  // Address phase timeout threshold
    input  logic [3:0]               i_cfg_data_cnt,  // Data phase timeout threshold
    input  logic [3:0]               i_cfg_resp_cnt,  // Response phase timeout threshold

    // Packet type configuration
    input  logic                     i_cfg_timeout_enable, // Enable dedicated timeout packets

    // Output signals
    output logic [MAX_TRANSACTIONS-1:0] o_timeout_detected   // Indicates which transactions had timeouts
);

    // Local copy of transaction table for modifications (flopped) - use unpacked array
    axi_transaction_t r_trans_table_local[MAX_TRANSACTIONS];

    // Flag to track if timeouts have been detected for each transaction (flopped)
    logic [MAX_TRANSACTIONS-1:0] r_timeout_detected;
    assign o_timeout_detected = r_timeout_detected;

    // Timeout detection logic
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            // Reset local table
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                r_trans_table_local[idx] <= '0;
            end
            r_timeout_detected <= '0;
        end else begin
            // Update local table from input and process individually
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                r_trans_table_local[idx] <= i_trans_table[idx];

                // If this transaction has a state change to non-active, mark it as no longer timing out
                if (i_trans_table[idx].state == TRANS_COMPLETE ||
                    i_trans_table[idx].state == TRANS_ERROR ||
                    i_trans_table[idx].state == TRANS_EMPTY) begin
                    r_timeout_detected[idx] <= 1'b0;
                end
            end

            // If timer tick, check for timeouts
            if (i_timer_tick) begin
                for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                    if (r_trans_table_local[idx].valid && !r_timeout_detected[idx]) begin

                        // Address phase timeout detection
                        if (r_trans_table_local[idx].state == TRANS_ADDR_PHASE &&
                            !r_trans_table_local[idx].addr_received) begin

                            // Increment address timer
                            r_trans_table_local[idx].addr_timer <= r_trans_table_local[idx].addr_timer + 1'b1;

                            // Check for timeout
                            /* verilator lint_off WIDTHEXPAND */
                            if (r_trans_table_local[idx].addr_timer >= {12'h0, i_cfg_addr_cnt}) begin
                            /* verilator lint_on WIDTHEXPAND */
                                r_trans_table_local[idx].state <= TRANS_ERROR;
                                r_trans_table_local[idx].error_code <= EVT_ADDR_TIMEOUT;
                                r_timeout_detected[idx] <= 1'b1;
                            end
                        end

                        // Data phase timeout detection
                        if ((r_trans_table_local[idx].state == TRANS_ADDR_PHASE ||
                                r_trans_table_local[idx].state == TRANS_DATA_PHASE) &&
                                r_trans_table_local[idx].addr_received &&
                                r_trans_table_local[idx].data_started &&
                                !r_trans_table_local[idx].data_completed) begin

                            // Increment data timer
                            r_trans_table_local[idx].data_timer <= r_trans_table_local[idx].data_timer + 1'b1;

                            // Check for timeout
                            /* verilator lint_off WIDTHEXPAND */
                            if (r_trans_table_local[idx].data_timer >= {12'h0, i_cfg_data_cnt}) begin
                            /* verilator lint_on WIDTHEXPAND */
                                r_trans_table_local[idx].state <= TRANS_ERROR;
                                r_trans_table_local[idx].error_code <= EVT_DATA_TIMEOUT;
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
                            if (r_trans_table_local[idx].resp_timer >= {12'h0, i_cfg_resp_cnt}) begin
                            /* verilator lint_on WIDTHEXPAND */
                                r_trans_table_local[idx].state <= TRANS_ERROR;
                                r_trans_table_local[idx].error_code <= EVT_RESP_TIMEOUT;
                                r_timeout_detected[idx] <= 1'b1;
                            end
                        end
                    end
                end
            end
        end
    end

endmodule : axi_errmon_timeout