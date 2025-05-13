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
 */
module axi_errmon_timeout
#(
    parameter int MAX_TRANSACTIONS   = 16,   // Maximum outstanding transactions
    parameter int ADDR_WIDTH         = 32,   // Width of address bus
    parameter bit IS_READ            = 1     // 1 for read, 0 for write
)
(
    // Global Clock and Reset
    input  logic                     aclk,
    input  logic                     aresetn,

    // Transaction table (read-modify access)
    input  axi_errmon_types::axi_transaction_t [MAX_TRANSACTIONS-1:0] i_trans_table,

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

    import axi_errmon_types::*;

    // Local copy of transaction table for modifications
    axi_transaction_t trans_table_local[MAX_TRANSACTIONS];

    // Flag to track if timeouts have been detected for each transaction
    logic [MAX_TRANSACTIONS-1:0] timeout_detected;
    assign o_timeout_detected = timeout_detected;

    // Timeout detection logic
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            // Reset local table
            trans_table_local <= '{default: '0};
            timeout_detected <= '0;
        end else begin
            // Update local table from input and process individually
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                trans_table_local[i] <= i_trans_table[i];

                // If this transaction has a state change to non-active, mark it as no longer timing out
                if (i_trans_table[i].state == TRANS_COMPLETE ||
                    i_trans_table[i].state == TRANS_ERROR ||
                    i_trans_table[i].state == TRANS_EMPTY) begin
                    timeout_detected[i] <= 1'b0;
                end
            end

            // If timer tick, check for timeouts
            if (i_timer_tick) begin
                for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                    if (trans_table_local[i].valid && !timeout_detected[i]) begin

                        // Address phase timeout detection
                        if (trans_table_local[i].state == TRANS_ADDR_PHASE &&
                            !trans_table_local[i].addr_received) begin

                            // Increment address timer
                            trans_table_local[i].addr_timer <= trans_table_local[i].addr_timer + 1'b1;

                            // Check for timeout
                            if (trans_table_local[i].addr_timer >= i_cfg_addr_cnt) begin
                                trans_table_local[i].state <= TRANS_ERROR;
                                trans_table_local[i].error_code <= EVT_ADDR_TIMEOUT;
                                timeout_detected[i] <= 1'b1;
                            end
                        end

                        // Data phase timeout detection
                        if ((trans_table_local[i].state == TRANS_ADDR_PHASE ||
                                trans_table_local[i].state == TRANS_DATA_PHASE) &&
                                trans_table_local[i].addr_received &&
                                trans_table_local[i].data_started &&
                                !trans_table_local[i].data_completed) begin

                            // Increment data timer
                            trans_table_local[i].data_timer <= trans_table_local[i].data_timer + 1'b1;

                            // Check for timeout
                            if (trans_table_local[i].data_timer >= i_cfg_data_cnt) begin
                                trans_table_local[i].state <= TRANS_ERROR;
                                trans_table_local[i].error_code <= EVT_DATA_TIMEOUT;
                                timeout_detected[i] <= 1'b1;
                            end
                        end

                        // Response phase timeout detection (write only)
                        if (!IS_READ &&
                            trans_table_local[i].state == TRANS_DATA_PHASE &&
                            trans_table_local[i].data_completed &&
                            !trans_table_local[i].resp_received) begin

                            // Increment response timer
                            trans_table_local[i].resp_timer <= trans_table_local[i].resp_timer + 1'b1;

                            // Check for timeout
                            if (trans_table_local[i].resp_timer >= i_cfg_resp_cnt) begin
                                trans_table_local[i].state <= TRANS_ERROR;
                                trans_table_local[i].error_code <= EVT_RESP_TIMEOUT;
                                timeout_detected[i] <= 1'b1;
                            end
                        end
                    end
                end
            end
        end
    end

endmodule : axi_errmon_timeout
