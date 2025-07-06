`timescale 1ns / 1ps

/**
 * AXI Interrupt Bus Transaction Manager
 *
 * This module manages the transaction tracking table, tracking each AXI
 * transaction through its lifecycle and handling all of the protocol
 * complexities including out-of-order phase arrivals.
 *
 * When ENABLE_PERF_PACKETS is set, additional performance tracking is enabled.
 * Includes state change detection to support debug functionality.
 *
 * Updated with proper naming conventions: w_ for combo, r_ for flopped
 * Fixed for Verilator compatibility and consistent array declarations
 */
module axi_monitor_trans_mgr
    import monitor_pkg::*;
#(
    parameter int MAX_TRANSACTIONS    = 16,   // Maximum outstanding transactions
    parameter int ADDR_WIDTH          = 32,   // Width of address bus
    parameter int ID_WIDTH            = 8,    // Width of ID bus
    parameter bit IS_READ             = 1'b1,   // 1 for read, 0 for write
    parameter bit IS_AXI              = 1'b1,   // 1 for AXI, 0 for AXI-Lite
    parameter bit ENABLE_PERF_PACKETS = 1'b0,   // Enable performance metrics tracking

    // Short params
    parameter int AW                  = ADDR_WIDTH,
    parameter int IW                  = ID_WIDTH
)
(
    // Global Clock and Reset
    input  logic                     aclk,
    input  logic                     aresetn,

    // Address channel
    input  logic                     i_addr_valid,
    input  logic                     i_addr_ready,
    input  logic [IW-1:0]            i_addr_id,
    input  logic [AW-1:0]            i_addr_addr,
    input  logic [7:0]               i_addr_len,
    input  logic [2:0]               i_addr_size,
    input  logic [1:0]               i_addr_burst,

    // Data channel
    input  logic                     i_data_valid,
    input  logic                     i_data_ready,
    input  logic [IW-1:0]            i_data_id,
    input  logic                     i_data_last,
    input  logic [1:0]               i_data_resp,

    // Response channel (write only)
    input  logic                     i_resp_valid,
    input  logic                     i_resp_ready,
    input  logic [IW-1:0]            i_resp_id,
    input  logic [1:0]               i_resp,

    // Timestamp input
    input  logic [31:0]              i_timestamp,

    // Transaction table output - Fixed: Use unpacked array
    output bus_transaction_t         o_trans_table[MAX_TRANSACTIONS],
    output logic [7:0]               o_active_count,

    // State change detection (for debug module)
    output logic [MAX_TRANSACTIONS-1:0] o_state_change
);

    // Transaction table (flopped) - use unpacked array
    bus_transaction_t r_trans_table[MAX_TRANSACTIONS];
    bus_transaction_t r_trans_table_prev[MAX_TRANSACTIONS]; // Previous state for change detection (flopped)
    assign o_trans_table = r_trans_table;

    // Active transaction counter (flopped)
    logic [7:0] r_active_count;
    assign o_active_count = r_active_count;

    // State change detection (flopped)
    logic [MAX_TRANSACTIONS-1:0] r_state_change;
    assign o_state_change = r_state_change;

    // Transaction indices for various operations (combinational)
    int w_addr_trans_idx;
    int w_addr_free_idx;
    int w_data_trans_idx;
    int w_data_free_idx;
    int w_resp_trans_idx;
    int w_resp_free_idx;

    // Channel index for AXI ID (combinational)
    int w_addr_chan_idx;

    // Cleanup flags (combinational)
    logic [MAX_TRANSACTIONS-1:0] w_can_cleanup;

    // -------------------------------------------------------------------------
    // Transaction lookup combinational logic
    // -------------------------------------------------------------------------

    // Find transaction based on ID, -1 if not found
    always_comb begin
        // Address transaction lookup
        w_addr_trans_idx = -1;
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (w_addr_trans_idx == -1 && r_trans_table[idx].valid && 
                r_trans_table[idx].id[IW-1:0] == i_addr_id) begin
                w_addr_trans_idx = idx;
            end
        end

        // Find free slot for address phase
        w_addr_free_idx = -1;
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (w_addr_free_idx == -1 && !r_trans_table[idx].valid) begin
                w_addr_free_idx = idx;
            end
        end

        // Calculate channel index from ID
        /* verilator lint_off WIDTHTRUNC */
        w_addr_chan_idx = IS_AXI ? (({24'h0, i_addr_id} % 64)) : 0;
        /* verilator lint_on WIDTHTRUNC */

        // Find transaction for data phase
        if (IS_READ) begin
            // For reads, we use the ID
            w_data_trans_idx = -1;
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (w_data_trans_idx == -1 && r_trans_table[idx].valid && 
                    r_trans_table[idx].id[IW-1:0] == i_data_id) begin
                    w_data_trans_idx = idx;
                end
            end
        end else begin
            // For writes, find matching transaction
            w_data_trans_idx = -1;
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (w_data_trans_idx == -1 && r_trans_table[idx].valid &&
                        (r_trans_table[idx].state == TRANS_ADDR_PHASE ||
                        r_trans_table[idx].state == TRANS_DATA_PHASE) &&
                        r_trans_table[idx].addr_received &&
                        !r_trans_table[idx].data_completed) begin
                    w_data_trans_idx = idx;
                end
            end
        end

        // Find free slot for data phase
        w_data_free_idx = -1;
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (w_data_free_idx == -1 && !r_trans_table[idx].valid) begin
                w_data_free_idx = idx;
            end
        end

        // Find transaction and free slot for response phase
        if (!IS_READ) begin
            w_resp_trans_idx = -1;
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (w_resp_trans_idx == -1 && r_trans_table[idx].valid && 
                    r_trans_table[idx].id[IW-1:0] == i_resp_id) begin
                    w_resp_trans_idx = idx;
                end
            end

            w_resp_free_idx = -1;
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (w_resp_free_idx == -1 && !r_trans_table[idx].valid) begin
                    w_resp_free_idx = idx;
                end
            end
        end else begin
            // Don't care for read channels
            w_resp_trans_idx = -1;
            w_resp_free_idx = -1;
        end

        // Determine which transactions can be cleaned up
        for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
            if (r_trans_table[idx].valid) begin
                case (r_trans_table[idx].state)
                    TRANS_COMPLETE: begin
                        // Clean up completed transactions (delay a bit for reporting)
                        w_can_cleanup[idx] = r_trans_table[idx].event_reported;
                    end
                    TRANS_ERROR, TRANS_ORPHANED: begin
                        // Clean up error transactions only after reporting
                        w_can_cleanup[idx] = r_trans_table[idx].event_reported;
                    end
                    default: begin
                        w_can_cleanup[idx] = 1'b0;
                    end
                endcase
            end else begin
                w_can_cleanup[idx] = 1'b0;
            end
        end
    end

    // -------------------------------------------------------------------------
    // State Change Detection
    // -------------------------------------------------------------------------
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                r_trans_table_prev[idx] <= '0;
            end
            r_state_change <= '0;
        end else begin
            // Update previous state for change detection
            r_trans_table_prev <= r_trans_table;

            // Detect state changes
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (r_trans_table[idx].valid && r_trans_table_prev[idx].valid) begin
                    if (r_trans_table[idx].state != r_trans_table_prev[idx].state) begin
                        r_state_change[idx] <= 1'b1;
                    end else begin
                        r_state_change[idx] <= 1'b0;
                    end
                end else begin
                    r_state_change[idx] <= 1'b0;
                end
            end
        end
    end

    // -------------------------------------------------------------------------
    // Address Phase Processor
    // -------------------------------------------------------------------------
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                r_trans_table[idx].valid <= 1'b0;
            end
            r_active_count <= '0;
        end else begin
            
            // =====================================================================
            // STEP 1: Create transaction when addr_valid asserted (before handshake)
            // =====================================================================
            if (i_addr_valid) begin
                // Check if we need to create a new transaction
                if (w_addr_trans_idx < 0 && w_addr_free_idx >= 0) begin
                    // Create new transaction entry immediately when valid asserted
                    r_trans_table[w_addr_free_idx].valid <= 1'b1;
                    r_trans_table[w_addr_free_idx].state <= TRANS_ADDR_PHASE;
                    r_trans_table[w_addr_free_idx].id <= '0;
                    r_trans_table[w_addr_free_idx].id[IW-1:0] <= i_addr_id;
                    r_trans_table[w_addr_free_idx].addr <= '0;
                    r_trans_table[w_addr_free_idx].addr[AW-1:0] <= i_addr_addr;
                    r_trans_table[w_addr_free_idx].len <= i_addr_len;
                    r_trans_table[w_addr_free_idx].size <= i_addr_size;
                    r_trans_table[w_addr_free_idx].burst <= i_addr_burst;
                    
                    // CRITICAL: Address NOT received yet, timer starts now
                    r_trans_table[w_addr_free_idx].addr_received <= 1'b0;  // Not received until handshake
                    r_trans_table[w_addr_free_idx].addr_timer <= '0;       // Start timer immediately
                    
                    r_trans_table[w_addr_free_idx].data_started <= 1'b0;
                    r_trans_table[w_addr_free_idx].data_completed <= 1'b0;
                    r_trans_table[w_addr_free_idx].resp_received <= 1'b0;
                    r_trans_table[w_addr_free_idx].error_code <= EVT_NONE;
                    r_trans_table[w_addr_free_idx].event_reported <= 1'b0;
                    r_trans_table[w_addr_free_idx].data_timer <= '0;
                    r_trans_table[w_addr_free_idx].resp_timer <= '0;
                    r_trans_table[w_addr_free_idx].addr_timestamp <= i_timestamp;
                    r_trans_table[w_addr_free_idx].expected_beats <= IS_AXI ? (i_addr_len + 8'h1) : 8'h1;
                    r_trans_table[w_addr_free_idx].data_beat_count <= '0;
                    r_trans_table[w_addr_free_idx].channel <= 6'(w_addr_chan_idx);
    
                    // Increment active count
                    r_active_count <= r_active_count + 1'b1;
                end
            end
    
            // =====================================================================
            // STEP 2: Mark address received when handshake completes
            // =====================================================================
            if (i_addr_valid && i_addr_ready) begin
                if (w_addr_trans_idx >= 0) begin
                    // Mark address phase as complete
                    r_trans_table[w_addr_trans_idx].addr_received <= 1'b1;
                    r_trans_table[w_addr_trans_idx].addr_timer <= '0;  // Stop/clear timer
                    r_trans_table[w_addr_trans_idx].addr_timestamp <= i_timestamp;
                end
            end
    
            // Clean up completed transactions
            for (int idx = 0; idx < MAX_TRANSACTIONS; idx++) begin
                if (r_trans_table[idx].valid && w_can_cleanup[idx]) begin
                    r_trans_table[idx].valid <= 1'b0;
                    r_active_count <= r_active_count - 1'b1;
                end
            end
        end
    end

    // -------------------------------------------------------------------------
    // Data Phase Processor
    // -------------------------------------------------------------------------
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            // Reset handled by address processor
        end else begin
            // Process data phase transactions
            if (i_data_valid && i_data_ready) begin
                if (IS_READ) begin
                    // For reads, we have an ID so we can find the transaction
                    if (w_data_trans_idx >= 0) begin
                        // Update transaction data phase info
                        r_trans_table[w_data_trans_idx].data_started <= 1'b1;
                        r_trans_table[w_data_trans_idx].data_beat_count <=
                            r_trans_table[w_data_trans_idx].data_beat_count + 1'b1;

                        // Reset data timeout timer
                        r_trans_table[w_data_trans_idx].data_timer <= '0;

                        // Update state
                        if (r_trans_table[w_data_trans_idx].state != TRANS_ERROR) begin
                            r_trans_table[w_data_trans_idx].state <= TRANS_DATA_PHASE;
                        end

                        // Check if data completed (last beat)
                        if (i_data_last) begin
                            r_trans_table[w_data_trans_idx].data_completed <= 1'b1;
                            r_trans_table[w_data_trans_idx].data_timestamp <= i_timestamp;

                            // For reads, transaction is complete once last data beat arrives
                            if (r_trans_table[w_data_trans_idx].state != TRANS_ERROR) begin
                                r_trans_table[w_data_trans_idx].state <= TRANS_COMPLETE;

                                // Performance metrics - calculate and store latencies
                                if (ENABLE_PERF_PACKETS) begin
                                    // Additional performance tracking can be added here
                                end
                            end
                        end

                        // Check for data response error
                        if (i_data_resp[1]) begin
                            r_trans_table[w_data_trans_idx].state <= TRANS_ERROR;
                            // Properly distinguish between SLVERR and DECERR
                            r_trans_table[w_data_trans_idx].error_code <= (i_data_resp[0]) ? EVT_RESP_DECERR : EVT_RESP_SLVERR;
                        end
                    end else if (IS_AXI && w_data_free_idx >= 0) begin
                        // Orphaned read data - create entry to track it
                        // Create orphaned transaction
                        r_trans_table[w_data_free_idx].valid <= 1'b1;
                        r_trans_table[w_data_free_idx].state <= TRANS_ORPHANED;
                        r_trans_table[w_data_free_idx].id <= '0;
                        r_trans_table[w_data_free_idx].id[IW-1:0] <= i_data_id;
                        r_trans_table[w_data_free_idx].data_started <= 1'b1;
                        r_trans_table[w_data_free_idx].data_completed <= i_data_last;
                        r_trans_table[w_data_free_idx].data_beat_count <= 8'h1;
                        r_trans_table[w_data_free_idx].data_timestamp <= i_timestamp;
                        r_trans_table[w_data_free_idx].error_code <= EVT_DATA_ORPHAN;
                        /* verilator lint_off WIDTHTRUNC */
                        r_trans_table[w_data_free_idx].channel <= 6'(({24'h0, i_data_id} % 64));
                        /* verilator lint_on WIDTHTRUNC */

                        // Increment active count
                        r_active_count <= r_active_count + 1'b1;
                    end
                end else begin
                    // For writes, we need to find matching transaction without ID
                    if (w_data_trans_idx >= 0) begin
                        // Update transaction data phase info
                        r_trans_table[w_data_trans_idx].data_started <= 1'b1;
                        r_trans_table[w_data_trans_idx].data_beat_count <=
                            r_trans_table[w_data_trans_idx].data_beat_count + 1'b1;

                        // Reset data timeout timer
                        r_trans_table[w_data_trans_idx].data_timer <= '0;

                        // Update state
                        if (r_trans_table[w_data_trans_idx].state != TRANS_ERROR) begin
                            r_trans_table[w_data_trans_idx].state <= TRANS_DATA_PHASE;
                        end

                        // Check if data completed (last beat or expected count reached)
                        if (i_data_last || r_trans_table[w_data_trans_idx].data_beat_count + 1 ==
                                        r_trans_table[w_data_trans_idx].expected_beats) begin
                            r_trans_table[w_data_trans_idx].data_completed <= 1'b1;
                            r_trans_table[w_data_trans_idx].data_timestamp <= i_timestamp;

                            // Performance metrics - data phase latency
                            if (ENABLE_PERF_PACKETS) begin
                                // Additional performance tracking can be added here
                            end
                        end
                    end else if (!IS_AXI && w_data_free_idx >= 0) begin
                        // For AXI-Lite, create an orphaned entry for data-before-address
                        // Create orphaned transaction
                        r_trans_table[w_data_free_idx].valid <= 1'b1;
                        r_trans_table[w_data_free_idx].state <= TRANS_ORPHANED;
                        r_trans_table[w_data_free_idx].id <= '0; // No ID for AXI-Lite
                        r_trans_table[w_data_free_idx].data_started <= 1'b1;
                        r_trans_table[w_data_free_idx].data_completed <= i_data_last;
                        r_trans_table[w_data_free_idx].data_beat_count <= 8'h1;
                        r_trans_table[w_data_free_idx].expected_beats <= 8'h1; // AXI-Lite is single beat
                        r_trans_table[w_data_free_idx].data_timestamp <= i_timestamp;
                        r_trans_table[w_data_free_idx].error_code <= EVT_DATA_ORPHAN;
                        r_trans_table[w_data_free_idx].channel <= 6'h0; // AXI-Lite always channel 0

                        // Increment active count
                        r_active_count <= r_active_count + 1'b1;
                    end
                end
            end
        end
    end

    // -------------------------------------------------------------------------
    // Response Phase Processor (write only)
    // -------------------------------------------------------------------------
    generate
        if (!IS_READ) begin : gen_resp_processor
            always_ff @(posedge aclk or negedge aresetn) begin
                if (!aresetn) begin
                    // Reset handled by address processor
                end else begin
                    // Process response phase
                    if (i_resp_valid && i_resp_ready) begin
                        if (w_resp_trans_idx >= 0) begin
                            // Update transaction response info
                            r_trans_table[w_resp_trans_idx].resp_received <= 1'b1;
                            r_trans_table[w_resp_trans_idx].resp_timestamp <= i_timestamp;

                            // Reset response timeout timer
                            r_trans_table[w_resp_trans_idx].resp_timer <= '0;

                            // Check for response error
                            if (i_resp[1]) begin
                                r_trans_table[w_resp_trans_idx].state <= TRANS_ERROR;
                                // Properly distinguish between SLVERR and DECERR
                                r_trans_table[w_resp_trans_idx].error_code <= (i_resp[0]) ? EVT_RESP_DECERR : EVT_RESP_SLVERR;
                            end else if (r_trans_table[w_resp_trans_idx].data_completed) begin
                                // Transaction completed successfully
                                if (r_trans_table[w_resp_trans_idx].state != TRANS_ERROR) begin
                                    r_trans_table[w_resp_trans_idx].state <= TRANS_COMPLETE;

                                    // Performance metrics - calculate and store latencies
                                    if (ENABLE_PERF_PACKETS) begin
                                        // Additional performance tracking can be added here
                                    end
                                end
                            end else if (r_trans_table[w_resp_trans_idx].data_started) begin
                                // Response received before data completion (protocol violation)
                                r_trans_table[w_resp_trans_idx].state <= TRANS_ERROR;
                                r_trans_table[w_resp_trans_idx].error_code <= EVT_PROTOCOL;
                            end else begin
                                // Response received before data started (protocol violation)
                                r_trans_table[w_resp_trans_idx].state <= TRANS_ERROR;
                                r_trans_table[w_resp_trans_idx].error_code <= EVT_PROTOCOL;
                            end
                        end else if (w_resp_free_idx >= 0) begin
                            if (IS_AXI) begin
                                // Orphaned response (no matching transaction) - create entry
                                // Create orphaned transaction
                                r_trans_table[w_resp_free_idx].valid <= 1'b1;
                                r_trans_table[w_resp_free_idx].state <= TRANS_ORPHANED;
                                r_trans_table[w_resp_free_idx].id <= '0;
                                r_trans_table[w_resp_free_idx].id[IW-1:0] <= i_resp_id;
                                r_trans_table[w_resp_free_idx].resp_received <= 1'b1;
                                r_trans_table[w_resp_free_idx].resp_timestamp <= i_timestamp;
                                r_trans_table[w_resp_free_idx].error_code <= EVT_RESP_ORPHAN;
                                /* verilator lint_off WIDTHTRUNC */
                                r_trans_table[w_resp_free_idx].channel <= 6'(i_resp_id % 64);
                                /* verilator lint_on WIDTHTRUNC */
                            end else begin
                                // For AXI-Lite, orphaned response
                                // Create orphaned transaction
                                r_trans_table[w_resp_free_idx].valid <= 1'b1;
                                r_trans_table[w_resp_free_idx].state <= TRANS_ORPHANED;
                                r_trans_table[w_resp_free_idx].id <= '0; // No ID for AXI-Lite
                                r_trans_table[w_resp_free_idx].resp_received <= 1'b1;
                                r_trans_table[w_resp_free_idx].resp_timestamp <= i_timestamp;
                                r_trans_table[w_resp_free_idx].error_code <= EVT_RESP_ORPHAN;
                                r_trans_table[w_resp_free_idx].channel <= 6'h0; // AXI-Lite always channel 0
                            end

                            // Increment active count
                            r_active_count <= r_active_count + 1'b1;
                        end
                    end
                end
            end
        end
    endgenerate

endmodule : axi_monitor_trans_mgr
