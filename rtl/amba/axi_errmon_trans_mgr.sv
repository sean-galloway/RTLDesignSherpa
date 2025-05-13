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
 */
module axi_errmon_trans_mgr
#(
    parameter int MAX_TRANSACTIONS    = 16,   // Maximum outstanding transactions
    parameter int ADDR_WIDTH          = 32,   // Width of address bus
    parameter int ID_WIDTH            = 8,    // Width of ID bus
    parameter bit IS_READ             = 1,    // 1 for read, 0 for write
    parameter bit IS_AXI              = 1,    // 1 for AXI, 0 for AXI-Lite
    parameter bit ENABLE_PERF_PACKETS = 0,    // Enable performance metrics tracking

    // Short params
    parameter int AW                 = ADDR_WIDTH,
    parameter int IW                 = ID_WIDTH
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

    // Transaction table output
    output axi_errmon_types::axi_transaction_t [MAX_TRANSACTIONS-1:0] o_trans_table,
    output logic [7:0]               o_active_count,

    // State change detection (for debug module)
    output logic [MAX_TRANSACTIONS-1:0] o_state_change
);

    import axi_errmon_types::*;

    // Transaction table
    axi_transaction_t trans_table[MAX_TRANSACTIONS];
    axi_transaction_t trans_table_prev[MAX_TRANSACTIONS]; // Previous state for change detection
    assign o_trans_table = trans_table;

    // Active transaction counter
    logic [7:0] active_count;
    assign o_active_count = active_count;

    // State change detection
    logic [MAX_TRANSACTIONS-1:0] state_change;
    assign o_state_change = state_change;

    // Transaction indices for various operations
    int addr_trans_idx;
    int addr_free_idx;
    int data_trans_idx;
    int data_free_idx;
    int resp_trans_idx;
    int resp_free_idx;

    // Channel index for AXI ID
    int addr_chan_idx;

    // Cleanup flags
    logic [MAX_TRANSACTIONS-1:0] can_cleanup;

    // -------------------------------------------------------------------------
    // Transaction lookup combinational logic
    // -------------------------------------------------------------------------

    // Find transaction based on ID, -1 if not found
    always_comb begin
        // Address transaction lookup
        addr_trans_idx = -1;
        for (int i = 0; i < MAX_TRANSACTIONS && addr_trans_idx == -1; i++) begin
            if (trans_table[i].valid && trans_table[i].id[IW-1:0] == i_addr_id) begin
                addr_trans_idx = i;
            end
        end

        // Find free slot for address phase
        addr_free_idx = -1;
        for (int i = 0; i < MAX_TRANSACTIONS && addr_free_idx == -1; i++) begin
            if (!trans_table[i].valid) begin
                addr_free_idx = i;
            end
        end

        // Calculate channel index from ID
        addr_chan_idx = IS_AXI ? (i_addr_id % 64) : 0;

        // Find transaction for data phase
        if (IS_READ) begin
            // For reads, we use the ID
            data_trans_idx = -1;
            for (int i = 0; i < MAX_TRANSACTIONS && data_trans_idx == -1; i++) begin
                if (trans_table[i].valid && trans_table[i].id[IW-1:0] == i_data_id) begin
                    data_trans_idx = i;
                end
            end
        end else begin
            // For writes, find matching transaction
            data_trans_idx = -1;
            for (int i = 0; i < MAX_TRANSACTIONS && data_trans_idx == -1; i++) begin
                if (trans_table[i].valid &&
                        (trans_table[i].state == TRANS_ADDR_PHASE ||
                        trans_table[i].state == TRANS_DATA_PHASE) &&
                        trans_table[i].addr_received &&
                        !trans_table[i].data_completed) begin
                    data_trans_idx = i;
                end
            end
        end

        // Find free slot for data phase
        data_free_idx = -1;
        for (int i = 0; i < MAX_TRANSACTIONS && data_free_idx == -1; i++) begin
            if (!trans_table[i].valid) begin
                data_free_idx = i;
            end
        end

        // Find transaction and free slot for response phase
        if (!IS_READ) begin
            resp_trans_idx = -1;
            for (int i = 0; i < MAX_TRANSACTIONS && resp_trans_idx == -1; i++) begin
                if (trans_table[i].valid && trans_table[i].id[IW-1:0] == i_resp_id) begin
                    resp_trans_idx = i;
                end
            end

            resp_free_idx = -1;
            for (int i = 0; i < MAX_TRANSACTIONS && resp_free_idx == -1; i++) begin
                if (!trans_table[i].valid) begin
                    resp_free_idx = i;
                end
            end
        end else begin
            // Don't care for read channels
            resp_trans_idx = -1;
            resp_free_idx = -1;
        end

        // Determine which transactions can be cleaned up
        for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
            if (trans_table[i].valid) begin
                case (trans_table[i].state)
                    TRANS_COMPLETE: begin
                        // Clean up completed transactions (delay a bit for reporting)
                        can_cleanup[i] = trans_table[i].event_reported;
                    end
                    TRANS_ERROR, TRANS_ORPHANED: begin
                        // Clean up error transactions only after reporting
                        can_cleanup[i] = trans_table[i].event_reported;
                    end
                    default: begin
                        can_cleanup[i] = 1'b0;
                    end
                endcase
            end else begin
                can_cleanup[i] = 1'b0;
            end
        end
    end

    // -------------------------------------------------------------------------
    // State Change Detection
    // -------------------------------------------------------------------------
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            trans_table_prev <= '{default: '0};
            state_change <= '0;
        end else begin
            // Update previous state for change detection
            trans_table_prev <= trans_table;

            // Detect state changes
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                if (trans_table[i].valid && trans_table_prev[i].valid) begin
                    if (trans_table[i].state != trans_table_prev[i].state) begin
                        state_change[i] <= 1'b1;
                    end else begin
                        state_change[i] <= 1'b0;
                    end
                end else begin
                    state_change[i] <= 1'b0;
                end
            end
        end
    end

    // -------------------------------------------------------------------------
    // Address Phase Processor
    // -------------------------------------------------------------------------
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                trans_table[i].valid <= 1'b0;
            end
            active_count <= '0;
        end else begin
            // Process address phase transactions
            if (i_addr_valid && i_addr_ready) begin
                if (addr_trans_idx < 0) begin
                    // New transaction - create entry
                    if (addr_free_idx >= 0) begin
                        // Initialize new transaction
                        trans_table[addr_free_idx].valid <= 1'b1;
                        trans_table[addr_free_idx].state <= TRANS_ADDR_PHASE;
                        trans_table[addr_free_idx].id <= '0;
                        trans_table[addr_free_idx].id[IW-1:0] <= i_addr_id;
                        trans_table[addr_free_idx].addr <= '0;
                        trans_table[addr_free_idx].addr[AW-1:0] <= i_addr_addr;
                        trans_table[addr_free_idx].len <= i_addr_len;
                        trans_table[addr_free_idx].size <= i_addr_size;
                        trans_table[addr_free_idx].burst <= i_addr_burst;
                        trans_table[addr_free_idx].addr_received <= 1'b1;
                        trans_table[addr_free_idx].data_started <= 1'b0;
                        trans_table[addr_free_idx].data_completed <= 1'b0;
                        trans_table[addr_free_idx].resp_received <= 1'b0;
                        trans_table[addr_free_idx].error_code <= EVT_NONE;
                        trans_table[addr_free_idx].event_reported <= 1'b0;
                        trans_table[addr_free_idx].addr_timer <= '0;
                        trans_table[addr_free_idx].data_timer <= '0;
                        trans_table[addr_free_idx].resp_timer <= '0;
                        trans_table[addr_free_idx].addr_timestamp <= i_timestamp;
                        trans_table[addr_free_idx].expected_beats <= IS_AXI ? (i_addr_len + 1'b1) : 1'b1;
                        trans_table[addr_free_idx].data_beat_count <= '0;
                        trans_table[addr_free_idx].channel <= 6'(addr_chan_idx);

                        // Increment active count
                        active_count <= active_count + 1'b1;
                    end
                end else begin
                    // Existing transaction - update address info
                    // This can happen in AXI-Lite if data arrives first
                    trans_table[addr_trans_idx].addr <= '0;
                    trans_table[addr_trans_idx].addr[AW-1:0] <= i_addr_addr;

                    if (IS_AXI) begin
                        trans_table[addr_trans_idx].len <= i_addr_len;
                        trans_table[addr_trans_idx].size <= i_addr_size;
                        trans_table[addr_trans_idx].burst <= i_addr_burst;
                        trans_table[addr_trans_idx].expected_beats <= i_addr_len + 1'b1;
                    end else begin
                        // AXI-Lite is always single beat
                        trans_table[addr_trans_idx].len <= '0;
                        trans_table[addr_trans_idx].size <= i_addr_size;
                        trans_table[addr_trans_idx].burst <= 2'b01; // INCR
                        trans_table[addr_trans_idx].expected_beats <= 1'b1;
                    end

                    trans_table[addr_trans_idx].addr_received <= 1'b1;
                    trans_table[addr_trans_idx].addr_timestamp <= i_timestamp;
                    trans_table[addr_trans_idx].channel <= 6'(addr_chan_idx);

                    // Update state if not already in error
                    if (trans_table[addr_trans_idx].state != TRANS_ERROR &&
                        trans_table[addr_trans_idx].state != TRANS_ORPHANED) begin
                        if (trans_table[addr_trans_idx].data_started) begin
                            trans_table[addr_trans_idx].state <= TRANS_DATA_PHASE;
                        end else begin
                            trans_table[addr_trans_idx].state <= TRANS_ADDR_PHASE;
                        end
                    end

                    // Reset addr timer
                    trans_table[addr_trans_idx].addr_timer <= '0;
                end
            end

            // Clean up completed transactions
            for (int i = 0; i < MAX_TRANSACTIONS; i++) begin
                if (trans_table[i].valid && can_cleanup[i]) begin
                    trans_table[i].valid <= 1'b0;
                    active_count <= active_count - 1'b1;
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
                    if (data_trans_idx >= 0) begin
                        // Update transaction data phase info
                        trans_table[data_trans_idx].data_started <= 1'b1;
                        trans_table[data_trans_idx].data_beat_count <=
                            trans_table[data_trans_idx].data_beat_count + 1'b1;

                        // Reset data timeout timer
                        trans_table[data_trans_idx].data_timer <= '0;

                        // Update state
                        if (trans_table[data_trans_idx].state != TRANS_ERROR) begin
                            trans_table[data_trans_idx].state <= TRANS_DATA_PHASE;
                        end

                        // Check if data completed (last beat)
                        if (i_data_last) begin
                            trans_table[data_trans_idx].data_completed <= 1'b1;
                            trans_table[data_trans_idx].data_timestamp <= i_timestamp;

                            // For reads, transaction is complete once last data beat arrives
                            if (trans_table[data_trans_idx].state != TRANS_ERROR) begin
                                trans_table[data_trans_idx].state <= TRANS_COMPLETE;

                                // Performance metrics - calculate and store latencies
                                if (ENABLE_PERF_PACKETS) begin
                                    // Additional performance tracking can be added here
                                end
                            end
                        end

                        // Check for data response error
                        if (i_data_resp[1]) begin
                            trans_table[data_trans_idx].state <= TRANS_ERROR;
                            // Properly distinguish between SLVERR and DECERR
                            trans_table[data_trans_idx].error_code <= (i_data_resp[0]) ? EVT_RESP_DECERR : EVT_RESP_SLVERR;
                        end
                    end else if (IS_AXI && data_free_idx >= 0) begin
                        // Orphaned read data - create entry to track it
                        // Create orphaned transaction
                        trans_table[data_free_idx].valid <= 1'b1;
                        trans_table[data_free_idx].state <= TRANS_ORPHANED;
                        trans_table[data_free_idx].id <= '0;
                        trans_table[data_free_idx].id[IW-1:0] <= i_data_id;
                        trans_table[data_free_idx].data_started <= 1'b1;
                        trans_table[data_free_idx].data_completed <= i_data_last;
                        trans_table[data_free_idx].data_beat_count <= 1'b1;
                        trans_table[data_free_idx].data_timestamp <= i_timestamp;
                        trans_table[data_free_idx].error_code <= EVT_DATA_ORPHAN;
                        trans_table[data_free_idx].channel <= 6'(i_data_id % 64);

                        // Increment active count
                        active_count <= active_count + 1'b1;
                    end
                end else begin
                    // For writes, we need to find matching transaction without ID
                    if (data_trans_idx >= 0) begin
                        // Update transaction data phase info
                        trans_table[data_trans_idx].data_started <= 1'b1;
                        trans_table[data_trans_idx].data_beat_count <=
                            trans_table[data_trans_idx].data_beat_count + 1'b1;

                        // Reset data timeout timer
                        trans_table[data_trans_idx].data_timer <= '0;

                        // Update state
                        if (trans_table[data_trans_idx].state != TRANS_ERROR) begin
                            trans_table[data_trans_idx].state <= TRANS_DATA_PHASE;
                        end

                        // Check if data completed (last beat or expected count reached)
                        if (i_data_last || trans_table[data_trans_idx].data_beat_count + 1 ==
                                        trans_table[data_trans_idx].expected_beats) begin
                            trans_table[data_trans_idx].data_completed <= 1'b1;
                            trans_table[data_trans_idx].data_timestamp <= i_timestamp;

                            // Performance metrics - data phase latency
                            if (ENABLE_PERF_PACKETS) begin
                                // Additional performance tracking can be added here
                            end
                        end
                    end else if (!IS_AXI && data_free_idx >= 0) begin
                        // For AXI-Lite, create an orphaned entry for data-before-address
                        // Create orphaned transaction
                        trans_table[data_free_idx].valid <= 1'b1;
                        trans_table[data_free_idx].state <= TRANS_ORPHANED;
                        trans_table[data_free_idx].id <= '0; // No ID for AXI-Lite
                        trans_table[data_free_idx].data_started <= 1'b1;
                        trans_table[data_free_idx].data_completed <= i_data_last;
                        trans_table[data_free_idx].data_beat_count <= 1'b1;
                        trans_table[data_free_idx].expected_beats <= 1'b1; // AXI-Lite is single beat
                        trans_table[data_free_idx].data_timestamp <= i_timestamp;
                        trans_table[data_free_idx].error_code <= EVT_DATA_ORPHAN;
                        trans_table[data_free_idx].channel <= 6'h0; // AXI-Lite always channel 0

                        // Increment active count
                        active_count <= active_count + 1'b1;
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
                        if (resp_trans_idx >= 0) begin
                            // Update transaction response info
                            trans_table[resp_trans_idx].resp_received <= 1'b1;
                            trans_table[resp_trans_idx].resp_timestamp <= i_timestamp;

                            // Reset response timeout timer
                            trans_table[resp_trans_idx].resp_timer <= '0;

                            // Check for response error
                            if (i_resp[1]) begin
                                trans_table[resp_trans_idx].state <= TRANS_ERROR;
                                // Properly distinguish between SLVERR and DECERR
                                trans_table[resp_trans_idx].error_code <= (i_resp[0]) ? EVT_RESP_DECERR : EVT_RESP_SLVERR;
                            end else if (trans_table[resp_trans_idx].data_completed) begin
                                // Transaction completed successfully
                                if (trans_table[resp_trans_idx].state != TRANS_ERROR) begin
                                    trans_table[resp_trans_idx].state <= TRANS_COMPLETE;

                                    // Performance metrics - calculate and store latencies
                                    if (ENABLE_PERF_PACKETS) begin
                                        // Additional performance tracking can be added here
                                    end
                                end
                            end else if (trans_table[resp_trans_idx].data_started) begin
                                // Response received before data completion (protocol violation)
                                trans_table[resp_trans_idx].state <= TRANS_ERROR;
                                trans_table[resp_trans_idx].error_code <= EVT_PROTOCOL;
                            end else begin
                                // Response received before data started (protocol violation)
                                trans_table[resp_trans_idx].state <= TRANS_ERROR;
                                trans_table[resp_trans_idx].error_code <= EVT_PROTOCOL;
                            end
                        end else if (resp_free_idx >= 0) begin
                            if (IS_AXI) begin
                                // Orphaned response (no matching transaction) - create entry
                                // Create orphaned transaction
                                trans_table[resp_free_idx].valid <= 1'b1;
                                trans_table[resp_free_idx].state <= TRANS_ORPHANED;
                                trans_table[resp_free_idx].id <= '0;
                                trans_table[resp_free_idx].id[IW-1:0] <= i_resp_id;
                                trans_table[resp_free_idx].resp_received <= 1'b1;
                                trans_table[resp_free_idx].resp_timestamp <= i_timestamp;
                                trans_table[resp_free_idx].error_code <= EVT_RESP_ORPHAN;
                                trans_table[resp_free_idx].channel <= 6'(i_resp_id % 64);
                            end else begin
                                // For AXI-Lite, orphaned response
                                // Create orphaned transaction
                                trans_table[resp_free_idx].valid <= 1'b1;
                                trans_table[resp_free_idx].state <= TRANS_ORPHANED;
                                trans_table[resp_free_idx].id <= '0; // No ID for AXI-Lite
                                trans_table[resp_free_idx].resp_received <= 1'b1;
                                trans_table[resp_free_idx].resp_timestamp <= i_timestamp;
                                trans_table[resp_free_idx].error_code <= EVT_RESP_ORPHAN;
                                trans_table[resp_free_idx].channel <= 6'h0; // AXI-Lite always channel 0
                            end

                            // Increment active count
                            active_count <= active_count + 1'b1;
                        end
                    end
                end
            end
        end
    endgenerate

endmodule : axi_errmon_trans_mgr
