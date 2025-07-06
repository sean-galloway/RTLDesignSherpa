`timescale 1ns / 1ps
/**
 * AXI Interrupt Bus Base Module
 *
 * This module provides a robust implementation for tracking AXI/AXI-Lite
 * transactions and reporting events and errors through the interrupt bus.
 *
 * Features:
 * - Transaction-based tracking for both AXI and AXI-Lite
 * - Proper handling of out-of-order transactions
 * - Support for data arriving before address
 * - Complete protocol compliance
 * - Consolidated 64-bit event packet output for system event bus
 * - Optional performance metrics tracking
 *
 * Updated with proper naming conventions: w_ for combo, r_ for flopped
 * Fixed array declaration consistency for Verilator compatibility
 */
module axi_monitor_base
#(
    // Error Packet Identifiers
    parameter int UNIT_ID             = 9,     // 4-bit Unit ID
    parameter int AGENT_ID            = 99,    // 8-bit Agent ID

    // General parameters
    parameter int MAX_TRANSACTIONS    = 16,    // Maximum outstanding transactions
    parameter int ADDR_WIDTH          = 32,    // Width of address bus
    parameter int ID_WIDTH            = 8,     // Width of ID bus (0 for AXIL)
    parameter int ADDR_BITS_IN_PKT    = 38,    // Number of address bits to include in error packet

    // Configuration options
    parameter int IS_READ             = 1, // 1 for read, 0 for write
    parameter int IS_AXI              = 1, // 1 for AXI, 0 for AXI-Lite
    parameter int ENABLE_PERF_PACKETS = 0, // Enable performance metrics tracking
    parameter int ENABLE_DEBUG_MODULE = 0, // Enable debug tracking module

    // FIFO depths
    parameter int INTR_FIFO_DEPTH     = 8,     // Interrupt FIFO depth
    parameter int DEBUG_FIFO_DEPTH    = 8,     // Debug FIFO depth

    // Short params
    parameter int AW                 = ADDR_WIDTH,
    parameter int IW                 = ID_WIDTH,

    // Verify address bits parameter
    parameter int ADDR_BITS          = (ADDR_BITS_IN_PKT > AW) ? AW : ADDR_BITS_IN_PKT
)
(
    // Global Clock and Reset
    input  logic                     aclk,
    input  logic                     aresetn,

    // Command phase (AW/AR)
    input  logic [AW-1:0]            i_addr_addr,    // Address value
    input  logic [IW-1:0]            i_addr_id,      // Transaction ID
    input  logic                     i_addr_valid,   // Command valid
    input  logic                     i_addr_ready,   // Command ready
    input  logic [7:0]               i_addr_len,     // Burst length (AXI only)
    input  logic [2:0]               i_addr_size,    // Burst size (AXI only)
    input  logic [1:0]               i_addr_burst,   // Burst type (AXI only)

    // Data channel (W/R)
    input  logic [IW-1:0]            i_data_id,      // Data ID (read only)
    input  logic                     i_data_last,    // Last data flag
    input  logic [1:0]               i_data_resp,    // Response code (read only)
    input  logic                     i_data_valid,   // Data valid
    input  logic                     i_data_ready,   // Data ready

    // Response channel (B)
    input  logic [IW-1:0]            i_resp_id,      // Response ID (write only)
    input  logic [1:0]               i_resp,         // Response code
    input  logic                     i_resp_valid,   // Response valid
    input  logic                     i_resp_ready,   // Response ready

    // Timer configs
    input  logic [3:0]               i_cfg_freq_sel, // Frequency selection (configurable)
    input  logic [3:0]               i_cfg_addr_cnt, // ADDR match for a timeout
    input  logic [3:0]               i_cfg_data_cnt, // DATA match for a timeout
    input  logic [3:0]               i_cfg_resp_cnt, // RESP match for a timeout

    // Packet type enables
    input  logic                     i_cfg_error_enable,    // Enable error event packets
    input  logic                     i_cfg_compl_enable,    // Enable transaction completion packets
    input  logic                     i_cfg_threshold_enable,// Enable threshold crossed packets
    input  logic                     i_cfg_timeout_enable,  // Enable timeout event packets
    input  logic                     i_cfg_perf_enable,     // Enable performance metric packets
    input  logic                     i_cfg_debug_enable,    // Enable debug/trace packets

    // Debug configuration (only used when ENABLE_DEBUG_MODULE=1)
    input  logic [3:0]               i_cfg_debug_level, // Debug verbosity level
    input  logic [15:0]              i_cfg_debug_mask,  // Event type mask

    // Threshold configuration
    input  logic [15:0]              i_cfg_active_trans_threshold, // Active transaction threshold
    input  logic [31:0]              i_cfg_latency_threshold,      // Latency threshold

    // Consolidated 64-bit event packet interface (interrupt bus)
    output logic                     o_monbus_valid,  // Interrupt valid
    input  logic                     i_monbus_ready,  // Interrupt ready
    output logic [63:0]              o_monbus_packet, // Consolidated interrupt packet

    // Flow control and status
    output logic                     o_block_ready,    // Flow control signal
    output logic                     o_busy,           // Monitor is busy
    output logic [7:0]               o_active_count    // Number of active transactions
);

    // Import standard monitor types and constants
    import monitor_pkg::*;

    // Transaction tracking table - Fixed: Use unpacked array consistently
    axi_transaction_t w_trans_table[MAX_TRANSACTIONS];

    // Transaction statistics (combinational)
    logic [7:0]  w_active_count;
    logic [15:0] w_event_count;
    logic [15:0] w_debug_count;

    // Timer tick from the frequency invariant timer (combinational)
    logic w_timer_tick;

    // Timestamp counter for transaction timing (flopped)
    logic [31:0] r_timestamp;

    // State change detection for debug module (combinational)
    logic [MAX_TRANSACTIONS-1:0] w_state_change_detected;
    logic [MAX_TRANSACTIONS-1:0] w_timeout_detected;

    // Interrupt outputs from different modules (combinational)
    logic                     w_reporter_monbus_valid;
    logic [63:0]              w_reporter_monbus_packet;
    logic                     w_debug_monbus_valid;
    logic [63:0]              w_debug_monbus_packet;

    // Performance metrics registers (only used when ENABLE_PERF_PACKETS=1) (flopped)
    logic [15:0] r_perf_completed_count;
    logic [15:0] r_perf_error_count;

    // -------------------------------------------------------------------------
    // Module Instantiations
    // -------------------------------------------------------------------------

    // Transaction Table Manager
    axi_monitor_trans_mgr #(
        .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
        .ADDR_WIDTH(ADDR_WIDTH),
        .ID_WIDTH(ID_WIDTH),
        .IS_READ(1'(IS_READ)),
        .IS_AXI(1'(IS_AXI)),
        .ENABLE_PERF_PACKETS(1'(ENABLE_PERF_PACKETS))
    ) i_trans_mgr (
        .aclk(aclk),
        .aresetn(aresetn),
        .i_addr_valid(i_addr_valid),
        .i_addr_ready(i_addr_ready),
        .i_addr_id(i_addr_id),
        .i_addr_addr(i_addr_addr),
        .i_addr_len(i_addr_len),
        .i_addr_size(i_addr_size),
        .i_addr_burst(i_addr_burst),
        .i_data_valid(i_data_valid),
        .i_data_ready(i_data_ready),
        .i_data_id(i_data_id),
        .i_data_last(i_data_last),
        .i_data_resp(i_data_resp),
        .i_resp_valid(i_resp_valid),
        .i_resp_ready(i_resp_ready),
        .i_resp_id(i_resp_id),
        .i_resp(i_resp),
        .i_timestamp(r_timestamp),
        .o_trans_table(w_trans_table),
        .o_active_count(w_active_count),
        .o_state_change(w_state_change_detected)
    );

    // Invariant Timer using counter_freq_invariant
    axi_monitor_timer i_timer (
        .aclk(aclk),
        .aresetn(aresetn),
        .i_cfg_freq_sel(i_cfg_freq_sel),
        .o_timer_tick(w_timer_tick),
        .o_timestamp(r_timestamp)
    );

    // Timeout Detector
    axi_monitor_timeout #(
        .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
        .ADDR_WIDTH(ADDR_WIDTH),
        .IS_READ(1'(IS_READ))
    ) i_timeout (
        .aclk(aclk),
        .aresetn(aresetn),
        .i_trans_table(w_trans_table),
        .i_timer_tick(w_timer_tick),
        .i_cfg_addr_cnt(i_cfg_addr_cnt),
        .i_cfg_data_cnt(i_cfg_data_cnt),
        .i_cfg_resp_cnt(i_cfg_resp_cnt),
        .i_cfg_timeout_enable(i_cfg_timeout_enable),
        .o_timeout_detected(w_timeout_detected)
    );

    // Interrupt Reporter with gaxi_fifo_sync
    axi_monitor_reporter #(
        .MAX_TRANSACTIONS(MAX_TRANSACTIONS),
        .ADDR_WIDTH(ADDR_WIDTH),
        .UNIT_ID(UNIT_ID),
        .AGENT_ID(AGENT_ID),
        .IS_READ(1'(IS_READ)),
        .ENABLE_PERF_PACKETS(1'(ENABLE_PERF_PACKETS)),
        .INTR_FIFO_DEPTH(INTR_FIFO_DEPTH)
    ) i_reporter (
        .aclk(aclk),
        .aresetn(aresetn),
        .i_trans_table(w_trans_table),
        .i_cfg_error_enable(i_cfg_error_enable),
        .i_cfg_compl_enable(i_cfg_compl_enable),
        .i_cfg_threshold_enable(i_cfg_threshold_enable),
        .i_cfg_timeout_enable(i_cfg_timeout_enable),
        .i_cfg_perf_enable(i_cfg_perf_enable),
        .i_cfg_debug_enable(i_cfg_debug_enable),
        .i_monbus_ready(i_monbus_ready),
        .o_monbus_valid(w_reporter_monbus_valid),
        .o_monbus_packet(w_reporter_monbus_packet),
        .o_event_count(w_event_count),
        .o_perf_completed_count(r_perf_completed_count),
        .o_perf_error_count(r_perf_error_count),
        .i_active_trans_threshold(i_cfg_active_trans_threshold),
        .i_latency_threshold(i_cfg_latency_threshold)
    );

    // -------------------------------------------------------------------------
    // Interrupt Bus Arbitration
    // -------------------------------------------------------------------------

    // Simple priority arbitration between reporter and debug packets
    always_comb begin
        if (w_reporter_monbus_valid) begin
            o_monbus_valid = w_reporter_monbus_valid;
            o_monbus_packet = w_reporter_monbus_packet;
        end else if (w_debug_monbus_valid) begin
            o_monbus_valid = w_debug_monbus_valid;
            o_monbus_packet = w_debug_monbus_packet;
        end else begin
            o_monbus_valid = 1'b0;
            o_monbus_packet = '0;
        end
    end

    // -------------------------------------------------------------------------
    // Flow Control Logic
    // -------------------------------------------------------------------------

    // Flow control - block when too many outstanding transactions
    assign o_block_ready = ({24'h0, w_active_count} >= (MAX_TRANSACTIONS - 2));

    // Busy signal
    assign o_busy = (w_active_count > 0);

    // Active transaction count
    assign o_active_count = w_active_count;

endmodule : axi_monitor_base