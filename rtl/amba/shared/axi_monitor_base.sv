`timescale 1ns / 1ps
/**
 * AXI Monitor Bus Base Module
 *
 * This module provides a robust implementation for tracking AXI/AXI-Lite
 * transactions and reporting events and errors through the monitor bus.
 *
 * Features:
 * - Transaction-based tracking for both AXI and AXI-Lite
 * - Proper handling of out-of-order transactions
 * - Support for data arriving before address
 * - Complete protocol compliance
 * - Consolidated 64-bit event packet output for system event bus
 * - Optional performance metrics tracking

### Assumption 1: Address is always aligned to the data bus width
**Assumption**: All AXI transactions are aligned to the data bus width.

- **Implication**: `AxADDRESS` is always set to match the data bus width
    - if DATA_WIDTH = 512bits, `AxADDRESS` is always 64-byte aligned

### Assumption 2: Fixed Transfer Size
**Assumption**: All AXI transfers use the maximum transfer size equal to the bus width.

- **Implication**: `AxSIZE` is always set to match the data bus width
- **Rationale**: Maximizes bus utilization and simplifies address alignment
- **Implementation**:
    - 32-bit bus → `AxSIZE = 3'b010` (4 bytes)
    - 64-bit bus → `AxSIZE = 3'b011` (8 bytes)
    - 128-bit bus → `AxSIZE = 3'b100` (16 bytes)

### Assumption 3: Incrementing Bursts Only
**Assumption**: All AXI bursts use incrementing address mode (`AxBURST = 2'b01`).

- **Implication**: No FIXED (`2'b00`) or WRAP (`2'b10`) bursts supported
- **Rationale**: Simplifies address generation logic and covers most use cases
- **Benefit**: Eliminates wrap boundary calculations and fixed address handling

### Assumption 4: No Address Wraparound
**Assumption**: Transactions never wrap around the top of address space (0xFFFFFFFF -> 0x00000000).

- **Implication**: No wraparound handling in boundary crossing logic
- **Rationale**: Real systems never allow this condition due to memory layout and software design
- **Benefit**: Dramatically simplified boundary crossing detection logic

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
    input  logic [AW-1:0]            cmd_addr,    // Address value
    input  logic [IW-1:0]            cmd_id,      // Transaction ID
    input  logic [7:0]               cmd_len,     // Burst length (AXI only)
    input  logic [2:0]               cmd_size,    // Burst size (AXI only)
    input  logic [1:0]               cmd_burst,   // Burst type (AXI only)
    input  logic                     cmd_valid,   // Command valid
    input  logic                     cmd_ready,   // Command ready

    // Data channel (W/R)
    input  logic [IW-1:0]            data_id,      // Data ID (read only)
    input  logic                     data_last,    // Last data flag
    input  logic [1:0]               data_resp,    // Response code (read only)
    input  logic                     data_valid,   // Data valid
    input  logic                     data_ready,   // Data ready

    // Response channel (B)
    input  logic [IW-1:0]            resp_id,      // Response ID (write only)
    input  logic [1:0]               resp_code,    // Response code
    input  logic                     resp_valid,   // Response valid
    input  logic                     resp_ready,   // Response ready

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

    // Consolidated 64-bit event packet interface (monitor bus)
    output logic                     monbus_valid,  // Interrupt valid
    input  logic                     monbus_ready,  // Interrupt ready
    output logic [63:0]              monbus_packet, // Consolidated interrupt packet

    // Flow control and status
    output logic                     block_ready,    // Flow control signal
    output logic                     busy,           // Monitor is busy
    output logic [7:0]               active_count    // Number of active transactions
);

    // Import standard monitor types and constants
    import monitor_pkg::*;

    // Transaction tracking table - Fixed: Use unpacked array consistently
    bus_transaction_t w_trans_table[MAX_TRANSACTIONS];

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
        .MAX_TRANSACTIONS   (MAX_TRANSACTIONS),
        .ADDR_WIDTH         (ADDR_WIDTH),
        .ID_WIDTH           (ID_WIDTH),
        .IS_READ            (1'(IS_READ)),
        .IS_AXI             (1'(IS_AXI)),
        .ENABLE_PERF_PACKETS(1'(ENABLE_PERF_PACKETS))
    ) i_trans_mgr(
        .aclk               (aclk),
        .aresetn            (aresetn),
        .cmd_valid          (cmd_valid),
        .cmd_ready          (cmd_ready),
        .cmd_id             (cmd_id),
        .cmd_addr           (cmd_addr),
        .cmd_len            (cmd_len),
        .cmd_size           (cmd_size),
        .cmd_burst          (cmd_burst),
        .data_valid         (data_valid),
        .data_ready         (data_ready),
        .data_id            (data_id),
        .data_last          (data_last),
        .data_resp          (data_resp),
        .resp_valid         (resp_valid),
        .resp_ready         (resp_ready),
        .resp_id            (resp_id),
        .resp_code          (resp_code),
        .timestamp          (r_timestamp),
        .trans_table        (w_trans_table),
        .active_count       (w_active_count),
        .state_change       (w_state_change_detected)
    );

    // Invariant Timer using counter_freq_invariant
    axi_monitor_timer i_timer (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .i_cfg_freq_sel(i_cfg_freq_sel),
        .timer_tick    (w_timer_tick),
        .timestamp     (r_timestamp)
    );

    // Timeout Detector
    axi_monitor_timeout #(
        .MAX_TRANSACTIONS    (MAX_TRANSACTIONS),
        .ADDR_WIDTH          (ADDR_WIDTH),
        .IS_READ             (1'(IS_READ))
    ) i_timeout(
        .aclk                (aclk),
        .aresetn             (aresetn),
        .trans_table         (w_trans_table),
        .timer_tick          (w_timer_tick),
        .i_cfg_addr_cnt      (i_cfg_addr_cnt),
        .i_cfg_data_cnt      (i_cfg_data_cnt),
        .i_cfg_resp_cnt      (i_cfg_resp_cnt),
        .i_cfg_timeout_enable(i_cfg_timeout_enable),
        .timeout_detected    (w_timeout_detected)
    );

    // Interrupt Reporter with gaxi_fifo_sync
    axi_monitor_reporter #(
        .MAX_TRANSACTIONS      (MAX_TRANSACTIONS),
        .ADDR_WIDTH            (ADDR_WIDTH),
        .UNIT_ID               (UNIT_ID),
        .AGENT_ID              (AGENT_ID),
        .IS_READ               (1'(IS_READ)),
        .ENABLE_PERF_PACKETS   (1'(ENABLE_PERF_PACKETS)),
        .INTR_FIFO_DEPTH       (INTR_FIFO_DEPTH)
    ) i_reporter(
        .aclk                  (aclk),
        .aresetn               (aresetn),
        .trans_table           (w_trans_table),
        .i_cfg_error_enable    (i_cfg_error_enable),
        .i_cfg_compl_enable    (i_cfg_compl_enable),
        .i_cfg_threshold_enable(i_cfg_threshold_enable),
        .i_cfg_timeout_enable  (i_cfg_timeout_enable),
        .i_cfg_perf_enable     (i_cfg_perf_enable),
        .i_cfg_debug_enable    (i_cfg_debug_enable),
        .monbus_ready          (monbus_ready),
        .monbus_valid          (w_reporter_monbus_valid),
        .monbus_packet         (w_reporter_monbus_packet),
        .event_count           (w_event_count),
        .perf_completed_count  (r_perf_completed_count),
        .perf_error_count      (r_perf_error_count),
        .active_trans_threshold(i_cfg_active_trans_threshold),
        .latency_threshold     (i_cfg_latency_threshold)
    );

    // -------------------------------------------------------------------------
    // Monitor Bus Arbitration
    // -------------------------------------------------------------------------

    // Simple priority arbitration between reporter and debug packets
    always_comb begin
        if (w_reporter_monbus_valid) begin
            monbus_valid = w_reporter_monbus_valid;
            monbus_packet = w_reporter_monbus_packet;
        end else if (w_debug_monbus_valid) begin
            monbus_valid = w_debug_monbus_valid;
            monbus_packet = w_debug_monbus_packet;
        end else begin
            monbus_valid = 1'b0;
            monbus_packet = '0;
        end
    end

    // -------------------------------------------------------------------------
    // Flow Control Logic
    // -------------------------------------------------------------------------

    // Flow control - block when too many outstanding transactions
    assign block_ready = ({24'h0, w_active_count} >= (MAX_TRANSACTIONS - 2));

    // Busy signal
    assign busy = (w_active_count > 0);

    // Active transaction count
    assign active_count = w_active_count;

endmodule : axi_monitor_base
