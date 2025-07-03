`timescale 1ns / 1ps
/**
 * Monitor and Interrupt Bus Type Definitions
 *
 * This package defines common type definitions used across components
 * that that need monitoring, error handling and interrupt bus,
 * providing consistent data structures and enumerations.
 */
package monitor_types;

    // Event/Error code enumeration (4 bits)
    typedef enum logic [3:0] {
        EVT_NONE          = 4'h0,  // No event

        // Error events
        EVT_ADDR_TIMEOUT   = 4'h1,  // Address channel timeout
        EVT_DATA_TIMEOUT   = 4'h2,  // Data channel timeout
        EVT_RESP_TIMEOUT   = 4'h3,  // Response channel timeout
        EVT_RESP_SLVERR    = 4'h4,  // Error response (SLVERR)
        EVT_RESP_DECERR    = 4'h5,  // Error response (DECERR)
        EVT_DATA_ORPHAN    = 4'h6,  // Data without address
        EVT_RESP_ORPHAN    = 4'h7,  // Response without transaction
        EVT_PROTOCOL       = 4'h8,  // Protocol violation
        EVT_TRANS_COMPLETE = 4'h9,  // Transaction completed successfully
        EVT_ADDR_MISS_T0   = 4'hA,  // Address missed the address map
        EVT_ADDR_MISS_T1   = 4'hB,  // Address missed the address map
        // Reserved for future use
        EVT_RESERVED_C     = 4'hC,
        EVT_RESERVED_D     = 4'hD,
        EVT_RESERVED_E     = 4'hE,
        EVT_USER_DEFINED   = 4'hF    // User-defined event
    } axi_event_code_t;

    // Transaction state enumeration
    typedef enum logic [2:0] {
        TRANS_EMPTY          = 3'b000,  // Unused entry
        TRANS_ADDR_PHASE     = 3'b001,  // Address phase active
        TRANS_DATA_PHASE     = 3'b010,  // Data phase active
        TRANS_RESP_PHASE     = 3'b011,  // Response phase active
        TRANS_COMPLETE       = 3'b100,  // Transaction complete
        TRANS_ERROR          = 3'b101,  // Transaction has error
        TRANS_ORPHANED       = 3'b110   // Orphaned transaction
    } trans_state_t;

    // Transaction entry structure - one per outstanding transaction
    typedef struct packed {
        logic           valid;           // Entry is valid
        trans_state_t   state;           // Transaction state
        logic [31:0]    id;              // Transaction ID (padded to 32 bits)
        logic [63:0]    addr;            // Transaction address (padded to 64 bits)
        logic [7:0]     len;             // Burst length
        logic [2:0]     size;            // Access size
        logic [1:0]     burst;           // Burst type

        // Phase completion flags
        logic           addr_received;   // Address phase received
        logic           data_started;    // Data phase started
        logic           data_completed;  // Data phase completed
        logic           resp_received;   // Response received

        // Error detection and reporting
        axi_event_code_t event_code;     // Error code if any
        logic            event_reported; // Error or event has been reported

        // Timeout counters
        logic [15:0]     addr_timer;     // Address phase timer
        logic [15:0]     data_timer;     // Data phase timer
        logic [15:0]     resp_timer;     // Response phase timer

        // Timestamps for performance monitoring
        logic [31:0]     addr_timestamp; // When address phase completed
        logic [31:0]     data_timestamp; // When data phase completed
        logic [31:0]     resp_timestamp; // When response phase completed

        // Beat counters
        logic [7:0]      data_beat_count; // Number of data beats received
        logic [7:0]      expected_beats;  // Expected number of data beats

        // Additional tracking
        logic [5:0]     channel;        // Channel ID for multi-channel systems (6 bits)
    } axi_transaction_t;

    // Consolidated 64-bit interrupt bus packet
    // Fields are packed according to specified sizes:
    // - packet_type: 4 bits  [63:60] (error, completion, threshold, etc.)
    // - event_code:  4 bits  [59:56] (specific error or event code)
    // - channel_id:  6 bits  [55:50] (channel ID and AXI ID)
    // - unit_id:     4 bits  [49:46] (subsystem identifier)
    // - agent_id:    8 bits  [45:38] (module identifier)
    // - addr:        38 bits [37:0]  (address related to event)
    typedef logic [63:0] monitor_packet_t;

    // Interrupt bus packet types (used in packet_type field)
    localparam logic [3:0] PktTypeError      = 4'h0;  // Error event
    localparam logic [3:0] PktTypeCompletion = 4'h1;  // Transaction completion
    localparam logic [3:0] PktTypeThreshold  = 4'h2;  // Threshold crossed
    localparam logic [3:0] PktTypeTimeout    = 4'h3;  // Timeout event
    localparam logic [3:0] PktTypePerf       = 4'h4;  // Performance metric event
    localparam logic [3:0] PktTypeDebug      = 4'hF;  // Debug/trace event

    // Performance metric types (when PKT_TYPE_PERF is used)
    typedef enum logic [3:0] {
        PERF_ADDR_LATENCY    = 4'h0,  // Address phase latency
        PERF_DATA_LATENCY    = 4'h1,  // Data phase latency
        PERF_RESP_LATENCY    = 4'h2,  // Response phase latency
        PERF_TOTAL_LATENCY   = 4'h3,  // Total transaction latency
        PERF_THROUGHPUT      = 4'h4,  // Transaction throughput
        PERF_ERROR_RATE      = 4'h5,  // Error rate
        PERF_ACTIVE_COUNT    = 4'h6,  // Current active transaction count
        PERF_COMPLETED_COUNT = 4'h7,  // Total completed transaction count
        PERF_ERROR_COUNT     = 4'h8,  // Total error transaction count
        PERF_CUSTOM          = 4'hF   // Custom performance metric
    } perf_metric_t;

    // Debug event types (when PktTypeDebug is used)
    typedef enum logic [3:0] {
        DEBUG_STATE_CHANGE  = 4'h0,  // Transaction state changed
        DEBUG_ADDR_PHASE    = 4'h1,  // Address phase event
        DEBUG_DATA_PHASE    = 4'h2,  // Data phase event
        DEBUG_RESP_PHASE    = 4'h3,  // Response phase event
        DEBUG_TIMEOUT       = 4'h4,  // Timeout event detail
        DEBUG_ERROR         = 4'h5,  // Error event detail
        DEBUG_TRANS_CREATE  = 4'h6,  // Transaction created
        DEBUG_TRANS_REMOVE  = 4'h7,  // Transaction removed
        DEBUG_COUNTER       = 4'h8,  // Counter event
        DEBUG_CUSTOM        = 4'hF   // Custom debug event
    } debug_event_t;

    // Threshold event types (when PktTypeThreshold is used)
    typedef enum logic [3:0] {
        THRESH_ACTIVE_COUNT   = 4'h0,  // Active transaction count threshold
        THRESH_LATENCY        = 4'h1,  // Latency threshold
        THRESH_ERROR_RATE     = 4'h2,  // Error rate threshold
        THRESH_BUFFER_LEVEL   = 4'h3,  // Buffer fill level threshold
        THRESH_CUSTOM         = 4'hF   // Custom threshold
    } threshold_event_t;

endpackage : axi_errmon_types
