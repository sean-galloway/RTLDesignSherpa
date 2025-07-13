`timescale 1ns / 1ps
/**
 * Monitor Bus Type Definitions
 *
 * This package defines common type definitions used across components
 * that need monitoring, error handling and interrupt bus,
 * providing consistent data structures and enumerations for multiple
 * protocols.
 */
package monitor_pkg;

    // Protocol type enumeration for multi-protocol support
    typedef enum logic [1:0] {
        PROTOCOL_AXI    = 2'b00,
        PROTOCOL_PKT    = 2'b01,  // Packet-based protocol
        PROTOCOL_APB    = 2'b10,
        PROTOCOL_CUSTOM = 2'b11
    } protocol_type_t;

    // Legacy AXI Event/Error code enumeration (4 bits) - maintained for compatibility
    typedef enum logic [3:0] {
        EVT_NONE            = 4'h0,

        // Generic timeout events (work for any bus)
        EVT_CMD_TIMEOUT     = 4'h1,  // Command/Address timeout
        EVT_DATA_TIMEOUT    = 4'h2,  // Data timeout
        EVT_RESP_TIMEOUT    = 4'h3,  // Response timeout

        // Generic response errors
        EVT_RESP_ERROR      = 4'h4,  // Generic error response
        EVT_RESP_SLVERR     = 4'h5,  // Slave error (AXI/AHB)
        EVT_RESP_DECERR     = 4'h6,  // Decode error (AXI/AHB)

        // Generic protocol violations
        EVT_DATA_ORPHAN     = 4'h7,  // Data without command
        EVT_RESP_ORPHAN     = 4'h8,  // Response without transaction
        EVT_PROTOCOL        = 4'h9,  // Protocol violation
        EVT_TRANS_COMPLETE  = 4'hA,  // Transaction completed

        // Address miss events
        EVT_ADDR_MISS_T0    = 4'hB,
        EVT_ADDR_MISS_T1    = 4'hC,

        EVT_RESERVED_D      = 4'hD,
        EVT_RESERVED_E      = 4'hE,
        EVT_USER_DEFINED    = 4'hF
    } axi_event_code_t;

    // Packet-based protocol Event/Error code enumeration (4 bits to fit in packet format)
    // Uses packet_type field to provide additional context for event classification
    typedef enum logic [3:0] {
        // Basic events (shared across packet types)
        PKT_EVT_NONE           = 4'h0,  // No event
        PKT_EVT_COMPLETE       = 4'h1,  // Transaction/packet completed successfully
        PKT_EVT_TIMEOUT        = 4'h2,  // Timeout occurred (ACK/Credit/Packet)
        PKT_EVT_PARITY_ERR     = 4'h3,  // Parity error (Header/Payload/ACK)
        PKT_EVT_PROTOCOL_ERR   = 4'h4,  // Protocol violation
        PKT_EVT_OVERFLOW       = 4'h5,  // Buffer/Credit overflow
        PKT_EVT_UNDERFLOW      = 4'h6,  // Buffer/Credit underflow
        PKT_EVT_THRESHOLD      = 4'h7,  // Threshold crossed
        PKT_EVT_STALL          = 4'h8,  // Channel/Credit stall
        PKT_EVT_ORPHAN         = 4'h9,  // Orphaned packet/ACK
        PKT_EVT_INVALID        = 4'hA,  // Invalid type/channel/payload
        PKT_EVT_STREAM         = 4'hB,  // Stream event (start/end/abort)
        PKT_EVT_EFFICIENCY     = 4'hC,  // Efficiency/utilization metric
        PKT_EVT_COUNT          = 4'hD,  // Count milestone
        PKT_EVT_STATE          = 4'hE,  // State change
        PKT_EVT_USER           = 4'hF   // User defined
    } pkt_event_code_t;

    // Unified event code type that can handle both protocols (both 4-bit)
    typedef union packed {
        axi_event_code_t  axi_code;   // 4-bit AXI event code
        pkt_event_code_t  pkt_code;   // 4-bit packet-based event code
        logic [3:0]       raw_code;   // Raw 4-bit code
    } unified_event_code_t;

    // Packet protocol payload types
    typedef enum logic [1:0] {
        PKT_PAYLOAD_CONFIG = 2'b00,  // Configuration packet
        PKT_PAYLOAD_T0     = 2'b01,  // Timestamp packet
        PKT_PAYLOAD_T1     = 2'b10,  // Data packet
        PKT_PAYLOAD_T2     = 2'b11   // Raw packet
    } pkt_payload_type_t;

    // Packet protocol ACK types
    typedef enum logic [1:0] {
        PKT_ACK_STOP       = 2'b00,  // Stop acknowledgment
        PKT_ACK_START      = 2'b01,  // Start acknowledgment
        PKT_ACK_CREDIT_ON  = 2'b10,  // Credit enable acknowledgment
        PKT_ACK_STOP_AT_EOS = 2'b11  // Stop at end of stream
    } pkt_ack_type_t;

    // Transaction state enumeration (enhanced for packet protocols)
    typedef enum logic [2:0] {
        TRANS_EMPTY          = 3'b000,  // Unused entry
        TRANS_ADDR_PHASE     = 3'b001,  // Address phase active (AXI) / Packet sent (PKT)
        TRANS_DATA_PHASE     = 3'b010,  // Data phase active (AXI) / Waiting for ACK (PKT)
        TRANS_RESP_PHASE     = 3'b011,  // Response phase active (AXI) / ACK received (PKT)
        TRANS_COMPLETE       = 3'b100,  // Transaction complete
        TRANS_ERROR          = 3'b101,  // Transaction has error
        TRANS_ORPHANED       = 3'b110,  // Orphaned transaction
        TRANS_CREDIT_STALL   = 3'b111   // Credit stall (packet protocols only)
    } trans_state_t;

    // Enhanced transaction entry structure supporting both AXI and packet protocols
    typedef struct packed {
        logic                   valid;           // Entry is valid
        protocol_type_t         protocol;        // Protocol type (AXI/PKT)
        trans_state_t           state;           // Transaction state
        logic [31:0]            id;              // Transaction ID (AXI) / Sequence (PKT)
        logic [63:0]            addr;            // Transaction address / Channel addr
        logic [7:0]             len;             // Burst length (AXI) / Packet count (PKT)
        logic [2:0]             size;            // Access size (AXI) / Reserved (PKT)
        logic [1:0]             burst;           // Burst type (AXI) / Payload type (PKT)

        // Phase completion flags
        logic                   cmd_received;    // Address phase received / Packet sent
        logic                   data_started;    // Data phase started / ACK expected
        logic                   data_completed;  // Data phase completed / ACK received
        logic                   resp_received;   // Response received / Final ACK

        // Error detection and reporting
        unified_event_code_t    event_code;      // Error code if any
        logic                   event_reported;  // Error or event has been reported

        // Timeout counters
        logic [15:0]            addr_timer;      // Address phase timer / Packet timer
        logic [15:0]            data_timer;      // Data phase timer / ACK timer
        logic [15:0]            resp_timer;      // Response phase timer / Credit timer

        // Timestamps for performance monitoring
        logic [31:0]            addr_timestamp;  // When address/packet phase completed
        logic [31:0]            data_timestamp;  // When data/ack phase completed
        logic [31:0]            resp_timestamp;  // When response/final phase completed

        // Beat counters
        logic [7:0]             data_beat_count; // Data beats received / Packets sent
        logic [7:0]             expected_beats;  // Expected beats / Expected packets

        // Enhanced tracking for packet protocols
        logic [5:0]             channel;         // Channel ID (AXI ID / packet channel)
        logic                   eos_seen;        // EOS marker seen (packet protocols only)
        logic                   parity_error;    // Parity error detected (packet protocols only)
        logic [7:0]             credit_at_start; // Credits available at start (packet protocols only)
        logic [2:0]             retry_count;     // Number of retries (packet protocols only)
    } bus_transaction_t;

    // 64-bit monitor bus packet supporting both protocols
    // Fields are packed according to specified sizes:
    // - packet_type: 4 bits  [63:60] (error, completion, threshold, etc.)
    // - protocol:    2 bits  [59:58] (AXI/PKT/APB/Custom)
    // - event_code:  4 bits  [57:54] (specific error or event code)
    // - channel_id:  6 bits  [53:48] (channel ID and AXI ID)
    // - unit_id:     4 bits  [47:44] (subsystem identifier)
    // - agent_id:    8 bits  [43:36] (module identifier)
    // - event_data:  36 bits [35:0]  (event-specific data)
    typedef logic [63:0] monitor_packet_t;

    // Helper functions for monitor packet manipulation
    function automatic logic [3:0] get_packet_type(monitor_packet_t pkt);
        return pkt[63:60];
    endfunction

    function automatic protocol_type_t get_protocol_type(monitor_packet_t pkt);
        return protocol_type_t'(pkt[59:58]);
    endfunction

    function automatic logic [3:0] get_event_code(monitor_packet_t pkt);
        return pkt[57:54];
    endfunction

    function automatic logic [5:0] get_channel_id(monitor_packet_t pkt);
        return pkt[53:48];
    endfunction

    function automatic logic [3:0] get_unit_id(monitor_packet_t pkt);
        return pkt[47:44];
    endfunction

    function automatic logic [7:0] get_agent_id(monitor_packet_t pkt);
        return pkt[43:36];
    endfunction

    function automatic logic [35:0] get_event_data(monitor_packet_t pkt);
        return pkt[35:0];
    endfunction

    function automatic monitor_packet_t create_monitor_packet(
        logic [3:0]     packet_type,
        protocol_type_t protocol,
        logic [3:0]     event_code,
        logic [5:0]     channel_id,
        logic [3:0]     unit_id,
        logic [7:0]     agent_id,
        logic [35:0]    event_data
    );
        return {packet_type, protocol, event_code, channel_id, unit_id, agent_id, event_data};
    endfunction

    // monitor bus packet types (used in packet_type field)
    localparam logic [3:0] PktTypeError      = 4'h0;  // Error event
    localparam logic [3:0] PktTypeCompletion = 4'h1;  // Transaction completion
    localparam logic [3:0] PktTypeThreshold  = 4'h2;  // Threshold crossed
    localparam logic [3:0] PktTypeTimeout    = 4'h3;  // Timeout event
    localparam logic [3:0] PktTypePerf       = 4'h4;  // Performance metric event
    localparam logic [3:0] PktTypeCredit     = 4'h5;  // Credit status (packet protocols)
    localparam logic [3:0] PktTypeChannel    = 4'h6;  // Channel status (packet protocols)
    localparam logic [3:0] PktTypeStream     = 4'h7;  // Stream event (packet protocols)
    localparam logic [3:0] PktTypeDebug      = 4'hF;  // Debug/trace event

    // Performance metric types (when PktTypePerf is used)
    typedef enum logic [3:0] {
        PERF_ADDR_LATENCY      = 4'h0,  // Address phase latency
        PERF_DATA_LATENCY      = 4'h1,  // Data phase latency
        PERF_RESP_LATENCY      = 4'h2,  // Response phase latency
        PERF_TOTAL_LATENCY     = 4'h3,  // Total transaction latency
        PERF_THROUGHPUT        = 4'h4,  // Transaction throughput
        PERF_ERROR_RATE        = 4'h5,  // Error rate
        PERF_ACTIVE_COUNT      = 4'h6,  // Current active transaction count
        PERF_COMPLETED_COUNT   = 4'h7,  // Total completed transaction count
        PERF_ERROR_COUNT       = 4'h8,  // Total error transaction count
        PERF_CREDIT_EFFICIENCY = 4'h9, // Credit utilization (packet protocols)
        PERF_CHANNEL_UTIL      = 4'hA,  // Channel utilization (packet protocols)
        PERF_PACKET_RATE       = 4'hB,  // Packet rate (packet protocols)
        PERF_CUSTOM            = 4'hF   // Custom performance metric
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
        DEBUG_CREDIT_CHANGE = 4'h9,  // Credit change (packet protocols)
        DEBUG_PACKET_TRACE  = 4'hA,  // Packet trace (packet protocols)
        DEBUG_ACK_TRACE     = 4'hB,  // ACK trace (packet protocols)
        DEBUG_CUSTOM        = 4'hF   // Custom debug event
    } debug_event_t;

    // Threshold event types (when PktTypeThreshold is used)
    typedef enum logic [3:0] {
        THRESH_ACTIVE_COUNT   = 4'h0,  // Active transaction count threshold
        THRESH_LATENCY        = 4'h1,  // Latency threshold
        THRESH_ERROR_RATE     = 4'h2,  // Error rate threshold
        THRESH_BUFFER_LEVEL   = 4'h3,  // Buffer fill level threshold
        THRESH_CREDIT_LOW     = 4'h4,  // Credit low threshold (packet protocols)
        THRESH_PACKET_RATE    = 4'h5,  // Packet rate threshold (packet protocols)
        THRESH_CHANNEL_STALL  = 4'h6,  // Channel stall threshold (packet protocols)
        THRESH_CUSTOM         = 4'hF   // Custom threshold
    } threshold_event_t;

    // Credit event types (when PktTypeCredit is used - packet protocols only)
    typedef enum logic [3:0] {
        CREDIT_ALLOCATED     = 4'h0,  // Credits allocated
        CREDIT_CONSUMED      = 4'h1,  // Credits consumed
        CREDIT_RETURNED      = 4'h2,  // Credits returned
        CREDIT_OVERFLOW      = 4'h3,  // Credit overflow detected
        CREDIT_UNDERFLOW     = 4'h4,  // Credit underflow detected
        CREDIT_EXHAUSTED     = 4'h5,  // All credits exhausted
        CREDIT_RESTORED      = 4'h6,  // Credits restored
        CREDIT_EFFICIENCY    = 4'h7,  // Credit efficiency metric
        CREDIT_LEAK          = 4'h8,  // Credit leak detected
        CREDIT_CUSTOM        = 4'hF   // Custom credit event
    } credit_event_t;

    // Channel event types (when PktTypeChannel is used - packet protocols only)
    typedef enum logic [3:0] {
        CHANNEL_ACTIVE       = 4'h0,  // Channel became active
        CHANNEL_IDLE         = 4'h1,  // Channel became idle
        CHANNEL_STALLED      = 4'h2,  // Channel stalled
        CHANNEL_RESET        = 4'h3,  // Channel reset
        CHANNEL_ERROR        = 4'h4,  // Channel error
        CHANNEL_OVERFLOW     = 4'h5,  // Channel buffer overflow
        CHANNEL_UNDERFLOW    = 4'h6,  // Channel buffer underflow
        CHANNEL_THRESHOLD    = 4'h7,  // Channel threshold crossed
        CHANNEL_CUSTOM       = 4'hF   // Custom channel event
    } channel_event_t;

    // Stream event types (when PktTypeStream is used - packet protocols only)
    typedef enum logic [3:0] {
        STREAM_START         = 4'h0,  // Stream started
        STREAM_END           = 4'h1,  // Stream ended (EOS)
        STREAM_ABORT         = 4'h2,  // Stream aborted
        STREAM_PAUSE         = 4'h3,  // Stream paused
        STREAM_RESUME        = 4'h4,  // Stream resumed
        STREAM_ERROR         = 4'h5,  // Stream error
        STREAM_OVERFLOW      = 4'h6,  // Stream buffer overflow
        STREAM_UNDERFLOW     = 4'h7,  // Stream buffer underflow
        STREAM_CUSTOM        = 4'hF   // Custom stream event
    } stream_event_t;

endpackage : monitor_pkg
