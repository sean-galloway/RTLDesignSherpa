`timescale 1ns / 1ps
/**
 * Monitor Bus Type Definitions - Reorganized with Protocol-Specific Event Codes
 *
 * This package defines common type definitions used across components
 * that need monitoring, error handling and interrupt bus,
 * providing consistent data structures and enumerations for multiple
 * protocols with proper 1:1 mapping between packet types and event codes.
 *
 * Key Design Principle:
 * For each protocol, each packet type has exactly 16 event codes (4 bits).
 * This creates a clean categorization where:
 * - packet_type [63:60] defines the category (error, timeout, completion, etc.)
 * - protocol [59:58] defines which protocol (AXI, NOC, APB, Custom)
 * - event_code [57:54] defines the specific event within that category
 */
package monitor_pkg;

    // Protocol type enumeration for multi-protocol support
    typedef enum logic [1:0] {
        PROTOCOL_AXI    = 2'b00,
        PROTOCOL_NOC    = 2'b01,  // Network on Chip
        PROTOCOL_APB    = 2'b10,  // Advanced Peripheral Bus
        PROTOCOL_CUSTOM = 2'b11
    } protocol_type_t;

    // Monitor bus packet types (used in packet_type field [63:60])
    localparam logic [3:0] PktTypeError      = 4'h0;  // Error event
    localparam logic [3:0] PktTypeCompletion = 4'h1;  // Transaction completion
    localparam logic [3:0] PktTypeThreshold  = 4'h2;  // Threshold crossed
    localparam logic [3:0] PktTypeTimeout    = 4'h3;  // Timeout event
    localparam logic [3:0] PktTypePerf       = 4'h4;  // Performance metric event
    localparam logic [3:0] PktTypeCredit     = 4'h5;  // Credit status (NOC)
    localparam logic [3:0] PktTypeChannel    = 4'h6;  // Channel status (NOC)
    localparam logic [3:0] PktTypeStream     = 4'h7;  // Stream event (NOC)
    localparam logic [3:0] PktTypeAddrMatch  = 4'h8;  // Address match event (AXI)
    localparam logic [3:0] PktTypeAPB        = 4'h9;  // APB-specific event
    localparam logic [3:0] PktTypeReserved_A = 4'hA;  // Reserved
    localparam logic [3:0] PktTypeReserved_B = 4'hB;  // Reserved
    localparam logic [3:0] PktTypeReserved_C = 4'hC;  // Reserved
    localparam logic [3:0] PktTypeReserved_D = 4'hD;  // Reserved
    localparam logic [3:0] PktTypeReserved_E = 4'hE;  // Reserved
    localparam logic [3:0] PktTypeDebug      = 4'hF;  // Debug/trace event

    // =============================================================================
    // AXI PROTOCOL EVENT CODES (organized by packet type)
    // =============================================================================

    // AXI Error Events (packet_type = PktTypeError, protocol = PROTOCOL_AXI)
    typedef enum logic [3:0] {
        AXI_ERR_RESP_SLVERR         = 4'h0,  // Slave error response
        AXI_ERR_RESP_DECERR         = 4'h1,  // Decode error response
        AXI_ERR_DATA_ORPHAN         = 4'h2,  // Data without command
        AXI_ERR_RESP_ORPHAN         = 4'h3,  // Response without transaction
        AXI_ERR_PROTOCOL            = 4'h4,  // Protocol violation
        AXI_ERR_BURST_LENGTH        = 4'h5,  // Invalid burst length
        AXI_ERR_BURST_SIZE          = 4'h6,  // Invalid burst size
        AXI_ERR_BURST_TYPE          = 4'h7,  // Invalid burst type
        AXI_ERR_ID_COLLISION        = 4'h8,  // ID collision detected
        AXI_ERR_WRITE_BEFORE_ADDR   = 4'h9,  // Write data before address
        AXI_ERR_RESP_BEFORE_DATA    = 4'hA,  // Response before data complete
        AXI_ERR_LAST_MISSING        = 4'hB,  // Missing LAST signal
        AXI_ERR_STROBE_ERROR        = 4'hC,  // Write strobe error
        AXI_ERR_ARBITER_STARVATION  = 4'hD,  // Arbiter starvation detected
        AXI_ERR_CREDIT_VIOLATION    = 4'hE,  // Credit system violation
        AXI_ERR_USER_DEFINED        = 4'hF   // User-defined error
    } axi_error_code_t;

    // AXI Timeout Events (packet_type = PktTypeTimeout, protocol = PROTOCOL_AXI)
    typedef enum logic [3:0] {
        AXI_TIMEOUT_CMD          = 4'h0,  // Command/Address timeout
        AXI_TIMEOUT_DATA         = 4'h1,  // Data timeout
        AXI_TIMEOUT_RESP         = 4'h2,  // Response timeout
        AXI_TIMEOUT_HANDSHAKE    = 4'h3,  // Handshake timeout
        AXI_TIMEOUT_BURST        = 4'h4,  // Burst completion timeout
        AXI_TIMEOUT_EXCLUSIVE    = 4'h5,  // Exclusive access timeout
        AXI_TIMEOUT_RESERVED_6   = 4'h6,  // Reserved
        AXI_TIMEOUT_RESERVED_7   = 4'h7,  // Reserved
        AXI_TIMEOUT_RESERVED_8   = 4'h8,  // Reserved
        AXI_TIMEOUT_RESERVED_9   = 4'h9,  // Reserved
        AXI_TIMEOUT_RESERVED_A   = 4'hA,  // Reserved
        AXI_TIMEOUT_RESERVED_B   = 4'hB,  // Reserved
        AXI_TIMEOUT_RESERVED_C   = 4'hC,  // Reserved
        AXI_TIMEOUT_RESERVED_D   = 4'hD,  // Reserved
        AXI_TIMEOUT_RESERVED_E   = 4'hE,  // Reserved
        AXI_TIMEOUT_USER_DEFINED = 4'hF   // User-defined timeout
    } axi_timeout_code_t;

    // AXI Completion Events (packet_type = PktTypeCompletion, protocol = PROTOCOL_AXI)
    typedef enum logic [3:0] {
        AXI_COMPL_TRANS_COMPLETE = 4'h0,  // Transaction completed successfully
        AXI_COMPL_READ_COMPLETE  = 4'h1,  // Read transaction complete
        AXI_COMPL_WRITE_COMPLETE = 4'h2,  // Write transaction complete
        AXI_COMPL_BURST_COMPLETE = 4'h3,  // Burst transaction complete
        AXI_COMPL_EXCLUSIVE_OK   = 4'h4,  // Exclusive access completed
        AXI_COMPL_EXCLUSIVE_FAIL = 4'h5,  // Exclusive access failed
        AXI_COMPL_ATOMIC_OK      = 4'h6,  // Atomic operation completed
        AXI_COMPL_ATOMIC_FAIL    = 4'h7,  // Atomic operation failed
        AXI_COMPL_RESERVED_8     = 4'h8,  // Reserved
        AXI_COMPL_RESERVED_9     = 4'h9,  // Reserved
        AXI_COMPL_RESERVED_A     = 4'hA,  // Reserved
        AXI_COMPL_RESERVED_B     = 4'hB,  // Reserved
        AXI_COMPL_RESERVED_C     = 4'hC,  // Reserved
        AXI_COMPL_RESERVED_D     = 4'hD,  // Reserved
        AXI_COMPL_RESERVED_E     = 4'hE,  // Reserved
        AXI_COMPL_USER_DEFINED   = 4'hF   // User-defined completion
    } axi_completion_code_t;

    // AXI Threshold Events (packet_type = PktTypeThreshold, protocol = PROTOCOL_AXI)
    typedef enum logic [3:0] {
        AXI_THRESH_ACTIVE_COUNT   = 4'h0,  // Active transaction count threshold
        AXI_THRESH_LATENCY        = 4'h1,  // Latency threshold
        AXI_THRESH_ERROR_RATE     = 4'h2,  // Error rate threshold
        AXI_THRESH_THROUGHPUT     = 4'h3,  // Throughput threshold
        AXI_THRESH_QUEUE_DEPTH    = 4'h4,  // Queue depth threshold
        AXI_THRESH_BANDWIDTH      = 4'h5,  // Bandwidth utilization threshold
        AXI_THRESH_OUTSTANDING    = 4'h6,  // Outstanding transactions threshold
        AXI_THRESH_BURST_SIZE     = 4'h7,  // Average burst size threshold
        AXI_THRESH_GRANT_LATENCY  = 4'h8,  // Request-to-grant latency threshold
        AXI_THRESH_FAIRNESS       = 4'h9,  // Weighted fairness deviation threshold
        AXI_THRESH_RESERVED_A     = 4'hA,  // Reserved
        AXI_THRESH_RESERVED_B     = 4'hB,  // Reserved
        AXI_THRESH_RESERVED_C     = 4'hC,  // Reserved
        AXI_THRESH_RESERVED_D     = 4'hD,  // Reserved
        AXI_THRESH_RESERVED_E     = 4'hE,  // Reserved
        AXI_THRESH_USER_DEFINED   = 4'hF   // User-defined threshold
    } axi_threshold_code_t;

    // AXI Performance Events (packet_type = PktTypePerf, protocol = PROTOCOL_AXI)
    typedef enum logic [3:0] {
        AXI_PERF_ADDR_LATENCY      = 4'h0,  // Address phase latency
        AXI_PERF_DATA_LATENCY      = 4'h1,  // Data phase latency
        AXI_PERF_RESP_LATENCY      = 4'h2,  // Response phase latency
        AXI_PERF_TOTAL_LATENCY     = 4'h3,  // Total transaction latency
        AXI_PERF_THROUGHPUT        = 4'h4,  // Transaction throughput
        AXI_PERF_ERROR_RATE        = 4'h5,  // Error rate
        AXI_PERF_ACTIVE_COUNT      = 4'h6,  // Current active transaction count
        AXI_PERF_COMPLETED_COUNT   = 4'h7,  // Total completed transaction count
        AXI_PERF_ERROR_COUNT       = 4'h8,  // Total error transaction count
        AXI_PERF_BANDWIDTH_UTIL    = 4'h9,  // Bandwidth utilization
        AXI_PERF_QUEUE_DEPTH       = 4'hA,  // Average queue depth
        AXI_PERF_BURST_EFFICIENCY  = 4'hB,  // Burst efficiency metric
        AXI_PERF_GRANT_EFFICIENCY  = 4'hC,  // Grant utilization efficiency
        AXI_PERF_WEIGHT_COMPLIANCE = 4'hD,  // Weight compliance metric
        AXI_PERF_READ_WRITE_RATIO  = 4'hE,  // Read/write ratio
        AXI_PERF_USER_DEFINED      = 4'hF   // User-defined performance
    } axi_performance_code_t;

    // AXI Address Match Events (packet_type = PktTypeAddrMatch, protocol = PROTOCOL_AXI)
    typedef enum logic [3:0] {
        AXI_ADDR_MATCH_DESC         = 4'h0,  // Descriptor address match
        AXI_ADDR_MATCH_DATA         = 4'h1,  // Data address match
        AXI_ADDR_MATCH_READ         = 4'h2,  // Read address match
        AXI_ADDR_MATCH_WRITE        = 4'h3,  // Write address match
        AXI_ADDR_MATCH_RANGE        = 4'h4,  // Address range match
        AXI_ADDR_MATCH_EXACT        = 4'h5,  // Exact address match
        AXI_ADDR_MATCH_MASK         = 4'h6,  // Masked address match
        AXI_ADDR_MATCH_BURST        = 4'h7,  // Burst crossing boundary
        AXI_ADDR_MATCH_CACHEABLE    = 4'h8,  // Cacheable region match
        AXI_ADDR_MATCH_DEVICE       = 4'h9,  // Device region match
        AXI_ADDR_MATCH_SECURE       = 4'hA,  // Secure region match
        AXI_ADDR_MATCH_RESERVED_B   = 4'hB, // Reserved
        AXI_ADDR_MATCH_RESERVED_C   = 4'hC, // Reserved
        AXI_ADDR_MATCH_RESERVED_D   = 4'hD, // Reserved
        AXI_ADDR_MATCH_RESERVED_E   = 4'hE, // Reserved
        AXI_ADDR_MATCH_USER_DEFINED = 4'hF // User-defined match
    } axi_addr_match_code_t;

    // AXI Debug Events (packet_type = PktTypeDebug, protocol = PROTOCOL_AXI)
    typedef enum logic [3:0] {
        AXI_DEBUG_STATE_CHANGE   = 4'h0,  // Transaction state changed
        AXI_DEBUG_ADDR_PHASE     = 4'h1,  // Address phase event
        AXI_DEBUG_DATA_PHASE     = 4'h2,  // Data phase event
        AXI_DEBUG_RESP_PHASE     = 4'h3,  // Response phase event
        AXI_DEBUG_TRANS_CREATE   = 4'h4,  // Transaction created
        AXI_DEBUG_TRANS_REMOVE   = 4'h5,  // Transaction removed
        AXI_DEBUG_ID_ALLOCATION  = 4'h6,  // ID allocation/deallocation
        AXI_DEBUG_HANDSHAKE      = 4'h7,  // Handshake trace
        AXI_DEBUG_QUEUE_STATUS   = 4'h8,  // Queue status
        AXI_DEBUG_COUNTER        = 4'h9,  // Counter event
        AXI_DEBUG_FIFO_STATUS    = 4'hA,  // FIFO status
        AXI_DEBUG_CREDIT_STATUS  = 4'hB,  // Credit status
        AXI_DEBUG_ARBITER_STATE  = 4'hC,  // Arbiter state changes
        AXI_DEBUG_BLOCK_EVENT    = 4'hD,  // Blocking start/stop events
        AXI_DEBUG_RESERVED_E     = 4'hE,  // Reserved
        AXI_DEBUG_USER_DEFINED   = 4'hF   // User-defined debug
    } axi_debug_code_t;

    // =============================================================================
    // APB PROTOCOL EVENT CODES (organized by packet type)
    // =============================================================================

    // APB Error Events (packet_type = PktTypeError, protocol = PROTOCOL_APB)
    typedef enum logic [3:0] {
        APB_ERR_PSLVERR          = 4'h0,  // Peripheral slave error
        APB_ERR_SETUP_VIOLATION  = 4'h1,  // Setup phase protocol violation
        APB_ERR_ACCESS_VIOLATION = 4'h2,  // Access phase protocol violation
        APB_ERR_STROBE_ERROR     = 4'h3,  // Write strobe error
        APB_ERR_ADDR_DECODE      = 4'h4,  // Address decode error
        APB_ERR_PROT_VIOLATION   = 4'h5,  // Protection violation (PPROT)
        APB_ERR_ENABLE_ERROR     = 4'h6,  // Enable phase error
        APB_ERR_READY_ERROR      = 4'h7,  // PREADY protocol error
        APB_ERR_RESERVED_8       = 4'h8,  // Reserved
        APB_ERR_RESERVED_9       = 4'h9,  // Reserved
        APB_ERR_RESERVED_A       = 4'hA,  // Reserved
        APB_ERR_RESERVED_B       = 4'hB,  // Reserved
        APB_ERR_RESERVED_C       = 4'hC,  // Reserved
        APB_ERR_RESERVED_D       = 4'hD,  // Reserved
        APB_ERR_RESERVED_E       = 4'hE,  // Reserved
        APB_ERR_USER_DEFINED     = 4'hF   // User-defined error
    } apb_error_code_t;

    // APB Timeout Events (packet_type = PktTypeTimeout, protocol = PROTOCOL_APB)
    typedef enum logic [3:0] {
        APB_TIMEOUT_SETUP        = 4'h0,  // Setup phase timeout
        APB_TIMEOUT_ACCESS       = 4'h1,  // Access phase timeout
        APB_TIMEOUT_ENABLE       = 4'h2,  // Enable phase timeout (PREADY stuck)
        APB_TIMEOUT_PREADY_STUCK = 4'h3,  // PREADY stuck low
        APB_TIMEOUT_TRANSFER     = 4'h4,  // Overall transfer timeout
        APB_TIMEOUT_RESERVED_5   = 4'h5,  // Reserved
        APB_TIMEOUT_RESERVED_6   = 4'h6,  // Reserved
        APB_TIMEOUT_RESERVED_7   = 4'h7,  // Reserved
        APB_TIMEOUT_RESERVED_8   = 4'h8,  // Reserved
        APB_TIMEOUT_RESERVED_9   = 4'h9,  // Reserved
        APB_TIMEOUT_RESERVED_A   = 4'hA,  // Reserved
        APB_TIMEOUT_RESERVED_B   = 4'hB,  // Reserved
        APB_TIMEOUT_RESERVED_C   = 4'hC,  // Reserved
        APB_TIMEOUT_RESERVED_D   = 4'hD,  // Reserved
        APB_TIMEOUT_RESERVED_E   = 4'hE,  // Reserved
        APB_TIMEOUT_USER_DEFINED = 4'hF   // User-defined timeout
    } apb_timeout_code_t;

    // APB Completion Events (packet_type = PktTypeCompletion, protocol = PROTOCOL_APB)
    typedef enum logic [3:0] {
        APB_COMPL_TRANS_COMPLETE = 4'h0,  // Transaction completed
        APB_COMPL_READ_COMPLETE  = 4'h1,  // Read transaction complete
        APB_COMPL_WRITE_COMPLETE = 4'h2,  // Write transaction complete
        APB_COMPL_SECURE_ACCESS  = 4'h3,  // Secure access completed
        APB_COMPL_PRIV_ACCESS    = 4'h4,  // Privileged access completed
        APB_COMPL_RESERVED_5     = 4'h5,  // Reserved
        APB_COMPL_RESERVED_6     = 4'h6,  // Reserved
        APB_COMPL_RESERVED_7     = 4'h7,  // Reserved
        APB_COMPL_RESERVED_8     = 4'h8,  // Reserved
        APB_COMPL_RESERVED_9     = 4'h9,  // Reserved
        APB_COMPL_RESERVED_A     = 4'hA,  // Reserved
        APB_COMPL_RESERVED_B     = 4'hB,  // Reserved
        APB_COMPL_RESERVED_C     = 4'hC,  // Reserved
        APB_COMPL_RESERVED_D     = 4'hD,  // Reserved
        APB_COMPL_RESERVED_E     = 4'hE,  // Reserved
        APB_COMPL_USER_DEFINED   = 4'hF   // User-defined completion
    } apb_completion_code_t;

    // APB Threshold Events (packet_type = PktTypeThreshold, protocol = PROTOCOL_APB)
    typedef enum logic [3:0] {
        APB_THRESH_LATENCY       = 4'h0,  // APB latency threshold
        APB_THRESH_ERROR_RATE    = 4'h1,  // APB error rate threshold
        APB_THRESH_ACCESS_COUNT  = 4'h2,  // Access count threshold
        APB_THRESH_BANDWIDTH     = 4'h3,  // Bandwidth threshold
        APB_THRESH_RESERVED_4    = 4'h4,  // Reserved
        APB_THRESH_RESERVED_5    = 4'h5,  // Reserved
        APB_THRESH_RESERVED_6    = 4'h6,  // Reserved
        APB_THRESH_RESERVED_7    = 4'h7,  // Reserved
        APB_THRESH_RESERVED_8    = 4'h8,  // Reserved
        APB_THRESH_RESERVED_9    = 4'h9,  // Reserved
        APB_THRESH_RESERVED_A    = 4'hA,  // Reserved
        APB_THRESH_RESERVED_B    = 4'hB,  // Reserved
        APB_THRESH_RESERVED_C    = 4'hC,  // Reserved
        APB_THRESH_RESERVED_D    = 4'hD,  // Reserved
        APB_THRESH_RESERVED_E    = 4'hE,  // Reserved
        APB_THRESH_USER_DEFINED  = 4'hF   // User-defined threshold
    } apb_threshold_code_t;

    // APB Performance Events (packet_type = PktTypePerf, protocol = PROTOCOL_APB)
    typedef enum logic [3:0] {
        APB_PERF_SETUP_LATENCY   = 4'h0,  // Setup phase latency
        APB_PERF_ACCESS_LATENCY  = 4'h1,  // Access phase latency
        APB_PERF_ENABLE_LATENCY  = 4'h2,  // Enable phase latency
        APB_PERF_TOTAL_LATENCY   = 4'h3,  // Total transaction latency
        APB_PERF_THROUGHPUT      = 4'h4,  // Transaction throughput
        APB_PERF_ERROR_RATE      = 4'h5,  // Error rate
        APB_PERF_ACTIVE_COUNT    = 4'h6,  // Active transaction count
        APB_PERF_COMPLETED_COUNT = 4'h7,  // Completed transaction count
        APB_PERF_BANDWIDTH_UTIL  = 4'h8,  // Bandwidth utilization
        APB_PERF_RESERVED_9      = 4'h9,  // Reserved
        APB_PERF_RESERVED_A      = 4'hA,  // Reserved
        APB_PERF_RESERVED_B      = 4'hB,  // Reserved
        APB_PERF_RESERVED_C      = 4'hC,  // Reserved
        APB_PERF_RESERVED_D      = 4'hD,  // Reserved
        APB_PERF_RESERVED_E      = 4'hE,  // Reserved
        APB_PERF_USER_DEFINED    = 4'hF   // User-defined performance
    } apb_performance_code_t;

    // APB Debug Events (packet_type = PktTypeDebug, protocol = PROTOCOL_APB)
    typedef enum logic [3:0] {
        APB_DEBUG_STATE_CHANGE   = 4'h0,  // APB state changed
        APB_DEBUG_SETUP_PHASE    = 4'h1,  // Setup phase event
        APB_DEBUG_ACCESS_PHASE   = 4'h2,  // Access phase event
        APB_DEBUG_ENABLE_PHASE   = 4'h3,  // Enable phase event
        APB_DEBUG_PSEL_TRACE     = 4'h4,  // PSEL trace
        APB_DEBUG_PENABLE_TRACE  = 4'h5,  // PENABLE trace
        APB_DEBUG_PREADY_TRACE   = 4'h6,  // PREADY trace
        APB_DEBUG_PPROT_TRACE    = 4'h7,  // PPROT trace
        APB_DEBUG_PSTRB_TRACE    = 4'h8,  // PSTRB trace
        APB_DEBUG_RESERVED_9     = 4'h9,  // Reserved
        APB_DEBUG_RESERVED_A     = 4'hA,  // Reserved
        APB_DEBUG_RESERVED_B     = 4'hB,  // Reserved
        APB_DEBUG_RESERVED_C     = 4'hC,  // Reserved
        APB_DEBUG_RESERVED_D     = 4'hD,  // Reserved
        APB_DEBUG_RESERVED_E     = 4'hE,  // Reserved
        APB_DEBUG_USER_DEFINED   = 4'hF   // User-defined debug
    } apb_debug_code_t;

    // =============================================================================
    // NOC PROTOCOL EVENT CODES (organized by packet type)
    // =============================================================================

    // NOC Error Events (packet_type = PktTypeError, protocol = PROTOCOL_NOC)
    typedef enum logic [3:0] {
        NOC_ERR_PARITY          = 4'h0,  // Parity error (Header/Payload/ACK)
        NOC_ERR_PROTOCOL        = 4'h1,  // Protocol violation
        NOC_ERR_OVERFLOW        = 4'h2,  // Buffer/Credit overflow
        NOC_ERR_UNDERFLOW       = 4'h3,  // Buffer/Credit underflow
        NOC_ERR_ORPHAN          = 4'h4,  // Orphaned packet/ACK
        NOC_ERR_INVALID         = 4'h5,  // Invalid type/channel/payload
        NOC_ERR_HEADER_CRC      = 4'h6,  // Header CRC error
        NOC_ERR_PAYLOAD_CRC     = 4'h7,  // Payload CRC error
        NOC_ERR_SEQUENCE        = 4'h8,  // Sequence number error
        NOC_ERR_ROUTE           = 4'h9,  // Routing error
        NOC_ERR_DEADLOCK        = 4'hA,  // Deadlock detected
        NOC_ERR_RESERVED_B      = 4'hB,  // Reserved
        NOC_ERR_RESERVED_C      = 4'hC,  // Reserved
        NOC_ERR_RESERVED_D      = 4'hD,  // Reserved
        NOC_ERR_RESERVED_E      = 4'hE,  // Reserved
        NOC_ERR_USER_DEFINED    = 4'hF   // User-defined error
    } noc_error_code_t;

    // NOC Timeout Events (packet_type = PktTypeTimeout, protocol = PROTOCOL_NOC)
    typedef enum logic [3:0] {
        NOC_TIMEOUT_ACK          = 4'h0,  // ACK timeout
        NOC_TIMEOUT_CREDIT       = 4'h1,  // Credit timeout
        NOC_TIMEOUT_PACKET       = 4'h2,  // Packet timeout
        NOC_TIMEOUT_STALL        = 4'h3,  // Channel/Credit stall timeout
        NOC_TIMEOUT_ROUTE        = 4'h4,  // Routing timeout
        NOC_TIMEOUT_BUFFER       = 4'h5,  // Buffer drain timeout
        NOC_TIMEOUT_RESERVED_6   = 4'h6,  // Reserved
        NOC_TIMEOUT_RESERVED_7   = 4'h7,  // Reserved
        NOC_TIMEOUT_RESERVED_8   = 4'h8,  // Reserved
        NOC_TIMEOUT_RESERVED_9   = 4'h9,  // Reserved
        NOC_TIMEOUT_RESERVED_A   = 4'hA,  // Reserved
        NOC_TIMEOUT_RESERVED_B   = 4'hB,  // Reserved
        NOC_TIMEOUT_RESERVED_C   = 4'hC,  // Reserved
        NOC_TIMEOUT_RESERVED_D   = 4'hD,  // Reserved
        NOC_TIMEOUT_RESERVED_E   = 4'hE,  // Reserved
        NOC_TIMEOUT_USER_DEFINED = 4'hF   // User-defined timeout
    } noc_timeout_code_t;

    // NOC Completion Events (packet_type = PktTypeCompletion, protocol = PROTOCOL_NOC)
    typedef enum logic [3:0] {
        NOC_COMPL_PACKET_SENT   = 4'h0,  // Packet sent successfully
        NOC_COMPL_ACK_RECEIVED  = 4'h1,  // ACK received
        NOC_COMPL_STREAM_END    = 4'h2,  // Stream completed (EOS)
        NOC_COMPL_BURST_END     = 4'h3,  // Burst completed
        NOC_COMPL_ROUTE_FOUND   = 4'h4,  // Route established
        NOC_COMPL_RESERVED_5    = 4'h5,  // Reserved
        NOC_COMPL_RESERVED_6    = 4'h6,  // Reserved
        NOC_COMPL_RESERVED_7    = 4'h7,  // Reserved
        NOC_COMPL_RESERVED_8    = 4'h8,  // Reserved
        NOC_COMPL_RESERVED_9    = 4'h9,  // Reserved
        NOC_COMPL_RESERVED_A    = 4'hA,  // Reserved
        NOC_COMPL_RESERVED_B    = 4'hB,  // Reserved
        NOC_COMPL_RESERVED_C    = 4'hC,  // Reserved
        NOC_COMPL_RESERVED_D    = 4'hD,  // Reserved
        NOC_COMPL_RESERVED_E    = 4'hE,  // Reserved
        NOC_COMPL_USER_DEFINED  = 4'hF   // User-defined completion
    } noc_completion_code_t;

    // NOC Credit Events (packet_type = PktTypeCredit, protocol = PROTOCOL_NOC)
    typedef enum logic [3:0] {
        NOC_CREDIT_ALLOCATED    = 4'h0,  // Credits allocated
        NOC_CREDIT_CONSUMED     = 4'h1,  // Credits consumed
        NOC_CREDIT_RETURNED     = 4'h2,  // Credits returned
        NOC_CREDIT_OVERFLOW     = 4'h3,  // Credit overflow detected
        NOC_CREDIT_UNDERFLOW    = 4'h4,  // Credit underflow detected
        NOC_CREDIT_EXHAUSTED    = 4'h5,  // All credits exhausted
        NOC_CREDIT_RESTORED     = 4'h6,  // Credits restored
        NOC_CREDIT_EFFICIENCY   = 4'h7,  // Credit efficiency metric
        NOC_CREDIT_LEAK         = 4'h8,  // Credit leak detected
        NOC_CREDIT_RESERVED_9   = 4'h9,  // Reserved
        NOC_CREDIT_RESERVED_A   = 4'hA,  // Reserved
        NOC_CREDIT_RESERVED_B   = 4'hB,  // Reserved
        NOC_CREDIT_RESERVED_C   = 4'hC,  // Reserved
        NOC_CREDIT_RESERVED_D   = 4'hD,  // Reserved
        NOC_CREDIT_RESERVED_E   = 4'hE,  // Reserved
        NOC_CREDIT_USER_DEFINED = 4'hF   // User-defined credit event
    } noc_credit_code_t;

    // NOC Channel Events (packet_type = PktTypeChannel, protocol = PROTOCOL_NOC)
    typedef enum logic [3:0] {
        NOC_CHANNEL_ACTIVE       = 4'h0,  // Channel became active
        NOC_CHANNEL_IDLE         = 4'h1,  // Channel became idle
        NOC_CHANNEL_STALLED      = 4'h2,  // Channel stalled
        NOC_CHANNEL_RESET        = 4'h3,  // Channel reset
        NOC_CHANNEL_ERROR        = 4'h4,  // Channel error
        NOC_CHANNEL_OVERFLOW     = 4'h5,  // Channel buffer overflow
        NOC_CHANNEL_UNDERFLOW    = 4'h6,  // Channel buffer underflow
        NOC_CHANNEL_THRESHOLD    = 4'h7,  // Channel threshold crossed
        NOC_CHANNEL_CONGESTION   = 4'h8,  // Channel congestion detected
        NOC_CHANNEL_RESERVED_9   = 4'h9,  // Reserved
        NOC_CHANNEL_RESERVED_A   = 4'hA,  // Reserved
        NOC_CHANNEL_RESERVED_B   = 4'hB,  // Reserved
        NOC_CHANNEL_RESERVED_C   = 4'hC,  // Reserved
        NOC_CHANNEL_RESERVED_D   = 4'hD,  // Reserved
        NOC_CHANNEL_RESERVED_E   = 4'hE,  // Reserved
        NOC_CHANNEL_USER_DEFINED = 4'hF   // User-defined channel event
    } noc_channel_code_t;

    // NOC Stream Events (packet_type = PktTypeStream, protocol = PROTOCOL_NOC)
    typedef enum logic [3:0] {
        NOC_STREAM_START        = 4'h0,  // Stream started
        NOC_STREAM_END          = 4'h1,  // Stream ended (EOS)
        NOC_STREAM_ABORT        = 4'h2,  // Stream aborted
        NOC_STREAM_PAUSE        = 4'h3,  // Stream paused
        NOC_STREAM_RESUME       = 4'h4,  // Stream resumed
        NOC_STREAM_ERROR        = 4'h5,  // Stream error
        NOC_STREAM_OVERFLOW     = 4'h6,  // Stream buffer overflow
        NOC_STREAM_UNDERFLOW    = 4'h7,  // Stream buffer underflow
        NOC_STREAM_CONGESTION   = 4'h8,  // Stream congestion
        NOC_STREAM_RESERVED_9   = 4'h9,  // Reserved
        NOC_STREAM_RESERVED_A   = 4'hA,  // Reserved
        NOC_STREAM_RESERVED_B   = 4'hB,  // Reserved
        NOC_STREAM_RESERVED_C   = 4'hC,  // Reserved
        NOC_STREAM_RESERVED_D   = 4'hD,  // Reserved
        NOC_STREAM_RESERVED_E   = 4'hE,  // Reserved
        NOC_STREAM_USER_DEFINED = 4'hF   // User-defined stream event
    } noc_stream_code_t;

    // NOC Threshold Events (packet_type = PktTypeThreshold, protocol = PROTOCOL_NOC)
    typedef enum logic [3:0] {
        NOC_THRESH_CREDIT_LOW    = 4'h0,  // Credit low threshold
        NOC_THRESH_PACKET_RATE   = 4'h1,  // Packet rate threshold
        NOC_THRESH_CHANNEL_STALL = 4'h2,  // Channel stall threshold
        NOC_THRESH_BUFFER_LEVEL  = 4'h3,  // Buffer level threshold
        NOC_THRESH_LATENCY       = 4'h4,  // Latency threshold
        NOC_THRESH_BANDWIDTH     = 4'h5,  // Bandwidth threshold
        NOC_THRESH_CONGESTION    = 4'h6,  // Congestion threshold
        NOC_THRESH_RESERVED_7    = 4'h7,  // Reserved
        NOC_THRESH_RESERVED_8    = 4'h8,  // Reserved
        NOC_THRESH_RESERVED_9    = 4'h9,  // Reserved
        NOC_THRESH_RESERVED_A    = 4'hA,  // Reserved
        NOC_THRESH_RESERVED_B    = 4'hB,  // Reserved
        NOC_THRESH_RESERVED_C    = 4'hC,  // Reserved
        NOC_THRESH_RESERVED_D    = 4'hD,  // Reserved
        NOC_THRESH_RESERVED_E    = 4'hE,  // Reserved
        NOC_THRESH_USER_DEFINED  = 4'hF   // User-defined threshold
    } noc_threshold_code_t;

    // NOC Performance Events (packet_type = PktTypePerf, protocol = PROTOCOL_NOC)
    typedef enum logic [3:0] {
        NOC_PERF_PACKET_LATENCY    = 4'h0,  // Packet latency
        NOC_PERF_ROUTE_LATENCY     = 4'h1,  // Routing latency
        NOC_PERF_ACK_LATENCY       = 4'h2,  // ACK latency
        NOC_PERF_THROUGHPUT        = 4'h3,  // Throughput
        NOC_PERF_BANDWIDTH_UTIL    = 4'h4,  // Bandwidth utilization
        NOC_PERF_CREDIT_EFFICIENCY = 4'h5,  // Credit efficiency
        NOC_PERF_CHANNEL_UTIL      = 4'h6,  // Channel utilization
        NOC_PERF_PACKET_RATE       = 4'h7,  // Packet rate
        NOC_PERF_ERROR_RATE        = 4'h8,  // Error rate
        NOC_PERF_CONGESTION_INDEX  = 4'h9,  // Congestion index
        NOC_PERF_RESERVED_A        = 4'hA,  // Reserved
        NOC_PERF_RESERVED_B        = 4'hB,  // Reserved
        NOC_PERF_RESERVED_C        = 4'hC,  // Reserved
        NOC_PERF_RESERVED_D        = 4'hD,  // Reserved
        NOC_PERF_RESERVED_E        = 4'hE,  // Reserved
        NOC_PERF_USER_DEFINED      = 4'hF   // User-defined performance
    } noc_performance_code_t;

    // NOC Debug Events (packet_type = PktTypeDebug, protocol = PROTOCOL_NOC)
    typedef enum logic [3:0] {
        NOC_DEBUG_PACKET_TRACE   = 4'h0,  // Packet trace
        NOC_DEBUG_ACK_TRACE      = 4'h1,  // ACK trace
        NOC_DEBUG_CREDIT_CHANGE  = 4'h2,  // Credit change
        NOC_DEBUG_ROUTE_CHANGE   = 4'h3,  // Route change
        NOC_DEBUG_BUFFER_STATUS  = 4'h4,  // Buffer status
        NOC_DEBUG_CHANNEL_STATUS = 4'h5,  // Channel status
        NOC_DEBUG_ARBITER_STATE  = 4'h6,  // Arbiter state
        NOC_DEBUG_FLOW_CONTROL   = 4'h7,  // Flow control event
        NOC_DEBUG_RESERVED_8     = 4'h8,  // Reserved
        NOC_DEBUG_RESERVED_9     = 4'h9,  // Reserved
        NOC_DEBUG_RESERVED_A     = 4'hA,  // Reserved
        NOC_DEBUG_RESERVED_B     = 4'hB,  // Reserved
        NOC_DEBUG_RESERVED_C     = 4'hC,  // Reserved
        NOC_DEBUG_RESERVED_D     = 4'hD,  // Reserved
        NOC_DEBUG_RESERVED_E     = 4'hE,  // Reserved
        NOC_DEBUG_USER_DEFINED   = 4'hF   // User-defined debug
    } noc_debug_code_t;

    // =============================================================================
    // UNIFIED EVENT CODE TYPE (for backward compatibility)
    // =============================================================================

    // Unified event code type that can handle all protocols and packet types
    typedef union packed {
        // AXI event codes by packet type
        axi_error_code_t        axi_error;
        axi_timeout_code_t      axi_timeout;
        axi_completion_code_t   axi_completion;
        axi_threshold_code_t    axi_threshold;
        axi_performance_code_t  axi_performance;
        axi_addr_match_code_t   axi_addr_match;
        axi_debug_code_t        axi_debug;

        // APB event codes by packet type
        apb_error_code_t        apb_error;
        apb_timeout_code_t      apb_timeout;
        apb_completion_code_t   apb_completion;
        apb_threshold_code_t    apb_threshold;
        apb_performance_code_t  apb_performance;
        apb_debug_code_t        apb_debug;

        // NOC event codes by packet type
        noc_error_code_t       noc_error;
        noc_timeout_code_t     noc_timeout;
        noc_completion_code_t  noc_completion;
        noc_credit_code_t      noc_credit;
        noc_channel_code_t     noc_channel;
        noc_stream_code_t      noc_stream;
        noc_threshold_code_t   noc_threshold;
        noc_performance_code_t noc_performance;
        noc_debug_code_t       noc_debug;

        // Raw access
        logic [3:0]             raw_code;
    } unified_event_code_t;

    // =============================================================================
    // HELPER FUNCTIONS FOR EVENT CODE CREATION
    // =============================================================================

    // AXI event code creation functions
    function automatic unified_event_code_t create_axi_error_event(axi_error_code_t code);
        unified_event_code_t result;
        result.axi_error = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_axi_timeout_event(axi_timeout_code_t code);
        unified_event_code_t result;
        result.axi_timeout = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_axi_completion_event(axi_completion_code_t code);
        unified_event_code_t result;
        result.axi_completion = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_axi_threshold_event(axi_threshold_code_t code);
        unified_event_code_t result;
        result.axi_threshold = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_axi_performance_event(axi_performance_code_t code);
        unified_event_code_t result;
        result.axi_performance = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_axi_addr_match_event(axi_addr_match_code_t code);
        unified_event_code_t result;
        result.axi_addr_match = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_axi_debug_event(axi_debug_code_t code);
        unified_event_code_t result;
        result.axi_debug = code;
        return result;
    endfunction

    // APB event code creation functions
    function automatic unified_event_code_t create_apb_error_event(apb_error_code_t code);
        unified_event_code_t result;
        result.apb_error = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_apb_timeout_event(apb_timeout_code_t code);
        unified_event_code_t result;
        result.apb_timeout = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_apb_completion_event(apb_completion_code_t code);
        unified_event_code_t result;
        result.apb_completion = code;
        return result;
    endfunction

    // noc event code creation functions
    function automatic unified_event_code_t create_noc_error_event(noc_error_code_t code);
        unified_event_code_t result;
        result.noc_error = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_noc_timeout_event(noc_timeout_code_t code);
        unified_event_code_t result;
        result.noc_timeout = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_noc_completion_event(noc_completion_code_t code);
        unified_event_code_t result;
        result.noc_completion = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_noc_credit_event(noc_credit_code_t code);
        unified_event_code_t result;
        result.noc_credit = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_noc_channel_event(noc_channel_code_t code);
        unified_event_code_t result;
        result.noc_channel = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_noc_stream_event(noc_stream_code_t code);
        unified_event_code_t result;
        result.noc_stream = code;
        return result;
    endfunction

    // =============================================================================
    // PROTOCOL-SPECIFIC PAYLOAD AND ACK TYPES
    // =============================================================================

    // NOC payload types (from adaptation guide)
    typedef enum logic [1:0] {
        NOC_PAYLOAD_CONFIG = 2'b00,  // CONFIG_PKT
        NOC_PAYLOAD_TS     = 2'b01,  // TS_PKT
        NOC_PAYLOAD_RDA    = 2'b10,  // RDA_PKT
        NOC_PAYLOAD_RAW    = 2'b11   // RAW_PKT
    } noc_payload_type_t;

    // NOC ACK types (from adaptation guide)
    typedef enum logic [1:0] {
        NOC_ACK_STOP        = 2'b00,  // MSAP_STOP
        NOC_ACK_START       = 2'b01,  // MSAP_START
        NOC_ACK_CREDIT_ON   = 2'b10,  // MSAP_CREDIT_ON
        NOC_ACK_STOP_AT_EOS = 2'b11   // MSAP_STOP_AT_EOS
    } noc_ack_type_t;

    // APB transaction phases for state tracking
    typedef enum logic [1:0] {
        APB_PHASE_IDLE    = 2'b00,  // Bus idle
        APB_PHASE_SETUP   = 2'b01,  // Setup phase (PSEL asserted)
        APB_PHASE_ACCESS  = 2'b10,  // Access phase (PENABLE asserted)
        APB_PHASE_ENABLE  = 2'b11   // Enable phase (waiting for PREADY)
    } apb_phase_t;

    // APB protection types (PPROT encoding)
    typedef enum logic [2:0] {
        APB_PROT_NORMAL      = 3'b000,  // Normal access
        APB_PROT_PRIVILEGED  = 3'b001,  // Privileged access
        APB_PROT_SECURE      = 3'b010,  // Secure access
        APB_PROT_INSTRUCTION = 3'b100   // Instruction access
    } apb_prot_t;

    // =============================================================================
    // TRANSACTION STATE AND BUS TRANSACTION STRUCTURE
    // =============================================================================

    // Transaction state enumeration (enhanced for multiple protocols)
    typedef enum logic [2:0] {
        TRANS_EMPTY          = 3'b000,  // Unused entry
        TRANS_ADDR_PHASE     = 3'b001,  // Address phase active (AXI) / Packet sent (NOC) / Setup phase (APB)
        TRANS_DATA_PHASE     = 3'b010,  // Data phase active (AXI) / Waiting for ACK (NOC) / Access phase (APB)
        TRANS_RESP_PHASE     = 3'b011,  // Response phase active (AXI) / ACK received (NOC) / Enable phase (APB)
        TRANS_COMPLETE       = 3'b100,  // Transaction complete
        TRANS_ERROR          = 3'b101,  // Transaction has error
        TRANS_ORPHANED       = 3'b110,  // Orphaned transaction
        TRANS_CREDIT_STALL   = 3'b111   // Credit stall (NOC only)
    } trans_state_t;

    // Enhanced transaction entry structure supporting AXI, NOC, and APB
    typedef struct packed {
        logic                   valid;           // Entry is valid
        protocol_type_t         protocol;        // Protocol type (AXI/NOC/APB)
        trans_state_t           state;           // Transaction state
        logic [31:0]            id;              // Transaction ID (AXI) / Sequence (NOC) / PSEL encoding (APB)
        logic [63:0]            addr;            // Transaction address / Channel addr / PADDR
        logic [7:0]             len;             // Burst length (AXI) / Packet count (NOC) / Always 0 (APB)
        logic [2:0]             size;            // Access size (AXI) / Reserved (NOC) / Transfer size (APB)
        logic [1:0]             burst;           // Burst type (AXI) / Payload type (NOC) / PPROT[1:0] (APB)

        // Phase completion flags
        logic                   cmd_received;    // Address phase received / Packet sent / Setup phase (APB)
        logic                   data_started;    // Data phase started / ACK expected / Access phase (APB)
        logic                   data_completed;  // Data phase completed / ACK received / Enable phase (APB)
        logic                   resp_received;   // Response received / Final ACK / PREADY asserted (APB)

        // Error detection and reporting
        unified_event_code_t    event_code;      // Error code if any
        logic                   event_reported;  // Error or event has been reported

        // Timeout counters
        logic [15:0]            addr_timer;      // Address phase timer / Packet timer / Setup timer (APB)
        logic [15:0]            data_timer;      // Data phase timer / ACK timer / Access timer (APB)
        logic [15:0]            resp_timer;      // Response phase timer / Credit timer / PREADY timer (APB)

        // Timestamps for performance monitoring
        logic [31:0]            addr_timestamp;  // When address/packet/setup phase completed
        logic [31:0]            data_timestamp;  // When data/ack/access phase completed
        logic [31:0]            resp_timestamp;  // When response/final/enable phase completed

        // Beat counters
        logic [7:0]             data_beat_count; // Data beats received / Packets sent / Always 1 (APB)
        logic [7:0]             expected_beats;  // Expected beats / Expected packets / Always 1 (APB)

        // Enhanced tracking for NOC and address matching
        logic [5:0]             channel;         // Channel ID (AXI ID / NOC channel / PSEL bit position)
        logic                   eos_seen;        // EOS marker seen (NOC only)
        logic                   parity_error;    // Parity error detected (NOC only)
        logic [7:0]             credit_at_start; // Credits available at start (NOC only)
        logic [2:0]             retry_count;     // Number of retries (NOC only)

        // Address matching support (AXI)
        logic                   desc_addr_match; // Descriptor address match detected
        logic                   data_addr_match; // Data address match detected

        // APB-specific tracking
        apb_phase_t             apb_phase;       // Current APB phase (APB only)
        logic                   pslverr_seen;    // PSLVERR detected (APB only)
        logic [2:0]             pprot_value;     // PPROT value (APB only)
        logic [3:0]             pstrb_value;     // PSTRB value for writes (APB only)
    } bus_transaction_t;

    // =============================================================================
    // MONITOR BUS PACKET FORMAT AND HELPER FUNCTIONS
    // =============================================================================

    // 64-bit monitor bus packet supporting all protocols
    // Fields are packed according to specified sizes:
    // - packet_type: 4 bits  [63:60] (error, completion, threshold, etc.)
    // - protocol:    2 bits  [59:58] (AXI/NOC/APB/Custom)
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

    // Protocol and event validation functions
    function automatic bit is_valid_event_for_packet_type(
        logic [3:0] packet_type,
        protocol_type_t protocol,
        logic [3:0] event_code
    );
        // This function validates that an event code is appropriate
        // for the given packet type and protocol combination
        // Since all enum values use the full 4-bit range (0x0 to 0xF),
        // all event codes are valid within each category
        case (protocol)
            PROTOCOL_AXI: begin
                case (packet_type)
                    PktTypeError     : return 1'b1; // All 4-bit values valid for AXI errors
                    PktTypeTimeout   : return 1'b1; // All 4-bit values valid for AXI timeouts
                    PktTypeCompletion: return 1'b1; // All 4-bit values valid for AXI completions
                    PktTypeThreshold : return 1'b1; // All 4-bit values valid for AXI thresholds
                    PktTypePerf      : return 1'b1; // All 4-bit values valid for AXI performance
                    PktTypeAddrMatch : return 1'b1; // All 4-bit values valid for AXI address match
                    PktTypeDebug     : return 1'b1; // All 4-bit values valid for AXI debug
                    default          : return 1'b0; // Invalid packet type for AXI
                endcase
            end
            PROTOCOL_APB: begin
                case (packet_type)
                    PktTypeError     : return 1'b1; // All 4-bit values valid for APB errors
                    PktTypeTimeout   : return 1'b1; // All 4-bit values valid for APB timeouts
                    PktTypeCompletion: return 1'b1; // All 4-bit values valid for APB completions
                    PktTypeThreshold : return 1'b1; // All 4-bit values valid for APB thresholds
                    PktTypePerf      : return 1'b1; // All 4-bit values valid for APB performance
                    PktTypeDebug     : return 1'b1; // All 4-bit values valid for APB debug
                    default          : return 1'b0; // Invalid packet type for APB
                endcase
            end
            PROTOCOL_NOC: begin
                case (packet_type)
                    PktTypeError     : return 1'b1; // All 4-bit values valid for NOC errors
                    PktTypeTimeout   : return 1'b1; // All 4-bit values valid for NOC timeouts
                    PktTypeCompletion: return 1'b1; // All 4-bit values valid for NOC completions
                    PktTypeCredit    : return 1'b1; // All 4-bit values valid for NOC credits
                    PktTypeChannel   : return 1'b1; // All 4-bit values valid for NOC channels
                    PktTypeStream    : return 1'b1; // All 4-bit values valid for NOC streams
                    PktTypeThreshold : return 1'b1; // All 4-bit values valid for NOC thresholds
                    PktTypePerf      : return 1'b1; // All 4-bit values valid for NOC performance
                    PktTypeDebug     : return 1'b1; // All 4-bit values valid for NOC debug
                    default          : return 1'b0; // Invalid packet type for NOC
                endcase
            end
            default: return 1'b1; // Custom protocols can use any event codes
        endcase
    endfunction

    // Human-readable string functions for debugging
    function automatic string get_axi_error_name(axi_error_code_t code);
        case (code)
            AXI_ERR_RESP_SLVERR        : return "RESP_SLVERR";
            AXI_ERR_RESP_DECERR        : return "RESP_DECERR";
            AXI_ERR_DATA_ORPHAN        : return "DATA_ORPHAN";
            AXI_ERR_RESP_ORPHAN        : return "RESP_ORPHAN";
            AXI_ERR_PROTOCOL           : return "PROTOCOL";
            AXI_ERR_BURST_LENGTH       : return "BURST_LENGTH";
            AXI_ERR_BURST_SIZE         : return "BURST_SIZE";
            AXI_ERR_BURST_TYPE         : return "BURST_TYPE";
            AXI_ERR_ID_COLLISION       : return "ID_COLLISION";
            AXI_ERR_WRITE_BEFORE_ADDR  : return "WRITE_BEFORE_ADDR";
            AXI_ERR_RESP_BEFORE_DATA   : return "RESP_BEFORE_DATA";
            AXI_ERR_LAST_MISSING       : return "LAST_MISSING";
            AXI_ERR_STROBE_ERROR       : return "STROBE_ERROR";
            AXI_ERR_ARBITER_STARVATION : return "ARBITER_STARVATION";
            AXI_ERR_CREDIT_VIOLATION   : return "CREDIT_VIOLATION";
            AXI_ERR_USER_DEFINED       : return "USER_DEFINED";
            default                    : return "UNKNOWN_AXI_ERROR";
        endcase
    endfunction

    function automatic string get_packet_type_name(logic [3:0] pkt_type);
        case (pkt_type)
            PktTypeError     : return "ERROR";
            PktTypeCompletion: return "COMPLETION";
            PktTypeThreshold : return "THRESHOLD";
            PktTypeTimeout   : return "TIMEOUT";
            PktTypePerf      : return "PERF";
            PktTypeCredit    : return "CREDIT";
            PktTypeChannel   : return "CHANNEL";
            PktTypeStream    : return "STREAM";
            PktTypeAddrMatch : return "ADDR_MATCH";
            PktTypeAPB       : return "APB";
            PktTypeDebug     : return "DEBUG";
            default          : return "UNKNOWN";
        endcase
    endfunction

    function automatic string get_protocol_name(protocol_type_t protocol);
        case (protocol)
            PROTOCOL_AXI   : return "AXI";
            PROTOCOL_NOC   : return "NOC";
            PROTOCOL_APB   : return "APB";
            PROTOCOL_CUSTOM: return "CUSTOM";
            default        : return "UNKNOWN";
        endcase
    endfunction

    // Comprehensive event name function that handles all protocols and packet types
    function automatic string get_event_name(
        logic [3:0] packet_type,
        protocol_type_t protocol,
        logic [3:0] event_code
    );
        string base_name;

        case (protocol)
            PROTOCOL_AXI: begin
                case (packet_type)
                    PktTypeError: begin
                        case (axi_error_code_t'(event_code))
                            AXI_ERR_RESP_SLVERR        : base_name = "RESP_SLVERR";
                            AXI_ERR_RESP_DECERR        : base_name = "RESP_DECERR";
                            AXI_ERR_DATA_ORPHAN        : base_name = "DATA_ORPHAN";
                            AXI_ERR_RESP_ORPHAN        : base_name = "RESP_ORPHAN";
                            AXI_ERR_PROTOCOL           : base_name = "PROTOCOL";
                            AXI_ERR_BURST_LENGTH       : base_name = "BURST_LENGTH";
                            AXI_ERR_BURST_SIZE         : base_name = "BURST_SIZE";
                            AXI_ERR_BURST_TYPE         : base_name = "BURST_TYPE";
                            AXI_ERR_ID_COLLISION       : base_name = "ID_COLLISION";
                            AXI_ERR_WRITE_BEFORE_ADDR  : base_name = "WRITE_BEFORE_ADDR";
                            AXI_ERR_RESP_BEFORE_DATA   : base_name = "RESP_BEFORE_DATA";
                            AXI_ERR_LAST_MISSING       : base_name = "LAST_MISSING";
                            AXI_ERR_STROBE_ERROR       : base_name = "STROBE_ERROR";
                            AXI_ERR_ARBITER_STARVATION : base_name = "ARBITER_STARVATION";
                            AXI_ERR_CREDIT_VIOLATION   : base_name = "CREDIT_VIOLATION";
                            AXI_ERR_USER_DEFINED       : base_name = "USER_DEFINED";
                            default                    : base_name = $sformatf("UNKNOWN_ERR_%0X", event_code);
                        endcase
                    end
                    PktTypeTimeout                     : begin
                        case (axi_timeout_code_t'(event_code))
                            AXI_TIMEOUT_CMD            : base_name = "CMD";
                            AXI_TIMEOUT_DATA           : base_name = "DATA";
                            AXI_TIMEOUT_RESP           : base_name = "RESP";
                            AXI_TIMEOUT_HANDSHAKE      : base_name = "HANDSHAKE";
                            AXI_TIMEOUT_BURST          : base_name = "BURST";
                            AXI_TIMEOUT_EXCLUSIVE      : base_name = "EXCLUSIVE";
                            AXI_TIMEOUT_USER_DEFINED   : base_name = "USER_DEFINED";
                            default                    : base_name = $sformatf("UNKNOWN_TIMEOUT_%0X", event_code);
                        endcase
                    end
                    PktTypeCompletion                  : begin
                        case (axi_completion_code_t'(event_code))
                            AXI_COMPL_TRANS_COMPLETE   : base_name = "TRANS_COMPLETE";
                            AXI_COMPL_READ_COMPLETE    : base_name = "READ_COMPLETE";
                            AXI_COMPL_WRITE_COMPLETE   : base_name = "WRITE_COMPLETE";
                            AXI_COMPL_BURST_COMPLETE   : base_name = "BURST_COMPLETE";
                            AXI_COMPL_EXCLUSIVE_OK     : base_name = "EXCLUSIVE_OK";
                            AXI_COMPL_EXCLUSIVE_FAIL   : base_name = "EXCLUSIVE_FAIL";
                            AXI_COMPL_ATOMIC_OK        : base_name = "ATOMIC_OK";
                            AXI_COMPL_ATOMIC_FAIL      : base_name = "ATOMIC_FAIL";
                            AXI_COMPL_USER_DEFINED     : base_name = "USER_DEFINED";
                            default                    : base_name = $sformatf("UNKNOWN_COMPL_%0X", event_code);
                        endcase
                    end
                    PktTypeThreshold                   : begin
                        case (axi_threshold_code_t'(event_code))
                            AXI_THRESH_ACTIVE_COUNT    : base_name = "ACTIVE_COUNT";
                            AXI_THRESH_LATENCY         : base_name = "LATENCY";
                            AXI_THRESH_ERROR_RATE      : base_name = "ERROR_RATE";
                            AXI_THRESH_THROUGHPUT      : base_name = "THROUGHPUT";
                            AXI_THRESH_QUEUE_DEPTH     : base_name = "QUEUE_DEPTH";
                            AXI_THRESH_BANDWIDTH       : base_name = "BANDWIDTH";
                            AXI_THRESH_OUTSTANDING     : base_name = "OUTSTANDING";
                            AXI_THRESH_BURST_SIZE      : base_name = "BURST_SIZE";
                            AXI_THRESH_GRANT_LATENCY   : base_name = "GRANT_LATENCY";
                            AXI_THRESH_FAIRNESS        : base_name = "FAIRNESS";
                            AXI_THRESH_USER_DEFINED    : base_name = "USER_DEFINED";
                            default                    : base_name = $sformatf("UNKNOWN_THRESH_%0X", event_code);
                        endcase
                    end
                    PktTypePerf                        : begin
                        case (axi_performance_code_t'(event_code))
                            AXI_PERF_ADDR_LATENCY      : base_name = "ADDR_LATENCY";
                            AXI_PERF_DATA_LATENCY      : base_name = "DATA_LATENCY";
                            AXI_PERF_RESP_LATENCY      : base_name = "RESP_LATENCY";
                            AXI_PERF_TOTAL_LATENCY     : base_name = "TOTAL_LATENCY";
                            AXI_PERF_THROUGHPUT        : base_name = "THROUGHPUT";
                            AXI_PERF_ERROR_RATE        : base_name = "ERROR_RATE";
                            AXI_PERF_ACTIVE_COUNT      : base_name = "ACTIVE_COUNT";
                            AXI_PERF_COMPLETED_COUNT   : base_name = "COMPLETED_COUNT";
                            AXI_PERF_ERROR_COUNT       : base_name = "ERROR_COUNT";
                            AXI_PERF_BANDWIDTH_UTIL    : base_name = "BANDWIDTH_UTIL";
                            AXI_PERF_QUEUE_DEPTH       : base_name = "QUEUE_DEPTH";
                            AXI_PERF_BURST_EFFICIENCY  : base_name = "BURST_EFFICIENCY";
                            AXI_PERF_GRANT_EFFICIENCY  : base_name = "GRANT_EFFICIENCY";
                            AXI_PERF_WEIGHT_COMPLIANCE : base_name = "WEIGHT_COMPLIANCE";
                            AXI_PERF_READ_WRITE_RATIO  : base_name = "READ_WRITE_RATIO";
                            AXI_PERF_USER_DEFINED      : base_name = "USER_DEFINED";
                            default                    : base_name = $sformatf("UNKNOWN_PERF_%0X", event_code);
                        endcase
                    end
                    PktTypeAddrMatch                   : begin
                        case (axi_addr_match_code_t'(event_code))
                            AXI_ADDR_MATCH_DESC        : base_name = "DESC";
                            AXI_ADDR_MATCH_DATA        : base_name = "DATA";
                            AXI_ADDR_MATCH_READ        : base_name = "READ";
                            AXI_ADDR_MATCH_WRITE       : base_name = "WRITE";
                            AXI_ADDR_MATCH_RANGE       : base_name = "RANGE";
                            AXI_ADDR_MATCH_EXACT       : base_name = "EXACT";
                            AXI_ADDR_MATCH_MASK        : base_name = "MASK";
                            AXI_ADDR_MATCH_BURST       : base_name = "BURST";
                            AXI_ADDR_MATCH_CACHEABLE   : base_name = "CACHEABLE";
                            AXI_ADDR_MATCH_DEVICE      : base_name = "DEVICE";
                            AXI_ADDR_MATCH_SECURE      : base_name = "SECURE";
                            AXI_ADDR_MATCH_USER_DEFINED: base_name = "USER_DEFINED";
                            default                    : base_name = $sformatf("UNKNOWN_ADDR_MATCH_%0X", event_code);
                        endcase
                    end
                    PktTypeDebug                       : begin
                        case (axi_debug_code_t'(event_code))
                            AXI_DEBUG_STATE_CHANGE     : base_name = "STATE_CHANGE";
                            AXI_DEBUG_ADDR_PHASE       : base_name = "ADDR_PHASE";
                            AXI_DEBUG_DATA_PHASE       : base_name = "DATA_PHASE";
                            AXI_DEBUG_RESP_PHASE       : base_name = "RESP_PHASE";
                            AXI_DEBUG_TRANS_CREATE     : base_name = "TRANS_CREATE";
                            AXI_DEBUG_TRANS_REMOVE     : base_name = "TRANS_REMOVE";
                            AXI_DEBUG_ID_ALLOCATION    : base_name = "ID_ALLOCATION";
                            AXI_DEBUG_HANDSHAKE        : base_name = "HANDSHAKE";
                            AXI_DEBUG_QUEUE_STATUS     : base_name = "QUEUE_STATUS";
                            AXI_DEBUG_COUNTER          : base_name = "COUNTER";
                            AXI_DEBUG_FIFO_STATUS      : base_name = "FIFO_STATUS";
                            AXI_DEBUG_CREDIT_STATUS    : base_name = "CREDIT_STATUS";
                            AXI_DEBUG_ARBITER_STATE    : base_name = "ARBITER_STATE";
                            AXI_DEBUG_BLOCK_EVENT      : base_name = "BLOCK_EVENT";
                            AXI_DEBUG_USER_DEFINED     : base_name = "USER_DEFINED";
                            default                    : base_name = $sformatf("UNKNOWN_DEBUG_%0X", event_code);
                        endcase
                    end
                    default                            : base_name = $sformatf("UNKNOWN_PKT_TYPE_%0X_EVENT_%0X", packet_type, event_code);
                endcase
            end

            PROTOCOL_APB                               : begin
                case (packet_type)
                    PktTypeError                       : begin
                        case (apb_error_code_t'(event_code))
                            APB_ERR_PSLVERR            : base_name = "PSLVERR";
                            APB_ERR_SETUP_VIOLATION    : base_name = "SETUP_VIOLATION";
                            APB_ERR_ACCESS_VIOLATION   : base_name = "ACCESS_VIOLATION";
                            APB_ERR_STROBE_ERROR       : base_name = "STROBE_ERROR";
                            APB_ERR_ADDR_DECODE        : base_name = "ADDR_DECODE";
                            APB_ERR_PROT_VIOLATION     : base_name = "PROT_VIOLATION";
                            APB_ERR_ENABLE_ERROR       : base_name = "ENABLE_ERROR";
                            APB_ERR_READY_ERROR        : base_name = "READY_ERROR";
                            APB_ERR_USER_DEFINED       : base_name = "USER_DEFINED";
                            default                    : base_name = $sformatf("UNKNOWN_APB_ERR_%0X", event_code);
                        endcase
                    end
                    PktTypeTimeout                     : begin
                        case (apb_timeout_code_t'(event_code))
                            APB_TIMEOUT_SETUP          : base_name = "SETUP";
                            APB_TIMEOUT_ACCESS         : base_name = "ACCESS";
                            APB_TIMEOUT_ENABLE         : base_name = "ENABLE";
                            APB_TIMEOUT_PREADY_STUCK   : base_name = "PREADY_STUCK";
                            APB_TIMEOUT_TRANSFER       : base_name = "TRANSFER";
                            APB_TIMEOUT_USER_DEFINED   : base_name = "USER_DEFINED";
                            default                    : base_name = $sformatf("UNKNOWN_APB_TIMEOUT_%0X", event_code);
                        endcase
                    end
                    // Add other APB packet types as needed...
                    default                            : base_name = $sformatf("APB_PKT_%0X_EVENT_%0X", packet_type, event_code);
                endcase
            end

            PROTOCOL_NOC                               : begin
                case (packet_type)
                    PktTypeError                       : begin
                        case (noc_error_code_t'(event_code))
                            NOC_ERR_PARITY             : base_name = "PARITY";
                            NOC_ERR_PROTOCOL           : base_name = "PROTOCOL";
                            NOC_ERR_OVERFLOW           : base_name = "OVERFLOW";
                            NOC_ERR_UNDERFLOW          : base_name = "UNDERFLOW";
                            NOC_ERR_ORPHAN             : base_name = "ORPHAN";
                            NOC_ERR_INVALID            : base_name = "INVALID";
                            NOC_ERR_HEADER_CRC         : base_name = "HEADER_CRC";
                            NOC_ERR_PAYLOAD_CRC        : base_name = "PAYLOAD_CRC";
                            NOC_ERR_SEQUENCE           : base_name = "SEQUENCE";
                            NOC_ERR_ROUTE              : base_name = "ROUTE";
                            NOC_ERR_DEADLOCK           : base_name = "DEADLOCK";
                            NOC_ERR_USER_DEFINED       : base_name = "USER_DEFINED";
                            default                    : base_name = $sformatf("UNKNOWN_NOC_ERR_%0X", event_code);
                        endcase
                    end
                    PktTypeCredit                      : begin
                        case (noc_credit_code_t'(event_code))
                            NOC_CREDIT_ALLOCATED       : base_name = "ALLOCATED";
                            NOC_CREDIT_CONSUMED        : base_name = "CONSUMED";
                            NOC_CREDIT_RETURNED        : base_name = "RETURNED";
                            NOC_CREDIT_OVERFLOW        : base_name = "OVERFLOW";
                            NOC_CREDIT_UNDERFLOW       : base_name = "UNDERFLOW";
                            NOC_CREDIT_EXHAUSTED       : base_name = "EXHAUSTED";
                            NOC_CREDIT_RESTORED        : base_name = "RESTORED";
                            NOC_CREDIT_EFFICIENCY      : base_name = "EFFICIENCY";
                            NOC_CREDIT_LEAK            : base_name = "LEAK";
                            NOC_CREDIT_USER_DEFINED    : base_name = "USER_DEFINED";
                            default                    : base_name = $sformatf("UNKNOWN_NOC_CREDIT_%0X", event_code);
                        endcase
                    end
                    // Add other NOC packet types as needed...
                    default                            : base_name = $sformatf("NOC_PKT_%0X_EVENT_%0X", packet_type, event_code);
                endcase
            end

            default                                    : base_name = $sformatf("CUSTOM_PKT_%0X_EVENT_%0X", packet_type, event_code);
        endcase

        return base_name;
    endfunction

endpackage : monitor_pkg
