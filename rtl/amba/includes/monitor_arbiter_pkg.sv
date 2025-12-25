// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monitor_arbiter_pkg
// Purpose: Arbiter and Core protocol event codes
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-21

`timescale 1ns / 1ps
/**
 * Arbiter and Core Protocol Event Codes
 *
 * This package defines event codes for non-AMBA protocols:
 * - ARB (Arbiter) event codes for arbitration monitoring
 * - CORE event codes for internal accelerator/DMA engine monitoring
 */
package monitor_arbiter_pkg;

    import monitor_common_pkg::*;

    // =============================================================================
    // ARBITER PROTOCOL EVENT CODES
    // =============================================================================

    // ARB Error Events (packet_type = PktTypeError, protocol = PROTOCOL_ARB)
    typedef enum logic [3:0] {
        ARB_ERR_STARVATION         = 4'h0,  // Client request starvation
        ARB_ERR_ACK_TIMEOUT        = 4'h1,  // Grant ACK timeout
        ARB_ERR_PROTOCOL_VIOLATION = 4'h2,  // ACK protocol violation
        ARB_ERR_CREDIT_VIOLATION   = 4'h3,  // Credit system violation
        ARB_ERR_FAIRNESS_VIOLATION = 4'h4,  // Weighted fairness violation
        ARB_ERR_WEIGHT_UNDERFLOW   = 4'h5,  // Weight credit underflow
        ARB_ERR_CONCURRENT_GRANTS  = 4'h6,  // Multiple simultaneous grants
        ARB_ERR_INVALID_GRANT_ID   = 4'h7,  // Invalid grant ID detected
        ARB_ERR_ORPHAN_ACK         = 4'h8,  // ACK without pending grant
        ARB_ERR_GRANT_OVERLAP      = 4'h9,  // Overlapping grant periods
        ARB_ERR_MASK_ERROR         = 4'hA,  // Round-robin mask error
        ARB_ERR_STATE_MACHINE      = 4'hB,  // FSM state error
        ARB_ERR_CONFIGURATION      = 4'hC,  // Invalid configuration
        ARB_ERR_RESERVED_D         = 4'hD,  // Reserved
        ARB_ERR_RESERVED_E         = 4'hE,  // Reserved
        ARB_ERR_USER_DEFINED       = 4'hF   // User-defined error
    } arb_error_code_t;

    // ARB Timeout Events (packet_type = PktTypeTimeout, protocol = PROTOCOL_ARB)
    typedef enum logic [3:0] {
        ARB_TIMEOUT_GRANT_ACK     = 4'h0,  // Grant ACK timeout
        ARB_TIMEOUT_REQUEST_HOLD  = 4'h1,  // Request held too long
        ARB_TIMEOUT_WEIGHT_UPDATE = 4'h2,  // Weight update timeout
        ARB_TIMEOUT_BLOCK_RELEASE = 4'h3,  // Block release timeout
        ARB_TIMEOUT_CREDIT_UPDATE = 4'h4,  // Credit update timeout
        ARB_TIMEOUT_STATE_CHANGE  = 4'h5,  // State machine timeout
        ARB_TIMEOUT_RESERVED_6    = 4'h6,  // Reserved
        ARB_TIMEOUT_RESERVED_7    = 4'h7,  // Reserved
        ARB_TIMEOUT_RESERVED_8    = 4'h8,  // Reserved
        ARB_TIMEOUT_RESERVED_9    = 4'h9,  // Reserved
        ARB_TIMEOUT_RESERVED_A    = 4'hA,  // Reserved
        ARB_TIMEOUT_RESERVED_B    = 4'hB,  // Reserved
        ARB_TIMEOUT_RESERVED_C    = 4'hC,  // Reserved
        ARB_TIMEOUT_RESERVED_D    = 4'hD,  // Reserved
        ARB_TIMEOUT_RESERVED_E    = 4'hE,  // Reserved
        ARB_TIMEOUT_USER_DEFINED  = 4'hF   // User-defined timeout
    } arb_timeout_code_t;

    // ARB Completion Events (packet_type = PktTypeCompletion, protocol = PROTOCOL_ARB)
    typedef enum logic [3:0] {
        ARB_COMPL_GRANT_ISSUED    = 4'h0,  // Grant successfully issued
        ARB_COMPL_ACK_RECEIVED    = 4'h1,  // ACK successfully received
        ARB_COMPL_TRANSACTION     = 4'h2,  // Complete transaction (grant+ack)
        ARB_COMPL_WEIGHT_UPDATE   = 4'h3,  // Weight update completed
        ARB_COMPL_CREDIT_CYCLE    = 4'h4,  // Credit cycle completed
        ARB_COMPL_FAIRNESS_PERIOD = 4'h5,  // Fairness analysis period
        ARB_COMPL_BLOCK_PERIOD    = 4'h6,  // Block period completed
        ARB_COMPL_RESERVED_7      = 4'h7,  // Reserved
        ARB_COMPL_RESERVED_8      = 4'h8,  // Reserved
        ARB_COMPL_RESERVED_9      = 4'h9,  // Reserved
        ARB_COMPL_RESERVED_A      = 4'hA,  // Reserved
        ARB_COMPL_RESERVED_B      = 4'hB,  // Reserved
        ARB_COMPL_RESERVED_C      = 4'hC,  // Reserved
        ARB_COMPL_RESERVED_D      = 4'hD,  // Reserved
        ARB_COMPL_RESERVED_E      = 4'hE,  // Reserved
        ARB_COMPL_USER_DEFINED    = 4'hF   // User-defined completion
    } arb_completion_code_t;

    // ARB Threshold Events (packet_type = PktTypeThreshold, protocol = PROTOCOL_ARB)
    typedef enum logic [3:0] {
        ARB_THRESH_REQUEST_LATENCY  = 4'h0,  // Request-to-grant latency threshold
        ARB_THRESH_ACK_LATENCY      = 4'h1,  // Grant-to-ACK latency threshold
        ARB_THRESH_FAIRNESS_DEV     = 4'h2,  // Fairness deviation threshold
        ARB_THRESH_ACTIVE_REQUESTS  = 4'h3,  // Active request count threshold
        ARB_THRESH_GRANT_RATE       = 4'h4,  // Grant rate threshold
        ARB_THRESH_EFFICIENCY       = 4'h5,  // Grant efficiency threshold
        ARB_THRESH_CREDIT_LOW       = 4'h6,  // Low credit threshold
        ARB_THRESH_WEIGHT_IMBALANCE = 4'h7,  // Weight imbalance threshold
        ARB_THRESH_STARVATION_TIME  = 4'h8,  // Starvation time threshold
        ARB_THRESH_RESERVED_9       = 4'h9,  // Reserved
        ARB_THRESH_RESERVED_A       = 4'hA,  // Reserved
        ARB_THRESH_RESERVED_B       = 4'hB,  // Reserved
        ARB_THRESH_RESERVED_C       = 4'hC,  // Reserved
        ARB_THRESH_RESERVED_D       = 4'hD,  // Reserved
        ARB_THRESH_RESERVED_E       = 4'hE,  // Reserved
        ARB_THRESH_USER_DEFINED     = 4'hF   // User-defined threshold
    } arb_threshold_code_t;

    // ARB Performance Events (packet_type = PktTypePerf, protocol = PROTOCOL_ARB)
    typedef enum logic [3:0] {
        ARB_PERF_GRANT_ISSUED       = 4'h0,  // Grant issued event
        ARB_PERF_ACK_RECEIVED       = 4'h1,  // ACK received event
        ARB_PERF_GRANT_EFFICIENCY   = 4'h2,  // Grant completion efficiency
        ARB_PERF_FAIRNESS_METRIC    = 4'h3,  // Fairness compliance metric
        ARB_PERF_THROUGHPUT         = 4'h4,  // Arbitration throughput
        ARB_PERF_LATENCY_AVG        = 4'h5,  // Average latency measurement
        ARB_PERF_WEIGHT_COMPLIANCE  = 4'h6,  // Weight compliance metric
        ARB_PERF_CREDIT_UTILIZATION = 4'h7,  // Credit utilization efficiency
        ARB_PERF_CLIENT_ACTIVITY    = 4'h8,  // Per-client activity metric
        ARB_PERF_STARVATION_COUNT   = 4'h9,  // Starvation event count
        ARB_PERF_BLOCK_EFFICIENCY   = 4'hA,  // Block/unblock efficiency
        ARB_PERF_RESERVED_B         = 4'hB,  // Reserved
        ARB_PERF_RESERVED_C         = 4'hC,  // Reserved
        ARB_PERF_RESERVED_D         = 4'hD,  // Reserved
        ARB_PERF_RESERVED_E         = 4'hE,  // Reserved
        ARB_PERF_USER_DEFINED       = 4'hF   // User-defined performance
    } arb_performance_code_t;

    // ARB Debug Events (packet_type = PktTypeDebug, protocol = PROTOCOL_ARB)
    typedef enum logic [3:0] {
        ARB_DEBUG_STATE_CHANGE     = 4'h0,  // Arbiter state machine change
        ARB_DEBUG_MASK_UPDATE      = 4'h1,  // Round-robin mask update
        ARB_DEBUG_WEIGHT_CHANGE    = 4'h2,  // Weight configuration change
        ARB_DEBUG_CREDIT_UPDATE    = 4'h3,  // Credit level update
        ARB_DEBUG_CLIENT_MASK      = 4'h4,  // Client enable/disable mask
        ARB_DEBUG_PRIORITY_CHANGE  = 4'h5,  // Priority level change
        ARB_DEBUG_BLOCK_EVENT      = 4'h6,  // Block/unblock event
        ARB_DEBUG_QUEUE_STATUS     = 4'h7,  // Request queue status
        ARB_DEBUG_COUNTER_SNAPSHOT = 4'h8,  // Counter values snapshot
        ARB_DEBUG_FIFO_STATUS      = 4'h9,  // FIFO status change
        ARB_DEBUG_FAIRNESS_STATE   = 4'hA,  // Fairness tracking state
        ARB_DEBUG_ACK_STATE        = 4'hB,  // ACK protocol state
        ARB_DEBUG_RESERVED_C       = 4'hC,  // Reserved
        ARB_DEBUG_RESERVED_D       = 4'hD,  // Reserved
        ARB_DEBUG_RESERVED_E       = 4'hE,  // Reserved
        ARB_DEBUG_USER_DEFINED     = 4'hF   // User-defined debug
    } arb_debug_code_t;

    // =============================================================================
    // CORE PROTOCOL EVENT CODES
    // =============================================================================

    // CORE Error Events (packet_type = PktTypeError, protocol = PROTOCOL_CORE)
    typedef enum logic [3:0] {
        CORE_ERR_DESCRIPTOR_MALFORMED  = 4'h0,  // Missing magic number (0x900dc0de)
        CORE_ERR_DESCRIPTOR_BAD_ADDR   = 4'h1,  // Invalid descriptor address
        CORE_ERR_DATA_BAD_ADDR         = 4'h2,  // Invalid data address (fetch or runtime)
        CORE_ERR_FLAG_COMPARISON       = 4'h3,  // Flag mask/compare mismatch
        CORE_ERR_CREDIT_UNDERFLOW      = 4'h4,  // Credit system violation
        CORE_ERR_STATE_MACHINE         = 4'h5,  // Invalid FSM state transition
        CORE_ERR_DESCRIPTOR_ENGINE     = 4'h6,  // Descriptor engine FSM error
        CORE_ERR_FLAG_ENGINE           = 4'h7,  // Flag engine FSM error (legacy - pre-ctrlrd)
        CORE_ERR_CTRLWR_ENGINE         = 4'h8,  // Control write engine FSM error
        CORE_ERR_DATA_ENGINE           = 4'h9,  // Data engine error
        CORE_ERR_CHANNEL_INVALID       = 4'hA,  // Invalid channel ID
        CORE_ERR_CONTROL_VIOLATION     = 4'hB,  // Control register violation
        CORE_ERR_OVERFLOW              = 4'hC,  // Overflow
        CORE_ERR_CTRLRD_MAX_RETRIES    = 4'hD,  // Control read max retries exceeded
        CORE_ERR_CTRLRD_ENGINE         = 4'hE,  // Control read engine FSM error
        CORE_ERR_USER_DEFINED          = 4'hF   // User-defined error
    } core_error_code_t;

    // CORE Timeout Events (packet_type = PktTypeTimeout, protocol = PROTOCOL_CORE)
    typedef enum logic [3:0] {
        CORE_TIMEOUT_DESCRIPTOR_FETCH  = 4'h0,  // Descriptor fetch timeout
        CORE_TIMEOUT_CTRLRD_RETRY      = 4'h1,  // Control read retry timeout
        CORE_TIMEOUT_CTRLWR_WRITE      = 4'h2,  // Control write timeout
        CORE_TIMEOUT_DATA_TRANSFER     = 4'h3,  // Data transfer timeout
        CORE_TIMEOUT_CREDIT_WAIT       = 4'h4,  // Credit wait timeout
        CORE_TIMEOUT_CONTROL_WAIT      = 4'h5,  // Control enable wait timeout
        CORE_TIMEOUT_ENGINE_RESPONSE   = 4'h6,  // Sub-engine response timeout
        CORE_TIMEOUT_STATE_TRANSITION  = 4'h7,  // FSM state transition timeout
        CORE_TIMEOUT_RESERVED_8        = 4'h8,  // Reserved
        CORE_TIMEOUT_RESERVED_9        = 4'h9,  // Reserved
        CORE_TIMEOUT_RESERVED_A        = 4'hA,  // Reserved
        CORE_TIMEOUT_RESERVED_B        = 4'hB,  // Reserved
        CORE_TIMEOUT_RESERVED_C        = 4'hC,  // Reserved
        CORE_TIMEOUT_RESERVED_D        = 4'hD,  // Reserved
        CORE_TIMEOUT_RESERVED_E        = 4'hE,  // Reserved
        CORE_TIMEOUT_USER_DEFINED      = 4'hF   // User-defined timeout
    } core_timeout_code_t;

    // CORE Completion Events (packet_type = PktTypeCompletion, protocol = PROTOCOL_CORE)
    typedef enum logic [3:0] {
        CORE_COMPL_DESCRIPTOR_LOADED   = 4'h0,  // Descriptor successfully loaded
        CORE_COMPL_DESCRIPTOR_CHAIN    = 4'h1,  // Descriptor chain completed
        CORE_COMPL_CTRLRD_COMPLETED    = 4'h2,  // Control read completed (with match)
        CORE_COMPL_CTRLWR_COMPLETED    = 4'h3,  // Control write completed
        CORE_COMPL_DATA_TRANSFER       = 4'h4,  // Data transfer completed
        CORE_COMPL_CREDIT_CYCLE        = 4'h5,  // Credit cycle completed
        CORE_COMPL_CHANNEL_COMPLETE    = 4'h6,  // Channel processing complete
        CORE_COMPL_ENGINE_READY        = 4'h7,  // Sub-engine ready
        CORE_COMPL_RESERVED_8          = 4'h8,  // Reserved
        CORE_COMPL_RESERVED_9          = 4'h9,  // Reserved
        CORE_COMPL_RESERVED_A          = 4'hA,  // Reserved
        CORE_COMPL_RESERVED_B          = 4'hB,  // Reserved
        CORE_COMPL_RESERVED_C          = 4'hC,  // Reserved
        CORE_COMPL_RESERVED_D          = 4'hD,  // Reserved
        CORE_COMPL_RESERVED_E          = 4'hE,  // Reserved
        CORE_COMPL_USER_DEFINED        = 4'hF   // User-defined completion
    } core_completion_code_t;

    // CORE Threshold Events (packet_type = PktTypeThreshold, protocol = PROTOCOL_CORE)
    typedef enum logic [3:0] {
        CORE_THRESH_DESCRIPTOR_QUEUE   = 4'h0,  // Descriptor queue depth threshold
        CORE_THRESH_CREDIT_LOW         = 4'h1,  // Credit low threshold
        CORE_THRESH_FLAG_RETRY_COUNT   = 4'h2,  // Flag retry count threshold
        CORE_THRESH_LATENCY            = 4'h3,  // Processing latency threshold
        CORE_THRESH_ERROR_RATE         = 4'h4,  // Error rate threshold
        CORE_THRESH_THROUGHPUT         = 4'h5,  // Throughput threshold
        CORE_THRESH_ACTIVE_CHANNELS    = 4'h6,  // Active channel count threshold
        CORE_THRESH_PROGRAM_LATENCY    = 4'h7,  // Program write latency threshold
        CORE_THRESH_DATA_RATE          = 4'h8,  // Data transfer rate threshold
        CORE_THRESH_RESERVED_9         = 4'h9,  // Reserved
        CORE_THRESH_RESERVED_A         = 4'hA,  // Reserved
        CORE_THRESH_RESERVED_B         = 4'hB,  // Reserved
        CORE_THRESH_RESERVED_C         = 4'hC,  // Reserved
        CORE_THRESH_RESERVED_D         = 4'hD,  // Reserved
        CORE_THRESH_RESERVED_E         = 4'hE,  // Reserved
        CORE_THRESH_USER_DEFINED       = 4'hF   // User-defined threshold
    } core_threshold_code_t;

    // CORE Performance Events (packet_type = PktTypePerf, protocol = PROTOCOL_CORE)
    typedef enum logic [3:0] {
        CORE_PERF_END_OF_DATA          = 4'h0,  // Stream continuation signal
        CORE_PERF_END_OF_STREAM        = 4'h1,  // Stream termination signal
        CORE_PERF_ENTERING_IDLE        = 4'h2,  // FSM returning to idle
        CORE_PERF_CREDIT_INCREMENTED   = 4'h3,  // Credit added by software
        CORE_PERF_CREDIT_EXHAUSTED     = 4'h4,  // Credit blocking execution
        CORE_PERF_STATE_TRANSITION     = 4'h5,  // FSM state change
        CORE_PERF_DESCRIPTOR_ACTIVE    = 4'h6,  // Data processing started
        CORE_PERF_CTRLRD_RETRY         = 4'h7,  // Control read retry attempt
        CORE_PERF_CHANNEL_ENABLE       = 4'h8,  // Channel enabled by software
        CORE_PERF_CHANNEL_DISABLE      = 4'h9,  // Channel disabled by software
        CORE_PERF_CREDIT_UTILIZATION   = 4'hA,  // Credit utilization metric
        CORE_PERF_PROCESSING_LATENCY   = 4'hB,  // Total processing latency
        CORE_PERF_QUEUE_DEPTH          = 4'hC,  // Current queue depth
        CORE_PERF_RESERVED_D           = 4'hD,  // Reserved
        CORE_PERF_RESERVED_E           = 4'hE,  // Reserved
        CORE_PERF_USER_DEFINED         = 4'hF   // User-defined performance
    } core_performance_code_t;

    // CORE Debug Events (packet_type = PktTypeDebug, protocol = PROTOCOL_CORE)
    typedef enum logic [3:0] {
        CORE_DEBUG_FSM_STATE_CHANGE    = 4'h0,  // Descriptor FSM state change
        CORE_DEBUG_DESCRIPTOR_CONTENT  = 4'h1,  // Descriptor content trace
        CORE_DEBUG_CTRLRD_ENGINE_STATE = 4'h2,  // Control read engine state trace
        CORE_DEBUG_CTRLWR_ENGINE_STATE = 4'h3,  // Control write engine state trace
        CORE_DEBUG_CREDIT_OPERATION    = 4'h4,  // Credit system operation
        CORE_DEBUG_CONTROL_REGISTER    = 4'h5,  // Control register access
        CORE_DEBUG_ENGINE_HANDSHAKE    = 4'h6,  // Engine handshake trace
        CORE_DEBUG_QUEUE_STATUS        = 4'h7,  // Queue status change
        CORE_DEBUG_COUNTER_SNAPSHOT    = 4'h8,  // Counter values snapshot
        CORE_DEBUG_ADDRESS_TRACE       = 4'h9,  // Address progression trace
        CORE_DEBUG_PAYLOAD_TRACE       = 4'hA,  // Payload content trace
        CORE_DEBUG_RESERVED_B          = 4'hB,  // Reserved
        CORE_DEBUG_RESERVED_C          = 4'hC,  // Reserved
        CORE_DEBUG_RESERVED_D          = 4'hD,  // Reserved
        CORE_DEBUG_RESERVED_E          = 4'hE,  // Reserved
        CORE_DEBUG_USER_DEFINED        = 4'hF   // User-defined debug
    } core_debug_code_t;

    // =============================================================================
    // ARB/CORE UNIFIED EVENT CODE UNION
    // =============================================================================

    typedef union packed {
        // ARB protocol event codes
        arb_error_code_t       arb_error;
        arb_timeout_code_t     arb_timeout;
        arb_completion_code_t  arb_completion;
        arb_threshold_code_t   arb_threshold;
        arb_performance_code_t arb_performance;
        arb_debug_code_t       arb_debug;

        // CORE protocol event codes
        core_error_code_t       core_error;
        core_timeout_code_t     core_timeout;
        core_completion_code_t  core_completion;
        core_threshold_code_t   core_threshold;
        core_performance_code_t core_performance;
        core_debug_code_t       core_debug;

        // Raw 4-bit value for direct access
        logic [3:0]            raw;
    } arb_core_event_code_t;

    // =============================================================================
    // ARB EVENT CODE CREATION HELPER FUNCTIONS
    // =============================================================================

    function automatic arb_core_event_code_t create_arb_error_event(arb_error_code_t code);
        arb_core_event_code_t result;
        result.arb_error = code;
        return result;
    endfunction

    function automatic arb_core_event_code_t create_arb_timeout_event(arb_timeout_code_t code);
        arb_core_event_code_t result;
        result.arb_timeout = code;
        return result;
    endfunction

    function automatic arb_core_event_code_t create_arb_completion_event(arb_completion_code_t code);
        arb_core_event_code_t result;
        result.arb_completion = code;
        return result;
    endfunction

    function automatic arb_core_event_code_t create_arb_threshold_event(arb_threshold_code_t code);
        arb_core_event_code_t result;
        result.arb_threshold = code;
        return result;
    endfunction

    function automatic arb_core_event_code_t create_arb_performance_event(arb_performance_code_t code);
        arb_core_event_code_t result;
        result.arb_performance = code;
        return result;
    endfunction

    function automatic arb_core_event_code_t create_arb_debug_event(arb_debug_code_t code);
        arb_core_event_code_t result;
        result.arb_debug = code;
        return result;
    endfunction

    // =============================================================================
    // STRING FUNCTIONS FOR DEBUGGING
    // =============================================================================

    function automatic string get_arb_error_name(arb_error_code_t code);
        case (code)
            ARB_ERR_STARVATION        : return "STARVATION";
            ARB_ERR_ACK_TIMEOUT       : return "ACK_TIMEOUT";
            ARB_ERR_PROTOCOL_VIOLATION : return "PROTOCOL_VIOLATION";
            ARB_ERR_CREDIT_VIOLATION  : return "CREDIT_VIOLATION";
            ARB_ERR_FAIRNESS_VIOLATION : return "FAIRNESS_VIOLATION";
            ARB_ERR_WEIGHT_UNDERFLOW  : return "WEIGHT_UNDERFLOW";
            ARB_ERR_CONCURRENT_GRANTS : return "CONCURRENT_GRANTS";
            ARB_ERR_INVALID_GRANT_ID  : return "INVALID_GRANT_ID";
            ARB_ERR_ORPHAN_ACK        : return "ORPHAN_ACK";
            ARB_ERR_GRANT_OVERLAP     : return "GRANT_OVERLAP";
            ARB_ERR_MASK_ERROR        : return "MASK_ERROR";
            ARB_ERR_STATE_MACHINE     : return "STATE_MACHINE";
            ARB_ERR_CONFIGURATION     : return "CONFIGURATION";
            ARB_ERR_USER_DEFINED      : return "USER_DEFINED";
            default                   : return "UNKNOWN_ARB_ERROR";
        endcase
    endfunction

    function automatic string get_core_error_name(core_error_code_t code);
        case (code)
            CORE_ERR_DESCRIPTOR_MALFORMED : return "DESCRIPTOR_MALFORMED";
            CORE_ERR_DESCRIPTOR_BAD_ADDR  : return "DESCRIPTOR_BAD_ADDR";
            CORE_ERR_DATA_BAD_ADDR        : return "DATA_BAD_ADDR";
            CORE_ERR_FLAG_COMPARISON      : return "FLAG_COMPARISON";
            CORE_ERR_CREDIT_UNDERFLOW     : return "CREDIT_UNDERFLOW";
            CORE_ERR_STATE_MACHINE        : return "STATE_MACHINE";
            CORE_ERR_DESCRIPTOR_ENGINE    : return "DESCRIPTOR_ENGINE";
            CORE_ERR_FLAG_ENGINE          : return "FLAG_ENGINE";
            CORE_ERR_CTRLWR_ENGINE        : return "CTRLWR_ENGINE";
            CORE_ERR_DATA_ENGINE          : return "DATA_ENGINE";
            CORE_ERR_CHANNEL_INVALID      : return "CHANNEL_INVALID";
            CORE_ERR_CONTROL_VIOLATION    : return "CONTROL_VIOLATION";
            CORE_ERR_OVERFLOW             : return "OVERFLOW";
            CORE_ERR_CTRLRD_MAX_RETRIES   : return "CTRLRD_MAX_RETRIES";
            CORE_ERR_CTRLRD_ENGINE        : return "CTRLRD_ENGINE";
            CORE_ERR_USER_DEFINED         : return "USER_DEFINED";
            default                       : return "UNKNOWN_CORE_ERROR";
        endcase
    endfunction

    // Protocol and event validation functions
    function automatic bit is_valid_arb_event_for_packet_type(
        logic [3:0] packet_type,
        protocol_type_t protocol,
        logic [3:0] event_code
    );
        case (protocol)
            PROTOCOL_ARB: begin
                case (packet_type)
                    PktTypeError     : return 1'b1;
                    PktTypeTimeout   : return 1'b1;
                    PktTypeCompletion: return 1'b1;
                    PktTypeThreshold : return 1'b1;
                    PktTypePerf      : return 1'b1;
                    PktTypeDebug     : return 1'b1;
                    default          : return 1'b0;
                endcase
            end
            PROTOCOL_CORE: begin
                case (packet_type)
                    PktTypeError     : return 1'b1;
                    PktTypeTimeout   : return 1'b1;
                    PktTypeCompletion: return 1'b1;
                    PktTypeThreshold : return 1'b1;
                    PktTypePerf      : return 1'b1;
                    PktTypeDebug     : return 1'b1;
                    default          : return 1'b0;
                endcase
            end
            default: return 1'b0;
        endcase
    endfunction

endpackage : monitor_arbiter_pkg
