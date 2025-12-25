// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monitor_amba4_pkg
// Purpose: AMBA4 protocol event codes (AXI4, APB4, AXIS4)
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-21

`timescale 1ns / 1ps
/**
 * AMBA4 Protocol Event Codes
 *
 * This package defines event codes for AMBA4 protocols:
 * - AXI4/AXI4-Lite event codes
 * - APB4 event codes
 * - AXIS4 (AXI4-Stream) event codes
 *
 * Each protocol has event codes for error, timeout, completion,
 * threshold, performance, and debug events.
 */
package monitor_amba4_pkg;

    import monitor_common_pkg::*;

    // =============================================================================
    // AXI4 PROTOCOL EVENT CODES
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
        AXI_ERR_RESERVED_D          = 4'hD,  // Reserved
        AXI_ERR_RESERVED_E          = 4'hE,  // Reserved
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
        AXI_THRESH_RESERVED_8     = 4'h8,  // Reserved
        AXI_THRESH_RESERVED_9     = 4'h9,  // Reserved
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
        AXI_PERF_RESERVED_C        = 4'hC,  // Reserved
        AXI_PERF_RESERVED_D        = 4'hD,  // Reserved
        AXI_PERF_READ_WRITE_RATIO  = 4'hE,  // Read/Write transaction ratio
        AXI_PERF_USER_DEFINED      = 4'hF   // User-defined performance
    } axi_performance_code_t;

    // AXI Address Match Events (packet_type = PktTypeAddrMatch, protocol = PROTOCOL_AXI)
    typedef enum logic [3:0] {
        AXI_ADDR_EXACT_MATCH     = 4'h0,  // Exact address match
        AXI_ADDR_RANGE_MATCH     = 4'h1,  // Address within range
        AXI_ADDR_MASK_MATCH      = 4'h2,  // Address mask match
        AXI_ADDR_PATTERN_MATCH   = 4'h3,  // Address pattern match
        AXI_ADDR_SEQUENTIAL      = 4'h4,  // Sequential address access
        AXI_ADDR_STRIDE_MATCH    = 4'h5,  // Stride pattern match
        AXI_ADDR_HOTSPOT         = 4'h6,  // Address hotspot detected
        AXI_ADDR_CONFLICT        = 4'h7,  // Address conflict detected
        AXI_ADDR_RESERVED_8      = 4'h8,  // Reserved
        AXI_ADDR_RESERVED_9      = 4'h9,  // Reserved
        AXI_ADDR_RESERVED_A      = 4'hA,  // Reserved
        AXI_ADDR_RESERVED_B      = 4'hB,  // Reserved
        AXI_ADDR_RESERVED_C      = 4'hC,  // Reserved
        AXI_ADDR_RESERVED_D      = 4'hD,  // Reserved
        AXI_ADDR_RESERVED_E      = 4'hE,  // Reserved
        AXI_ADDR_USER_DEFINED    = 4'hF   // User-defined address match
    } axi_addr_match_code_t;

    // AXI Debug Events (packet_type = PktTypeDebug, protocol = PROTOCOL_AXI)
    typedef enum logic [3:0] {
        AXI_DEBUG_STATE_CHANGE   = 4'h0,  // AXI state machine change
        AXI_DEBUG_PIPELINE_STALL = 4'h1,  // Pipeline stall event
        AXI_DEBUG_BACKPRESSURE   = 4'h2,  // Backpressure event
        AXI_DEBUG_OUTSTANDING    = 4'h3,  // Outstanding transaction count
        AXI_DEBUG_REORDER_BUFFER = 4'h4,  // Reorder buffer status
        AXI_DEBUG_ID_ALLOCATION  = 4'h5,  // Transaction ID allocation
        AXI_DEBUG_QOS_ESCALATION = 4'h6,  // QoS escalation event
        AXI_DEBUG_HANDSHAKE      = 4'h7,  // Handshake timing event
        AXI_DEBUG_QUEUE_STATUS   = 4'h8,  // Queue status change
        AXI_DEBUG_COUNTER        = 4'h9,  // Counter snapshot
        AXI_DEBUG_FIFO_STATUS    = 4'hA,  // FIFO status
        AXI_DEBUG_RESERVED_B     = 4'hB,  // Reserved
        AXI_DEBUG_RESERVED_C     = 4'hC,  // Reserved
        AXI_DEBUG_RESERVED_D     = 4'hD,  // Reserved
        AXI_DEBUG_RESERVED_E     = 4'hE,  // Reserved
        AXI_DEBUG_USER_DEFINED   = 4'hF   // User-defined debug
    } axi_debug_code_t;

    // =============================================================================
    // APB4 PROTOCOL EVENT CODES
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
        APB_COMPL_RESERVED_3     = 4'h3,  // Reserved
        APB_COMPL_RESERVED_4     = 4'h4,  // Reserved
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
        APB_THRESH_LATENCY       = 4'h0,  // Transaction latency threshold
        APB_THRESH_ERROR_RATE    = 4'h1,  // Error rate threshold
        APB_THRESH_ACTIVE_COUNT  = 4'h2,  // Active transaction count threshold
        APB_THRESH_THROUGHPUT    = 4'h3,  // Throughput threshold
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
        APB_PERF_READ_LATENCY    = 4'h0,  // Read transaction latency
        APB_PERF_WRITE_LATENCY   = 4'h1,  // Write transaction latency
        APB_PERF_THROUGHPUT      = 4'h2,  // Transaction throughput
        APB_PERF_ERROR_RATE      = 4'h3,  // Error rate
        APB_PERF_ACTIVE_COUNT    = 4'h4,  // Active transaction count
        APB_PERF_COMPLETED_COUNT = 4'h5,  // Completed transaction count
        APB_PERF_RESERVED_6      = 4'h6,  // Reserved
        APB_PERF_RESERVED_7      = 4'h7,  // Reserved
        APB_PERF_RESERVED_8      = 4'h8,  // Reserved
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
    // AXIS4 PROTOCOL EVENT CODES
    // =============================================================================

    // AXIS Error Events (packet_type = PktTypeError, protocol = PROTOCOL_AXIS)
    typedef enum logic [3:0] {
        AXIS_ERR_PROTOCOL        = 4'h0,  // Protocol violation
        AXIS_ERR_READY_TIMING    = 4'h1,  // TREADY timing violation
        AXIS_ERR_VALID_TIMING    = 4'h2,  // TVALID timing violation
        AXIS_ERR_LAST_MISSING    = 4'h3,  // Missing TLAST signal
        AXIS_ERR_LAST_ORPHAN     = 4'h4,  // Orphaned TLAST signal
        AXIS_ERR_STRB_INVALID    = 4'h5,  // Invalid TSTRB pattern
        AXIS_ERR_KEEP_INVALID    = 4'h6,  // Invalid TKEEP pattern
        AXIS_ERR_DATA_ALIGNMENT  = 4'h7,  // Data alignment error
        AXIS_ERR_ID_VIOLATION    = 4'h8,  // TID violation
        AXIS_ERR_DEST_VIOLATION  = 4'h9,  // TDEST violation
        AXIS_ERR_USER_VIOLATION  = 4'hA,  // TUSER violation
        AXIS_ERR_RESERVED_B      = 4'hB,  // Reserved
        AXIS_ERR_RESERVED_C      = 4'hC,  // Reserved
        AXIS_ERR_RESERVED_D      = 4'hD,  // Reserved
        AXIS_ERR_RESERVED_E      = 4'hE,  // Reserved
        AXIS_ERR_USER_DEFINED    = 4'hF   // User-defined error
    } axis_error_code_t;

    // AXIS Timeout Events (packet_type = PktTypeTimeout, protocol = PROTOCOL_AXIS)
    typedef enum logic [3:0] {
        AXIS_TIMEOUT_HANDSHAKE    = 4'h0,  // TVALID/TREADY handshake timeout
        AXIS_TIMEOUT_STREAM       = 4'h1,  // Stream completion timeout
        AXIS_TIMEOUT_PACKET       = 4'h2,  // Packet timeout (TLAST)
        AXIS_TIMEOUT_BACKPRESSURE = 4'h3,  // Backpressure timeout
        AXIS_TIMEOUT_BUFFER       = 4'h4,  // Buffer drain timeout
        AXIS_TIMEOUT_STALL        = 4'h5,  // Stream stall timeout
        AXIS_TIMEOUT_RESERVED_6   = 4'h6,  // Reserved
        AXIS_TIMEOUT_RESERVED_7   = 4'h7,  // Reserved
        AXIS_TIMEOUT_RESERVED_8   = 4'h8,  // Reserved
        AXIS_TIMEOUT_RESERVED_9   = 4'h9,  // Reserved
        AXIS_TIMEOUT_RESERVED_A   = 4'hA,  // Reserved
        AXIS_TIMEOUT_RESERVED_B   = 4'hB,  // Reserved
        AXIS_TIMEOUT_RESERVED_C   = 4'hC,  // Reserved
        AXIS_TIMEOUT_RESERVED_D   = 4'hD,  // Reserved
        AXIS_TIMEOUT_RESERVED_E   = 4'hE,  // Reserved
        AXIS_TIMEOUT_USER_DEFINED = 4'hF   // User-defined timeout
    } axis_timeout_code_t;

    // AXIS Completion Events (packet_type = PktTypeCompletion, protocol = PROTOCOL_AXIS)
    typedef enum logic [3:0] {
        AXIS_COMPL_STREAM_END    = 4'h0,  // Stream completed (TLAST)
        AXIS_COMPL_PACKET_SENT   = 4'h1,  // Packet sent successfully
        AXIS_COMPL_TRANSFER      = 4'h2,  // Data transfer completed
        AXIS_COMPL_BURST_END     = 4'h3,  // Burst completed
        AXIS_COMPL_HANDSHAKE     = 4'h4,  // Successful handshake
        AXIS_COMPL_RESERVED_5    = 4'h5,  // Reserved
        AXIS_COMPL_RESERVED_6    = 4'h6,  // Reserved
        AXIS_COMPL_RESERVED_7    = 4'h7,  // Reserved
        AXIS_COMPL_RESERVED_8    = 4'h8,  // Reserved
        AXIS_COMPL_RESERVED_9    = 4'h9,  // Reserved
        AXIS_COMPL_RESERVED_A    = 4'hA,  // Reserved
        AXIS_COMPL_RESERVED_B    = 4'hB,  // Reserved
        AXIS_COMPL_RESERVED_C    = 4'hC,  // Reserved
        AXIS_COMPL_RESERVED_D    = 4'hD,  // Reserved
        AXIS_COMPL_RESERVED_E    = 4'hE,  // Reserved
        AXIS_COMPL_USER_DEFINED  = 4'hF   // User-defined completion
    } axis_completion_code_t;

    // AXIS Credit Events (packet_type = PktTypeCredit, protocol = PROTOCOL_AXIS)
    typedef enum logic [3:0] {
        AXIS_CREDIT_READY_ASSERT   = 4'h0,  // TREADY asserted
        AXIS_CREDIT_READY_DEASSERT = 4'h1,  // TREADY deasserted
        AXIS_CREDIT_BUFFER_AVAILABLE = 4'h2,  // Buffer space available
        AXIS_CREDIT_BUFFER_FULL    = 4'h3,  // Buffer full
        AXIS_CREDIT_FLOW_CONTROL   = 4'h4,  // Flow control event
        AXIS_CREDIT_BACKPRESSURE   = 4'h5,  // Backpressure applied
        AXIS_CREDIT_THROUGHPUT     = 4'h6,  // Throughput event
        AXIS_CREDIT_EFFICIENCY     = 4'h7,  // Transfer efficiency
        AXIS_CREDIT_RESERVED_8     = 4'h8,  // Reserved
        AXIS_CREDIT_RESERVED_9     = 4'h9,  // Reserved
        AXIS_CREDIT_RESERVED_A     = 4'hA,  // Reserved
        AXIS_CREDIT_RESERVED_B     = 4'hB,  // Reserved
        AXIS_CREDIT_RESERVED_C     = 4'hC,  // Reserved
        AXIS_CREDIT_RESERVED_D     = 4'hD,  // Reserved
        AXIS_CREDIT_RESERVED_E     = 4'hE,  // Reserved
        AXIS_CREDIT_USER_DEFINED   = 4'hF   // User-defined credit event
    } axis_credit_code_t;

    // AXIS Channel Events (packet_type = PktTypeChannel, protocol = PROTOCOL_AXIS)
    typedef enum logic [3:0] {
        AXIS_CHAN_CONNECT        = 4'h0,  // Channel connected
        AXIS_CHAN_DISCONNECT     = 4'h1,  // Channel disconnected
        AXIS_CHAN_STALL          = 4'h2,  // Channel stalled
        AXIS_CHAN_RESUME         = 4'h3,  // Channel resumed
        AXIS_CHAN_CONGESTION     = 4'h4,  // Channel congestion
        AXIS_CHAN_ID_CHANGE      = 4'h5,  // TID change detected
        AXIS_CHAN_DEST_CHANGE    = 4'h6,  // TDEST change detected
        AXIS_CHAN_CONFIG_CHANGE  = 4'h7,  // Channel configuration change
        AXIS_CHAN_RESERVED_8     = 4'h8,  // Reserved
        AXIS_CHAN_RESERVED_9     = 4'h9,  // Reserved
        AXIS_CHAN_RESERVED_A     = 4'hA,  // Reserved
        AXIS_CHAN_RESERVED_B     = 4'hB,  // Reserved
        AXIS_CHAN_RESERVED_C     = 4'hC,  // Reserved
        AXIS_CHAN_RESERVED_D     = 4'hD,  // Reserved
        AXIS_CHAN_RESERVED_E     = 4'hE,  // Reserved
        AXIS_CHAN_USER_DEFINED   = 4'hF   // User-defined channel event
    } axis_channel_code_t;

    // AXIS Stream Events (packet_type = PktTypeStream, protocol = PROTOCOL_AXIS)
    typedef enum logic [3:0] {
        AXIS_STREAM_START        = 4'h0,  // Stream started
        AXIS_STREAM_END          = 4'h1,  // Stream ended (TLAST)
        AXIS_STREAM_PAUSE        = 4'h2,  // Stream paused
        AXIS_STREAM_RESUME       = 4'h3,  // Stream resumed
        AXIS_STREAM_OVERFLOW     = 4'h4,  // Stream buffer overflow
        AXIS_STREAM_UNDERFLOW    = 4'h5,  // Stream buffer underflow
        AXIS_STREAM_TRANSFER     = 4'h6,  // Active data transfer
        AXIS_STREAM_IDLE         = 4'h7,  // Stream idle
        AXIS_STREAM_RESERVED_8   = 4'h8,  // Reserved
        AXIS_STREAM_RESERVED_9   = 4'h9,  // Reserved
        AXIS_STREAM_RESERVED_A   = 4'hA,  // Reserved
        AXIS_STREAM_RESERVED_B   = 4'hB,  // Reserved
        AXIS_STREAM_RESERVED_C   = 4'hC,  // Reserved
        AXIS_STREAM_RESERVED_D   = 4'hD,  // Reserved
        AXIS_STREAM_RESERVED_E   = 4'hE,  // Reserved
        AXIS_STREAM_USER_DEFINED = 4'hF   // User-defined stream event
    } axis_stream_code_t;

    // =============================================================================
    // UNIFIED EVENT CODE UNION (for multi-protocol support)
    // =============================================================================

    typedef union packed {
        // AXI protocol event codes
        axi_error_code_t       axi_error;
        axi_timeout_code_t     axi_timeout;
        axi_completion_code_t  axi_completion;
        axi_threshold_code_t   axi_threshold;
        axi_performance_code_t axi_performance;
        axi_addr_match_code_t  axi_addr_match;
        axi_debug_code_t       axi_debug;

        // APB protocol event codes
        apb_error_code_t       apb_error;
        apb_timeout_code_t     apb_timeout;
        apb_completion_code_t  apb_completion;
        apb_threshold_code_t   apb_threshold;
        apb_performance_code_t apb_performance;
        apb_debug_code_t       apb_debug;

        // AXIS protocol event codes
        axis_error_code_t      axis_error;
        axis_timeout_code_t    axis_timeout;
        axis_completion_code_t axis_completion;
        axis_credit_code_t     axis_credit;
        axis_channel_code_t    axis_channel;
        axis_stream_code_t     axis_stream;

        // Raw 4-bit value for direct access
        logic [3:0]            raw;
    } unified_event_code_t;

    // =============================================================================
    // EVENT CODE CREATION HELPER FUNCTIONS
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

    function automatic unified_event_code_t create_apb_threshold_event(apb_threshold_code_t code);
        unified_event_code_t result;
        result.apb_threshold = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_apb_performance_event(apb_performance_code_t code);
        unified_event_code_t result;
        result.apb_performance = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_apb_debug_event(apb_debug_code_t code);
        unified_event_code_t result;
        result.apb_debug = code;
        return result;
    endfunction

    // AXIS event code creation functions
    function automatic unified_event_code_t create_axis_error_event(axis_error_code_t code);
        unified_event_code_t result;
        result.axis_error = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_axis_timeout_event(axis_timeout_code_t code);
        unified_event_code_t result;
        result.axis_timeout = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_axis_completion_event(axis_completion_code_t code);
        unified_event_code_t result;
        result.axis_completion = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_axis_credit_event(axis_credit_code_t code);
        unified_event_code_t result;
        result.axis_credit = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_axis_channel_event(axis_channel_code_t code);
        unified_event_code_t result;
        result.axis_channel = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_axis_stream_event(axis_stream_code_t code);
        unified_event_code_t result;
        result.axis_stream = code;
        return result;
    endfunction

    // =============================================================================
    // AXI MONITOR TRANSACTION STRUCTURE
    // =============================================================================

    // Event code union for AXI transactions
    typedef union packed {
        axi_error_code_t       axi_error;
        axi_timeout_code_t     axi_timeout;
        axi_completion_code_t  axi_completion;
        axi_threshold_code_t   axi_threshold;
        axi_performance_code_t axi_performance;
        logic [3:0]            raw_code;
    } event_code_union_t;

    // Bus transaction structure for AXI monitoring
    typedef struct packed {
        logic        valid;              // Transaction slot is valid/active
        logic        cmd_received;       // Address phase completed
        logic        data_started;       // Data phase started
        logic        data_completed;     // Data phase completed
        logic        resp_received;      // Response phase completed
        logic        event_reported;     // Event has been reported to monitor bus
        logic        eos_seen;           // End of stream seen (last beat)

        transaction_state_t state;       // Current transaction state

        logic [31:0] addr;               // Transaction address
        logic [7:0]  id;                 // Transaction ID
        logic [7:0]  len;                // Burst length
        logic [2:0]  size;               // Burst size
        logic [1:0]  burst;              // Burst type
        logic [5:0]  channel;            // Channel identifier

        logic [31:0] addr_timer;         // Address phase timer
        logic [31:0] data_timer;         // Data phase timer
        logic [31:0] resp_timer;         // Response phase timer
        logic [31:0] addr_timestamp;     // Address phase timestamp
        logic [31:0] data_timestamp;     // Data phase timestamp
        logic [31:0] resp_timestamp;     // Response phase timestamp

        logic [7:0]  expected_beats;     // Expected number of data beats
        logic [7:0]  data_beat_count;    // Current data beat count

        event_code_union_t event_code;   // Event code for this transaction
    } bus_transaction_t;

    // Legacy event constants for backward compatibility
    localparam logic [3:0] EVT_NONE                    = 4'h0;
    localparam axi_timeout_code_t EVT_CMD_TIMEOUT      = AXI_TIMEOUT_CMD;
    localparam axi_timeout_code_t EVT_DATA_TIMEOUT     = AXI_TIMEOUT_DATA;
    localparam axi_timeout_code_t EVT_RESP_TIMEOUT     = AXI_TIMEOUT_RESP;
    localparam axi_completion_code_t EVT_TRANS_COMPLETE = AXI_COMPL_TRANS_COMPLETE;
    localparam axi_error_code_t EVT_RESP_SLVERR        = AXI_ERR_RESP_SLVERR;
    localparam axi_error_code_t EVT_RESP_DECERR        = AXI_ERR_RESP_DECERR;
    localparam axi_error_code_t EVT_DATA_ORPHAN        = AXI_ERR_DATA_ORPHAN;
    localparam axi_error_code_t EVT_RESP_ORPHAN        = AXI_ERR_RESP_ORPHAN;
    localparam axi_error_code_t EVT_PROTOCOL           = AXI_ERR_PROTOCOL;

    // =============================================================================
    // STRING FUNCTIONS FOR DEBUGGING
    // =============================================================================

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
            AXI_ERR_RESERVED_D         : return "RESERVED_D";
            AXI_ERR_RESERVED_E         : return "RESERVED_E";
            AXI_ERR_USER_DEFINED       : return "USER_DEFINED";
            default                    : return "UNKNOWN_AXI_ERROR";
        endcase
    endfunction

    // Protocol and event validation functions
    function automatic bit is_valid_event_for_packet_type(
        logic [3:0] packet_type,
        protocol_type_t protocol,
        logic [3:0] event_code
    );
        case (protocol)
            PROTOCOL_AXI: begin
                case (packet_type)
                    PktTypeError     : return 1'b1;
                    PktTypeTimeout   : return 1'b1;
                    PktTypeCompletion: return 1'b1;
                    PktTypeThreshold : return 1'b1;
                    PktTypePerf      : return 1'b1;
                    PktTypeAddrMatch : return 1'b1;
                    PktTypeDebug     : return 1'b1;
                    default          : return 1'b0;
                endcase
            end
            PROTOCOL_AXIS: begin
                case (packet_type)
                    PktTypeError     : return 1'b1;
                    PktTypeTimeout   : return 1'b1;
                    PktTypeCompletion: return 1'b1;
                    PktTypeCredit    : return 1'b1;
                    PktTypeChannel   : return 1'b1;
                    PktTypeStream    : return 1'b1;
                    default          : return 1'b0;
                endcase
            end
            PROTOCOL_APB: begin
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

endpackage : monitor_amba4_pkg
