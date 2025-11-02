// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monitor_pkg
// Purpose: Monitor Pkg module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

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
 * - protocol [59:58] defines which protocol (AXI, AXIS, APB, ARB)
 * - event_code [57:54] defines the specific event within that category
 */
package monitor_pkg;

    // Protocol type enumeration for multi-protocol support
    typedef enum logic [2:0] {
        PROTOCOL_AXI    = 3'b000,
        PROTOCOL_AXIS   = 3'b001,  // AXI4-Stream
        PROTOCOL_APB    = 3'b010,  // Advanced Peripheral Bus
        PROTOCOL_ARB    = 3'b011,  // Arbiter specific packets
        PROTOCOL_CORE   = 3'b100   // Core specific packets
    } protocol_type_t;

    // Monitor bus packet types (used in packet_type field [63:60])
    localparam logic [3:0] PktTypeError      = 4'h0;  // Error event
    localparam logic [3:0] PktTypeCompletion = 4'h1;  // Transaction completion
    localparam logic [3:0] PktTypeThreshold  = 4'h2;  // Threshold crossed
    localparam logic [3:0] PktTypeTimeout    = 4'h3;  // Timeout event
    localparam logic [3:0] PktTypePerf       = 4'h4;  // Performance metric event
    localparam logic [3:0] PktTypeCredit     = 4'h5;  // Credit status (AXIS)
    localparam logic [3:0] PktTypeChannel    = 4'h6;  // Channel status (AXIS)
    localparam logic [3:0] PktTypeStream     = 4'h7;  // Stream event (AXIS)
    localparam logic [3:0] PktTypeAddrMatch  = 4'h8;  // Address match event (AXI)
    localparam logic [3:0] PktTypeAPB        = 4'h9;  // APB-specific event
    localparam logic [3:0] PktTypeReservedA  = 4'hA;  // Reserved
    localparam logic [3:0] PktTypeReservedB  = 4'hB;  // Reserved
    localparam logic [3:0] PktTypeReservedC  = 4'hC;  // Reserved
    localparam logic [3:0] PktTypeReservedD  = 4'hD;  // Reserved
    localparam logic [3:0] PktTypeReservedE  = 4'hE;  // Reserved
    localparam logic [3:0] PktTypeDebug      = 4'hF;  // Debug/trace event

    // =============================================================================
    // AXI PROTOCOL EVENT CODES (organized by packet type) - CLEANED UP
    // =============================================================================

    // AXI Error Events (packet_type = PktTypeError, protocol = PROTOCOL_AXI)
    // REMOVED: AXI_ERR_ARBITER_STARVATION and AXI_ERR_CREDIT_VIOLATION (moved to ARB protocol)
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
        AXI_ERR_RESERVED_D          = 4'hD,  // Reserved (was arbiter starvation)
        AXI_ERR_RESERVED_E          = 4'hE,  // Reserved (was credit violation)
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
    // REMOVED: AXI_THRESH_GRANT_LATENCY and AXI_THRESH_FAIRNESS (moved to ARB protocol)
    typedef enum logic [3:0] {
        AXI_THRESH_ACTIVE_COUNT   = 4'h0,  // Active transaction count threshold
        AXI_THRESH_LATENCY        = 4'h1,  // Latency threshold
        AXI_THRESH_ERROR_RATE     = 4'h2,  // Error rate threshold
        AXI_THRESH_THROUGHPUT     = 4'h3,  // Throughput threshold
        AXI_THRESH_QUEUE_DEPTH    = 4'h4,  // Queue depth threshold
        AXI_THRESH_BANDWIDTH      = 4'h5,  // Bandwidth utilization threshold
        AXI_THRESH_OUTSTANDING    = 4'h6,  // Outstanding transactions threshold
        AXI_THRESH_BURST_SIZE     = 4'h7,  // Average burst size threshold
        AXI_THRESH_RESERVED_8     = 4'h8,  // Reserved (was grant latency)
        AXI_THRESH_RESERVED_9     = 4'h9,  // Reserved (was fairness)
        AXI_THRESH_RESERVED_A     = 4'hA,  // Reserved
        AXI_THRESH_RESERVED_B     = 4'hB,  // Reserved
        AXI_THRESH_RESERVED_C     = 4'hC,  // Reserved
        AXI_THRESH_RESERVED_D     = 4'hD,  // Reserved
        AXI_THRESH_RESERVED_E     = 4'hE,  // Reserved
        AXI_THRESH_USER_DEFINED   = 4'hF   // User-defined threshold
    } axi_threshold_code_t;

    // AXI Performance Events (packet_type = PktTypePerf, protocol = PROTOCOL_AXI)
    // REMOVED: AXI_PERF_GRANT_EFFICIENCY and AXI_PERF_WEIGHT_COMPLIANCE (moved to ARB protocol)
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
        AXI_PERF_RESERVED_C        = 4'hC,  // Reserved (was grant efficiency)
        AXI_PERF_RESERVED_D        = 4'hD,  // Reserved (was weight compliance)
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
    // AXIS PROTOCOL EVENT CODES (organized by packet type)
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
        AXIS_CREDIT_READY_ASSERT = 4'h0,  // TREADY asserted
        AXIS_CREDIT_READY_DEASSERT = 4'h1,  // TREADY deasserted
        AXIS_CREDIT_BUFFER_AVAILABLE = 4'h2,  // Buffer space available
        AXIS_CREDIT_BUFFER_FULL  = 4'h3,  // Buffer full
        AXIS_CREDIT_FLOW_CONTROL = 4'h4,  // Flow control event
        AXIS_CREDIT_BACKPRESSURE = 4'h5,  // Backpressure applied
        AXIS_CREDIT_THROUGHPUT   = 4'h6,  // Throughput event
        AXIS_CREDIT_EFFICIENCY   = 4'h7,  // Transfer efficiency
        AXIS_CREDIT_RESERVED_8   = 4'h8,  // Reserved
        AXIS_CREDIT_RESERVED_9   = 4'h9,  // Reserved
        AXIS_CREDIT_RESERVED_A   = 4'hA,  // Reserved
        AXIS_CREDIT_RESERVED_B   = 4'hB,  // Reserved
        AXIS_CREDIT_RESERVED_C   = 4'hC,  // Reserved
        AXIS_CREDIT_RESERVED_D   = 4'hD,  // Reserved
        AXIS_CREDIT_RESERVED_E   = 4'hE,  // Reserved
        AXIS_CREDIT_USER_DEFINED = 4'hF   // User-defined credit event
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
    // ARBITER PROTOCOL EVENT CODES (NEW - organized by packet type)
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
    // CORE PROTOCOL EVENT CODES (organized by packet type)
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

        // ARB protocol event codes
        arb_error_code_t       arb_error;
        arb_timeout_code_t     arb_timeout;
        arb_completion_code_t  arb_completion;
        arb_threshold_code_t   arb_threshold;
        arb_performance_code_t arb_performance;
        arb_debug_code_t       arb_debug;

        // Raw 4-bit value for direct access
        logic [3:0]            raw;
    } unified_event_code_t;

    // =============================================================================
    // MONITOR PACKET STRUCTURE AND HELPER FUNCTIONS
    // =============================================================================

    // Enhanced 64-bit monitor packet format:
    // [63:60] - packet_type: 4 bits (error, timeout, completion, etc.)
    // [59:57] - protocol:    3 bits (AXI/Network/APB/ARB/CORE)
    // [56:53] - event_code:  4 bits (specific error or event code)
    // [52:47] - channel_id:  6 bits (channel ID and AXI ID)
    // [46:43] - unit_id:     4 bits (subsystem identifier)
    // [42:35] - agent_id:    8 bits (module identifier)
    // [34:0]  - event_data:  35 bits (event-specific data)
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
        logic [34:0]    event_data
    );
        return {packet_type, protocol, event_code, channel_id, unit_id, agent_id, event_data};
    endfunction

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

    // ARB event code creation functions
    function automatic unified_event_code_t create_arb_error_event(arb_error_code_t code);
        unified_event_code_t result;
        result.arb_error = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_arb_timeout_event(arb_timeout_code_t code);
        unified_event_code_t result;
        result.arb_timeout = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_arb_completion_event(arb_completion_code_t code);
        unified_event_code_t result;
        result.arb_completion = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_arb_threshold_event(arb_threshold_code_t code);
        unified_event_code_t result;
        result.arb_threshold = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_arb_performance_event(arb_performance_code_t code);
        unified_event_code_t result;
        result.arb_performance = code;
        return result;
    endfunction

    function automatic unified_event_code_t create_arb_debug_event(arb_debug_code_t code);
        unified_event_code_t result;
        result.arb_debug = code;
        return result;
    endfunction

    // =============================================================================
    // PROTOCOL-SPECIFIC PAYLOAD AND ACK TYPES
    // =============================================================================

    // AXIS transfer types
    typedef enum logic [1:0] {
        AXIS_TRANSFER_DATA   = 2'b00,  // Data transfer
        AXIS_TRANSFER_LAST   = 2'b01,  // Last data transfer
        AXIS_TRANSFER_NULL   = 2'b10,  // Null transfer (positioning)
        AXIS_TRANSFER_IDLE   = 2'b11   // Idle (no transfer)
    } axis_transfer_type_t;

    // AXIS handshake states
    typedef enum logic [1:0] {
        AXIS_HANDSHAKE_IDLE   = 2'b00,  // No activity
        AXIS_HANDSHAKE_VALID  = 2'b01,  // TVALID asserted
        AXIS_HANDSHAKE_READY  = 2'b10,  // TREADY asserted
        AXIS_HANDSHAKE_ACTIVE = 2'b11   // Both TVALID & TREADY
    } axis_handshake_state_t;

    // APB transaction phases for state tracking
    typedef enum logic [1:0] {
        APB_PHASE_IDLE    = 2'b00,  // Bus idle
        APB_PHASE_SETUP   = 2'b01,  // Setup phase (PSEL asserted)
        APB_PHASE_ACCESS  = 2'b10,  // Access phase (PENABLE asserted)
        APB_PHASE_ENABLE  = 2'b11   // Enable phase (waiting for PREADY)
    } apb_phase_t;

    // APB protection types (PPROT encoding)
    typedef enum logic [2:0] {
        APB_PROT_NORMAL        = 3'b000,  // Normal access
        APB_PROT_PRIVILEGED    = 3'b001,  // Privileged access
        APB_PROT_SECURE        = 3'b010,  // Secure access
        APB_PROT_PRIV_SECURE   = 3'b011,  // Privileged + Secure
        APB_PROT_DATA          = 3'b100,  // Data access
        APB_PROT_DATA_PRIV     = 3'b101,  // Data + Privileged
        APB_PROT_DATA_SECURE   = 3'b110,  // Data + Secure
        APB_PROT_DATA_PRIV_SEC = 3'b111   // Data + Privileged + Secure
    } apb_prot_type_t;

    // ARB arbitration types for configuration tracking
    typedef enum logic [1:0] {
        ARB_TYPE_ROUND_ROBIN = 2'b00,  // Round-robin arbitration
        ARB_TYPE_WEIGHTED_RR = 2'b01,  // Weighted round-robin
        ARB_TYPE_PRIORITY    = 2'b10,  // Fixed priority
        ARB_TYPE_CUSTOM      = 2'b11   // Custom arbitration algorithm
    } arb_type_t;

    // ARB state for state machine tracking
    typedef enum logic [2:0] {
        ARB_STATE_IDLE       = 3'b000,  // Idle state
        ARB_STATE_ARBITRATE  = 3'b001,  // Performing arbitration
        ARB_STATE_GRANT      = 3'b010,  // Grant issued, waiting for ACK
        ARB_STATE_BLOCKED    = 3'b011,  // Arbitration blocked
        ARB_STATE_WEIGHT_UPD = 3'b100,  // Weight update in progress
        ARB_STATE_ERROR      = 3'b101,  // Error state
        ARB_STATE_RESERVED_6 = 3'b110,  // Reserved
        ARB_STATE_RESERVED_7 = 3'b111   // Reserved
    } arb_state_t;

    // =============================================================================
    // PROTOCOL AND EVENT VALIDATION FUNCTIONS
    // =============================================================================

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
            PROTOCOL_AXIS: begin
                case (packet_type)
                    PktTypeError     : return 1'b1; // All 4-bit values valid for AXIS errors
                    PktTypeTimeout   : return 1'b1; // All 4-bit values valid for AXIS timeouts
                    PktTypeCompletion: return 1'b1; // All 4-bit values valid for AXIS completions
                    PktTypeCredit    : return 1'b1; // All 4-bit values valid for AXIS credits
                    PktTypeChannel   : return 1'b1; // All 4-bit values valid for AXIS channels
                    PktTypeStream    : return 1'b1; // All 4-bit values valid for AXIS streams
                    default          : return 1'b0; // Invalid packet type for AXIS
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
            PROTOCOL_ARB: begin
                case (packet_type)
                    PktTypeError     : return 1'b1; // All 4-bit values valid for ARB errors
                    PktTypeTimeout   : return 1'b1; // All 4-bit values valid for ARB timeouts
                    PktTypeCompletion: return 1'b1; // All 4-bit values valid for ARB completions
                    PktTypeThreshold : return 1'b1; // All 4-bit values valid for ARB thresholds
                    PktTypePerf      : return 1'b1; // All 4-bit values valid for ARB performance
                    PktTypeDebug     : return 1'b1; // All 4-bit values valid for ARB debug
                    default          : return 1'b0; // Invalid packet type for ARB
                endcase
            end
            default: return 1'b0; // Unknown protocol
        endcase
    endfunction

    // =============================================================================
    // HUMAN-READABLE STRING FUNCTIONS FOR DEBUGGING
    // =============================================================================

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
            AXI_ERR_RESERVED_D         : return "RESERVED_D";
            AXI_ERR_RESERVED_E         : return "RESERVED_E";
            AXI_ERR_USER_DEFINED       : return "USER_DEFINED";
            default                    : return "UNKNOWN_AXI_ERROR";
        endcase
    endfunction

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
            PROTOCOL_AXIS  : return "AXIS";
            PROTOCOL_APB   : return "APB";
            PROTOCOL_ARB   : return "ARB";
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
                            AXI_ERR_RESERVED_D         : base_name = "RESERVED_D";
                            AXI_ERR_RESERVED_E         : base_name = "RESERVED_E";
                            AXI_ERR_USER_DEFINED       : base_name = "USER_DEFINED";
                            default                    : base_name = $sformatf("UNKNOWN_ERR_%0X", event_code);
                        endcase
                    end
                    PktTypeTimeout: begin
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
                    // Add other AXI packet types as needed...
                    default: base_name = $sformatf("AXI_PKT_%0X_EVENT_%0X", packet_type, event_code);
                endcase
            end

            PROTOCOL_APB: begin
                case (packet_type)
                    PktTypeError: begin
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
                    PktTypeTimeout: begin
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
                    default: base_name = $sformatf("APB_PKT_%0X_EVENT_%0X", packet_type, event_code);
                endcase
            end

            PROTOCOL_AXIS: begin
                case (packet_type)
                    PktTypeError: begin
                        case (axis_error_code_t'(event_code))
                            AXIS_ERR_PROTOCOL          : base_name = "PROTOCOL";
                            AXIS_ERR_READY_TIMING      : base_name = "READY_TIMING";
                            AXIS_ERR_VALID_TIMING      : base_name = "VALID_TIMING";
                            AXIS_ERR_LAST_MISSING      : base_name = "LAST_MISSING";
                            AXIS_ERR_LAST_ORPHAN       : base_name = "LAST_ORPHAN";
                            AXIS_ERR_STRB_INVALID      : base_name = "STRB_INVALID";
                            AXIS_ERR_KEEP_INVALID      : base_name = "KEEP_INVALID";
                            AXIS_ERR_DATA_ALIGNMENT    : base_name = "DATA_ALIGNMENT";
                            AXIS_ERR_ID_VIOLATION      : base_name = "ID_VIOLATION";
                            AXIS_ERR_DEST_VIOLATION    : base_name = "DEST_VIOLATION";
                            AXIS_ERR_USER_VIOLATION    : base_name = "USER_VIOLATION";
                            AXIS_ERR_USER_DEFINED      : base_name = "USER_DEFINED";
                            default                    : base_name = $sformatf("UNKNOWN_AXIS_ERR_%0X", event_code);
                        endcase
                    end
                    PktTypeTimeout: begin
                        case (axis_timeout_code_t'(event_code))
                            AXIS_TIMEOUT_HANDSHAKE     : base_name = "HANDSHAKE";
                            AXIS_TIMEOUT_STREAM        : base_name = "STREAM";
                            AXIS_TIMEOUT_PACKET        : base_name = "PACKET";
                            AXIS_TIMEOUT_BACKPRESSURE  : base_name = "BACKPRESSURE";
                            AXIS_TIMEOUT_BUFFER        : base_name = "BUFFER";
                            AXIS_TIMEOUT_STALL         : base_name = "STALL";
                            AXIS_TIMEOUT_USER_DEFINED  : base_name = "USER_DEFINED";
                            default                    : base_name = $sformatf("UNKNOWN_AXIS_TIMEOUT_%0X", event_code);
                        endcase
                    end
                    // Add other AXIS packet types as needed...
                    default: base_name = $sformatf("AXIS_PKT_%0X_EVENT_%0X", packet_type, event_code);
                endcase
            end

            PROTOCOL_ARB: begin
                case (packet_type)
                    PktTypeError: begin
                        case (arb_error_code_t'(event_code))
                            ARB_ERR_STARVATION        : base_name = "STARVATION";
                            ARB_ERR_ACK_TIMEOUT       : base_name = "ACK_TIMEOUT";
                            ARB_ERR_PROTOCOL_VIOLATION : base_name = "PROTOCOL_VIOLATION";
                            ARB_ERR_CREDIT_VIOLATION  : base_name = "CREDIT_VIOLATION";
                            ARB_ERR_FAIRNESS_VIOLATION : base_name = "FAIRNESS_VIOLATION";
                            ARB_ERR_WEIGHT_UNDERFLOW  : base_name = "WEIGHT_UNDERFLOW";
                            ARB_ERR_CONCURRENT_GRANTS : base_name = "CONCURRENT_GRANTS";
                            ARB_ERR_INVALID_GRANT_ID  : base_name = "INVALID_GRANT_ID";
                            ARB_ERR_ORPHAN_ACK        : base_name = "ORPHAN_ACK";
                            ARB_ERR_GRANT_OVERLAP     : base_name = "GRANT_OVERLAP";
                            ARB_ERR_MASK_ERROR        : base_name = "MASK_ERROR";
                            ARB_ERR_STATE_MACHINE     : base_name = "STATE_MACHINE";
                            ARB_ERR_CONFIGURATION     : base_name = "CONFIGURATION";
                            ARB_ERR_USER_DEFINED      : base_name = "USER_DEFINED";
                            default                   : base_name = $sformatf("UNKNOWN_ARB_ERR_%0X", event_code);
                        endcase
                    end
                    PktTypeTimeout: begin
                        case (arb_timeout_code_t'(event_code))
                            ARB_TIMEOUT_GRANT_ACK     : base_name = "GRANT_ACK";
                            ARB_TIMEOUT_REQUEST_HOLD  : base_name = "REQUEST_HOLD";
                            ARB_TIMEOUT_WEIGHT_UPDATE : base_name = "WEIGHT_UPDATE";
                            ARB_TIMEOUT_BLOCK_RELEASE : base_name = "BLOCK_RELEASE";
                            ARB_TIMEOUT_CREDIT_UPDATE : base_name = "CREDIT_UPDATE";
                            ARB_TIMEOUT_STATE_CHANGE  : base_name = "STATE_CHANGE";
                            ARB_TIMEOUT_USER_DEFINED  : base_name = "USER_DEFINED";
                            default                   : base_name = $sformatf("UNKNOWN_ARB_TIMEOUT_%0X", event_code);
                        endcase
                    end
                    PktTypeCompletion: begin
                        case (arb_completion_code_t'(event_code))
                            ARB_COMPL_GRANT_ISSUED    : base_name = "GRANT_ISSUED";
                            ARB_COMPL_ACK_RECEIVED    : base_name = "ACK_RECEIVED";
                            ARB_COMPL_TRANSACTION     : base_name = "TRANSACTION";
                            ARB_COMPL_WEIGHT_UPDATE   : base_name = "WEIGHT_UPDATE";
                            ARB_COMPL_CREDIT_CYCLE    : base_name = "CREDIT_CYCLE";
                            ARB_COMPL_FAIRNESS_PERIOD : base_name = "FAIRNESS_PERIOD";
                            ARB_COMPL_BLOCK_PERIOD    : base_name = "BLOCK_PERIOD";
                            ARB_COMPL_USER_DEFINED    : base_name = "USER_DEFINED";
                            default                   : base_name = $sformatf("UNKNOWN_ARB_COMPL_%0X", event_code);
                        endcase
                    end
                    PktTypeThreshold: begin
                        case (arb_threshold_code_t'(event_code))
                            ARB_THRESH_REQUEST_LATENCY : base_name = "REQUEST_LATENCY";
                            ARB_THRESH_ACK_LATENCY     : base_name = "ACK_LATENCY";
                            ARB_THRESH_FAIRNESS_DEV    : base_name = "FAIRNESS_DEV";
                            ARB_THRESH_ACTIVE_REQUESTS : base_name = "ACTIVE_REQUESTS";
                            ARB_THRESH_GRANT_RATE      : base_name = "GRANT_RATE";
                            ARB_THRESH_EFFICIENCY      : base_name = "EFFICIENCY";
                            ARB_THRESH_CREDIT_LOW      : base_name = "CREDIT_LOW";
                            ARB_THRESH_WEIGHT_IMBALANCE : base_name = "WEIGHT_IMBALANCE";
                            ARB_THRESH_STARVATION_TIME : base_name = "STARVATION_TIME";
                            ARB_THRESH_USER_DEFINED    : base_name = "USER_DEFINED";
                            default                   : base_name = $sformatf("UNKNOWN_ARB_THRESH_%0X", event_code);
                        endcase
                    end
                    PktTypePerf: begin
                        case (arb_performance_code_t'(event_code))
                            ARB_PERF_GRANT_ISSUED     : base_name = "GRANT_ISSUED";
                            ARB_PERF_ACK_RECEIVED     : base_name = "ACK_RECEIVED";
                            ARB_PERF_GRANT_EFFICIENCY : base_name = "GRANT_EFFICIENCY";
                            ARB_PERF_FAIRNESS_METRIC  : base_name = "FAIRNESS_METRIC";
                            ARB_PERF_THROUGHPUT       : base_name = "THROUGHPUT";
                            ARB_PERF_LATENCY_AVG      : base_name = "LATENCY_AVG";
                            ARB_PERF_WEIGHT_COMPLIANCE : base_name = "WEIGHT_COMPLIANCE";
                            ARB_PERF_CREDIT_UTILIZATION : base_name = "CREDIT_UTILIZATION";
                            ARB_PERF_CLIENT_ACTIVITY  : base_name = "CLIENT_ACTIVITY";
                            ARB_PERF_STARVATION_COUNT : base_name = "STARVATION_COUNT";
                            ARB_PERF_BLOCK_EFFICIENCY : base_name = "BLOCK_EFFICIENCY";
                            ARB_PERF_USER_DEFINED     : base_name = "USER_DEFINED";
                            default                   : base_name = $sformatf("UNKNOWN_ARB_PERF_%0X", event_code);
                        endcase
                    end
                    PktTypeDebug: begin
                        case (arb_debug_code_t'(event_code))
                            ARB_DEBUG_STATE_CHANGE    : base_name = "STATE_CHANGE";
                            ARB_DEBUG_MASK_UPDATE     : base_name = "MASK_UPDATE";
                            ARB_DEBUG_WEIGHT_CHANGE   : base_name = "WEIGHT_CHANGE";
                            ARB_DEBUG_CREDIT_UPDATE   : base_name = "CREDIT_UPDATE";
                            ARB_DEBUG_CLIENT_MASK     : base_name = "CLIENT_MASK";
                            ARB_DEBUG_PRIORITY_CHANGE : base_name = "PRIORITY_CHANGE";
                            ARB_DEBUG_BLOCK_EVENT     : base_name = "BLOCK_EVENT";
                            ARB_DEBUG_QUEUE_STATUS    : base_name = "QUEUE_STATUS";
                            ARB_DEBUG_COUNTER_SNAPSHOT : base_name = "COUNTER_SNAPSHOT";
                            ARB_DEBUG_FIFO_STATUS     : base_name = "FIFO_STATUS";
                            ARB_DEBUG_FAIRNESS_STATE  : base_name = "FAIRNESS_STATE";
                            ARB_DEBUG_ACK_STATE       : base_name = "ACK_STATE";
                            ARB_DEBUG_USER_DEFINED    : base_name = "USER_DEFINED";
                            default                   : base_name = $sformatf("UNKNOWN_ARB_DEBUG_%0X", event_code);
                        endcase
                    end
                    default: base_name = $sformatf("ARB_PKT_%0X_EVENT_%0X", packet_type, event_code);
                endcase
            end

            default: base_name = $sformatf("UNKNOWN_PROTO_%0X_PKT_%0X_EVENT_%0X", protocol, packet_type, event_code);
        endcase

        return base_name;
    endfunction

    // Complete packet formatting function for human-readable output
    function automatic string format_monitor_packet(monitor_packet_t pkt);
        protocol_type_t protocol = get_protocol_type(pkt);
        logic [3:0] packet_type = get_packet_type(pkt);
        logic [3:0] event_code = get_event_code(pkt);
        logic [7:0] agent_id = get_agent_id(pkt);
        logic [3:0] unit_id = get_unit_id(pkt);
        logic [5:0] channel_id = get_channel_id(pkt);
        logic [35:0] event_data = get_event_data(pkt);

        string protocol_str = get_protocol_name(protocol);
        string packet_type_str = get_packet_type_name(packet_type);
        string event_name = get_event_name(packet_type, protocol, event_code);

        return $sformatf("[%s_%s] %s | Agent:%02X Unit:%X Ch:%02X | Data:%09X",
                        protocol_str, packet_type_str, event_name,
                        agent_id, unit_id, channel_id, event_data);
    endfunction

    // =============================================================================
    // AXI MONITOR TRANSACTION STRUCTURE AND LEGACY EVENT CONSTANTS
    // =============================================================================
    // Added for compatibility with existing AXI monitor RTL

    // Transaction state enumeration for AXI monitoring (must be defined first)
    typedef enum logic [2:0] {
        TRANS_IDLE       = 3'h0,  // Transaction slot is idle/free
        TRANS_ADDR_PHASE = 3'h1,  // Address phase in progress
        TRANS_DATA_PHASE = 3'h2,  // Data phase in progress
        TRANS_COMPLETE   = 3'h3,  // Transaction completed successfully
        TRANS_ERROR      = 3'h4,  // Transaction has error
        TRANS_ORPHANED   = 3'h5   // Orphaned transaction (no matching phase)
    } transaction_state_t;

    // Event code union for different protocols
    typedef union packed {
        axi_error_code_t      axi_error;
        axi_timeout_code_t    axi_timeout;
        axi_completion_code_t axi_completion;
        axi_threshold_code_t  axi_threshold;
        axi_performance_code_t axi_performance;
        logic [3:0]           raw_code;
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

    // Legacy event constants for backward compatibility - use proper enums
    localparam logic [3:0] EVT_NONE                    = 4'h0;  // No event (generic)
    localparam axi_timeout_code_t EVT_CMD_TIMEOUT      = AXI_TIMEOUT_CMD;
    localparam axi_timeout_code_t EVT_DATA_TIMEOUT     = AXI_TIMEOUT_DATA;
    localparam axi_timeout_code_t EVT_RESP_TIMEOUT     = AXI_TIMEOUT_RESP;
    localparam axi_completion_code_t EVT_TRANS_COMPLETE = AXI_COMPL_TRANS_COMPLETE;
    localparam axi_error_code_t EVT_RESP_SLVERR        = AXI_ERR_RESP_SLVERR;
    localparam axi_error_code_t EVT_RESP_DECERR        = AXI_ERR_RESP_DECERR;
    localparam axi_error_code_t EVT_DATA_ORPHAN        = AXI_ERR_DATA_ORPHAN;
    localparam axi_error_code_t EVT_RESP_ORPHAN        = AXI_ERR_RESP_ORPHAN;
    localparam axi_error_code_t EVT_PROTOCOL           = AXI_ERR_PROTOCOL;

endpackage : monitor_pkg
