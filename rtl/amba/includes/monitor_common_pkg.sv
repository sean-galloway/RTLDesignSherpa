// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monitor_common_pkg
// Purpose: Common monitor bus types and functions shared across all protocols
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-21

`timescale 1ns / 1ps
/**
 * Monitor Bus Common Type Definitions
 *
 * This package defines common type definitions used across all monitoring
 * protocols including protocol type enumeration, packet type constants,
 * packet structure, and manipulation functions.
 *
 * Packet width is locked at 128 bits via MONBUS_PKT_WIDTH (this file).
 * Side-band timestamp width is locked at 64 bits via MONBUS_TS_WIDTH.
 * Neither is exposed as a per-module parameter — there's exactly one
 * packet format and one timestamp format in the codebase.
 */
package monitor_common_pkg;

    // -------------------------------------------------------------------------
    // Single source of truth: monitor bus packet + timestamp widths
    // -------------------------------------------------------------------------
    // ANY consumer that declares a bus or FIFO holding a packet MUST reference
    // these localparams, not hard-code 128 / 64. See MON-PKT-64-to-128-plan.md.
    localparam int MONBUS_PKT_WIDTH = 128;
    localparam int MONBUS_TS_WIDTH  = 64;

    // Protocol type enumeration for multi-protocol support
    // 4 bits — 16 protocols max
    typedef enum logic [3:0] {
        PROTOCOL_AXI    = 4'h0,
        PROTOCOL_AXIS   = 4'h1,  // AXI4-Stream
        PROTOCOL_APB    = 4'h2,  // Advanced Peripheral Bus
        PROTOCOL_ARB    = 4'h3,  // Arbiter specific packets
        PROTOCOL_CORE   = 4'h4   // Core specific packets
    } protocol_type_t;

    // Monitor bus packet types (used in packet_type field [127:124])
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
    // PerfWin: window-aggregate performance — cycle buckets, byte/beat
    //   counters. One packet per metric, emitted on window close. See
    //   rtl/amba/PRD/RFCs/RFC-perfmon-window-buckets.md for event_code
    //   assignments per protocol package (e.g. AXI_PERFWIN_* enum).
    localparam logic [3:0] PktTypePerfWin    = 4'hD;
    // PerfHist: histogram bucket counts. event_code[7:4]=histogram select,
    //   event_code[3:0]=bucket index (0..15, log2 cycle thresholds).
    //   See RFC for full encoding.
    localparam logic [3:0] PktTypePerfHist   = 4'hE;
    localparam logic [3:0] PktTypeDebug      = 4'hF;  // Debug/trace event

    // =============================================================================
    // MONITOR PACKET STRUCTURE AND HELPER FUNCTIONS
    // =============================================================================

    // 128-bit monitor packet format:
    // [127:124] - packet_type:  4 bits (error, timeout, completion, etc.)
    // [123:109] - reserved:    15 bits (forward-compat slack)
    // [108:105] - protocol:     4 bits (AXI/AXIS/APB/ARB/CORE)
    // [104: 97] - event_code:   8 bits (specific error or event code)
    // [ 96: 88] - channel_id:   9 bits (channel ID and AXI ID)
    // [ 87: 72] - agent_id:    16 bits (module identifier)
    // [ 71: 64] - unit_id:      8 bits (subsystem identifier)
    // [ 63:  0] - event_data:  64 bits (event-specific data, full 64-bit address)
    typedef logic [MONBUS_PKT_WIDTH-1:0] monitor_packet_t;

    // Side-band timestamp paired with each packet through the arbiter to the
    // monbus_axil_group. Sampled by the wrapper at emission time.
    typedef logic [MONBUS_TS_WIDTH-1:0]  monbus_timestamp_t;

    // Helper functions for monitor packet manipulation
    function automatic logic [3:0] get_packet_type(monitor_packet_t pkt);
        return pkt[127:124];
    endfunction

    function automatic logic [14:0] get_reserved(monitor_packet_t pkt);
        return pkt[123:109];
    endfunction

    function automatic protocol_type_t get_protocol_type(monitor_packet_t pkt);
        return protocol_type_t'(pkt[108:105]);
    endfunction

    function automatic logic [7:0] get_event_code(monitor_packet_t pkt);
        return pkt[104:97];
    endfunction

    function automatic logic [8:0] get_channel_id(monitor_packet_t pkt);
        return pkt[96:88];
    endfunction

    function automatic logic [15:0] get_agent_id(monitor_packet_t pkt);
        return pkt[87:72];
    endfunction

    function automatic logic [7:0] get_unit_id(monitor_packet_t pkt);
        return pkt[71:64];
    endfunction

    function automatic logic [63:0] get_event_data(monitor_packet_t pkt);
        return pkt[63:0];
    endfunction

    function automatic monitor_packet_t create_monitor_packet(
        logic [3:0]     packet_type,
        protocol_type_t protocol,
        logic [7:0]     event_code,
        logic [8:0]     channel_id,
        logic [7:0]     unit_id,
        logic [15:0]    agent_id,
        logic [63:0]    event_data
    );
        // Layout: {packet_type[4], reserved[15], protocol[4], event_code[8],
        //         channel_id[9], agent_id[16], unit_id[8], event_data[64]}
        return {packet_type, 15'h0, protocol, event_code,
                channel_id, agent_id, unit_id, event_data};
    endfunction

    // =============================================================================
    // COMMON PROTOCOL AND PAYLOAD TYPES
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

    // Transaction state enumeration for AXI monitoring
    typedef enum logic [2:0] {
        TRANS_IDLE       = 3'h0,  // Transaction slot is idle/free
        TRANS_ADDR_PHASE = 3'h1,  // Address phase in progress
        TRANS_DATA_PHASE = 3'h2,  // Data phase in progress
        TRANS_COMPLETE   = 3'h3,  // Transaction completed successfully
        TRANS_ERROR      = 3'h4,  // Transaction has error
        TRANS_ORPHANED   = 3'h5   // Orphaned transaction (no matching phase)
    } transaction_state_t;

    // =============================================================================
    // COMMON STRING FUNCTIONS FOR DEBUGGING
    // =============================================================================

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
            PktTypePerfWin   : return "PERFWIN";
            PktTypePerfHist  : return "PERFHIST";
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
            PROTOCOL_CORE  : return "CORE";
            default        : return "UNKNOWN";
        endcase
    endfunction

endpackage : monitor_common_pkg
