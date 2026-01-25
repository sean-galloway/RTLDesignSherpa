//      // verilator_coverage annotation
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
         * Key Design Principle:
         * For each protocol, each packet type has exactly 16 event codes (4 bits).
         * This creates a clean categorization where:
         * - packet_type [63:60] defines the category (error, timeout, completion, etc.)
         * - protocol [59:57] defines which protocol (AXI, AXIS, APB, ARB, CORE)
         * - event_code [56:53] defines the specific event within that category
         */
        package monitor_common_pkg;
        
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
            // MONITOR PACKET STRUCTURE AND HELPER FUNCTIONS
            // =============================================================================
        
            // Enhanced 64-bit monitor packet format:
            // [63:60] - packet_type: 4 bits (error, timeout, completion, etc.)
            // [59:57] - protocol:    3 bits (AXI/AXIS/APB/ARB/CORE)
            // [56:53] - event_code:  4 bits (specific error or event code)
            // [52:47] - channel_id:  6 bits (channel ID and AXI ID)
            // [46:43] - unit_id:     4 bits (subsystem identifier)
            // [42:35] - agent_id:    8 bits (module identifier)
            // [34:0]  - event_data:  35 bits (event-specific data)
            typedef logic [63:0] monitor_packet_t;
        
            // Helper functions for monitor packet manipulation
 000010     function automatic logic [3:0] get_packet_type(monitor_packet_t pkt);
 000010         return pkt[63:60];
            endfunction
        
%000000     function automatic protocol_type_t get_protocol_type(monitor_packet_t pkt);
%000000         return protocol_type_t'(pkt[59:57]);
            endfunction
        
 000010     function automatic logic [3:0] get_event_code(monitor_packet_t pkt);
 000010         return pkt[56:53];
            endfunction
        
%000000     function automatic logic [5:0] get_channel_id(monitor_packet_t pkt);
%000000         return pkt[52:47];
            endfunction
        
%000000     function automatic logic [3:0] get_unit_id(monitor_packet_t pkt);
%000000         return pkt[46:43];
            endfunction
        
%000000     function automatic logic [7:0] get_agent_id(monitor_packet_t pkt);
%000000         return pkt[42:35];
            endfunction
        
 057102     function automatic logic [34:0] get_event_data(monitor_packet_t pkt);
 057102         return pkt[34:0];
            endfunction
        
 004326     function automatic monitor_packet_t create_monitor_packet(
                logic [3:0]     packet_type,
                protocol_type_t protocol,
                logic [3:0]     event_code,
                logic [5:0]     channel_id,
                logic [3:0]     unit_id,
                logic [7:0]     agent_id,
                logic [34:0]    event_data
            );
 004326         return {packet_type, protocol, event_code, channel_id, unit_id, agent_id, event_data};
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
        
%000000     function automatic string get_packet_type_name(logic [3:0] pkt_type);
%000000         case (pkt_type)
%000000             PktTypeError     : return "ERROR";
%000000             PktTypeCompletion: return "COMPLETION";
%000000             PktTypeThreshold : return "THRESHOLD";
%000000             PktTypeTimeout   : return "TIMEOUT";
%000000             PktTypePerf      : return "PERF";
%000000             PktTypeCredit    : return "CREDIT";
%000000             PktTypeChannel   : return "CHANNEL";
%000000             PktTypeStream    : return "STREAM";
%000000             PktTypeAddrMatch : return "ADDR_MATCH";
%000000             PktTypeAPB       : return "APB";
%000000             PktTypeDebug     : return "DEBUG";
%000000             default          : return "UNKNOWN";
                endcase
            endfunction
        
%000000     function automatic string get_protocol_name(protocol_type_t protocol);
%000000         case (protocol)
%000000             PROTOCOL_AXI   : return "AXI";
%000000             PROTOCOL_AXIS  : return "AXIS";
%000000             PROTOCOL_APB   : return "APB";
%000000             PROTOCOL_ARB   : return "ARB";
%000000             PROTOCOL_CORE  : return "CORE";
%000000             default        : return "UNKNOWN";
                endcase
            endfunction
        
        endpackage : monitor_common_pkg
        
