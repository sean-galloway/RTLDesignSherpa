// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monitor_pkg
// Purpose: Unified monitor package - backward compatibility wrapper
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18
// Modified: 2025-12-21 - Split into protocol-specific packages

`timescale 1ns / 1ps
/**
 * Monitor Bus Type Definitions - Unified Package
 *
 * This package provides backward compatibility by importing and re-exporting
 * all types from the split protocol-specific packages:
 *
 * - monitor_common_pkg:   Common types, packet structure, helper functions
 * - monitor_amba4_pkg:    AXI4, APB4, AXIS4 event codes
 * - monitor_amba5_pkg:    AXI5, APB5, AXIS5 extended event codes
 * - monitor_arbiter_pkg:  ARB and CORE event codes
 *
 * Existing code using `import monitor_pkg::*;` will continue to work unchanged.
 *
 * Key Design Principle:
 * For each protocol, each packet type has exactly 16 event codes (4 bits).
 * This creates a clean categorization where:
 * - packet_type [63:60] defines the category (error, timeout, completion, etc.)
 * - protocol [59:57] defines which protocol (AXI, AXIS, APB, ARB, CORE)
 * - event_code [56:53] defines the specific event within that category
 */
package monitor_pkg;

    // Import all protocol-specific packages
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
    import monitor_amba5_pkg::*;
    import monitor_arbiter_pkg::*;

    // =============================================================================
    // RE-EXPORT COMMON TYPES FROM monitor_common_pkg
    // =============================================================================

    // Protocol type enumeration
    typedef monitor_common_pkg::protocol_type_t protocol_type_t;

    // NOTE: Packet type constants are available via `import monitor_common_pkg::*;`
    // in consuming modules. The wildcard import brings PktTypeError, PktTypeCompletion, etc.

    // Monitor packet type
    typedef monitor_common_pkg::monitor_packet_t monitor_packet_t;

    // Common state types
    typedef monitor_common_pkg::axis_transfer_type_t axis_transfer_type_t;
    typedef monitor_common_pkg::axis_handshake_state_t axis_handshake_state_t;
    typedef monitor_common_pkg::apb_phase_t apb_phase_t;
    typedef monitor_common_pkg::apb_prot_type_t apb_prot_type_t;
    typedef monitor_common_pkg::arb_type_t arb_type_t;
    typedef monitor_common_pkg::arb_state_t arb_state_t;
    typedef monitor_common_pkg::transaction_state_t transaction_state_t;

    // =============================================================================
    // RE-EXPORT AMBA4 TYPES FROM monitor_amba4_pkg
    // =============================================================================

    // AXI event codes
    typedef monitor_amba4_pkg::axi_error_code_t axi_error_code_t;
    typedef monitor_amba4_pkg::axi_timeout_code_t axi_timeout_code_t;
    typedef monitor_amba4_pkg::axi_completion_code_t axi_completion_code_t;
    typedef monitor_amba4_pkg::axi_threshold_code_t axi_threshold_code_t;
    typedef monitor_amba4_pkg::axi_performance_code_t axi_performance_code_t;
    typedef monitor_amba4_pkg::axi_addr_match_code_t axi_addr_match_code_t;
    typedef monitor_amba4_pkg::axi_debug_code_t axi_debug_code_t;

    // APB event codes
    typedef monitor_amba4_pkg::apb_error_code_t apb_error_code_t;
    typedef monitor_amba4_pkg::apb_timeout_code_t apb_timeout_code_t;
    typedef monitor_amba4_pkg::apb_completion_code_t apb_completion_code_t;
    typedef monitor_amba4_pkg::apb_threshold_code_t apb_threshold_code_t;
    typedef monitor_amba4_pkg::apb_performance_code_t apb_performance_code_t;
    typedef monitor_amba4_pkg::apb_debug_code_t apb_debug_code_t;

    // AXIS event codes
    typedef monitor_amba4_pkg::axis_error_code_t axis_error_code_t;
    typedef monitor_amba4_pkg::axis_timeout_code_t axis_timeout_code_t;
    typedef monitor_amba4_pkg::axis_completion_code_t axis_completion_code_t;
    typedef monitor_amba4_pkg::axis_credit_code_t axis_credit_code_t;
    typedef monitor_amba4_pkg::axis_channel_code_t axis_channel_code_t;
    typedef monitor_amba4_pkg::axis_stream_code_t axis_stream_code_t;

    // Unified event code union and transaction structure
    typedef monitor_amba4_pkg::unified_event_code_t unified_event_code_t;
    typedef monitor_amba4_pkg::event_code_union_t event_code_union_t;
    typedef monitor_amba4_pkg::bus_transaction_t bus_transaction_t;

    // NOTE: Legacy event constants (EVT_NONE, EVT_CMD_TIMEOUT, etc.) are available
    // via `import monitor_amba4_pkg::*;` in consuming modules.

    // =============================================================================
    // RE-EXPORT AMBA5 TYPES FROM monitor_amba5_pkg
    // =============================================================================

    // AXI5 event codes
    typedef monitor_amba5_pkg::axi5_atomic_code_t axi5_atomic_code_t;
    typedef monitor_amba5_pkg::axi5_trace_code_t axi5_trace_code_t;

    // APB5 event codes
    typedef monitor_amba5_pkg::apb5_wakeup_code_t apb5_wakeup_code_t;
    typedef monitor_amba5_pkg::apb5_parity_code_t apb5_parity_code_t;
    typedef monitor_amba5_pkg::apb5_user_code_t apb5_user_code_t;

    // AXIS5 event codes
    typedef monitor_amba5_pkg::axis5_wakeup_code_t axis5_wakeup_code_t;
    typedef monitor_amba5_pkg::axis5_parity_code_t axis5_parity_code_t;
    typedef monitor_amba5_pkg::axis5_crc_code_t axis5_crc_code_t;

    // AMBA5 unified event code
    typedef monitor_amba5_pkg::amba5_event_code_t amba5_event_code_t;

    // =============================================================================
    // RE-EXPORT ARBITER TYPES FROM monitor_arbiter_pkg
    // =============================================================================

    // ARB event codes
    typedef monitor_arbiter_pkg::arb_error_code_t arb_error_code_t;
    typedef monitor_arbiter_pkg::arb_timeout_code_t arb_timeout_code_t;
    typedef monitor_arbiter_pkg::arb_completion_code_t arb_completion_code_t;
    typedef monitor_arbiter_pkg::arb_threshold_code_t arb_threshold_code_t;
    typedef monitor_arbiter_pkg::arb_performance_code_t arb_performance_code_t;
    typedef monitor_arbiter_pkg::arb_debug_code_t arb_debug_code_t;

    // CORE event codes
    typedef monitor_arbiter_pkg::core_error_code_t core_error_code_t;
    typedef monitor_arbiter_pkg::core_timeout_code_t core_timeout_code_t;
    typedef monitor_arbiter_pkg::core_completion_code_t core_completion_code_t;
    typedef monitor_arbiter_pkg::core_threshold_code_t core_threshold_code_t;
    typedef monitor_arbiter_pkg::core_performance_code_t core_performance_code_t;
    typedef monitor_arbiter_pkg::core_debug_code_t core_debug_code_t;

    // ARB/CORE unified event code
    typedef monitor_arbiter_pkg::arb_core_event_code_t arb_core_event_code_t;

    // =============================================================================
    // HELPER FUNCTIONS - DELEGATE TO APPROPRIATE PACKAGE
    // =============================================================================

    // Packet manipulation functions (from common)
    function automatic logic [3:0] get_packet_type(monitor_packet_t pkt);
        return monitor_common_pkg::get_packet_type(pkt);
    endfunction

    function automatic protocol_type_t get_protocol_type(monitor_packet_t pkt);
        return monitor_common_pkg::get_protocol_type(pkt);
    endfunction

    function automatic logic [3:0] get_event_code(monitor_packet_t pkt);
        return monitor_common_pkg::get_event_code(pkt);
    endfunction

    function automatic logic [5:0] get_channel_id(monitor_packet_t pkt);
        return monitor_common_pkg::get_channel_id(pkt);
    endfunction

    function automatic logic [3:0] get_unit_id(monitor_packet_t pkt);
        return monitor_common_pkg::get_unit_id(pkt);
    endfunction

    function automatic logic [7:0] get_agent_id(monitor_packet_t pkt);
        return monitor_common_pkg::get_agent_id(pkt);
    endfunction

    function automatic logic [34:0] get_event_data(monitor_packet_t pkt);
        return monitor_common_pkg::get_event_data(pkt);
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
        return monitor_common_pkg::create_monitor_packet(
            packet_type, protocol, event_code, channel_id, unit_id, agent_id, event_data
        );
    endfunction

    // String functions (from common)
    function automatic string get_packet_type_name(logic [3:0] pkt_type);
        return monitor_common_pkg::get_packet_type_name(pkt_type);
    endfunction

    function automatic string get_protocol_name(protocol_type_t protocol);
        return monitor_common_pkg::get_protocol_name(protocol);
    endfunction

    // AMBA4 string functions
    function automatic string get_axi_error_name(axi_error_code_t code);
        return monitor_amba4_pkg::get_axi_error_name(code);
    endfunction

    // Arbiter string functions
    function automatic string get_arb_error_name(arb_error_code_t code);
        return monitor_arbiter_pkg::get_arb_error_name(code);
    endfunction

    function automatic string get_core_error_name(core_error_code_t code);
        return monitor_arbiter_pkg::get_core_error_name(code);
    endfunction

    // AMBA5 string functions
    function automatic string get_apb5_wakeup_name(apb5_wakeup_code_t code);
        return monitor_amba5_pkg::get_apb5_wakeup_name(code);
    endfunction

    function automatic string get_apb5_parity_name(apb5_parity_code_t code);
        return monitor_amba5_pkg::get_apb5_parity_name(code);
    endfunction

    function automatic string get_axis5_wakeup_name(axis5_wakeup_code_t code);
        return monitor_amba5_pkg::get_axis5_wakeup_name(code);
    endfunction

    function automatic string get_axis5_crc_name(axis5_crc_code_t code);
        return monitor_amba5_pkg::get_axis5_crc_name(code);
    endfunction

    // =============================================================================
    // EVENT CODE CREATION FUNCTIONS - DELEGATE TO APPROPRIATE PACKAGE
    // =============================================================================

    // AXI event code creation (from amba4)
    function automatic unified_event_code_t create_axi_error_event(axi_error_code_t code);
        return monitor_amba4_pkg::create_axi_error_event(code);
    endfunction

    function automatic unified_event_code_t create_axi_timeout_event(axi_timeout_code_t code);
        return monitor_amba4_pkg::create_axi_timeout_event(code);
    endfunction

    function automatic unified_event_code_t create_axi_completion_event(axi_completion_code_t code);
        return monitor_amba4_pkg::create_axi_completion_event(code);
    endfunction

    function automatic unified_event_code_t create_axi_threshold_event(axi_threshold_code_t code);
        return monitor_amba4_pkg::create_axi_threshold_event(code);
    endfunction

    function automatic unified_event_code_t create_axi_performance_event(axi_performance_code_t code);
        return monitor_amba4_pkg::create_axi_performance_event(code);
    endfunction

    function automatic unified_event_code_t create_axi_addr_match_event(axi_addr_match_code_t code);
        return monitor_amba4_pkg::create_axi_addr_match_event(code);
    endfunction

    function automatic unified_event_code_t create_axi_debug_event(axi_debug_code_t code);
        return monitor_amba4_pkg::create_axi_debug_event(code);
    endfunction

    // APB event code creation (from amba4)
    function automatic unified_event_code_t create_apb_error_event(apb_error_code_t code);
        return monitor_amba4_pkg::create_apb_error_event(code);
    endfunction

    function automatic unified_event_code_t create_apb_timeout_event(apb_timeout_code_t code);
        return monitor_amba4_pkg::create_apb_timeout_event(code);
    endfunction

    function automatic unified_event_code_t create_apb_completion_event(apb_completion_code_t code);
        return monitor_amba4_pkg::create_apb_completion_event(code);
    endfunction

    function automatic unified_event_code_t create_apb_threshold_event(apb_threshold_code_t code);
        return monitor_amba4_pkg::create_apb_threshold_event(code);
    endfunction

    function automatic unified_event_code_t create_apb_performance_event(apb_performance_code_t code);
        return monitor_amba4_pkg::create_apb_performance_event(code);
    endfunction

    function automatic unified_event_code_t create_apb_debug_event(apb_debug_code_t code);
        return monitor_amba4_pkg::create_apb_debug_event(code);
    endfunction

    // AXIS event code creation (from amba4)
    function automatic unified_event_code_t create_axis_error_event(axis_error_code_t code);
        return monitor_amba4_pkg::create_axis_error_event(code);
    endfunction

    function automatic unified_event_code_t create_axis_timeout_event(axis_timeout_code_t code);
        return monitor_amba4_pkg::create_axis_timeout_event(code);
    endfunction

    function automatic unified_event_code_t create_axis_completion_event(axis_completion_code_t code);
        return monitor_amba4_pkg::create_axis_completion_event(code);
    endfunction

    function automatic unified_event_code_t create_axis_credit_event(axis_credit_code_t code);
        return monitor_amba4_pkg::create_axis_credit_event(code);
    endfunction

    function automatic unified_event_code_t create_axis_channel_event(axis_channel_code_t code);
        return monitor_amba4_pkg::create_axis_channel_event(code);
    endfunction

    function automatic unified_event_code_t create_axis_stream_event(axis_stream_code_t code);
        return monitor_amba4_pkg::create_axis_stream_event(code);
    endfunction

    // ARB event code creation (from arbiter)
    function automatic arb_core_event_code_t create_arb_error_event(arb_error_code_t code);
        return monitor_arbiter_pkg::create_arb_error_event(code);
    endfunction

    function automatic arb_core_event_code_t create_arb_timeout_event(arb_timeout_code_t code);
        return monitor_arbiter_pkg::create_arb_timeout_event(code);
    endfunction

    function automatic arb_core_event_code_t create_arb_completion_event(arb_completion_code_t code);
        return monitor_arbiter_pkg::create_arb_completion_event(code);
    endfunction

    function automatic arb_core_event_code_t create_arb_threshold_event(arb_threshold_code_t code);
        return monitor_arbiter_pkg::create_arb_threshold_event(code);
    endfunction

    function automatic arb_core_event_code_t create_arb_performance_event(arb_performance_code_t code);
        return monitor_arbiter_pkg::create_arb_performance_event(code);
    endfunction

    function automatic arb_core_event_code_t create_arb_debug_event(arb_debug_code_t code);
        return monitor_arbiter_pkg::create_arb_debug_event(code);
    endfunction

    // AMBA5 event code creation (from amba5)
    function automatic amba5_event_code_t create_axi5_atomic_event(axi5_atomic_code_t code);
        return monitor_amba5_pkg::create_axi5_atomic_event(code);
    endfunction

    function automatic amba5_event_code_t create_axi5_trace_event(axi5_trace_code_t code);
        return monitor_amba5_pkg::create_axi5_trace_event(code);
    endfunction

    function automatic amba5_event_code_t create_apb5_wakeup_event(apb5_wakeup_code_t code);
        return monitor_amba5_pkg::create_apb5_wakeup_event(code);
    endfunction

    function automatic amba5_event_code_t create_apb5_parity_event(apb5_parity_code_t code);
        return monitor_amba5_pkg::create_apb5_parity_event(code);
    endfunction

    function automatic amba5_event_code_t create_apb5_user_event(apb5_user_code_t code);
        return monitor_amba5_pkg::create_apb5_user_event(code);
    endfunction

    function automatic amba5_event_code_t create_axis5_wakeup_event(axis5_wakeup_code_t code);
        return monitor_amba5_pkg::create_axis5_wakeup_event(code);
    endfunction

    function automatic amba5_event_code_t create_axis5_parity_event(axis5_parity_code_t code);
        return monitor_amba5_pkg::create_axis5_parity_event(code);
    endfunction

    function automatic amba5_event_code_t create_axis5_crc_event(axis5_crc_code_t code);
        return monitor_amba5_pkg::create_axis5_crc_event(code);
    endfunction

    // =============================================================================
    // VALIDATION FUNCTIONS
    // =============================================================================

    function automatic bit is_valid_event_for_packet_type(
        logic [3:0] packet_type,
        protocol_type_t protocol,
        logic [3:0] event_code
    );
        case (protocol)
            monitor_common_pkg::PROTOCOL_AXI,
            monitor_common_pkg::PROTOCOL_AXIS,
            monitor_common_pkg::PROTOCOL_APB:
                return monitor_amba4_pkg::is_valid_event_for_packet_type(packet_type, protocol, event_code);
            monitor_common_pkg::PROTOCOL_ARB,
            monitor_common_pkg::PROTOCOL_CORE:
                return monitor_arbiter_pkg::is_valid_arb_event_for_packet_type(packet_type, protocol, event_code);
            default:
                return 1'b0;
        endcase
    endfunction

    // =============================================================================
    // COMPREHENSIVE EVENT NAME FUNCTION
    // =============================================================================

    function automatic string get_event_name(
        logic [3:0] packet_type,
        protocol_type_t protocol,
        logic [3:0] event_code
    );
        string base_name;

        case (protocol)
            monitor_common_pkg::PROTOCOL_AXI: begin
                case (packet_type)
                    PktTypeError: begin
                        case (axi_error_code_t'(event_code))
                            monitor_amba4_pkg::AXI_ERR_RESP_SLVERR       : base_name = "RESP_SLVERR";
                            monitor_amba4_pkg::AXI_ERR_RESP_DECERR       : base_name = "RESP_DECERR";
                            monitor_amba4_pkg::AXI_ERR_DATA_ORPHAN       : base_name = "DATA_ORPHAN";
                            monitor_amba4_pkg::AXI_ERR_RESP_ORPHAN       : base_name = "RESP_ORPHAN";
                            monitor_amba4_pkg::AXI_ERR_PROTOCOL          : base_name = "PROTOCOL";
                            monitor_amba4_pkg::AXI_ERR_BURST_LENGTH      : base_name = "BURST_LENGTH";
                            monitor_amba4_pkg::AXI_ERR_BURST_SIZE        : base_name = "BURST_SIZE";
                            monitor_amba4_pkg::AXI_ERR_BURST_TYPE        : base_name = "BURST_TYPE";
                            monitor_amba4_pkg::AXI_ERR_ID_COLLISION      : base_name = "ID_COLLISION";
                            monitor_amba4_pkg::AXI_ERR_WRITE_BEFORE_ADDR : base_name = "WRITE_BEFORE_ADDR";
                            monitor_amba4_pkg::AXI_ERR_RESP_BEFORE_DATA  : base_name = "RESP_BEFORE_DATA";
                            monitor_amba4_pkg::AXI_ERR_LAST_MISSING      : base_name = "LAST_MISSING";
                            monitor_amba4_pkg::AXI_ERR_STROBE_ERROR      : base_name = "STROBE_ERROR";
                            monitor_amba4_pkg::AXI_ERR_USER_DEFINED      : base_name = "USER_DEFINED";
                            default                                      : base_name = $sformatf("UNKNOWN_ERR_%0X", event_code);
                        endcase
                    end
                    PktTypeTimeout: begin
                        case (axi_timeout_code_t'(event_code))
                            monitor_amba4_pkg::AXI_TIMEOUT_CMD          : base_name = "CMD";
                            monitor_amba4_pkg::AXI_TIMEOUT_DATA         : base_name = "DATA";
                            monitor_amba4_pkg::AXI_TIMEOUT_RESP         : base_name = "RESP";
                            monitor_amba4_pkg::AXI_TIMEOUT_HANDSHAKE    : base_name = "HANDSHAKE";
                            monitor_amba4_pkg::AXI_TIMEOUT_BURST        : base_name = "BURST";
                            monitor_amba4_pkg::AXI_TIMEOUT_EXCLUSIVE    : base_name = "EXCLUSIVE";
                            monitor_amba4_pkg::AXI_TIMEOUT_USER_DEFINED : base_name = "USER_DEFINED";
                            default                                      : base_name = $sformatf("UNKNOWN_TIMEOUT_%0X", event_code);
                        endcase
                    end
                    default: base_name = $sformatf("AXI_PKT_%0X_EVENT_%0X", packet_type, event_code);
                endcase
            end

            monitor_common_pkg::PROTOCOL_APB: begin
                case (packet_type)
                    PktTypeError: begin
                        case (apb_error_code_t'(event_code))
                            monitor_amba4_pkg::APB_ERR_PSLVERR          : base_name = "PSLVERR";
                            monitor_amba4_pkg::APB_ERR_SETUP_VIOLATION  : base_name = "SETUP_VIOLATION";
                            monitor_amba4_pkg::APB_ERR_ACCESS_VIOLATION : base_name = "ACCESS_VIOLATION";
                            monitor_amba4_pkg::APB_ERR_STROBE_ERROR     : base_name = "STROBE_ERROR";
                            monitor_amba4_pkg::APB_ERR_ADDR_DECODE      : base_name = "ADDR_DECODE";
                            monitor_amba4_pkg::APB_ERR_PROT_VIOLATION   : base_name = "PROT_VIOLATION";
                            monitor_amba4_pkg::APB_ERR_ENABLE_ERROR     : base_name = "ENABLE_ERROR";
                            monitor_amba4_pkg::APB_ERR_READY_ERROR      : base_name = "READY_ERROR";
                            monitor_amba4_pkg::APB_ERR_USER_DEFINED     : base_name = "USER_DEFINED";
                            default                                      : base_name = $sformatf("UNKNOWN_APB_ERR_%0X", event_code);
                        endcase
                    end
                    default: base_name = $sformatf("APB_PKT_%0X_EVENT_%0X", packet_type, event_code);
                endcase
            end

            monitor_common_pkg::PROTOCOL_AXIS: begin
                case (packet_type)
                    PktTypeError: begin
                        case (axis_error_code_t'(event_code))
                            monitor_amba4_pkg::AXIS_ERR_PROTOCOL       : base_name = "PROTOCOL";
                            monitor_amba4_pkg::AXIS_ERR_READY_TIMING   : base_name = "READY_TIMING";
                            monitor_amba4_pkg::AXIS_ERR_VALID_TIMING   : base_name = "VALID_TIMING";
                            monitor_amba4_pkg::AXIS_ERR_LAST_MISSING   : base_name = "LAST_MISSING";
                            monitor_amba4_pkg::AXIS_ERR_LAST_ORPHAN    : base_name = "LAST_ORPHAN";
                            monitor_amba4_pkg::AXIS_ERR_STRB_INVALID   : base_name = "STRB_INVALID";
                            monitor_amba4_pkg::AXIS_ERR_KEEP_INVALID   : base_name = "KEEP_INVALID";
                            monitor_amba4_pkg::AXIS_ERR_DATA_ALIGNMENT : base_name = "DATA_ALIGNMENT";
                            monitor_amba4_pkg::AXIS_ERR_ID_VIOLATION   : base_name = "ID_VIOLATION";
                            monitor_amba4_pkg::AXIS_ERR_DEST_VIOLATION : base_name = "DEST_VIOLATION";
                            monitor_amba4_pkg::AXIS_ERR_USER_VIOLATION : base_name = "USER_VIOLATION";
                            monitor_amba4_pkg::AXIS_ERR_USER_DEFINED   : base_name = "USER_DEFINED";
                            default                                     : base_name = $sformatf("UNKNOWN_AXIS_ERR_%0X", event_code);
                        endcase
                    end
                    default: base_name = $sformatf("AXIS_PKT_%0X_EVENT_%0X", packet_type, event_code);
                endcase
            end

            monitor_common_pkg::PROTOCOL_ARB: begin
                case (packet_type)
                    PktTypeError: begin
                        base_name = monitor_arbiter_pkg::get_arb_error_name(arb_error_code_t'(event_code));
                    end
                    default: base_name = $sformatf("ARB_PKT_%0X_EVENT_%0X", packet_type, event_code);
                endcase
            end

            monitor_common_pkg::PROTOCOL_CORE: begin
                case (packet_type)
                    PktTypeError: begin
                        base_name = monitor_arbiter_pkg::get_core_error_name(core_error_code_t'(event_code));
                    end
                    default: base_name = $sformatf("CORE_PKT_%0X_EVENT_%0X", packet_type, event_code);
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
        logic [34:0] event_data = get_event_data(pkt);

        string protocol_str = get_protocol_name(protocol);
        string packet_type_str = get_packet_type_name(packet_type);
        string event_name = get_event_name(packet_type, protocol, event_code);

        return $sformatf("[%s_%s] %s | Agent:%02X Unit:%X Ch:%02X | Data:%09X",
                        protocol_str, packet_type_str, event_name,
                        agent_id, unit_id, channel_id, event_data);
    endfunction

endpackage : monitor_pkg
