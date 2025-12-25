// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monitor_amba5_pkg
// Purpose: AMBA5 protocol extensions (AXI5, APB5, AXIS5)
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-12-21

`timescale 1ns / 1ps
/**
 * AMBA5 Protocol Event Code Extensions
 *
 * This package defines AMBA5-specific event codes that extend AMBA4:
 * - AXI5: Atomic operations, QoS extensions, trace
 * - APB5: Wake-up signaling, parity support, user signals
 * - AXIS5: Wake-up, parity, CRC support
 *
 * These event codes use the reserved slots in AMBA4 enums where possible,
 * or define new protocol-specific event types.
 */
package monitor_amba5_pkg;

    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;

    // =============================================================================
    // AXI5 EXTENDED EVENT CODES
    // =============================================================================

    // AXI5 Atomic Operation Events (extends AXI4 completion codes)
    typedef enum logic [3:0] {
        AXI5_ATOMIC_LOAD             = 4'h0,  // Atomic load operation
        AXI5_ATOMIC_SWAP             = 4'h1,  // Atomic swap operation
        AXI5_ATOMIC_COMPARE          = 4'h2,  // Atomic compare operation
        AXI5_ATOMIC_ADD              = 4'h3,  // Atomic add operation
        AXI5_ATOMIC_CLR              = 4'h4,  // Atomic clear operation
        AXI5_ATOMIC_XOR              = 4'h5,  // Atomic XOR operation
        AXI5_ATOMIC_SET              = 4'h6,  // Atomic set operation
        AXI5_ATOMIC_SMAX             = 4'h7,  // Atomic signed max
        AXI5_ATOMIC_SMIN             = 4'h8,  // Atomic signed min
        AXI5_ATOMIC_UMAX             = 4'h9,  // Atomic unsigned max
        AXI5_ATOMIC_UMIN             = 4'hA,  // Atomic unsigned min
        AXI5_ATOMIC_RESERVED_B       = 4'hB,  // Reserved
        AXI5_ATOMIC_RESERVED_C       = 4'hC,  // Reserved
        AXI5_ATOMIC_RESERVED_D       = 4'hD,  // Reserved
        AXI5_ATOMIC_RESERVED_E       = 4'hE,  // Reserved
        AXI5_ATOMIC_USER_DEFINED     = 4'hF   // User-defined atomic
    } axi5_atomic_code_t;

    // AXI5 QoS and Trace Events
    typedef enum logic [3:0] {
        AXI5_TRACE_START             = 4'h0,  // Trace session start
        AXI5_TRACE_END               = 4'h1,  // Trace session end
        AXI5_TRACE_DATA              = 4'h2,  // Trace data packet
        AXI5_QOS_ESCALATION          = 4'h3,  // QoS level escalation
        AXI5_QOS_DEESCALATION        = 4'h4,  // QoS level de-escalation
        AXI5_POISON_DETECTED         = 4'h5,  // Poison bit detected
        AXI5_LOOP_DETECTED           = 4'h6,  // Loop detection triggered
        AXI5_MPAM_EVENT              = 4'h7,  // MPAM partition event
        AXI5_RESERVED_8              = 4'h8,  // Reserved
        AXI5_RESERVED_9              = 4'h9,  // Reserved
        AXI5_RESERVED_A              = 4'hA,  // Reserved
        AXI5_RESERVED_B              = 4'hB,  // Reserved
        AXI5_RESERVED_C              = 4'hC,  // Reserved
        AXI5_RESERVED_D              = 4'hD,  // Reserved
        AXI5_RESERVED_E              = 4'hE,  // Reserved
        AXI5_USER_DEFINED            = 4'hF   // User-defined
    } axi5_trace_code_t;

    // =============================================================================
    // APB5 EXTENDED EVENT CODES
    // =============================================================================

    // APB5 Wake-up Events (new in APB5)
    typedef enum logic [3:0] {
        APB5_WAKEUP_REQUEST          = 4'h0,  // PWAKEUP asserted by slave
        APB5_WAKEUP_ACKNOWLEDGED     = 4'h1,  // Wake-up acknowledged
        APB5_WAKEUP_TIMEOUT          = 4'h2,  // Wake-up request timeout
        APB5_WAKEUP_REJECTED         = 4'h3,  // Wake-up request rejected
        APB5_SLEEP_REQUEST           = 4'h4,  // Sleep mode request
        APB5_SLEEP_ENTERED           = 4'h5,  // Entered sleep mode
        APB5_WAKEUP_RESERVED_6       = 4'h6,  // Reserved
        APB5_WAKEUP_RESERVED_7       = 4'h7,  // Reserved
        APB5_WAKEUP_RESERVED_8       = 4'h8,  // Reserved
        APB5_WAKEUP_RESERVED_9       = 4'h9,  // Reserved
        APB5_WAKEUP_RESERVED_A       = 4'hA,  // Reserved
        APB5_WAKEUP_RESERVED_B       = 4'hB,  // Reserved
        APB5_WAKEUP_RESERVED_C       = 4'hC,  // Reserved
        APB5_WAKEUP_RESERVED_D       = 4'hD,  // Reserved
        APB5_WAKEUP_RESERVED_E       = 4'hE,  // Reserved
        APB5_WAKEUP_USER_DEFINED     = 4'hF   // User-defined wake-up
    } apb5_wakeup_code_t;

    // APB5 Parity Error Events (new in APB5)
    typedef enum logic [3:0] {
        APB5_PARITY_PWDATA_ERROR     = 4'h0,  // PWDATA parity error (PPARITY)
        APB5_PARITY_PRDATA_ERROR     = 4'h1,  // PRDATA parity error (PRDATAPARITY)
        APB5_PARITY_PREADY_ERROR     = 4'h2,  // PREADY parity error (PREADYPARITY)
        APB5_PARITY_PSLVERR_ERROR    = 4'h3,  // PSLVERR parity error (PSLVERRPARITY)
        APB5_PARITY_CORRECTED        = 4'h4,  // Parity error corrected
        APB5_PARITY_UNCORRECTED      = 4'h5,  // Parity error uncorrectable
        APB5_PARITY_CHECK_DISABLED   = 4'h6,  // Parity checking disabled
        APB5_PARITY_CHECK_ENABLED    = 4'h7,  // Parity checking enabled
        APB5_PARITY_RESERVED_8       = 4'h8,  // Reserved
        APB5_PARITY_RESERVED_9       = 4'h9,  // Reserved
        APB5_PARITY_RESERVED_A       = 4'hA,  // Reserved
        APB5_PARITY_RESERVED_B       = 4'hB,  // Reserved
        APB5_PARITY_RESERVED_C       = 4'hC,  // Reserved
        APB5_PARITY_RESERVED_D       = 4'hD,  // Reserved
        APB5_PARITY_RESERVED_E       = 4'hE,  // Reserved
        APB5_PARITY_USER_DEFINED     = 4'hF   // User-defined parity
    } apb5_parity_code_t;

    // APB5 User Signal Events (new in APB5)
    typedef enum logic [3:0] {
        APB5_USER_PUSER_VALID        = 4'h0,  // PUSER valid on master
        APB5_USER_PSUSER_VALID       = 4'h1,  // PSUSER valid on slave
        APB5_USER_SIGNAL_MISMATCH    = 4'h2,  // User signal mismatch
        APB5_USER_RESERVED_3         = 4'h3,  // Reserved
        APB5_USER_RESERVED_4         = 4'h4,  // Reserved
        APB5_USER_RESERVED_5         = 4'h5,  // Reserved
        APB5_USER_RESERVED_6         = 4'h6,  // Reserved
        APB5_USER_RESERVED_7         = 4'h7,  // Reserved
        APB5_USER_RESERVED_8         = 4'h8,  // Reserved
        APB5_USER_RESERVED_9         = 4'h9,  // Reserved
        APB5_USER_RESERVED_A         = 4'hA,  // Reserved
        APB5_USER_RESERVED_B         = 4'hB,  // Reserved
        APB5_USER_RESERVED_C         = 4'hC,  // Reserved
        APB5_USER_RESERVED_D         = 4'hD,  // Reserved
        APB5_USER_RESERVED_E         = 4'hE,  // Reserved
        APB5_USER_USER_DEFINED       = 4'hF   // User-defined
    } apb5_user_code_t;

    // =============================================================================
    // AXIS5 EXTENDED EVENT CODES
    // =============================================================================

    // AXIS5 Wake-up Events (new in AXIS5)
    typedef enum logic [3:0] {
        AXIS5_WAKEUP_REQUEST         = 4'h0,  // TWAKEUP asserted
        AXIS5_WAKEUP_ACKNOWLEDGED    = 4'h1,  // Wake-up acknowledged
        AXIS5_WAKEUP_TIMEOUT         = 4'h2,  // Wake-up timeout
        AXIS5_WAKEUP_ACTIVE          = 4'h3,  // Wake-up active, data pending
        AXIS5_SLEEP_ENTERING         = 4'h4,  // Entering sleep mode
        AXIS5_SLEEP_EXITING          = 4'h5,  // Exiting sleep mode
        AXIS5_WAKEUP_RESERVED_6      = 4'h6,  // Reserved
        AXIS5_WAKEUP_RESERVED_7      = 4'h7,  // Reserved
        AXIS5_WAKEUP_RESERVED_8      = 4'h8,  // Reserved
        AXIS5_WAKEUP_RESERVED_9      = 4'h9,  // Reserved
        AXIS5_WAKEUP_RESERVED_A      = 4'hA,  // Reserved
        AXIS5_WAKEUP_RESERVED_B      = 4'hB,  // Reserved
        AXIS5_WAKEUP_RESERVED_C      = 4'hC,  // Reserved
        AXIS5_WAKEUP_RESERVED_D      = 4'hD,  // Reserved
        AXIS5_WAKEUP_RESERVED_E      = 4'hE,  // Reserved
        AXIS5_WAKEUP_USER_DEFINED    = 4'hF   // User-defined wake-up
    } axis5_wakeup_code_t;

    // AXIS5 Parity Events (new in AXIS5)
    typedef enum logic [3:0] {
        AXIS5_PARITY_TDATA_ERROR     = 4'h0,  // TDATA parity error (TPARITY)
        AXIS5_PARITY_CORRECTED       = 4'h1,  // Parity error corrected
        AXIS5_PARITY_UNCORRECTED     = 4'h2,  // Parity error uncorrectable
        AXIS5_PARITY_CHECK_DISABLED  = 4'h3,  // Parity checking disabled
        AXIS5_PARITY_CHECK_ENABLED   = 4'h4,  // Parity checking enabled
        AXIS5_PARITY_RESERVED_5      = 4'h5,  // Reserved
        AXIS5_PARITY_RESERVED_6      = 4'h6,  // Reserved
        AXIS5_PARITY_RESERVED_7      = 4'h7,  // Reserved
        AXIS5_PARITY_RESERVED_8      = 4'h8,  // Reserved
        AXIS5_PARITY_RESERVED_9      = 4'h9,  // Reserved
        AXIS5_PARITY_RESERVED_A      = 4'hA,  // Reserved
        AXIS5_PARITY_RESERVED_B      = 4'hB,  // Reserved
        AXIS5_PARITY_RESERVED_C      = 4'hC,  // Reserved
        AXIS5_PARITY_RESERVED_D      = 4'hD,  // Reserved
        AXIS5_PARITY_RESERVED_E      = 4'hE,  // Reserved
        AXIS5_PARITY_USER_DEFINED    = 4'hF   // User-defined parity
    } axis5_parity_code_t;

    // AXIS5 CRC Events (optional in AXIS5)
    typedef enum logic [3:0] {
        AXIS5_CRC_VALID              = 4'h0,  // CRC check passed
        AXIS5_CRC_ERROR              = 4'h1,  // CRC error detected (TCRC_ERROR)
        AXIS5_CRC_COMPUTED           = 4'h2,  // CRC computed and sent
        AXIS5_CRC_DISABLED           = 4'h3,  // CRC checking disabled
        AXIS5_CRC_ENABLED            = 4'h4,  // CRC checking enabled
        AXIS5_CRC_RESERVED_5         = 4'h5,  // Reserved
        AXIS5_CRC_RESERVED_6         = 4'h6,  // Reserved
        AXIS5_CRC_RESERVED_7         = 4'h7,  // Reserved
        AXIS5_CRC_RESERVED_8         = 4'h8,  // Reserved
        AXIS5_CRC_RESERVED_9         = 4'h9,  // Reserved
        AXIS5_CRC_RESERVED_A         = 4'hA,  // Reserved
        AXIS5_CRC_RESERVED_B         = 4'hB,  // Reserved
        AXIS5_CRC_RESERVED_C         = 4'hC,  // Reserved
        AXIS5_CRC_RESERVED_D         = 4'hD,  // Reserved
        AXIS5_CRC_RESERVED_E         = 4'hE,  // Reserved
        AXIS5_CRC_USER_DEFINED       = 4'hF   // User-defined CRC
    } axis5_crc_code_t;

    // =============================================================================
    // AMBA5 UNIFIED EVENT CODE UNION
    // =============================================================================

    typedef union packed {
        // AXI5 specific event codes
        axi5_atomic_code_t     axi5_atomic;
        axi5_trace_code_t      axi5_trace;

        // APB5 specific event codes
        apb5_wakeup_code_t     apb5_wakeup;
        apb5_parity_code_t     apb5_parity;
        apb5_user_code_t       apb5_user;

        // AXIS5 specific event codes
        axis5_wakeup_code_t    axis5_wakeup;
        axis5_parity_code_t    axis5_parity;
        axis5_crc_code_t       axis5_crc;

        // Raw 4-bit value for direct access
        logic [3:0]            raw;
    } amba5_event_code_t;

    // =============================================================================
    // AMBA5 EVENT CODE CREATION HELPER FUNCTIONS
    // =============================================================================

    // AXI5 event code creation functions
    function automatic amba5_event_code_t create_axi5_atomic_event(axi5_atomic_code_t code);
        amba5_event_code_t result;
        result.axi5_atomic = code;
        return result;
    endfunction

    function automatic amba5_event_code_t create_axi5_trace_event(axi5_trace_code_t code);
        amba5_event_code_t result;
        result.axi5_trace = code;
        return result;
    endfunction

    // APB5 event code creation functions
    function automatic amba5_event_code_t create_apb5_wakeup_event(apb5_wakeup_code_t code);
        amba5_event_code_t result;
        result.apb5_wakeup = code;
        return result;
    endfunction

    function automatic amba5_event_code_t create_apb5_parity_event(apb5_parity_code_t code);
        amba5_event_code_t result;
        result.apb5_parity = code;
        return result;
    endfunction

    function automatic amba5_event_code_t create_apb5_user_event(apb5_user_code_t code);
        amba5_event_code_t result;
        result.apb5_user = code;
        return result;
    endfunction

    // AXIS5 event code creation functions
    function automatic amba5_event_code_t create_axis5_wakeup_event(axis5_wakeup_code_t code);
        amba5_event_code_t result;
        result.axis5_wakeup = code;
        return result;
    endfunction

    function automatic amba5_event_code_t create_axis5_parity_event(axis5_parity_code_t code);
        amba5_event_code_t result;
        result.axis5_parity = code;
        return result;
    endfunction

    function automatic amba5_event_code_t create_axis5_crc_event(axis5_crc_code_t code);
        amba5_event_code_t result;
        result.axis5_crc = code;
        return result;
    endfunction

    // =============================================================================
    // STRING FUNCTIONS FOR DEBUGGING
    // =============================================================================

    function automatic string get_apb5_wakeup_name(apb5_wakeup_code_t code);
        case (code)
            APB5_WAKEUP_REQUEST      : return "WAKEUP_REQUEST";
            APB5_WAKEUP_ACKNOWLEDGED : return "WAKEUP_ACKNOWLEDGED";
            APB5_WAKEUP_TIMEOUT      : return "WAKEUP_TIMEOUT";
            APB5_WAKEUP_REJECTED     : return "WAKEUP_REJECTED";
            APB5_SLEEP_REQUEST       : return "SLEEP_REQUEST";
            APB5_SLEEP_ENTERED       : return "SLEEP_ENTERED";
            APB5_WAKEUP_USER_DEFINED : return "USER_DEFINED";
            default                  : return "UNKNOWN_APB5_WAKEUP";
        endcase
    endfunction

    function automatic string get_apb5_parity_name(apb5_parity_code_t code);
        case (code)
            APB5_PARITY_PWDATA_ERROR   : return "PWDATA_ERROR";
            APB5_PARITY_PRDATA_ERROR   : return "PRDATA_ERROR";
            APB5_PARITY_PREADY_ERROR   : return "PREADY_ERROR";
            APB5_PARITY_PSLVERR_ERROR  : return "PSLVERR_ERROR";
            APB5_PARITY_CORRECTED      : return "CORRECTED";
            APB5_PARITY_UNCORRECTED    : return "UNCORRECTED";
            APB5_PARITY_CHECK_DISABLED : return "CHECK_DISABLED";
            APB5_PARITY_CHECK_ENABLED  : return "CHECK_ENABLED";
            APB5_PARITY_USER_DEFINED   : return "USER_DEFINED";
            default                    : return "UNKNOWN_APB5_PARITY";
        endcase
    endfunction

    function automatic string get_axis5_wakeup_name(axis5_wakeup_code_t code);
        case (code)
            AXIS5_WAKEUP_REQUEST      : return "WAKEUP_REQUEST";
            AXIS5_WAKEUP_ACKNOWLEDGED : return "WAKEUP_ACKNOWLEDGED";
            AXIS5_WAKEUP_TIMEOUT      : return "WAKEUP_TIMEOUT";
            AXIS5_WAKEUP_ACTIVE       : return "WAKEUP_ACTIVE";
            AXIS5_SLEEP_ENTERING      : return "SLEEP_ENTERING";
            AXIS5_SLEEP_EXITING       : return "SLEEP_EXITING";
            AXIS5_WAKEUP_USER_DEFINED : return "USER_DEFINED";
            default                   : return "UNKNOWN_AXIS5_WAKEUP";
        endcase
    endfunction

    function automatic string get_axis5_crc_name(axis5_crc_code_t code);
        case (code)
            AXIS5_CRC_VALID          : return "CRC_VALID";
            AXIS5_CRC_ERROR          : return "CRC_ERROR";
            AXIS5_CRC_COMPUTED       : return "CRC_COMPUTED";
            AXIS5_CRC_DISABLED       : return "CRC_DISABLED";
            AXIS5_CRC_ENABLED        : return "CRC_ENABLED";
            AXIS5_CRC_USER_DEFINED   : return "USER_DEFINED";
            default                  : return "UNKNOWN_AXIS5_CRC";
        endcase
    endfunction

endpackage : monitor_amba5_pkg
