// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monitor_wb4_pkg
// Purpose: Wishbone B4 event codes for monitor bus packets (protocol =
//          PROTOCOL_WB). Imported by wb4_monitor alongside
//          monitor_common_pkg; NOT re-exported by monitor_pkg, so no
//          existing consumer's filelist changes.
//
// Documentation: docs/markdown/rtl-amba/wb4/wb4_monitor.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-09

`timescale 1ns / 1ps

package monitor_wb4_pkg;

    // Error events (packet_type = PktTypeError, protocol = PROTOCOL_WB)
    typedef enum logic [7:0] {
        WB_ERR_ERR              = 8'h0,  // Slave terminated with ERR
        WB_ERR_ORPHAN_RSP       = 8'h1,  // Response with no request outstanding
        WB_ERR_TRACK_LOST       = 8'h2,  // Request accepted with no free tracking slot
        WB_ERR_RESERVED_3       = 8'h3,
        WB_ERR_RESERVED_4       = 8'h4,
        WB_ERR_RESERVED_5       = 8'h5,
        WB_ERR_RESERVED_6       = 8'h6,
        WB_ERR_RESERVED_7       = 8'h7,
        WB_ERR_ADDR_RANGE       = 8'h8,  // Address-range violation (apb_monitor_addr_check, same code as APB)
        WB_ERR_RESERVED_9       = 8'h9,
        WB_ERR_RESERVED_A       = 8'hA,
        WB_ERR_RESERVED_B       = 8'hB,
        WB_ERR_RESERVED_C       = 8'hC,
        WB_ERR_RESERVED_D       = 8'hD,
        WB_ERR_RESERVED_E       = 8'hE,
        WB_ERR_USER_DEFINED     = 8'hF
    } wb_error_code_t;

    // Timeout events (packet_type = PktTypeTimeout, protocol = PROTOCOL_WB)
    typedef enum logic [7:0] {
        WB_TIMEOUT_CMD          = 8'h0,  // Request offered (cmd_valid) but not taken for cfg_cmd_timeout_cnt clocks
        WB_TIMEOUT_RSP          = 8'h1,  // Oldest outstanding request unterminated for cfg_rsp_timeout_cnt clocks
        WB_TIMEOUT_RESERVED_2   = 8'h2,
        WB_TIMEOUT_RESERVED_3   = 8'h3,
        WB_TIMEOUT_RESERVED_4   = 8'h4,
        WB_TIMEOUT_RESERVED_5   = 8'h5,
        WB_TIMEOUT_RESERVED_6   = 8'h6,
        WB_TIMEOUT_RESERVED_7   = 8'h7,
        WB_TIMEOUT_RESERVED_8   = 8'h8,
        WB_TIMEOUT_RESERVED_9   = 8'h9,
        WB_TIMEOUT_RESERVED_A   = 8'hA,
        WB_TIMEOUT_RESERVED_B   = 8'hB,
        WB_TIMEOUT_RESERVED_C   = 8'hC,
        WB_TIMEOUT_RESERVED_D   = 8'hD,
        WB_TIMEOUT_RESERVED_E   = 8'hE,
        WB_TIMEOUT_USER_DEFINED = 8'hF
    } wb_timeout_code_t;

    // Completion events (packet_type = PktTypeCompletion, protocol = PROTOCOL_WB)
    typedef enum logic [7:0] {
        WB_COMPL_ACK            = 8'h0,  // Terminated ACK (direction in aux_data)
        WB_COMPL_READ           = 8'h1,  // Read terminated ACK
        WB_COMPL_WRITE          = 8'h2,  // Write terminated ACK
        WB_COMPL_RTY            = 8'h3,  // Terminated RTY: not an error, the FUB decides
        WB_COMPL_RESERVED_4     = 8'h4,
        WB_COMPL_RESERVED_5     = 8'h5,
        WB_COMPL_RESERVED_6     = 8'h6,
        WB_COMPL_RESERVED_7     = 8'h7,
        WB_COMPL_RESERVED_8     = 8'h8,
        WB_COMPL_RESERVED_9     = 8'h9,
        WB_COMPL_RESERVED_A     = 8'hA,
        WB_COMPL_RESERVED_B     = 8'hB,
        WB_COMPL_RESERVED_C     = 8'hC,
        WB_COMPL_RESERVED_D     = 8'hD,
        WB_COMPL_RESERVED_E     = 8'hE,
        WB_COMPL_USER_DEFINED   = 8'hF
    } wb_completion_code_t;

    // Performance events (packet_type = PktTypePerf, protocol = PROTOCOL_WB)
    typedef enum logic [7:0] {
        WB_PERF_READ_LATENCY    = 8'h0,  // Read latency crossed cfg_latency_threshold
        WB_PERF_WRITE_LATENCY   = 8'h1,  // Write latency crossed cfg_latency_threshold
        WB_PERF_RESERVED_2      = 8'h2,
        WB_PERF_RESERVED_3      = 8'h3,
        WB_PERF_RESERVED_4      = 8'h4,
        WB_PERF_RESERVED_5      = 8'h5,
        WB_PERF_RESERVED_6      = 8'h6,
        WB_PERF_RESERVED_7      = 8'h7,
        WB_PERF_RESERVED_8      = 8'h8,
        WB_PERF_RESERVED_9      = 8'h9,
        WB_PERF_RESERVED_A      = 8'hA,
        WB_PERF_RESERVED_B      = 8'hB,
        WB_PERF_RESERVED_C      = 8'hC,
        WB_PERF_RESERVED_D      = 8'hD,
        WB_PERF_RESERVED_E      = 8'hE,
        WB_PERF_USER_DEFINED    = 8'hF
    } wb_perf_code_t;

    // Debug events (packet_type = PktTypeDebug, protocol = PROTOCOL_WB)
    typedef enum logic [7:0] {
        WB_DEBUG_QUEUE_ACTIVE   = 8'h0,  // Tracking queue went from empty to non-empty
        WB_DEBUG_QUEUE_IDLE     = 8'h1,  // Tracking queue drained
        WB_DEBUG_RESERVED_2     = 8'h2,
        WB_DEBUG_RESERVED_3     = 8'h3,
        WB_DEBUG_RESERVED_4     = 8'h4,
        WB_DEBUG_RESERVED_5     = 8'h5,
        WB_DEBUG_RESERVED_6     = 8'h6,
        WB_DEBUG_RESERVED_7     = 8'h7,
        WB_DEBUG_RESERVED_8     = 8'h8,
        WB_DEBUG_RESERVED_9     = 8'h9,
        WB_DEBUG_RESERVED_A     = 8'hA,
        WB_DEBUG_RESERVED_B     = 8'hB,
        WB_DEBUG_RESERVED_C     = 8'hC,
        WB_DEBUG_RESERVED_D     = 8'hD,
        WB_DEBUG_RESERVED_E     = 8'hE,
        WB_DEBUG_USER_DEFINED   = 8'hF
    } wb_debug_code_t;

endpackage : monitor_wb4_pkg
