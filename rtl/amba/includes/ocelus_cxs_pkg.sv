// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ocelus_cxs_pkg
// Purpose: CXS (Arm IHI 0079) event codes for ocelus bus packets (protocol =
//          PROTOCOL_CXS). Imported by cxs_monitor_lite alongside
//          ocelus_common_pkg; NOT re-exported by ocelus_pkg, so no
//          existing consumer's filelist changes (the WB4 precedent).
//
// Documentation: docs/markdown/rtl-amba/monitor/cxs_monitor_lite.md
// Subsystem: amba
//
// Packet classes used (packet_type, ocelus_common_pkg): Error, Timeout,
// Completion, and the stream classes Credit / Channel / Stream that AXIS
// introduced -- CXS is a stream too, so the classes mean the same thing.
// EVENT_DROPPED is 8'hE in every lite ocelus (AXI, AXIS, CXS), so host tooling
// decodes a drop report the same way whatever the protocol.
//
// Author: sean galloway
// Created: 2026-10-15

`timescale 1ns / 1ps

// File carries the Ocelus brand; the package uses the monitor_*_pkg name every
// other ocelus package is imported by (see ocelus_wb4_pkg.sv).
/* verilator lint_off DECLFILENAME */
package ocelus_cxs_pkg;
/* verilator lint_on DECLFILENAME */

    // Error events (packet_type = PktTypeError)
    typedef enum logic [7:0] {
        CXS_ERR_PROTOCOL        = 8'h0,  // the endpoint's protocol_error rose (credit/link/CXSCNTL rule broken)
        CXS_ERR_PARITY          = 8'h1,  // the endpoint's parity_error rose (an Odd_Byte_Parity check failed)
        CXS_ERR_ENDERROR        = 8'h2,  // a flit ended one or more packets with ENDERROR
        CXS_ERR_RESERVED_3      = 8'h3,
        CXS_ERR_RESERVED_4      = 8'h4,
        CXS_ERR_RESERVED_5      = 8'h5,
        CXS_ERR_RESERVED_6      = 8'h6,
        CXS_ERR_RESERVED_7      = 8'h7,
        CXS_ERR_RESERVED_8      = 8'h8,
        CXS_ERR_RESERVED_9      = 8'h9,
        CXS_ERR_RESERVED_A      = 8'hA,
        CXS_ERR_RESERVED_B      = 8'hB,
        CXS_ERR_RESERVED_C      = 8'hC,
        CXS_ERR_RESERVED_D      = 8'hD,
        CXS_ERR_EVENT_DROPPED   = 8'hE,  // events lost to monbus backpressure (event_data = count)
        CXS_ERR_USER_DEFINED    = 8'hF
    } cxs_error_code_t;

    // Timeout events (packet_type = PktTypeTimeout); thresholds in MICROSECONDS
    typedef enum logic [7:0] {
        CXS_TIMEOUT_CREDIT      = 8'h0,  // a flit waited for a credit (TX) / the pool stayed exhausted (RX)
        CXS_TIMEOUT_LINK        = 8'h1,  // the link sat in ACTIVATE or DEACTIVATE (a stuck 4-phase handshake)
        CXS_TIMEOUT_PACKET      = 8'h2,  // a packet open with no flit
        CXS_TIMEOUT_RESERVED_3  = 8'h3,
        CXS_TIMEOUT_RESERVED_4  = 8'h4,
        CXS_TIMEOUT_RESERVED_5  = 8'h5,
        CXS_TIMEOUT_RESERVED_6  = 8'h6,
        CXS_TIMEOUT_RESERVED_7  = 8'h7,
        CXS_TIMEOUT_RESERVED_8  = 8'h8,
        CXS_TIMEOUT_RESERVED_9  = 8'h9,
        CXS_TIMEOUT_RESERVED_A  = 8'hA,
        CXS_TIMEOUT_RESERVED_B  = 8'hB,
        CXS_TIMEOUT_RESERVED_C  = 8'hC,
        CXS_TIMEOUT_RESERVED_D  = 8'hD,
        CXS_TIMEOUT_RESERVED_E  = 8'hE,
        CXS_TIMEOUT_USER_DEFINED = 8'hF
    } cxs_timeout_code_t;

    // Completion events (packet_type = PktTypeCompletion)
    typedef enum logic [7:0] {
        CXS_COMPL_PACKET_END    = 8'h0,  // a flit ended one or more packets (CXS-Lite: every flit)
        CXS_COMPL_RESERVED_1    = 8'h1,
        CXS_COMPL_RESERVED_2    = 8'h2,
        CXS_COMPL_RESERVED_3    = 8'h3,
        CXS_COMPL_RESERVED_4    = 8'h4,
        CXS_COMPL_RESERVED_5    = 8'h5,
        CXS_COMPL_RESERVED_6    = 8'h6,
        CXS_COMPL_RESERVED_7    = 8'h7,
        CXS_COMPL_RESERVED_8    = 8'h8,
        CXS_COMPL_RESERVED_9    = 8'h9,
        CXS_COMPL_RESERVED_A    = 8'hA,
        CXS_COMPL_RESERVED_B    = 8'hB,
        CXS_COMPL_RESERVED_C    = 8'hC,
        CXS_COMPL_RESERVED_D    = 8'hD,
        CXS_COMPL_RESERVED_E    = 8'hE,
        CXS_COMPL_USER_DEFINED  = 8'hF
    } cxs_completion_code_t;

    // Credit events (packet_type = PktTypeCredit); thresholds in CYCLES
    typedef enum logic [7:0] {
        CXS_CREDIT_STARVED      = 8'h0,  // credit starvation lasted cfg_stall_threshold cycles
        CXS_CREDIT_BACKPRESSURE = 8'h1,  // the FUB handshake stalled cfg_stall_threshold cycles
        CXS_CREDIT_RESERVED_2   = 8'h2,
        CXS_CREDIT_RESERVED_3   = 8'h3,
        CXS_CREDIT_RESERVED_4   = 8'h4,
        CXS_CREDIT_RESERVED_5   = 8'h5,
        CXS_CREDIT_RESERVED_6   = 8'h6,
        CXS_CREDIT_RESERVED_7   = 8'h7,
        CXS_CREDIT_RESERVED_8   = 8'h8,
        CXS_CREDIT_RESERVED_9   = 8'h9,
        CXS_CREDIT_RESERVED_A   = 8'hA,
        CXS_CREDIT_RESERVED_B   = 8'hB,
        CXS_CREDIT_RESERVED_C   = 8'hC,
        CXS_CREDIT_RESERVED_D   = 8'hD,
        CXS_CREDIT_RESERVED_E   = 8'hE,
        CXS_CREDIT_USER_DEFINED = 8'hF
    } cxs_credit_code_t;

    // Channel events (packet_type = PktTypeChannel)
    typedef enum logic [7:0] {
        CXS_CHAN_STREAM_CHANGE  = 8'h0,  // CXSPRCLTYPE / CXSSRCID / CXSTGTID differ from the previous flit (2.5.2)
        CXS_CHAN_RESERVED_1     = 8'h1,
        CXS_CHAN_RESERVED_2     = 8'h2,
        CXS_CHAN_RESERVED_3     = 8'h3,
        CXS_CHAN_RESERVED_4     = 8'h4,
        CXS_CHAN_RESERVED_5     = 8'h5,
        CXS_CHAN_RESERVED_6     = 8'h6,
        CXS_CHAN_RESERVED_7     = 8'h7,
        CXS_CHAN_RESERVED_8     = 8'h8,
        CXS_CHAN_RESERVED_9     = 8'h9,
        CXS_CHAN_RESERVED_A     = 8'hA,
        CXS_CHAN_RESERVED_B     = 8'hB,
        CXS_CHAN_RESERVED_C     = 8'hC,
        CXS_CHAN_RESERVED_D     = 8'hD,
        CXS_CHAN_RESERVED_E     = 8'hE,
        CXS_CHAN_USER_DEFINED   = 8'hF
    } cxs_channel_code_t;

    // Stream events (packet_type = PktTypeStream): link state changes,
    // named for the state ENTERED (IHI 0079D Figure 5-2)
    typedef enum logic [7:0] {
        CXS_STREAM_LINK_ACTIVATE   = 8'h0,  // STOP -> ACTIVATE (ACTIVEREQ rose)
        CXS_STREAM_LINK_UP         = 8'h1,  // -> RUN (ACTIVEACK rose)
        CXS_STREAM_LINK_DEACTIVATE = 8'h2,  // RUN -> DEACTIVATE (ACTIVEREQ fell)
        CXS_STREAM_LINK_DOWN       = 8'h3,  // -> STOP (ACTIVEACK fell, every credit home)
        CXS_STREAM_RESERVED_4      = 8'h4,
        CXS_STREAM_RESERVED_5      = 8'h5,
        CXS_STREAM_RESERVED_6      = 8'h6,
        CXS_STREAM_RESERVED_7      = 8'h7,
        CXS_STREAM_RESERVED_8      = 8'h8,
        CXS_STREAM_RESERVED_9      = 8'h9,
        CXS_STREAM_RESERVED_A      = 8'hA,
        CXS_STREAM_RESERVED_B      = 8'hB,
        CXS_STREAM_RESERVED_C      = 8'hC,
        CXS_STREAM_RESERVED_D      = 8'hD,
        CXS_STREAM_RESERVED_E      = 8'hE,
        CXS_STREAM_USER_DEFINED    = 8'hF
    } cxs_stream_code_t;

endpackage : ocelus_cxs_pkg
