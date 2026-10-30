// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ocelus_chi_pkg
// Purpose: CHI (Arm IHI 0050) event codes for ocelus bus packets (protocol =
//          PROTOCOL_CHI). Imported by chi_monitor_lite alongside
//          ocelus_common_pkg; NOT re-exported by ocelus_pkg, so no existing
//          consumer's filelist changes (the WB4 / CXS precedent).
//
// Documentation: docs/markdown/rtl-amba/monitor/chi_monitor_lite.md
// Subsystem: amba
//
// Packet classes used (packet_type, ocelus_common_pkg): Error, Timeout,
// Completion, Credit, Channel, Stream -- the stream set, because a CHI port
// is credited links like CXS, plus transactions on top. EVENT_DROPPED is
// 8'hE in every lite ocelus (AXI, AXIS, CXS, CHI), so host tooling decodes a
// drop report the same way whatever the protocol.
//
// Author: sean galloway
// Created: 2026-10-30

`timescale 1ns / 1ps

// File carries the Ocelus brand; the package uses the monitor_*_pkg name every
// other ocelus package is imported by (see ocelus_wb4_pkg.sv).
/* verilator lint_off DECLFILENAME */
package ocelus_chi_pkg;
/* verilator lint_on DECLFILENAME */

    // Error events (packet_type = PktTypeError)
    typedef enum logic [7:0] {
        CHI_ERR_PROTOCOL        = 8'h0,  // the port's protocol_error rose (credit / FLITPEND / LCrdReturn rule broken)
        CHI_ERR_RESP_ERR        = 8'h1,  // a completion or read data toward the requester carried RespErr DERR / NDERR
        CHI_ERR_ORPHAN_RSP      = 8'h2,  // a RSP toward the requester matched no open request (TxnID)
        CHI_ERR_ORPHAN_DAT      = 8'h3,  // read data toward the requester matched no open request (TxnID)
        CHI_ERR_ORPHAN_ACK      = 8'h4,  // a CompAck or write data from the requester matched no DBID handed out
        CHI_ERR_ORPHAN_SNP_RSP  = 8'h5,  // a snoop response matched no open snoop (TxnID)
        CHI_ERR_TABLE_FULL      = 8'h6,  // a request found no free slot: counted, not tracked
        CHI_ERR_SNP_TABLE_FULL  = 8'h7,  // a snoop found no free slot: counted, not tracked
        CHI_ERR_RESERVED_8      = 8'h8,
        CHI_ERR_RESERVED_9      = 8'h9,
        CHI_ERR_RESERVED_A      = 8'hA,
        CHI_ERR_RESERVED_B      = 8'hB,
        CHI_ERR_RESERVED_C      = 8'hC,
        CHI_ERR_RESERVED_D      = 8'hD,
        CHI_ERR_EVENT_DROPPED   = 8'hE,  // events lost to monbus backpressure (event_data = count)
        CHI_ERR_USER_DEFINED    = 8'hF
    } chi_error_code_t;

    // Timeout events (packet_type = PktTypeTimeout); thresholds in MICROSECONDS
    typedef enum logic [7:0] {
        CHI_TIMEOUT_TXN         = 8'h0,  // a request open (no completion, data, DBID or CompAck owed) for cfg us
        CHI_TIMEOUT_SNP         = 8'h1,  // a snoop unanswered for cfg us
        CHI_TIMEOUT_CREDIT      = 8'h2,  // a TX channel starved of credits for cfg us
        CHI_TIMEOUT_LINK        = 8'h3,  // a direction sat in ACTIVATE or DEACTIVATE for cfg us
        CHI_TIMEOUT_RESERVED_4  = 8'h4,
        CHI_TIMEOUT_RESERVED_5  = 8'h5,
        CHI_TIMEOUT_RESERVED_6  = 8'h6,
        CHI_TIMEOUT_RESERVED_7  = 8'h7,
        CHI_TIMEOUT_RESERVED_8  = 8'h8,
        CHI_TIMEOUT_RESERVED_9  = 8'h9,
        CHI_TIMEOUT_RESERVED_A  = 8'hA,
        CHI_TIMEOUT_RESERVED_B  = 8'hB,
        CHI_TIMEOUT_RESERVED_C  = 8'hC,
        CHI_TIMEOUT_RESERVED_D  = 8'hD,
        CHI_TIMEOUT_RESERVED_E  = 8'hE,
        CHI_TIMEOUT_USER_DEFINED = 8'hF
    } chi_timeout_code_t;

    // Completion events (packet_type = PktTypeCompletion)
    typedef enum logic [7:0] {
        CHI_COMPL_TXN           = 8'h0,  // a request retired: every completion, data packet, write data and CompAck it owed is in
        CHI_COMPL_RETRY         = 8'h1,  // a request retired by RetryAck (it will be re-sent with a P-Credit)
        CHI_COMPL_SNP           = 8'h2,  // a snoop answered (SnpResp, or the last SnpRespData packet)
        CHI_COMPL_RESERVED_3    = 8'h3,
        CHI_COMPL_RESERVED_4    = 8'h4,
        CHI_COMPL_RESERVED_5    = 8'h5,
        CHI_COMPL_RESERVED_6    = 8'h6,
        CHI_COMPL_RESERVED_7    = 8'h7,
        CHI_COMPL_RESERVED_8    = 8'h8,
        CHI_COMPL_RESERVED_9    = 8'h9,
        CHI_COMPL_RESERVED_A    = 8'hA,
        CHI_COMPL_RESERVED_B    = 8'hB,
        CHI_COMPL_RESERVED_C    = 8'hC,
        CHI_COMPL_RESERVED_D    = 8'hD,
        CHI_COMPL_RESERVED_E    = 8'hE,
        CHI_COMPL_USER_DEFINED  = 8'hF
    } chi_completion_code_t;

    // Credit events (packet_type = PktTypeCredit); thresholds in CYCLES
    typedef enum logic [7:0] {
        CHI_CREDIT_STARVED      = 8'h0,  // a TX channel held a flit with no credit for cfg_stall_threshold cycles
        CHI_CREDIT_BACKPRESSURE = 8'h1,  // a FUB-side receive channel held valid without ready for cfg_stall_threshold cycles
        CHI_CREDIT_RESERVED_2   = 8'h2,
        CHI_CREDIT_RESERVED_3   = 8'h3,
        CHI_CREDIT_RESERVED_4   = 8'h4,
        CHI_CREDIT_RESERVED_5   = 8'h5,
        CHI_CREDIT_RESERVED_6   = 8'h6,
        CHI_CREDIT_RESERVED_7   = 8'h7,
        CHI_CREDIT_RESERVED_8   = 8'h8,
        CHI_CREDIT_RESERVED_9   = 8'h9,
        CHI_CREDIT_RESERVED_A   = 8'hA,
        CHI_CREDIT_RESERVED_B   = 8'hB,
        CHI_CREDIT_RESERVED_C   = 8'hC,
        CHI_CREDIT_RESERVED_D   = 8'hD,
        CHI_CREDIT_RESERVED_E   = 8'hE,
        CHI_CREDIT_USER_DEFINED = 8'hF
    } chi_credit_code_t;

    // Channel events (packet_type = PktTypeChannel): protocol-credit and
    // ordering messages that belong to no tracked transaction
    typedef enum logic [7:0] {
        CHI_CHAN_PCRD_GRANT     = 8'h0,  // a PCrdGrant toward the requester (B2.10)
        CHI_CHAN_PCRD_RETURN    = 8'h1,  // a PCrdReturn request (B2.10.1)
        CHI_CHAN_READ_RECEIPT   = 8'h2,  // a ReadReceipt toward the requester (ordered read accepted)
        CHI_CHAN_RESERVED_3     = 8'h3,
        CHI_CHAN_RESERVED_4     = 8'h4,
        CHI_CHAN_RESERVED_5     = 8'h5,
        CHI_CHAN_RESERVED_6     = 8'h6,
        CHI_CHAN_RESERVED_7     = 8'h7,
        CHI_CHAN_RESERVED_8     = 8'h8,
        CHI_CHAN_RESERVED_9     = 8'h9,
        CHI_CHAN_RESERVED_A     = 8'hA,
        CHI_CHAN_RESERVED_B     = 8'hB,
        CHI_CHAN_RESERVED_C     = 8'hC,
        CHI_CHAN_RESERVED_D     = 8'hD,
        CHI_CHAN_RESERVED_E     = 8'hE,
        CHI_CHAN_USER_DEFINED   = 8'hF
    } chi_channel_code_t;

    // Stream events (packet_type = PktTypeStream): link state changes per
    // direction, named for the state ENTERED (Table B14.1)
    typedef enum logic [7:0] {
        CHI_STREAM_TX_ACTIVATE    = 8'h0,  // TX: STOP -> ACTIVATE (TXLINKACTIVEREQ rose)
        CHI_STREAM_TX_UP          = 8'h1,  // TX: -> RUN
        CHI_STREAM_TX_DEACTIVATE  = 8'h2,  // TX: RUN -> DEACTIVATE
        CHI_STREAM_TX_DOWN        = 8'h3,  // TX: -> STOP
        CHI_STREAM_RX_ACTIVATE    = 8'h4,  // RX: STOP -> ACTIVATE (RXLINKACTIVEREQ seen)
        CHI_STREAM_RX_UP          = 8'h5,  // RX: -> RUN
        CHI_STREAM_RX_DEACTIVATE  = 8'h6,  // RX: RUN -> DEACTIVATE
        CHI_STREAM_RX_DOWN        = 8'h7,  // RX: -> STOP
        CHI_STREAM_RESERVED_8     = 8'h8,
        CHI_STREAM_RESERVED_9     = 8'h9,
        CHI_STREAM_RESERVED_A     = 8'hA,
        CHI_STREAM_RESERVED_B     = 8'hB,
        CHI_STREAM_RESERVED_C     = 8'hC,
        CHI_STREAM_RESERVED_D     = 8'hD,
        CHI_STREAM_RESERVED_E     = 8'hE,
        CHI_STREAM_USER_DEFINED   = 8'hF
    } chi_stream_code_t;

endpackage : ocelus_chi_pkg
