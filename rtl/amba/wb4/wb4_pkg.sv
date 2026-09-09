// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: wb4_pkg
// Purpose: The response-status encoding shared by wb4_master and wb4_slave.
//
// Documentation: docs/markdown/rtl-amba/wb4/wb4_master.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-09

`timescale 1ns / 1ps

package wb4_pkg;

    // Wishbone B4 terminates a transfer with exactly one of ACK, ERR or RTY.
    // The FUB-side response packet carries that as a 2-bit status so a FUB can
    // see a retry (RTY) and decide its own policy; the master does NOT re-issue
    // on RTY. Encoding is ONE source here for both blocks and the DV.
    localparam int WB4_STATUS_WIDTH = 2;

    typedef enum logic [WB4_STATUS_WIDTH-1:0] {
        WB4_RSP_ACK = 2'b00,   // normal completion (read data valid)
        WB4_RSP_ERR = 2'b01,   // slave error
        WB4_RSP_RTY = 2'b10    // slave asks for a retry
    } wb4_status_t;

endpackage : wb4_pkg
