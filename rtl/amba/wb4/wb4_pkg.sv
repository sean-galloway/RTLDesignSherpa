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


    // ------------------------------------------------------------------------
    // Registered-feedback burst hints (B4 chapter 4). ADVISORY: a slave that
    // does not implement them treats every cycle as classic, which is why the
    // encodings put CLASSIC and LINEAR at zero -- a tied-off bus is a legal
    // non-burst bus.
    // ------------------------------------------------------------------------
    localparam int WB4_CTI_WIDTH = 3;
    localparam int WB4_BTE_WIDTH = 2;

    typedef enum logic [WB4_CTI_WIDTH-1:0] {
        WB4_CTI_CLASSIC     = 3'b000,  // classic cycle, no burst
        WB4_CTI_CONST_ADDR  = 3'b001,  // constant-address burst (FIFO-like)
        WB4_CTI_INCR        = 3'b010,  // incrementing burst
        WB4_CTI_RSVD_3      = 3'b011,
        WB4_CTI_RSVD_4      = 3'b100,
        WB4_CTI_RSVD_5      = 3'b101,
        WB4_CTI_RSVD_6      = 3'b110,
        WB4_CTI_EOB         = 3'b111   // end-of-burst: the last transfer
    } wb4_cti_t;

    typedef enum logic [WB4_BTE_WIDTH-1:0] {
        WB4_BTE_LINEAR = 2'b00,
        WB4_BTE_WRAP4  = 2'b01,
        WB4_BTE_WRAP8  = 2'b10,
        WB4_BTE_WRAP16 = 2'b11
    } wb4_bte_t;

endpackage : wb4_pkg
