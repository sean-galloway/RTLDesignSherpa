// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_pkg
// Purpose: Axi Pkg module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`ifndef AXI_PKG_SV
`define AXI_PKG_SV

package axi_pkg;
    // Basic AXI4 interface parameters
    parameter int AXI_ID_WIDTH      = 4;    // ID width for transaction identification
    parameter int AXI_ADDR_WIDTH    = 32;   // Address width for memory space
    parameter int AXI_DATA_WIDTH    = 32;   // Data width for bus transfers
    parameter int AXI_USER_WIDTH    = 1;    // User-defined signal width

    // Derived parameters
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8;  // Write strobe width

    // Interface specific parameters
    parameter int AXI_TDEST_WIDTH   = 4;    // Destination ID width
    parameter int AXI_TUSER_WIDTH   = 1;    // Stream user signal width

    // Burst parameters
    parameter int AXI_MAX_BURST_LENGTH = 16;  // Maximum burst length
    parameter int AXI_BURST_SIZE_WIDTH = 3;   // Burst size width

    // Optional feature parameters
    parameter int AXI_SUPPORTS_READ  = 1;    // Enable read channels
    parameter int AXI_SUPPORTS_WRITE = 1;    // Enable write channels

    // Protocol specific widths
    parameter int AXI_PROT_WIDTH     = 3;    // Protection type width
    parameter int AXI_QOS_WIDTH      = 4;    // QoS signaling width
    parameter int AXI_REGION_WIDTH   = 4;    // Region identifier width
    parameter int AXI_CACHE_WIDTH    = 4;    // Cache type width
    parameter int AXI_LOCK_WIDTH     = 1;    // Lock type width
    parameter int AXI_RESP_WIDTH     = 2;    // Response status width

    // Protocol Constants
    localparam logic [1:0] BURST_TYPE_FIXED = 2'b00;
    localparam logic [1:0] BURST_TYPE_INCR  = 2'b01;
    localparam logic [1:0] BURST_TYPE_WRAP  = 2'b10;

    localparam logic [1:0] RESP_OKAY   = 2'b00;
    localparam logic [1:0] RESP_EXOKAY = 2'b01;
    localparam logic [1:0] RESP_SLVERR = 2'b10;
    localparam logic [1:0] RESP_DECERR = 2'b11;

    localparam logic [2:0] PROT_PRIVILEGED   = 3'b001;
    localparam logic [2:0] PROT_SECURE       = 3'b010;
    localparam logic [2:0] PROT_INSTRUCTION  = 3'b100;

    // Channel Structures (without valid signals)
    typedef struct packed {
        logic [AXI_ID_WIDTH-1:0]      id;
        logic [AXI_ADDR_WIDTH-1:0]    addr;
        logic [7:0]                   len;
        logic [2:0]                   size;
        logic [1:0]                   burst;
        logic                         lock;
        logic [3:0]                   cache;
        logic [2:0]                   prot;
        logic [3:0]                   qos;
        logic [3:0]                   region;
        logic [AXI_USER_WIDTH-1:0]    user;
    } axi_aw_chan_t;

    typedef struct packed {
        logic [AXI_DATA_WIDTH-1:0]    data;
        logic [AXI_WSTRB_WIDTH-1:0]   strb;
        logic                         last;
        logic [AXI_USER_WIDTH-1:0]    user;
    } axi_w_chan_t;

    typedef struct packed {
        logic [AXI_ID_WIDTH-1:0]     id;
        logic [1:0]                  resp;
        logic [AXI_USER_WIDTH-1:0]   user;
    } axi_b_chan_t;

    typedef struct packed {
        logic [AXI_ID_WIDTH-1:0]      id;
        logic [AXI_ADDR_WIDTH-1:0]    addr;
        logic [7:0]                   len;
        logic [2:0]                   size;
        logic [1:0]                   burst;
        logic                         lock;
        logic [3:0]                   cache;
        logic [2:0]                   prot;
        logic [3:0]                   qos;
        logic [3:0]                   region;
        logic [AXI_USER_WIDTH-1:0]    user;
    } axi_ar_chan_t;

    typedef struct packed {
        logic [AXI_ID_WIDTH-1:0]      id;
        logic [AXI_DATA_WIDTH-1:0]    data;
        logic [1:0]                   resp;
        logic                         last;
        logic [AXI_USER_WIDTH-1:0]    user;
    } axi_r_chan_t;

endpackage : axi_pkg

`endif
