// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_ace_issue_th
// Purpose:
//   Unit-side wrapper for the amber_ace_issue Table 2.8.1 row suite: the
//   block's engine-side and wrapper-side pins become top-level ports so
//   the cocotb TB can drive cache events and the engine handshakes
//   directly and capture the snoop fields the block stamps (or, for
//   CleanUnique/MakeUnique/Evict, originates). Pure wiring -- no logic.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/08_amber_ace_issue.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-09

`timescale 1ns / 1ps

module amber_ace_issue_th
    import amber_pkg::*;
#(
    parameter int ADDR_WIDTH     = AMBER_ADDR_WIDTH,
    parameter int BUS_WIDTH      = AMBER_BUS_WIDTH,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 1,
    localparam int STRB_W       = BUS_WIDTH / 8,
    localparam int IW           = AXI_ID_WIDTH,
    localparam int UW           = AXI_USER_WIDTH
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // ------------------------------------------------------------------
    // cache-event inputs (MAS ch02/08 Table 2.8.1)
    // ------------------------------------------------------------------
    input  logic                        ace_rd_req,
    input  logic [2:0]                  ace_rd_type,
    input  logic [ADDR_WIDTH-1:0]       ace_rd_addr,
    input  logic [7:0]                  ace_rd_len,
    input  logic                        ace_wr_req,
    input  logic [2:0]                  ace_wr_type,
    input  logic [ADDR_WIDTH-1:0]       ace_wr_addr,
    input  logic [7:0]                  ace_wr_len,

    // ------------------------------------------------------------------
    // engine side: amber_fill AR / amber_drain AW / amber_drain B
    // ------------------------------------------------------------------
    input  logic [IW-1:0]               eng_arid,
    input  logic [ADDR_WIDTH-1:0]       eng_araddr,
    input  logic [7:0]                  eng_arlen,
    input  logic [2:0]                  eng_arsize,
    input  logic [1:0]                  eng_arburst,
    input  logic                        eng_arlock,
    input  logic [3:0]                  eng_arcache,
    input  logic [2:0]                  eng_arprot,
    input  logic [3:0]                  eng_arqos,
    input  logic [3:0]                  eng_arregion,
    input  logic [UW-1:0]               eng_aruser,
    input  logic                        eng_arvalid,
    output logic                        eng_arready,

    input  logic [IW-1:0]               eng_awid,
    input  logic [ADDR_WIDTH-1:0]       eng_awaddr,
    input  logic [7:0]                  eng_awlen,
    input  logic [2:0]                  eng_awsize,
    input  logic [1:0]                  eng_awburst,
    input  logic                        eng_awlock,
    input  logic [3:0]                  eng_awcache,
    input  logic [2:0]                  eng_awprot,
    input  logic [3:0]                  eng_awqos,
    input  logic [3:0]                  eng_awregion,
    input  logic [UW-1:0]               eng_awuser,
    input  logic                        eng_awvalid,
    output logic                        eng_awready,

    output logic [IW-1:0]               eng_bid,
    output logic [1:0]                  eng_bresp,
    output logic [UW-1:0]               eng_buser,
    output logic                        eng_bvalid,
    input  logic                        eng_bready,

    // ------------------------------------------------------------------
    // wrapper side: axi4ace_master_rd AR / axi4ace_master_wr AW + B
    // ------------------------------------------------------------------
    output logic [IW-1:0]               fub_arid,
    output logic [ADDR_WIDTH-1:0]       fub_araddr,
    output logic [7:0]                  fub_arlen,
    output logic [2:0]                  fub_arsize,
    output logic [1:0]                  fub_arburst,
    output logic                        fub_arlock,
    output logic [3:0]                  fub_arcache,
    output logic [2:0]                  fub_arprot,
    output logic [3:0]                  fub_arqos,
    output logic [3:0]                  fub_arregion,
    output logic [UW-1:0]               fub_aruser,
    output logic [3:0]                  fub_arsnoop,
    output logic                        fub_arvalid,
    input  logic                        fub_arready,

    output logic [IW-1:0]               fub_awid,
    output logic [ADDR_WIDTH-1:0]       fub_awaddr,
    output logic [7:0]                  fub_awlen,
    output logic [2:0]                  fub_awsize,
    output logic [1:0]                  fub_awburst,
    output logic                        fub_awlock,
    output logic [3:0]                  fub_awcache,
    output logic [2:0]                  fub_awprot,
    output logic [3:0]                  fub_awqos,
    output logic [3:0]                  fub_awregion,
    output logic [UW-1:0]               fub_awuser,
    output logic [2:0]                  fub_awsnoop,
    output logic                        fub_awvalid,
    input  logic                        fub_awready,

    input  logic [IW-1:0]               fub_bid,
    input  logic [1:0]                  fub_bresp,
    input  logic [UW-1:0]               fub_buser,
    input  logic                        fub_bvalid,
    output logic                        fub_bready
);

    amber_ace_issue #(
        .ADDR_WIDTH     (ADDR_WIDTH),
        .BUS_WIDTH      (BUS_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_USER_WIDTH (AXI_USER_WIDTH)
    ) u_issue (
        .aclk          (clk),
        .aresetn       (rst_n),
        .ace_rd_req    (ace_rd_req),
        .ace_rd_type   (ace_rd_type),
        .ace_rd_addr   (ace_rd_addr),
        .ace_rd_len    (ace_rd_len),
        .ace_wr_req    (ace_wr_req),
        .ace_wr_type   (ace_wr_type),
        .ace_wr_addr   (ace_wr_addr),
        .ace_wr_len    (ace_wr_len),
        .eng_arid      (eng_arid),
        .eng_araddr    (eng_araddr),
        .eng_arlen     (eng_arlen),
        .eng_arsize    (eng_arsize),
        .eng_arburst   (eng_arburst),
        .eng_arlock    (eng_arlock),
        .eng_arcache   (eng_arcache),
        .eng_arprot    (eng_arprot),
        .eng_arqos     (eng_arqos),
        .eng_arregion  (eng_arregion),
        .eng_aruser    (eng_aruser),
        .eng_arvalid   (eng_arvalid),
        .eng_arready   (eng_arready),
        .eng_awid      (eng_awid),
        .eng_awaddr    (eng_awaddr),
        .eng_awlen     (eng_awlen),
        .eng_awsize    (eng_awsize),
        .eng_awburst   (eng_awburst),
        .eng_awlock    (eng_awlock),
        .eng_awcache   (eng_awcache),
        .eng_awprot    (eng_awprot),
        .eng_awqos     (eng_awqos),
        .eng_awregion  (eng_awregion),
        .eng_awuser    (eng_awuser),
        .eng_awvalid   (eng_awvalid),
        .eng_awready   (eng_awready),
        .eng_bid       (eng_bid),
        .eng_bresp     (eng_bresp),
        .eng_buser     (eng_buser),
        .eng_bvalid    (eng_bvalid),
        .eng_bready    (eng_bready),
        .fub_arid      (fub_arid),
        .fub_araddr    (fub_araddr),
        .fub_arlen     (fub_arlen),
        .fub_arsize    (fub_arsize),
        .fub_arburst   (fub_arburst),
        .fub_arlock    (fub_arlock),
        .fub_arcache   (fub_arcache),
        .fub_arprot    (fub_arprot),
        .fub_arqos     (fub_arqos),
        .fub_arregion  (fub_arregion),
        .fub_aruser    (fub_aruser),
        .fub_arsnoop   (fub_arsnoop),
        .fub_arvalid   (fub_arvalid),
        .fub_arready   (fub_arready),
        .fub_awid      (fub_awid),
        .fub_awaddr    (fub_awaddr),
        .fub_awlen     (fub_awlen),
        .fub_awsize    (fub_awsize),
        .fub_awburst   (fub_awburst),
        .fub_awlock    (fub_awlock),
        .fub_awcache   (fub_awcache),
        .fub_awprot    (fub_awprot),
        .fub_awqos     (fub_awqos),
        .fub_awregion  (fub_awregion),
        .fub_awuser    (fub_awuser),
        .fub_awsnoop   (fub_awsnoop),
        .fub_awvalid   (fub_awvalid),
        .fub_awready   (fub_awready),
        .fub_bid       (fub_bid),
        .fub_bresp     (fub_bresp),
        .fub_buser     (fub_buser),
        .fub_bvalid    (fub_bvalid),
        .fub_bready    (fub_bready)
    );

endmodule : amber_ace_issue_th
