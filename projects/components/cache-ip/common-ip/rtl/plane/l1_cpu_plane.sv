// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: l1_cpu_plane
// Purpose:
//   CPU plane for the cache-ip shared MESI L1 (cache-ip plane restructure,
//   Task 1): isolates the GAXI CPU slave (l1_cpu_frontend) as a named
//   protocol-generation boundary. The plane translates the CPU GAXI
//   cpu_req_wr_*/cpu_rsp_rd_* pins into the core-facing CPU seam
//   (fe_req_valid/addr/we/be/wdata, ctrl_req_ready, ctrl_rsp_valid/data).
//   Pure structural integration: no new control logic.
//
// Documentation: projects/components/cache-ip/common-ip/docs/l1_fabric_contract.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-11-01

`timescale 1ns / 1ps

//==============================================================================
// Module: l1_cpu_plane
//==============================================================================
// Description:
//   The CPU-side protocol-generation plane. Every CPU-generation variant
//   (amber, jet, future RV32A) owns its CPU plane; this common-ip block is
//   the amber CPU seam v1. The module is intentionally thin: all cache-side
//   state and partner wiring lives in the coherence core plane.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / WAYS / LINE_BYTES / BUS_WIDTH:
//     Description: geometry per l1_pkg defaults (HAS Table 5.0)
//     Type: int
//
//------------------------------------------------------------------------------
// Notes:
//   - Single clock / active-low reset domain (clk / rst_n).
//   - The CPU seam is the same handshake exported by l1_cpu_frontend; the
//     coherence core plane consumes it unchanged.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: l1_core (aggregate), amber_top / amber_ace_top
//   - Instantiated: l1_cpu_frontend
//   - Package: l1_pkg
//
//==============================================================================

module l1_cpu_plane
    import l1_pkg::*;
#(
    parameter int ADDR_WIDTH = AMBER_ADDR_WIDTH,
    parameter int SETS       = AMBER_SETS,
    parameter int WAYS       = AMBER_WAYS,
    parameter int LINE_BYTES = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH  = AMBER_BUS_WIDTH,
    localparam int STRB_W    = BUS_WIDTH / 8,
    localparam int CPU_REQ_W = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH,
    localparam int CPU_RSP_W = BUS_WIDTH
)(
    input  logic                        clk,
    input  logic                        rst_n,

    // ------------------------------------------------------------------
    // CPU GAXI slave (MAS ch03/01; packed {addr, we, be, wdata} /
    // {rdata})
    // ------------------------------------------------------------------
    input  logic                        cpu_req_wr_valid,
    output logic                        cpu_req_wr_ready,
    input  logic [CPU_REQ_W-1:0]        cpu_req_wr_data,
    output logic                        cpu_rsp_rd_valid,
    input  logic                        cpu_rsp_rd_ready,
    output logic [CPU_RSP_W-1:0]        cpu_rsp_rd_data,

    // ------------------------------------------------------------------
    // CPU seam to the coherence core plane
    // ------------------------------------------------------------------
    output logic                        fe_req_valid,
    output logic [ADDR_WIDTH-1:0]       fe_req_addr,
    output logic                        fe_req_we,
    output logic [STRB_W-1:0]           fe_req_be,
    output logic [BUS_WIDTH-1:0]        fe_req_wdata,
    input  logic                        ctrl_req_ready,
    input  logic                        ctrl_rsp_valid,
    input  logic [BUS_WIDTH-1:0]        ctrl_rsp_data
);

    // ------------------------------------------------------------------
    // CPU frontend: GAXI slave <-> CPU seam
    // ------------------------------------------------------------------
    l1_cpu_frontend #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .SETS       (SETS),
        .WAYS       (WAYS),
        .LINE_BYTES (LINE_BYTES),
        .BUS_WIDTH  (BUS_WIDTH)
    ) u_frontend (
        .clk               (clk),
        .rst_n             (rst_n),
        .cpu_req_wr_valid  (cpu_req_wr_valid),
        .cpu_req_wr_ready  (cpu_req_wr_ready),
        .cpu_req_wr_data   (cpu_req_wr_data),
        .cpu_rsp_rd_valid  (cpu_rsp_rd_valid),
        .cpu_rsp_rd_ready  (cpu_rsp_rd_ready),
        .cpu_rsp_rd_data   (cpu_rsp_rd_data),
        .req_valid         (fe_req_valid),
        .req_addr          (fe_req_addr),
        .req_we            (fe_req_we),
        .req_be            (fe_req_be),
        .req_wdata         (fe_req_wdata),
        .ctrl_req_ready    (ctrl_req_ready),
        .ctrl_rsp_valid    (ctrl_rsp_valid),
        .ctrl_rsp_data     (ctrl_rsp_data)
    );

endmodule : l1_cpu_plane
