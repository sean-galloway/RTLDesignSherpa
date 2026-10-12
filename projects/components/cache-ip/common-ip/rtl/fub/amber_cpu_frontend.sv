// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: amber_cpu_frontend
// Purpose:
//   CPU-facing GAXI slave for the amber MESI L1 (MAS ch02_blocks/09 +
//   ch03_interfaces/01): accepts the packed {addr, we, be, wdata} request
//   on the cpu_req_wr_* write stream, presents it to amber_control as a
//   single-cycle req_valid pulse with the fields held until the response,
//   and returns the response on the cpu_rsp_rd_* read stream. The cache
//   is blocking -- exactly one request is in flight -- and this module is
//   the only port the CPU sees.
//
// Documentation: projects/components/cache-ip/amber-mesi-l1/docs/amber_mas/ch02_blocks/09_frontend_monlite.md
// Subsystem: amber
//
// Author: sean galloway
// Created: 2026-10-08

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: amber_cpu_frontend
//==============================================================================
// Description:
//   Request channel (MAS ch02/09 Table: cpu_req_wr_*):
//     cpu_req_wr_ready = ctrl_req_ready && stage_wr_ready: asserted only
//     while amber_control is in CTRL_IDLE (no snoop priority stall) AND
//     the response staging queue has room for this request's response.
//     The request fields pass through combinationally from the packed
//     payload -- the GAXI master holds them stable while valid is up, and
//     amber_control latches {addr, we, be, wdata} in the accept cycle, so
//     no frontend register is needed; req_valid = the GAXI handshake, a
//     single-cycle pulse by construction (ready drops the cycle after the
//     accept as control leaves CTRL_IDLE).
//
//   Response channel (DECISION D-6): amber_control's ctrl_rsp_valid is a
//     one-cycle pulse (hit states re-assert it for one cycle only), so
//     the response is staged in a gaxi_fifo_sync DEPTH=2: cpu_rsp_rd_valid
//     is the FIFO's not-empty, the payload is the FIFO read port (held
//     byte-stable while the read pointer is parked), and the handshake is
//     cpu_rsp_rd_ready. The FIFO cannot overflow: a new request is only
//     accepted with wr_ready high (>= 1 free entry), and the blocking
//     pipeline produces at most one response per accepted request.
//
//   A miss (fill + DECISION D-4 replay) is a single GAXI transaction: the
//     replay re-drives control's own latched request internally; the
//     frontend sees one request, one response.
//
//   Packed payloads (MAS ch02/09):
//     CPU_REQ_W = ADDR_WIDTH + 1 + BUS_WIDTH/8 + BUS_WIDTH
//     cpu_req_wr_data = {addr[ADDR_WIDTH-1:0], we, be[STRB_W-1:0],
//                        wdata[BUS_WIDTH-1:0]}      (addr at the MSBs)
//     CPU_RSP_W = BUS_WIDTH
//     cpu_rsp_rd_data = {rdata[BUS_WIDTH-1:0]}
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH / SETS / WAYS / LINE_BYTES / BUS_WIDTH:
//     Description: geometry per amber_pkg defaults (HAS Table 5.0)
//     Type: int
//
//------------------------------------------------------------------------------
// Notes:
//   - Pure wiring + the staging FIFO: no other registers in this module.
//   - The snoop-priority detour (CTRL_SNOOP granted at IDLE while a
//     request is pending) is control's concern; the handshake here is
//     unchanged -- the response arrives after the service either way.
//
//------------------------------------------------------------------------------
// Related Modules:
//   - Instantiated by: amber_core (test harness: dv/tb/amber_frontend_th.sv)
//   - Binds to: amber_control req_valid/ctrl_req_ready/ctrl_rsp_* contract
//   - Queue: gaxi_fifo_sync u_rsp_stage, DEPTH=2 (DECISION D-6)
//
//------------------------------------------------------------------------------
// Test:
//   Location: projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_frontend.py
//   Run: pytest projects/components/cache-ip/amber-mesi-l1/dv/tests/test_amber_frontend.py -v
//
//==============================================================================

module amber_cpu_frontend
    import amber_pkg::*;
#(
    parameter int ADDR_WIDTH = AMBER_ADDR_WIDTH,
    parameter int SETS       = AMBER_SETS,
    parameter int WAYS       = AMBER_WAYS,
    parameter int LINE_BYTES = AMBER_LINE_BYTES,
    parameter int BUS_WIDTH  = AMBER_BUS_WIDTH,
    localparam int STRB_W     = BUS_WIDTH / 8,
    localparam int CPU_REQ_W  = ADDR_WIDTH + 1 + STRB_W + BUS_WIDTH,
    localparam int CPU_RSP_W  = BUS_WIDTH
)(
    input  logic                     clk,
    input  logic                     rst_n,

    // CPU GAXI request channel (write stream)
    input  logic                     cpu_req_wr_valid,
    output logic                     cpu_req_wr_ready,
    input  logic [CPU_REQ_W-1:0]     cpu_req_wr_data,

    // CPU GAXI response channel (read stream)
    output logic                     cpu_rsp_rd_valid,
    input  logic                     cpu_rsp_rd_ready,
    output logic [CPU_RSP_W-1:0]     cpu_rsp_rd_data,

    // amber_control request/response contract
    output logic                     req_valid,
    output logic [ADDR_WIDTH-1:0]    req_addr,
    output logic                     req_we,
    output logic [STRB_W-1:0]        req_be,
    output logic [BUS_WIDTH-1:0]     req_wdata,
    input  logic                     ctrl_req_ready,
    input  logic                     ctrl_rsp_valid,
    input  logic [BUS_WIDTH-1:0]     ctrl_rsp_data
);

    // ------------------------------------------------------------------
    // Elaboration-time geometry checks (same contract as the arrays)
    // ------------------------------------------------------------------
    initial begin
        if ((SETS & (SETS - 1)) != 0)
            $error("amber_cpu_frontend: SETS must be a power of two");
        if ((LINE_BYTES & (LINE_BYTES - 1)) != 0)
            $error("amber_cpu_frontend: LINE_BYTES must be a power of two");
        if ((BUS_WIDTH % 8) != 0)
            $error("amber_cpu_frontend: BUS_WIDTH must be a multiple of 8");
    end

    // ------------------------------------------------------------------
    // Response staging queue (DECISION D-6)
    // ------------------------------------------------------------------
    logic                 stage_wr_ready;
    logic                 stage_rd_valid;
    logic [BUS_WIDTH-1:0] stage_rd_data;

    gaxi_fifo_sync #(
        .DATA_WIDTH (BUS_WIDTH),
        .DEPTH      (2)
    ) u_rsp_stage (
        .axi_aclk    (clk),
        .axi_aresetn (rst_n),
        .wr_valid    (ctrl_rsp_valid),
        .wr_ready    (stage_wr_ready),
        .wr_data     (ctrl_rsp_data),
        .rd_ready    (cpu_rsp_rd_ready),
        .count       (),
        .rd_valid    (stage_rd_valid),
        .rd_data     (stage_rd_data)
    );

    // ------------------------------------------------------------------
    // Request channel: pass-through with the accept handshake
    // ------------------------------------------------------------------
    // Ready only in CTRL_IDLE (ctrl_req_ready) with room for this
    // request's response in the staging queue (MAS ch02/09: the front end
    // does not accept a new request until it can complete the old one).
    assign cpu_req_wr_ready = ctrl_req_ready && stage_wr_ready;

    // The control-side accept: a single-cycle pulse in the GAXI handshake
    // cycle; control latches the fields there and holds them internally
    // until the response.
    assign req_valid = cpu_req_wr_valid && cpu_req_wr_ready;
    assign req_addr  = cpu_req_wr_data[CPU_REQ_W-1 -: ADDR_WIDTH];
    assign req_we    = cpu_req_wr_data[BUS_WIDTH + STRB_W];
    assign req_be    = cpu_req_wr_data[BUS_WIDTH + STRB_W - 1 : BUS_WIDTH];
    assign req_wdata = cpu_req_wr_data[BUS_WIDTH-1:0];

    // ------------------------------------------------------------------
    // Response channel: the FIFO read port, held stable by the parked
    // read pointer while cpu_rsp_rd_ready is low
    // ------------------------------------------------------------------
    assign cpu_rsp_rd_valid = stage_rd_valid;
    assign cpu_rsp_rd_data  = stage_rd_data;

endmodule : amber_cpu_frontend
