// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: avmm_to_axil4
// Purpose: Avalon-MM slave in, AXI4-Lite master out.
//
// Documentation: projects/fpga-systems/DE10-Standard/fabric-benchmark/PRD.md
// Subsystem: converters
//
// Author: sean galloway
// Created: 2026-10-14
//
//==============================================================================
// Description:
//   The host front-end for Intel boards. Quartus has no JTAG-to-AXI master;
//   its debug master is the "JTAG to Avalon Master Bridge", an Avalon-MM
//   master. This block sits behind it and presents the AXI4-Lite master the
//   harness bridges expect, so an Intel harness has the same front-end
//   contract as the Xilinx harnesses' uart_axil_bridge.
//
//   One transfer at a time. waitrequest is held until the AXI side has
//   answered, which makes every write non-posted: a configuration write is
//   complete at the slave before the next command is accepted, and the order
//   the host wrote things in is the order they land. The JTAG master is
//   nowhere near fast enough for pipelining to matter.
//
//   Avalon side (pipelined, variable latency):
//     - byte addresses (declare addressUnits SYMBOLS if packaged for
//       Platform Designer); address and byteenable pass straight through
//     - a read is accepted in the clock its R beat arrives and returned one
//       clock later on readdatavalid, as Avalon requires
//     - a write is accepted in the clock its B response arrives;
//       writeresponsevalid follows one clock later for masters that use it
//     - response[1:0] carries RRESP/BRESP unchanged: the two encodings are
//       identical (00 OKAY, 10 SLVERR/SLAVEERROR, 11 DECERR/DECODEERROR)
//     - read and write together is illegal Avalon; the write wins
//
//   No width conversion. Both sides share ADDR_WIDTH and DATA_WIDTH; put a
//   width converter behind this block when they differ.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH, DATA_WIDTH - shared by both sides
//   SKID_DEPTH_*           - the AXI4-Lite masters' channel skids
//   AXIL_PROT              - AWPROT/ARPROT driven on every command (Avalon
//                            carries no protection bits)
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - uart_axil_bridge (the Xilinx-board front-end this one stands in for)
//   - wb4_to_axil4.sv (the same job from a Wishbone master)
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/utility-ip/converters/dv/tests/test_avmm_to_axil4.py
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module avmm_to_axil4 #(
    parameter int ADDR_WIDTH    = 32,
    parameter int DATA_WIDTH    = 32,
    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 2,
    parameter int SKID_DEPTH_B  = 2,
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R  = 2,
    parameter logic [2:0] AXIL_PROT = 3'b000,
    // Short params
    parameter int AW = ADDR_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int SW = DW/8
)
(
    input  logic              aclk,
    input  logic              aresetn,

    // Avalon-MM slave
    input  logic [AW-1:0]     s_avmm_address,
    input  logic              s_avmm_read,
    input  logic              s_avmm_write,
    input  logic [DW-1:0]     s_avmm_writedata,
    input  logic [SW-1:0]     s_avmm_byteenable,
    output logic              s_avmm_waitrequest,
    output logic [DW-1:0]     s_avmm_readdata,
    output logic              s_avmm_readdatavalid,
    output logic [1:0]        s_avmm_response,
    output logic              s_avmm_writeresponsevalid,

    // AXI4-Lite master
    output logic [AW-1:0]     m_axil_awaddr,
    output logic [2:0]        m_axil_awprot,
    output logic              m_axil_awvalid,
    input  logic              m_axil_awready,
    output logic [DW-1:0]     m_axil_wdata,
    output logic [SW-1:0]     m_axil_wstrb,
    output logic              m_axil_wvalid,
    input  logic              m_axil_wready,
    input  logic [1:0]        m_axil_bresp,
    input  logic              m_axil_bvalid,
    output logic              m_axil_bready,
    output logic [AW-1:0]     m_axil_araddr,
    output logic [2:0]        m_axil_arprot,
    output logic              m_axil_arvalid,
    input  logic              m_axil_arready,
    input  logic [DW-1:0]     m_axil_rdata,
    input  logic [1:0]        m_axil_rresp,
    input  logic              m_axil_rvalid,
    output logic              m_axil_rready,

    output logic              busy
);
    // Boundary reset synchronization. The port aresetn is treated as an
    // asynchronous-assert input of unknown deassert quality: an N=3
    // reset_sync (rtl/cdc, formally proven) produces the internal reset
    // every block below sees.
    logic w_aresetn;
    reset_sync #(
        .N             (3),
        .KEEP_ATTRS    (1'b1),
        .IN_ACTIVE_LOW (1'b1),
        .OUT_ACTIVE_LOW(1'b1),
        .ASYNC_ASSERT  (1'b1)
    ) u_reset_sync (
        .clk        (aclk),
        .rst_n      (aresetn),
        .sync_rst_n (w_aresetn)
    );


    // core <-> axil masters
    logic          w_awvalid, w_awready, w_wvalid, w_wready;
    logic          w_bvalid, w_bready, w_arvalid, w_arready, w_rvalid, w_rready;
    logic [DW-1:0] w_rdata;
    logic [1:0]    w_bresp, w_rresp;
    logic          w_busy_wr, w_busy_rd;

    // ------------------------------------------------------------------------
    // Issue. The Avalon master holds the command steady while waitrequest is
    // high, so each channel is driven until its own handshake and then
    // remembered as sent; AW and W go independently.
    // ------------------------------------------------------------------------
    logic w_wr_req, w_rd_req;
    logic r_aw_sent, r_w_sent, r_ar_sent;
    logic w_aw_hs, w_w_hs, w_ar_hs;
    logic w_accept_wr, w_accept_rd;

    assign w_wr_req = s_avmm_write;
    assign w_rd_req = s_avmm_read && !s_avmm_write;

    assign w_awvalid = w_wr_req && !r_aw_sent;
    assign w_wvalid  = w_wr_req && !r_w_sent;
    assign w_arvalid = w_rd_req && !r_ar_sent;

    assign w_aw_hs = w_awvalid && w_awready;
    assign w_w_hs  = w_wvalid  && w_wready;
    assign w_ar_hs = w_arvalid && w_arready;

    // ------------------------------------------------------------------------
    // Accept. Only one transfer is ever open, so a B or R beat that arrives
    // after this transfer's issue belongs to it.
    // ------------------------------------------------------------------------
    assign w_accept_wr = w_wr_req && r_aw_sent && r_w_sent && w_bvalid;
    assign w_accept_rd = w_rd_req && r_ar_sent && w_rvalid;

    assign w_bready = w_accept_wr;
    assign w_rready = w_accept_rd;

    assign s_avmm_waitrequest = !(w_accept_wr || w_accept_rd);

    `ALWAYS_FF_RST(aclk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
            r_aw_sent <= 1'b0;
            r_w_sent  <= 1'b0;
            r_ar_sent <= 1'b0;
        end else begin
            r_aw_sent <= w_accept_wr ? 1'b0 : (r_aw_sent || w_aw_hs);
            r_w_sent  <= w_accept_wr ? 1'b0 : (r_w_sent  || w_w_hs);
            r_ar_sent <= w_accept_rd ? 1'b0 : (r_ar_sent || w_ar_hs);
        end
    )

    // ------------------------------------------------------------------------
    // Return. Avalon wants read data at least one clock after the command is
    // accepted, so the R beat is registered here; the write response rides
    // the same register.
    // ------------------------------------------------------------------------
    logic [DW-1:0] r_rdata;
    logic [1:0]    r_resp;
    logic          r_rdv, r_wrv;

    `ALWAYS_FF_RST(aclk, w_aresetn,
        if (`RST_ASSERTED(w_aresetn)) begin
            r_rdata <= '0;
            r_resp  <= 2'b00;
            r_rdv   <= 1'b0;
            r_wrv   <= 1'b0;
        end else begin
            r_rdv <= w_accept_rd;
            r_wrv <= w_accept_wr;
            if (w_accept_rd) begin
                r_rdata <= w_rdata;
                r_resp  <= w_rresp;
            end else if (w_accept_wr) begin
                r_resp  <= w_bresp;
            end
        end
    )

    assign s_avmm_readdata           = r_rdata;
    assign s_avmm_readdatavalid      = r_rdv;
    assign s_avmm_writeresponsevalid = r_wrv;
    assign s_avmm_response           = r_resp;

    axil4_master_wr #(
        .AXIL_ADDR_WIDTH (AW),
        .AXIL_DATA_WIDTH (DW),
        .SKID_DEPTH_AW   (SKID_DEPTH_AW),
        .SKID_DEPTH_W    (SKID_DEPTH_W),
        .SKID_DEPTH_B    (SKID_DEPTH_B)
    ) u_axil_wr (
        .aclk           (aclk),
        .aresetn        (w_aresetn),
        .fub_awaddr     (s_avmm_address),
        .fub_awprot     (AXIL_PROT),
        .fub_awvalid    (w_awvalid),
        .fub_awready    (w_awready),
        .fub_wdata      (s_avmm_writedata),
        .fub_wstrb      (s_avmm_byteenable),
        .fub_wvalid     (w_wvalid),
        .fub_wready     (w_wready),
        .fub_bresp      (w_bresp),
        .fub_bvalid     (w_bvalid),
        .fub_bready     (w_bready),
        .m_axil_awaddr  (m_axil_awaddr),
        .m_axil_awprot  (m_axil_awprot),
        .m_axil_awvalid (m_axil_awvalid),
        .m_axil_awready (m_axil_awready),
        .m_axil_wdata   (m_axil_wdata),
        .m_axil_wstrb   (m_axil_wstrb),
        .m_axil_wvalid  (m_axil_wvalid),
        .m_axil_wready  (m_axil_wready),
        .m_axil_bresp   (m_axil_bresp),
        .m_axil_bvalid  (m_axil_bvalid),
        .m_axil_bready  (m_axil_bready),
        .busy           (w_busy_wr)
    );

    axil4_master_rd #(
        .AXIL_ADDR_WIDTH (AW),
        .AXIL_DATA_WIDTH (DW),
        .SKID_DEPTH_AR   (SKID_DEPTH_AR),
        .SKID_DEPTH_R    (SKID_DEPTH_R)
    ) u_axil_rd (
        .aclk           (aclk),
        .aresetn        (w_aresetn),
        .fub_araddr     (s_avmm_address),
        .fub_arprot     (AXIL_PROT),
        .fub_arvalid    (w_arvalid),
        .fub_arready    (w_arready),
        .fub_rdata      (w_rdata),
        .fub_rresp      (w_rresp),
        .fub_rvalid     (w_rvalid),
        .fub_rready     (w_rready),
        .m_axil_araddr  (m_axil_araddr),
        .m_axil_arprot  (m_axil_arprot),
        .m_axil_arvalid (m_axil_arvalid),
        .m_axil_arready (m_axil_arready),
        .m_axil_rdata   (m_axil_rdata),
        .m_axil_rresp   (m_axil_rresp),
        .m_axil_rvalid  (m_axil_rvalid),
        .m_axil_rready  (m_axil_rready),
        .busy           (w_busy_rd)
    );

    assign busy = w_busy_wr || w_busy_rd || r_aw_sent || r_w_sent || r_ar_sent;

endmodule : avmm_to_axil4
