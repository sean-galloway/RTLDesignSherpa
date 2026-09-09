// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axil4_to_wb4_core
// Purpose: AXI4-Lite channel set (the fub_* side of axil4_slave_wr/rd) to
//          the Wishbone command/response queue contract of wb4_master.
//
// Documentation: projects/components/converters/docs/converter_mas/ch03_protocol_blocks/10_axil4_to_wb4.md
// Subsystem: converters
//
// Author: sean galloway
// Created: 2026-09-09
//
//==============================================================================
// Description:
//   Five AXI4-Lite channels in (AW, W, B, AR, R as plain valid/ready
//   channels, no ID, no burst), one command queue and one response queue
//   out. A write is issued when AW and W are both present; a read when AR
//   is. Both compete for the single command queue, and when both are ready
//   the one not served last wins, so neither side can starve the other.
//
//   Wishbone terminates in issue order, so a one-bit side queue (write or
//   read, pushed at issue) is all that is needed to steer each response to
//   B or R. Status maps ACK -> OKAY, ERR -> SLVERR, RTY -> RTY_RESP
//   (SLVERR by default; AXI has no retry, so the requester sees an error
//   unless a retry wrapper sits between this block and the master).
//
//   No width conversion: the AXI4-Lite and Wishbone address and data widths
//   are the same. Put an axi4_dwidth_* / axil_to_axi4_wide_align_* block in
//   front when they are not.
//
//------------------------------------------------------------------------------
// Parameters:
//------------------------------------------------------------------------------
//   ADDR_WIDTH, DATA_WIDTH - shared by both sides
//   SIDE_DEPTH             - direction queue depth; bounds the transfers in
//                            flight through this block. Size it to at least
//                            the master's CMD_DEPTH + RSP_DEPTH so the
//                            master, not this queue, sets the pipeline depth.
//   RTY_RESP               - AXI response returned for a Wishbone RTY
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - axil4_to_wb4.sv (wrapper with the AXI4-Lite skids and wb4_master)
//   - axil4_slave_wr.sv / axil4_slave_rd.sv, wb4_master.sv
//
//------------------------------------------------------------------------------
// Test:
//------------------------------------------------------------------------------
//   Location: projects/components/converters/dv/tests/test_axil4_to_wb4.py
//   (through the wrapper)
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axil4_to_wb4_core
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int SIDE_DEPTH = 8,
    parameter logic [1:0] RTY_RESP = 2'b10,   // SLVERR
    // Short params
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = DW/8,
    parameter int STW = WB4_STATUS_WIDTH
)
(
    input  logic              aclk,
    input  logic              aresetn,

    // AXI4-Lite channels (fub_* side of the slave skids)
    input  logic [AW-1:0]     fub_awaddr,
    input  logic [2:0]        fub_awprot,
    input  logic              fub_awvalid,
    output logic              fub_awready,

    input  logic [DW-1:0]     fub_wdata,
    input  logic [SW-1:0]     fub_wstrb,
    input  logic              fub_wvalid,
    output logic              fub_wready,

    output logic [1:0]        fub_bresp,
    output logic              fub_bvalid,
    input  logic              fub_bready,

    input  logic [AW-1:0]     fub_araddr,
    input  logic [2:0]        fub_arprot,
    input  logic              fub_arvalid,
    output logic              fub_arready,

    output logic [DW-1:0]     fub_rdata,
    output logic [1:0]        fub_rresp,
    output logic              fub_rvalid,
    input  logic              fub_rready,

    // Wishbone command / response queues (wb4_master side)
    output logic              cmd_valid,
    input  logic              cmd_ready,
    output logic              cmd_we,
    output logic [AW-1:0]     cmd_adr,
    output logic [DW-1:0]     cmd_dat,
    output logic [SW-1:0]     cmd_sel,

    input  logic              rsp_valid,
    output logic              rsp_ready,
    input  logic [STW-1:0]    rsp_status,
    input  logic [DW-1:0]     rsp_dat
);

    // ------------------------------------------------------------------------
    // Issue side: pick a write (AW and W present) or a read (AR present)
    // ------------------------------------------------------------------------
    logic w_wr_avail, w_rd_avail, w_pick_wr, w_issue;
    logic w_side_wr_ready, w_side_rd_valid, w_side_head_we;
    logic r_last_wr;

    assign w_wr_avail = fub_awvalid && fub_wvalid;
    assign w_rd_avail = fub_arvalid;
    // Both present: alternate. One present: take it.
    assign w_pick_wr  = w_wr_avail && (!w_rd_avail || !r_last_wr);

    assign cmd_valid  = (w_wr_avail || w_rd_avail) && w_side_wr_ready;
    assign cmd_we     = w_pick_wr;
    assign cmd_adr    = w_pick_wr ? fub_awaddr : fub_araddr;
    assign cmd_dat    = fub_wdata;
    assign cmd_sel    = w_pick_wr ? fub_wstrb : {SW{1'b1}};
    assign w_issue    = cmd_valid && cmd_ready;

    assign fub_awready = w_issue &&  w_pick_wr;
    assign fub_wready  = w_issue &&  w_pick_wr;
    assign fub_arready = w_issue && !w_pick_wr;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_last_wr <= 1'b0;
        else if (w_issue)           r_last_wr <= w_pick_wr;
    )

    // Direction of every issued command, in order (mux read: the head is
    // valid in the clock of its handshake, which is when B/R are formed).
    logic w_side_rd_ready;
    gaxi_fifo_sync #(
        .REGISTERED (0),
        .DATA_WIDTH (1),
        .DEPTH      (SIDE_DEPTH)
    ) side_queue (
        .axi_aclk    (aclk),
        .axi_aresetn (aresetn),
        .wr_valid    (w_issue),
        .wr_ready    (w_side_wr_ready),
        .wr_data     (w_pick_wr),
        .rd_ready    (w_side_rd_ready),
        /* verilator lint_off PINCONNECTEMPTY */
        .count       (),
        /* verilator lint_on PINCONNECTEMPTY */
        .rd_valid    (w_side_rd_valid),
        .rd_data     (w_side_head_we)
    );

    // ------------------------------------------------------------------------
    // Response side: steer the oldest termination to B or R
    // ------------------------------------------------------------------------
    logic [1:0] w_resp;
    always_comb begin
        case (rsp_status)
            STW'(WB4_RSP_ERR): w_resp = 2'b10;      // SLVERR
            STW'(WB4_RSP_RTY): w_resp = RTY_RESP;
            default:           w_resp = 2'b00;      // OKAY
        endcase
    end

    logic w_rsp_hs;
    assign fub_bvalid = rsp_valid && w_side_rd_valid &&  w_side_head_we;
    assign fub_rvalid = rsp_valid && w_side_rd_valid && !w_side_head_we;
    assign fub_bresp  = w_resp;
    assign fub_rresp  = w_resp;
    assign fub_rdata  = rsp_dat;

    // A response with nothing recorded is a master protocol violation
    // (wb4_master reports it in simulation); it is dropped here so the
    // queue cannot wedge on it.
    assign w_rsp_hs        = rsp_valid && (!w_side_rd_valid ||
                             (w_side_head_we ? fub_bready : fub_rready));
    assign rsp_ready       = w_rsp_hs;
    assign w_side_rd_ready = w_rsp_hs && w_side_rd_valid;

    // Protection bits are not carried by Wishbone.
    /* verilator lint_off UNUSEDSIGNAL */
    logic w_unused;
    assign w_unused = ^{fub_awprot, fub_arprot};
    /* verilator lint_on UNUSEDSIGNAL */

`ifdef FORMAL
    logic f_past_valid;
    initial f_past_valid = 1'b0;
    always_ff @(posedge aclk) f_past_valid <= 1'b1;
    always_ff @(posedge aclk) if (f_past_valid && aresetn && $past(aresetn)) begin
        // A write handshake takes AW and W together, never one alone.
        assert (fub_awready == fub_wready);
        // Never a write and a read issue in the same clock.
        assert (!(fub_awready && fub_arready));
        // B and R never fire together (one response queue, one direction).
        assert (!(fub_bvalid && fub_rvalid));
        // A command is only issued with a direction recorded.
        assert (!w_issue || w_side_wr_ready);
    end
`endif

endmodule : axil4_to_wb4_core
