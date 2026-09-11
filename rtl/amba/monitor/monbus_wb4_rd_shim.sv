// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: monbus_wb4_rd_shim
// Purpose: Wishbone B4 slave in, AXI4-Lite READ master out, for the
//          read-only CSR port of a monbus group.
//
// Documentation: docs/markdown/rtl-amba/monitor/monbus_wb4_groups.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2026-09-10
//
//==============================================================================
// Description:
//   A monbus group presents a read-only AXI4-Lite slave: a host reads the
//   drained records and the statistics, and writes nothing. This shim lets a
//   Wishbone host do the same, so a Wishbone-based system can own a monitor
//   group without an AXI bridge in the path.
//
//   Read-only is enforced, not assumed. A Wishbone WRITE to this space is
//   terminated with ERR rather than silently dropped or, worse, acknowledged
//   as if it had done something.
//
//   One transfer at a time. The CSR port is a host reading a drain register;
//   pipelining it would add a reorder buffer to save nothing.
//
//   This is deliberately NOT wb4_to_axil4: that block carries the write
//   channels and an outstanding queue this port has no use for.
//
//------------------------------------------------------------------------------
// Related Modules:
//------------------------------------------------------------------------------
//   - monbus_wb4_axil4_group.sv / monbus_wb4_axi4_group.sv (its only users)
//   - wb4_to_axil4.sv (the full bidirectional converter)
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module monbus_wb4_rd_shim
    import wb4_pkg::*;
#(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 64,      // the group's read beat
    parameter int CMD_DEPTH  = 2,
    parameter int RSP_DEPTH  = 2,
    parameter int CLASSIC    = 0,
    parameter logic [2:0] AXIL_PROT = 3'b000,
    // Short params
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int SW  = DW/8,
    parameter int CTW = WB4_CTI_WIDTH,
    parameter int BTW = WB4_BTE_WIDTH
)
(
    input  logic              clk,
    input  logic              aresetn,

    // Wishbone B4 slave (the host side)
    input  logic              s_wb_CYC,
    input  logic              s_wb_STB,
    input  logic              s_wb_WE,
    input  logic [AW-1:0]     s_wb_ADR,
    input  logic [DW-1:0]     s_wb_DAT_W,
    input  logic [SW-1:0]     s_wb_SEL,
    input  logic [CTW-1:0]    s_wb_CTI,
    input  logic [BTW-1:0]    s_wb_BTE,
    output logic              s_wb_STALL,
    output logic              s_wb_ACK,
    output logic              s_wb_ERR,
    output logic              s_wb_RTY,
    output logic [DW-1:0]     s_wb_DAT_R,

    // AXI4-Lite read master (into the group's CSR slave port)
    output logic              m_axil_arvalid,
    input  logic              m_axil_arready,
    output logic [AW-1:0]     m_axil_araddr,
    output logic [2:0]        m_axil_arprot,
    input  logic              m_axil_rvalid,
    output logic              m_axil_rready,
    input  logic [DW-1:0]     m_axil_rdata,
    input  logic [1:0]        m_axil_rresp
);

    // wb4_slave FUB side
    logic           w_cmd_valid, w_cmd_ready, w_cmd_we;
    logic [AW-1:0]  w_cmd_adr;
    logic [DW-1:0]  w_cmd_dat;
    logic [SW-1:0]  w_cmd_sel;
    logic [CTW-1:0] w_cmd_cti;
    logic [BTW-1:0] w_cmd_bte;
    logic           w_rsp_valid, w_rsp_ready;
    logic [1:0]     w_rsp_status;
    logic [DW-1:0]  w_rsp_dat;

    wb4_slave #(
        .ADDR_WIDTH      (AW),
        .DATA_WIDTH      (DW),
        .CMD_DEPTH       (CMD_DEPTH),
        .RSP_DEPTH       (RSP_DEPTH),
        .MAX_OUTSTANDING (1),
        .CLASSIC         (CLASSIC)
    ) u_wb_slave (
        .clk        (clk),
        .aresetn    (aresetn),
        .s_wb_CYC   (s_wb_CYC),
        .s_wb_STB   (s_wb_STB),
        .s_wb_WE    (s_wb_WE),
        .s_wb_ADR   (s_wb_ADR),
        .s_wb_DAT_W (s_wb_DAT_W),
        .s_wb_SEL   (s_wb_SEL),
        .s_wb_CTI   (s_wb_CTI),
        .s_wb_BTE   (s_wb_BTE),
        .s_wb_STALL (s_wb_STALL),
        .s_wb_ACK   (s_wb_ACK),
        .s_wb_ERR   (s_wb_ERR),
        .s_wb_RTY   (s_wb_RTY),
        .s_wb_DAT_R (s_wb_DAT_R),
        .cmd_valid  (w_cmd_valid),
        .cmd_ready  (w_cmd_ready),
        .cmd_we     (w_cmd_we),
        .cmd_adr    (w_cmd_adr),
        .cmd_dat    (w_cmd_dat),
        .cmd_sel    (w_cmd_sel),
        .cmd_cti    (w_cmd_cti),
        .cmd_bte    (w_cmd_bte),
        .rsp_valid  (w_rsp_valid),
        .rsp_ready  (w_rsp_ready),
        .rsp_status (w_rsp_status),
        .rsp_dat    (w_rsp_dat)
    );

    // ------------------------------------------------------------------------
    // One transfer at a time: a read goes out on AR and its R comes back as
    // the termination; a write is refused here and never reaches the group.
    // ------------------------------------------------------------------------
    logic r_busy;          // a read is out on AR/R
    logic w_take_rd, w_take_wr;

    // Both gates key off the DOWNSTREAM ready, never off w_rsp_valid: the
    // write's refusal is produced in the same clock it is accepted, so
    // gating the accept on its own valid is a combinational loop.
    assign w_take_rd = w_cmd_valid && !w_cmd_we && !r_busy && m_axil_arready;
    assign w_take_wr = w_cmd_valid &&  w_cmd_we && !r_busy && w_rsp_ready;

    assign m_axil_arvalid = w_cmd_valid && !w_cmd_we && !r_busy;
    assign m_axil_araddr  = w_cmd_adr;
    assign m_axil_arprot  = AXIL_PROT;
    assign m_axil_rready  = r_busy && w_rsp_ready;

    assign w_cmd_ready = w_take_rd || w_take_wr;

    // The write's refusal is produced in the clock the command is taken; a
    // read's termination comes from R.
    assign w_rsp_valid  = w_take_wr || (r_busy && m_axil_rvalid);
    assign w_rsp_status = w_take_wr           ? 2'(WB4_RSP_ERR) :
                          (m_axil_rresp == 2'b00) ? 2'(WB4_RSP_ACK) : 2'(WB4_RSP_ERR);
    assign w_rsp_dat    = m_axil_rdata;

    `ALWAYS_FF_RST(clk, aresetn,
        if (`RST_ASSERTED(aresetn))                      r_busy <= 1'b0;
        else if (w_take_rd)                              r_busy <= 1'b1;
        else if (r_busy && m_axil_rvalid && w_rsp_ready) r_busy <= 1'b0;
    )

    // Burst hints and write payload have no meaning on a read-only CSR port.
    /* verilator lint_off UNUSEDSIGNAL */
    logic w_unused;
    assign w_unused = ^{w_cmd_dat, w_cmd_sel, w_cmd_cti, w_cmd_bte};
    /* verilator lint_on UNUSEDSIGNAL */

`ifdef FORMAL
    logic f_past_valid;
    initial f_past_valid = 1'b0;
    always_ff @(posedge clk) f_past_valid <= 1'b1;
    always_ff @(posedge clk) if (f_past_valid && aresetn && $past(aresetn)) begin
        // A write NEVER reaches the group.
        assert (!(m_axil_arvalid && w_cmd_we));
        // One read at a time.
        assert (!(w_take_rd && r_busy));
        // R is only consumed while a read is outstanding.
        assert (!m_axil_rready || r_busy);
        // A write is always refused, never acknowledged.
        assert (!w_take_wr || w_rsp_status == 2'(WB4_RSP_ERR));
    end
`endif

endmodule : monbus_wb4_rd_shim
