// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gatling_tetrad_axil_split
// Purpose: one AXI4-Lite master to two slaves, steered by one address bit
//          (SEL_BIT): 0 -> m0, 1 -> m1.  One write and one read outstanding:
//          the select is taken at the address handshake and held until the
//          response handshake, and W is forwarded only after its AW.
//
// Documentation: projects/fpga-systems/NexysA7/riscv-ip/gatling/README.md
// Subsystem: fpga-systems / riscv-ip
//
// Created: 2026-11-26
//
// Notes:
//   - Sized for uart_axil_bridge, which issues one command and waits for its
//     response; a pipelined master would see one transaction per direction
//     at a time, which is correct but not fast.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gatling_tetrad_axil_split #(
    parameter int AW      = 32,
    parameter int SEL_BIT = 18
) (
    input  logic          aclk,
    input  logic          aresetn,

    input  logic [AW-1:0] s_awaddr,
    input  logic [2:0]    s_awprot,
    input  logic          s_awvalid,
    output logic          s_awready,
    input  logic [31:0]   s_wdata,
    input  logic [3:0]    s_wstrb,
    input  logic          s_wvalid,
    output logic          s_wready,
    output logic [1:0]    s_bresp,
    output logic          s_bvalid,
    input  logic          s_bready,
    input  logic [AW-1:0] s_araddr,
    input  logic [2:0]    s_arprot,
    input  logic          s_arvalid,
    output logic          s_arready,
    output logic [31:0]   s_rdata,
    output logic [1:0]    s_rresp,
    output logic          s_rvalid,
    input  logic          s_rready,

    // m[0] and m[1] share address/data; valids and readies are per slave
    output logic [AW-1:0] m_awaddr,
    output logic [2:0]    m_awprot,
    output logic [1:0]    m_awvalid,
    input  logic [1:0]    m_awready,
    output logic [31:0]   m_wdata,
    output logic [3:0]    m_wstrb,
    output logic [1:0]    m_wvalid,
    input  logic [1:0]    m_wready,
    input  logic [1:0]    m_bresp   [2],
    input  logic [1:0]    m_bvalid,
    output logic [1:0]    m_bready,
    output logic [AW-1:0] m_araddr,
    output logic [2:0]    m_arprot,
    output logic [1:0]    m_arvalid,
    input  logic [1:0]    m_arready,
    input  logic [31:0]   m_rdata   [2],
    input  logic [1:0]    m_rresp   [2],
    input  logic [1:0]    m_rvalid,
    output logic [1:0]    m_rready
);

    logic r_wbusy, r_wsel, r_waw, r_rbusy, r_rsel;
    logic w_aw_sel, w_ar_sel;

    assign w_aw_sel = s_awaddr[SEL_BIT];
    assign w_ar_sel = s_araddr[SEL_BIT];

    // ---- write: AW (when idle) -> W -> B ----
    assign m_awaddr  = s_awaddr;
    assign m_awprot  = s_awprot;
    assign m_awvalid = {s_awvalid && !r_wbusy &&  w_aw_sel,
                        s_awvalid && !r_wbusy && !w_aw_sel};
    assign s_awready = !r_wbusy && m_awready[w_aw_sel];

    assign m_wdata   = s_wdata;
    assign m_wstrb   = s_wstrb;
    assign m_wvalid  = {s_wvalid && r_waw &&  r_wsel,
                        s_wvalid && r_waw && !r_wsel};
    assign s_wready  = r_waw && m_wready[r_wsel];

    assign s_bvalid  = r_wbusy && m_bvalid[r_wsel];
    assign s_bresp   = m_bresp[r_wsel];
    assign m_bready  = {s_bready && r_wbusy &&  r_wsel,
                        s_bready && r_wbusy && !r_wsel};

    // ---- read: AR (when idle) -> R ----
    assign m_araddr  = s_araddr;
    assign m_arprot  = s_arprot;
    assign m_arvalid = {s_arvalid && !r_rbusy &&  w_ar_sel,
                        s_arvalid && !r_rbusy && !w_ar_sel};
    assign s_arready = !r_rbusy && m_arready[w_ar_sel];

    assign s_rvalid  = r_rbusy && m_rvalid[r_rsel];
    assign s_rdata   = m_rdata[r_rsel];
    assign s_rresp   = m_rresp[r_rsel];
    assign m_rready  = {s_rready && r_rbusy &&  r_rsel,
                        s_rready && r_rbusy && !r_rsel};

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wbusy <= 1'b0;
            r_wsel  <= 1'b0;
            r_waw   <= 1'b0;
            r_rbusy <= 1'b0;
            r_rsel  <= 1'b0;
        end else begin
            if (s_awvalid && s_awready) begin
                r_wbusy <= 1'b1;
                r_waw   <= 1'b1;
                r_wsel  <= w_aw_sel;
            end else begin
                if (s_wvalid && s_wready)  r_waw   <= 1'b0;
                if (s_bvalid && s_bready)  r_wbusy <= 1'b0;
            end
            if (s_arvalid && s_arready) begin
                r_rbusy <= 1'b1;
                r_rsel  <= w_ar_sel;
            end else if (s_rvalid && s_rready) begin
                r_rbusy <= 1'b0;
            end
        end
    )

endmodule : gatling_tetrad_axil_split
