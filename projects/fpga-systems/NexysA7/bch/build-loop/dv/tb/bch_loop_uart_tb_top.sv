// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: bch_loop_uart_tb_top
// Purpose:
//   Sim wrapper for the BCH loop harness: the REAL uart_axil_bridge (at a
//   lowered clocks-per-bit) plus bch_loop_harness, so the cocotb UART channel
//   drives the identical byte stream the board's host sends. The board top's
//   IBUF/BUFG and LED wiring are the only things left out.
//
// Documentation: projects/fpga-systems/NexysA7/bch/README.md
// Subsystem: bch (NexysA7 harness)
//
// Author: sean galloway
// Created: 2026-10-04

`timescale 1ns / 1ps

module bch_loop_uart_tb_top #(
    // 4, not the board's 868: no sim-harness test may exceed 100 ms of SIM
    // time, and at board baud the UART is the bottleneck -- raise the baud,
    // never shrink the campaign. The byte stream is what is under test and it
    // is identical at any baud. Same rate the rapids harnesses use.
    parameter int UART_CLKS_PER_BIT = 4,

    // Forwarded to the harness so a test can exercise both datapaths.
    parameter string IFACE = "AXIS"
) (
    input  logic aclk,
    input  logic aresetn,
    input  logic i_uart_rx,
    output logic o_uart_tx,
    output logic o_busy,
    output logic o_gen_done,
    output logic o_chk_a_ok,
    output logic o_chk_b_ok,
    output logic o_cmp_err
);

    logic [31:0] axil_awaddr, axil_araddr, axil_wdata, axil_rdata;
    logic [2:0]  axil_awprot, axil_arprot;
    logic [3:0]  axil_wstrb;
    logic [1:0]  axil_bresp, axil_rresp;
    logic        axil_awvalid, axil_awready, axil_wvalid, axil_wready, axil_bvalid, axil_bready;
    logic        axil_arvalid, axil_arready, axil_rvalid, axil_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH(32), .AXIL_DATA_WIDTH(32), .CLKS_PER_BIT(UART_CLKS_PER_BIT)
    ) u_uart_bridge (
        .aclk(aclk), .aresetn(aresetn),
        .i_uart_rx(i_uart_rx), .o_uart_tx(o_uart_tx),
        .m_axil_awaddr(axil_awaddr), .m_axil_awprot(axil_awprot),
        .m_axil_awvalid(axil_awvalid), .m_axil_awready(axil_awready),
        .m_axil_wdata(axil_wdata), .m_axil_wstrb(axil_wstrb),
        .m_axil_wvalid(axil_wvalid), .m_axil_wready(axil_wready),
        .m_axil_bresp(axil_bresp), .m_axil_bvalid(axil_bvalid), .m_axil_bready(axil_bready),
        .m_axil_araddr(axil_araddr), .m_axil_arprot(axil_arprot),
        .m_axil_arvalid(axil_arvalid), .m_axil_arready(axil_arready),
        .m_axil_rdata(axil_rdata), .m_axil_rresp(axil_rresp),
        .m_axil_rvalid(axil_rvalid), .m_axil_rready(axil_rready));

    bch_loop_harness #(
        .AXIL_ADDR_WIDTH(32), .IFACE(IFACE)
    ) u_harness (
        .aclk(aclk), .aresetn(aresetn),
        .s_axil_awaddr(axil_awaddr), .s_axil_awprot(axil_awprot),
        .s_axil_awvalid(axil_awvalid), .s_axil_awready(axil_awready),
        .s_axil_wdata(axil_wdata), .s_axil_wstrb(axil_wstrb),
        .s_axil_wvalid(axil_wvalid), .s_axil_wready(axil_wready),
        .s_axil_bresp(axil_bresp), .s_axil_bvalid(axil_bvalid), .s_axil_bready(axil_bready),
        .s_axil_araddr(axil_araddr), .s_axil_arprot(axil_arprot),
        .s_axil_arvalid(axil_arvalid), .s_axil_arready(axil_arready),
        .s_axil_rdata(axil_rdata), .s_axil_rresp(axil_rresp),
        .s_axil_rvalid(axil_rvalid), .s_axil_rready(axil_rready),
        .o_busy(o_busy), .o_gen_done(o_gen_done), .o_chk_a_ok(o_chk_a_ok), .o_chk_b_ok(o_chk_b_ok),
        .o_cmp_err(o_cmp_err));

endmodule : bch_loop_uart_tb_top
