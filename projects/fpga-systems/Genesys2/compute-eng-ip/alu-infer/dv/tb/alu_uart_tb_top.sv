// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: alu_uart_tb_top
// Purpose: UART-equivalence sim top: the REAL uart_axil_bridge + alu_harness
//          (with build-infer's alu_slot), driven over UART by the unmodified
//          host programs in ../../bin/alu_programs.py.

`timescale 1ns / 1ps

module alu_uart_tb_top #(
    // 4, not the board's 868: no sim-harness test may exceed 100 ms of SIM
    // time, and at board baud the UART is the bottleneck. The byte stream is
    // what is under test and it is identical at any baud.
    parameter int    UART_CLKS_PER_BIT = 4,
    parameter string PROFILE           = "FULL"
) (
    input  logic aclk,
    input  logic aresetn,
    input  logic i_uart_rx,
    output logic o_uart_tx,
    output logic o_busy,
    output logic o_done,
    output logic o_err_seen
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

    alu_harness #(
        .DEPTH(256), .CLK_MHZ(100), .PROFILE(PROFILE)
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
        .o_busy(o_busy), .o_done(o_done), .o_err_seen(o_err_seen));

endmodule : alu_uart_tb_top
