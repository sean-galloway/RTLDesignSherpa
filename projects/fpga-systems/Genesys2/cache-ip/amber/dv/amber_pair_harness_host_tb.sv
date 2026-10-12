// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Testbench wrapper for amber_pair_harness that exposes the generated
// bridge_amber_axil host AXIL4-Lite interface directly, bypassing the
// uart_axil_bridge. Driven by the cocotb/house AXIL4 master BFM.

`timescale 1ns / 1ps

module amber_pair_harness_host_tb (
    input  logic aclk,
    input  logic aresetn,

    // Direct AXIL4-Lite host interface to bridge_amber_axil
    input  logic [31:0] host_axi_awaddr,
    input  logic [2:0]  host_axi_awprot,
    input  logic        host_axi_awvalid,
    output logic        host_axi_awready,
    input  logic [31:0] host_axi_wdata,
    input  logic [3:0]  host_axi_wstrb,
    input  logic        host_axi_wvalid,
    output logic        host_axi_wready,
    output logic [1:0]  host_axi_bresp,
    output logic        host_axi_bvalid,
    input  logic        host_axi_bready,

    input  logic [31:0] host_axi_araddr,
    input  logic [2:0]  host_axi_arprot,
    input  logic        host_axi_arvalid,
    output logic        host_axi_arready,
    output logic [31:0] host_axi_rdata,
    output logic [1:0]  host_axi_rresp,
    output logic        host_axi_rvalid,
    input  logic        host_axi_rready,

    output logic o_done,
    output logic o_busy,
    output logic o_error
);

    amber_pair_harness #(
        .USE_DIRECT_HOST(1'b1)
    ) u_dut (
        .aclk    (aclk),
        .aresetn (aresetn),

        // UART unused in direct-host mode
        .i_uart_rx(1'b1),
        .o_uart_tx(),

        // Direct host AXIL4-Lite interface
        .host_axi_awaddr (host_axi_awaddr),
        .host_axi_awprot (host_axi_awprot),
        .host_axi_awvalid(host_axi_awvalid),
        .host_axi_awready(host_axi_awready),
        .host_axi_wdata  (host_axi_wdata),
        .host_axi_wstrb  (host_axi_wstrb),
        .host_axi_wvalid (host_axi_wvalid),
        .host_axi_wready (host_axi_wready),
        .host_axi_bresp  (host_axi_bresp),
        .host_axi_bvalid (host_axi_bvalid),
        .host_axi_bready (host_axi_bready),
        .host_axi_araddr (host_axi_araddr),
        .host_axi_arprot (host_axi_arprot),
        .host_axi_arvalid(host_axi_arvalid),
        .host_axi_arready(host_axi_arready),
        .host_axi_rdata  (host_axi_rdata),
        .host_axi_rresp  (host_axi_rresp),
        .host_axi_rvalid (host_axi_rvalid),
        .host_axi_rready (host_axi_rready),

        .o_done (o_done),
        .o_busy (o_busy),
        .o_error(o_error)
    );

endmodule : amber_pair_harness_host_tb
