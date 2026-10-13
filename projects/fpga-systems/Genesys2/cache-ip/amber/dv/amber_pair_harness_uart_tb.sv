// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Testbench wrapper for amber_pair_harness in board configuration
// (USE_DIRECT_HOST=0). The UART rx/tx pins are exposed so cocotb can
// bit-bang the uart_axil_bridge and reproduce the live read hang.

`timescale 1ns / 1ps

module amber_pair_harness_uart_tb #(
    parameter int FPGA_CLK_HZ   = 90_000_000,
    parameter int UART_BAUD     = 115_200
) (
    input  logic aclk,
    input  logic aresetn,

    // UART host interface
    input  logic i_uart_rx,
    output logic o_uart_tx,

    // Internal probe outputs for tracing the read path through the
    // generated bridge. These are the AXI4 R-channel signals seen by
    // the host_adapter on the 32b path (slave 0..2).
    output logic        probe_host_32b_rvalid,
    output logic        probe_host_32b_rready,
    output logic [31:0] probe_host_32b_rdata,
    output logic [1:0]  probe_host_32b_rresp,
    output logic        probe_host_32b_rlast,

    output logic        probe_fub_axi_rvalid,
    output logic        probe_fub_axi_rready,
    output logic [31:0] probe_fub_axi_rdata,
    output logic [1:0]  probe_fub_axi_rresp,
    output logic        probe_fub_axi_rlast,

    output logic        probe_converter_rvalid,
    output logic        probe_converter_rlast,
    output logic        probe_slave_rvalid,
    output logic        probe_slave_rready,

    output logic o_done,
    output logic o_busy,
    output logic o_error
);

    amber_pair_harness #(
        .USE_DIRECT_HOST(1'b0),
        .FPGA_CLK_HZ   (FPGA_CLK_HZ),
        .UART_BAUD     (UART_BAUD)
    ) u_dut (
        .aclk    (aclk),
        .aresetn (aresetn),

        .i_uart_rx(i_uart_rx),
        .o_uart_tx(o_uart_tx),

        // Direct host unused in UART mode
        .host_axi_awaddr ('0),
        .host_axi_awprot ('0),
        .host_axi_awvalid('0),
        .host_axi_awready(),
        .host_axi_wdata  ('0),
        .host_axi_wstrb  ('0),
        .host_axi_wvalid ('0),
        .host_axi_wready (),
        .host_axi_bresp  (),
        .host_axi_bvalid (),
        .host_axi_bready ('0),
        .host_axi_araddr ('0),
        .host_axi_arprot ('0),
        .host_axi_arvalid('0),
        .host_axi_arready(),
        .host_axi_rdata  (),
        .host_axi_rresp  (),
        .host_axi_rvalid (),
        .host_axi_rready ('0),

        .o_done (o_done),
        .o_busy (o_busy),
        .o_error(o_error)
    );

    // Hierarchy probes: reach into the generated bridge and the slave
    // adapter so the test can trace where the R beat stalls.
    assign probe_host_32b_rvalid = u_dut.u_bridge.host_32b_rvalid;
    assign probe_host_32b_rready = u_dut.u_bridge.host_32b_rready;
    assign probe_host_32b_rdata  = u_dut.u_bridge.host_32b_r.data;
    assign probe_host_32b_rresp  = u_dut.u_bridge.host_32b_r.resp;
    assign probe_host_32b_rlast  = u_dut.u_bridge.host_32b_r.last;

    assign probe_fub_axi_rvalid = u_dut.u_bridge.u_host_adapter.fub_axi_rvalid;
    assign probe_fub_axi_rready = u_dut.u_bridge.u_host_adapter.fub_axi_rready;
    assign probe_fub_axi_rdata  = u_dut.u_bridge.u_host_adapter.fub_axi_rdata;
    assign probe_fub_axi_rresp  = u_dut.u_bridge.u_host_adapter.fub_axi_rresp;
    assign probe_fub_axi_rlast  = u_dut.u_bridge.u_host_adapter.fub_axi_rlast;

    assign probe_converter_rvalid = u_dut.u_bridge.u_harness_csr_adapter.converter_rvalid;
    assign probe_converter_rlast  = u_dut.u_bridge.u_harness_csr_adapter.converter_rlast;

    assign probe_slave_rvalid = u_dut.s0_rvalid;
    assign probe_slave_rready = u_dut.s0_rready;

endmodule : amber_pair_harness_uart_tb
