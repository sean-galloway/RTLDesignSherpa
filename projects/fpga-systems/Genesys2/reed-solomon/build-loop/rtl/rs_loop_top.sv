// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rs_loop_top
// Purpose:
//   Nexys A7-100T board top for the Reed-Solomon loop harness: 100 MHz clock,
//   UART -> AXI4-Lite bridge, the harness, status on the LEDs.
//
// Documentation: projects/fpga-systems/Genesys2/reed-solomon/README.md
// Subsystem: reed-solomon (NexysA7 harness)
//
// Author: sean galloway
// Created: 2026-09-30

`timescale 1ns / 1ps
`include "reset_defs.svh"

module rs_loop_top
    import rs_loop_cfg_pkg::*;
#(
    // Which decoders this bitstream carries. Defaults are the board-proven
    // pair with the comparator between them; a build overrides them with
    // Vivado -generic to get a cheaper single-decoder image -- the Euclid
    // decoder alone is 7,163 LUTs of a 63,400-LUT part, so dropping it is
    // what buys room for a different fabric boundary in the same device.
    // The host does not need to be told which it got: it reads TOPOLOGY.
    // Which datapath this bitstream carries. "AXIS" is the stream pipe the
    // board was validated on; "AXI4" builds the memory-to-memory job chain
    // instead. A build selects it with Vivado -generic, and the host does not
    // need to be told -- it reads TOPOLOGY.
    parameter string IFACE          = "AXIS",
    parameter string KES_ALGO_A     = CFG_KES_A,
    parameter string KES_ALGO_B     = CFG_KES_B,
    // OFF: a bitstream carries one solver, never both. See the long note on
    // rs_loop_harness's own ENABLE_COMPARE -- the comparator belongs in
    // simulation. The board matrix is solver x datapath = four bitstreams.
    parameter bit    ENABLE_COMPARE = 1'b0
) (
    input  logic        CLK100MHZ,
    input  logic        CPU_RESETN,     // active-low
    input  logic        UART_TXD_IN,    // FTDI -> FPGA
    output logic        UART_RXD_OUT,   // FPGA -> FTDI
    output logic [7:0]  LED
);

    // -------------------------------------------------------------------------
    // Clock and reset
    // -------------------------------------------------------------------------
    logic sys_clk, sys_clk_pad, sys_rstn;
    IBUF u_sys_ibuf (.I(CLK100MHZ), .O(sys_clk_pad));
    BUFG u_sys_bufg (.I(sys_clk_pad), .O(sys_clk));

    (* ASYNC_REG = "TRUE" *) logic r_rstn_sync0, r_rstn_sync1;
    `ALWAYS_FF_RST(sys_clk, CPU_RESETN,
        if (`RST_ASSERTED(CPU_RESETN)) begin
            r_rstn_sync0 <= 1'b0;
            r_rstn_sync1 <= 1'b0;
        end else begin
            r_rstn_sync0 <= 1'b1;
            r_rstn_sync1 <= r_rstn_sync0;
        end
    )
    assign sys_rstn = r_rstn_sync1;

    // -------------------------------------------------------------------------
    // UART -> AXI4-Lite
    // -------------------------------------------------------------------------
    localparam int UART_CLKS_PER_BIT = (CFG_SYS_CLK_HZ + CFG_UART_BAUD / 2) / CFG_UART_BAUD;

    logic [31:0] axil_awaddr, axil_araddr, axil_wdata, axil_rdata;
    logic [2:0]  axil_awprot, axil_arprot;
    logic [3:0]  axil_wstrb;
    logic [1:0]  axil_bresp, axil_rresp;
    logic        axil_awvalid, axil_awready, axil_wvalid, axil_wready, axil_bvalid, axil_bready;
    logic        axil_arvalid, axil_arready, axil_rvalid, axil_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH(32), .AXIL_DATA_WIDTH(32), .CLKS_PER_BIT(UART_CLKS_PER_BIT)
    ) u_uart_bridge (
        .aclk(sys_clk), .aresetn(sys_rstn),
        .i_uart_rx(UART_TXD_IN), .o_uart_tx(UART_RXD_OUT),
        .m_axil_awaddr(axil_awaddr), .m_axil_awprot(axil_awprot),
        .m_axil_awvalid(axil_awvalid), .m_axil_awready(axil_awready),
        .m_axil_wdata(axil_wdata), .m_axil_wstrb(axil_wstrb),
        .m_axil_wvalid(axil_wvalid), .m_axil_wready(axil_wready),
        .m_axil_bresp(axil_bresp), .m_axil_bvalid(axil_bvalid), .m_axil_bready(axil_bready),
        .m_axil_araddr(axil_araddr), .m_axil_arprot(axil_arprot),
        .m_axil_arvalid(axil_arvalid), .m_axil_arready(axil_arready),
        .m_axil_rdata(axil_rdata), .m_axil_rresp(axil_rresp),
        .m_axil_rvalid(axil_rvalid), .m_axil_rready(axil_rready));

    // -------------------------------------------------------------------------
    // The harness
    // -------------------------------------------------------------------------
    logic w_busy, w_gen_done, w_chk_a_ok, w_chk_b_ok, w_cmp_err;

    rs_loop_harness #(
        .AXIL_ADDR_WIDTH(32), .IFACE(IFACE),
        .KES_ALGO_A(KES_ALGO_A), .KES_ALGO_B(KES_ALGO_B),
        .ENABLE_COMPARE(ENABLE_COMPARE)
    ) u_harness (
        .aclk(sys_clk), .aresetn(sys_rstn),
        .s_axil_awaddr(axil_awaddr), .s_axil_awprot(axil_awprot),
        .s_axil_awvalid(axil_awvalid), .s_axil_awready(axil_awready),
        .s_axil_wdata(axil_wdata), .s_axil_wstrb(axil_wstrb),
        .s_axil_wvalid(axil_wvalid), .s_axil_wready(axil_wready),
        .s_axil_bresp(axil_bresp), .s_axil_bvalid(axil_bvalid), .s_axil_bready(axil_bready),
        .s_axil_araddr(axil_araddr), .s_axil_arprot(axil_arprot),
        .s_axil_arvalid(axil_arvalid), .s_axil_arready(axil_arready),
        .s_axil_rdata(axil_rdata), .s_axil_rresp(axil_rresp),
        .s_axil_rvalid(axil_rvalid), .s_axil_rready(axil_rready),
        .o_busy(w_busy), .o_gen_done(w_gen_done), .o_chk_a_ok(w_chk_a_ok), .o_chk_b_ok(w_chk_b_ok),
        .o_cmp_err(w_cmp_err));

    // -------------------------------------------------------------------------
    // LEDs: heartbeat, UART activity, run state
    // -------------------------------------------------------------------------
    logic [26:0] r_heartbeat;
    `ALWAYS_FF_RST(sys_clk, sys_rstn,
        if (`RST_ASSERTED(sys_rstn)) r_heartbeat <= '0;
        else                         r_heartbeat <= r_heartbeat + 27'd1;
    )

    assign LED[0] = w_busy;
    assign LED[1] = w_gen_done;
    assign LED[2] = w_chk_a_ok;
    assign LED[3] = w_chk_b_ok;
    assign LED[4] = w_cmp_err;
    assign LED[5] = axil_awvalid || axil_arvalid;   // UART RX activity
    assign LED[6] = axil_rvalid  || axil_bvalid;    // UART TX activity
    assign LED[7] = r_heartbeat[26];

endmodule : rs_loop_top
