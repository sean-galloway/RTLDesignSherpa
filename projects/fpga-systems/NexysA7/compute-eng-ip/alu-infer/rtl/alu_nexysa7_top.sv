// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: alu_nexysa7_top
// Purpose: Nexys A7-100T board top for the ALU harness: 100 MHz -> MMCM ->
//          harness clock, reset synchronizer, UART -> AXI4-Lite, alu_harness,
//          LEDs. The harness and ALU slot are the Genesys 2 build's.
//
// Documentation: projects/fpga-systems/NexysA7/compute-eng-ip/alu-infer/README.md
// Subsystem: fpga-systems / compute-eng-ip
//
// Author: sean galloway
// Created: 2026-10-20

`timescale 1ns / 1ps

`include "reset_defs.svh"

module alu_nexysa7_top #(
    // The ALU slot's build profile, set per bitstream with Vivado -generic
    // (ALU_PROFILE env in the build Makefile); the host reads SLOT_INFO.
    parameter string PROFILE = "FULL"
) (
    input  logic        sysclk,         // 100 MHz oscillator (E3)
    input  logic        cpu_resetn,     // active-low pushbutton (C12)

    input  logic        uart_tx_in,     // host -> FPGA
    output logic        uart_rx_out,    // FPGA -> host

    output logic [7:0]  led
);

    // 4.6875 MHz: a functional bring-up clock. The slot builds alu_infer_top
    // with MUL_LATENCY = MAC_LATENCY = 0, so the command-RAM read runs
    // through the single-cycle fp32 accumulate FMA into the result FIFO in
    // one clock: 148 ns on this Artix-7 -1 (the full profile at 50 MHz
    // failed post-route at -128 ns). The slowest exact MMCM setting covers it.
    localparam int FPGA_CLK_HZ = 4_687_500;
    localparam int UART_BAUD   = 115_200;

    // -------------------------------------------------------------------------
    // 100 MHz -> MMCM: VCO = 100 MHz * 6 = 600 MHz (the floor of the -1
    // Artix 600-1200 MHz range); CLKOUT0 = 600 / 128 = 4.6875 MHz.
    // -------------------------------------------------------------------------
    logic clk_unbuf, clk, clkfb, clkfb_buf, mmcm_locked;

    MMCME2_BASE #(
        .BANDWIDTH         ("OPTIMIZED"),
        .CLKIN1_PERIOD     (10.000),
        .DIVCLK_DIVIDE     (1),
        .CLKFBOUT_MULT_F   (6.000),
        .CLKOUT0_DIVIDE_F  (128.000),
        .CLKOUT0_DUTY_CYCLE(0.500),
        .CLKOUT0_PHASE     (0.000),
        .STARTUP_WAIT      ("FALSE")
    ) u_mmcm (
        .CLKIN1   (sysclk),
        .CLKFBIN  (clkfb_buf),
        .CLKFBOUT (clkfb),
        .CLKFBOUTB(),
        .CLKOUT0  (clk_unbuf),
        .CLKOUT0B (), .CLKOUT1 (), .CLKOUT1B(), .CLKOUT2 (), .CLKOUT2B(),
        .CLKOUT3  (), .CLKOUT3B(), .CLKOUT4 (), .CLKOUT5 (), .CLKOUT6 (),
        .LOCKED   (mmcm_locked),
        .RST      (1'b0),
        .PWRDWN   (1'b0)
    );
    BUFG u_bufg_fb (.I(clkfb),        .O(clkfb_buf));
    BUFG u_bufg_c0 (.I(clk_unbuf), .O(clk));

    // -------------------------------------------------------------------------
    // Reset: held until the MMCM locks, OR the pushbutton; synchronized
    // -------------------------------------------------------------------------
    logic sys_clk, sys_rstn, rst_n_raw;
    assign sys_clk   = clk;
    assign rst_n_raw = cpu_resetn & mmcm_locked;

    (* ASYNC_REG = "TRUE" *) logic r_rstn_sync0, r_rstn_sync1;
    `ALWAYS_FF_RST(sys_clk, rst_n_raw,
        if (`RST_ASSERTED(rst_n_raw)) begin
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
    localparam int UART_CLKS_PER_BIT = (FPGA_CLK_HZ + UART_BAUD / 2) / UART_BAUD;

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
        .i_uart_rx(uart_tx_in), .o_uart_tx(uart_rx_out),
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
    logic w_busy, w_done, w_err_seen;

    alu_harness #(
        .DEPTH(256), .CLK_MHZ(FPGA_CLK_HZ / 1_000_000), .PROFILE(PROFILE)
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
        .o_busy(w_busy), .o_done(w_done), .o_err_seen(w_err_seen));

    // -------------------------------------------------------------------------
    // LEDs: run state, UART activity, heartbeat
    // -------------------------------------------------------------------------
    logic [26:0] r_heartbeat;
    `ALWAYS_FF_RST(sys_clk, sys_rstn,
        if (`RST_ASSERTED(sys_rstn)) r_heartbeat <= '0;
        else                         r_heartbeat <= r_heartbeat + 27'd1;
    )

    assign led[0] = w_busy;
    assign led[1] = w_done;
    assign led[2] = w_err_seen;
    assign led[3] = mmcm_locked;
    assign led[4] = 1'b0;
    assign led[5] = axil_awvalid || axil_arvalid;
    assign led[6] = axil_rvalid  || axil_bvalid;
    assign led[7] = r_heartbeat[26];

endmodule : alu_nexysa7_top
