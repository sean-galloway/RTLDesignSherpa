// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: bch_loop_genesys2_top
// Purpose:
//   Genesys 2 (Kintex-7 XC7K325T-2) board top for the BCH loop harness.
//   Derives the 100 MHz harness clock from the 200 MHz LVDS system clock via
//   IBUFDS + MMCM (VCO = 200 MHz x 6 = 1200 MHz, CLKOUT0_DIVIDE = 12 -> 100
//   MHz) and instantiates the board-agnostic bch_loop_harness unchanged.
//
//   The harness clock frequency is captured in FPGA_CLK_HZ so the UART divisor
//   and LED heartbeat can never disagree with the MMCM output.
//
// Documentation: projects/fpga-systems/Genesys2/bch/stable/MANIFEST.md
// Subsystem: bch (Genesys2 harness)
//
// Author: sean galloway
// Created: 2026-10-04

`timescale 1ns / 1ps
`include "reset_defs.svh"

module bch_loop_genesys2_top
    import bch_loop_cfg_pkg::*;
#(
    // Which datapath this bitstream carries. "AXIS" is the stream pipe the
    // board was validated on; "AXI4" builds the memory-to-memory job chain
    // instead. A build selects it with Vivado -generic, and the host does not
    // need to be told -- it reads TOPOLOGY.
    parameter string IFACE = "AXIS"
) (
    input  logic        sysclk_p,       // 200 MHz LVDS (+)
    input  logic        sysclk_n,       // 200 MHz LVDS (-)
    input  logic        cpu_resetn,     // active-low pushbutton (R19)

    input  logic        uart_tx_in,     // host -> FPGA
    output logic        uart_rx_out,    // FPGA -> host

    output logic [7:0]  led
);

    // -------------------------------------------------------------------------
    // Derived harness clock frequency; single source of truth for the UART
    // divisor and LED heartbeat. Must equal bch_loop_cfg_pkg::CFG_SYS_CLK_HZ.
    // -------------------------------------------------------------------------
    localparam int FPGA_CLK_HZ = 100_000_000;

    initial begin
        if (FPGA_CLK_HZ != CFG_SYS_CLK_HZ)
            $error("FPGA_CLK_HZ=%0d does not match CFG_SYS_CLK_HZ=%0d; \
                    MMCM output and package clock constant disagree", FPGA_CLK_HZ, CFG_SYS_CLK_HZ);
    end

    // -------------------------------------------------------------------------
    // 200 MHz LVDS -> single-ended -> MMCM -> 100 MHz
    // VCO = 200 MHz * 6 = 1200 MHz (in the -2 Kintex 600-1600 MHz range);
    // CLKOUT0 = 1200 / 12 = 100 MHz.
    // -------------------------------------------------------------------------
    logic sysclk_ib, clk100_unbuf, clk100, clkfb, clkfb_buf, mmcm_locked;

    IBUFDS u_ibufds (.I(sysclk_p), .IB(sysclk_n), .O(sysclk_ib));

    MMCME2_BASE #(
        .BANDWIDTH         ("OPTIMIZED"),
        .CLKIN1_PERIOD     (5.000),        // 200 MHz
        .DIVCLK_DIVIDE     (1),
        .CLKFBOUT_MULT_F   (6.000),        // VCO = 1200 MHz
        .CLKOUT0_DIVIDE_F  (12.000),       // 100 MHz
        .CLKOUT0_DUTY_CYCLE(0.500),
        .CLKOUT0_PHASE     (0.000),
        .STARTUP_WAIT      ("FALSE")
    ) u_mmcm (
        .CLKIN1   (sysclk_ib),
        .CLKFBIN  (clkfb_buf),
        .CLKFBOUT (clkfb),
        .CLKFBOUTB(),
        .CLKOUT0  (clk100_unbuf),
        .CLKOUT0B (), .CLKOUT1 (), .CLKOUT1B(), .CLKOUT2 (), .CLKOUT2B(),
        .CLKOUT3  (), .CLKOUT3B(), .CLKOUT4 (), .CLKOUT5 (), .CLKOUT6 (),
        .LOCKED   (mmcm_locked),
        .RST      (1'b0),
        .PWRDWN   (1'b0)
    );
    BUFG u_bufg_fb (.I(clkfb),        .O(clkfb_buf));
    BUFG u_bufg_c0 (.I(clk100_unbuf), .O(clk100));

    // -------------------------------------------------------------------------
    // Clock and reset
    // -------------------------------------------------------------------------
    logic sys_clk, sys_rstn;
    assign sys_clk = clk100;

    // Hold the harness in reset (active-low) until the MMCM locks; OR in the
    // pushbutton.
    logic rst_n_raw;
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
    localparam int UART_CLKS_PER_BIT = (FPGA_CLK_HZ + CFG_UART_BAUD / 2) / CFG_UART_BAUD;

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
    logic w_busy, w_gen_done, w_chk_a_ok, w_chk_b_ok, w_cmp_err;

    bch_loop_harness #(
        .AXIL_ADDR_WIDTH(32), .IFACE(IFACE)
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

    assign led[0] = w_busy;
    assign led[1] = w_gen_done;
    assign led[2] = w_chk_a_ok;
    assign led[3] = w_chk_b_ok;     // unused slot in BCH build
    assign led[4] = w_cmp_err;      // unused slot in BCH build
    assign led[5] = axil_awvalid || axil_arvalid;   // UART RX activity
    assign led[6] = axil_rvalid  || axil_bvalid;    // UART TX activity
    assign led[7] = r_heartbeat[26];

endmodule : bch_loop_genesys2_top
