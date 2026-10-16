// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
// Module: fb_genesys2_top
// Purpose: Genesys 2 board top of the fabric benchmark (K1): fb_harness on the
//          MIG DDR3 controller's ui_clk, the endpoint clock from a second
//          MMCM, UART to the host, status on the LEDs.
// Documentation: projects/fpga-systems/Genesys2/fabric-benchmark/PRD.md
// Author: sean galloway
// Created: 2026-10-15
//==============================================================================
// Clocks
//   sys_clk_p/n  200 MHz LVDS (AD12/AD11) -> fb_mig (its own IBUFDS + MMCM;
//                MIG's XDC places these pins, so the names are MIG's)
//   aclk         fb_mig ui_clk, 100 MHz (DDR3-800 at 4:1): STREAM, the fabric
//                under test, the harness -- and S0 needs no clock crossing
//   ep_clk       125 MHz from u_ep_mmcm (ui_clk x10 / 8), the endpoints' clock
//                (fb_endpoints crosses into it through axi4_cdc_{rd,wr}). The
//                K0 sim ran the same 100 / 125 MHz pair.
// Reset
//   cpu_resetn (R19) resets MIG (sys_rst, active low). The harness leaves reset
//   once ui_clk is stable (~ui_clk_sync_rst), NOT on calibration: W2 runs need
//   no DDR, and a calibration problem then shows on LED 7 instead of a dead
//   board. A transaction to S0 before calibration simply waits for MIG.
// LEDs
//   run finished: 0x23 PASS / 0x99 FAIL (the STREAM boards' patterns)
//   otherwise:    [0] stream_irq  [5] ep MMCM locked  [6] MIG MMCM locked
//                 [7] DDR3 init_calib_complete
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module fb_genesys2_top #(
    parameter int FPGA_CLK_HZ = 100_000_000,   // ui_clk
    parameter int UART_BAUD   = 115_200
) (
    input  logic        sys_clk_p,
    input  logic        sys_clk_n,
    input  logic        cpu_resetn,

    input  logic        uart_tx_in,     // host -> FPGA (Y20)
    output logic        uart_rx_out,    // FPGA -> host (Y23)
    output logic [7:0]  led,

    // DDR3 (2 x MT41J256M16, 32-bit) -- pins placed by fb_mig's XDC
    output logic [14:0] ddr3_addr,
    output logic [2:0]  ddr3_ba,
    output logic        ddr3_cas_n,
    output logic [0:0]  ddr3_ck_n,
    output logic [0:0]  ddr3_ck_p,
    output logic [0:0]  ddr3_cke,
    output logic        ddr3_ras_n,
    output logic        ddr3_reset_n,
    output logic        ddr3_we_n,
    inout  wire  [31:0] ddr3_dq,
    inout  wire  [3:0]  ddr3_dqs_n,
    inout  wire  [3:0]  ddr3_dqs_p,
    output logic [0:0]  ddr3_cs_n,
    output logic [3:0]  ddr3_dm,
    output logic [0:0]  ddr3_odt
);

    // =========================================================================
    // DDR3 controller (S0) and the fabric clock
    // =========================================================================
    logic        ui_clk, ui_clk_sync_rst, mig_mmcm_locked, init_calib_complete;
    logic        r_mig_aresetn;

    logic [9:0]   ddr_awid,   ddr_arid,   ddr_bid,   ddr_rid;
    logic [31:0]  ddr_awaddr, ddr_araddr;
    logic [7:0]   ddr_awlen,  ddr_arlen;
    logic [2:0]   ddr_awsize, ddr_arsize, ddr_awprot, ddr_arprot;
    logic [1:0]   ddr_awburst, ddr_arburst, ddr_bresp, ddr_rresp;
    logic         ddr_awlock, ddr_arlock;
    logic [3:0]   ddr_awcache, ddr_arcache, ddr_awqos, ddr_arqos;
    logic         ddr_awvalid, ddr_awready, ddr_wlast, ddr_wvalid, ddr_wready;
    logic         ddr_bvalid, ddr_bready, ddr_arvalid, ddr_arready;
    logic         ddr_rlast, ddr_rvalid, ddr_rready;
    logic [127:0] ddr_wdata, ddr_rdata;
    logic [15:0]  ddr_wstrb;

    fb_mig u_mig (
        .ddr3_addr, .ddr3_ba, .ddr3_cas_n, .ddr3_ck_n, .ddr3_ck_p, .ddr3_cke,
        .ddr3_ras_n, .ddr3_reset_n, .ddr3_we_n, .ddr3_dq, .ddr3_dqs_n,
        .ddr3_dqs_p, .ddr3_cs_n, .ddr3_dm, .ddr3_odt,
        .sys_clk_p, .sys_clk_n,
        .sys_rst             (cpu_resetn),        // ACTIVE LOW (fb_mig.prj)
        .init_calib_complete (init_calib_complete),
        .ui_clk              (ui_clk),
        .ui_clk_sync_rst     (ui_clk_sync_rst),
        .mmcm_locked         (mig_mmcm_locked),
        .aresetn             (r_mig_aresetn),
        .app_sr_req          (1'b0),
        .app_ref_req         (1'b0),
        .app_zq_req          (1'b0),
        .app_sr_active       (),
        .app_ref_ack         (),
        .app_zq_ack          (),
        // The fabric's slave port is 32-bit addressed; S0's window is 1 GB, so
        // the controller sees the low 30 bits (C0_S_AXI_ADDR_WIDTH = 30).
        .s_axi_awid    (ddr_awid),    .s_axi_awaddr  (ddr_awaddr[29:0]),
        .s_axi_awlen   (ddr_awlen),   .s_axi_awsize  (ddr_awsize),
        .s_axi_awburst (ddr_awburst), .s_axi_awlock  (ddr_awlock),
        .s_axi_awcache (ddr_awcache), .s_axi_awprot  (ddr_awprot),
        .s_axi_awqos   (ddr_awqos),   .s_axi_awvalid (ddr_awvalid),
        .s_axi_awready (ddr_awready),
        .s_axi_wdata   (ddr_wdata),   .s_axi_wstrb   (ddr_wstrb),
        .s_axi_wlast   (ddr_wlast),   .s_axi_wvalid  (ddr_wvalid),
        .s_axi_wready  (ddr_wready),
        .s_axi_bid     (ddr_bid),     .s_axi_bresp   (ddr_bresp),
        .s_axi_bvalid  (ddr_bvalid),  .s_axi_bready  (ddr_bready),
        .s_axi_arid    (ddr_arid),    .s_axi_araddr  (ddr_araddr[29:0]),
        .s_axi_arlen   (ddr_arlen),   .s_axi_arsize  (ddr_arsize),
        .s_axi_arburst (ddr_arburst), .s_axi_arlock  (ddr_arlock),
        .s_axi_arcache (ddr_arcache), .s_axi_arprot  (ddr_arprot),
        .s_axi_arqos   (ddr_arqos),   .s_axi_arvalid (ddr_arvalid),
        .s_axi_arready (ddr_arready),
        .s_axi_rid     (ddr_rid),     .s_axi_rdata   (ddr_rdata),
        .s_axi_rresp   (ddr_rresp),   .s_axi_rlast   (ddr_rlast),
        .s_axi_rvalid  (ddr_rvalid),  .s_axi_rready  (ddr_rready)
    );

    // Fabric reset: ui_clk_sync_rst is already synchronous to ui_clk. Assert
    // with it, release one cycle later from a flop, so the fan-out starts from
    // a clean register. MIG's own AXI shim takes the same reset.
    logic r_aresetn;
    wire  w_ui_rst_n = ~ui_clk_sync_rst;
    `ALWAYS_FF_RST(ui_clk, w_ui_rst_n,
        if (`RST_ASSERTED(w_ui_rst_n)) begin
            r_aresetn     <= 1'b0;
            r_mig_aresetn <= 1'b0;
        end else begin
            r_aresetn     <= 1'b1;
            r_mig_aresetn <= 1'b1;
        end
    )
    wire aclk    = ui_clk;
    wire aresetn = r_aresetn;

    // =========================================================================
    // Endpoint clock: 125 MHz from ui_clk (VCO 1000 MHz)
    // =========================================================================
    logic ep_clkfb, ep_clkfb_buf, ep_clk_unbuf, ep_clk, ep_locked;
    MMCME2_BASE #(
        .CLKIN1_PERIOD    (10.000),
        .CLKFBOUT_MULT_F  (10.000),
        .DIVCLK_DIVIDE    (1),
        .CLKOUT0_DIVIDE_F (8.000)
    ) u_ep_mmcm (
        .CLKIN1   (ui_clk),
        .CLKFBIN  (ep_clkfb_buf),
        .CLKFBOUT (ep_clkfb),
        .CLKFBOUTB(),
        .CLKOUT0  (ep_clk_unbuf),
        .CLKOUT0B (), .CLKOUT1 (), .CLKOUT1B(), .CLKOUT2 (), .CLKOUT2B(),
        .CLKOUT3  (), .CLKOUT3B(), .CLKOUT4 (), .CLKOUT5 (), .CLKOUT6 (),
        .LOCKED   (ep_locked),
        .RST      (ui_clk_sync_rst),
        .PWRDWN   (1'b0)
    );
    BUFG u_ep_bufg_fb (.I(ep_clkfb),     .O(ep_clkfb_buf));
    BUFG u_ep_bufg    (.I(ep_clk_unbuf), .O(ep_clk));

    // ep reset: async assert (fabric reset or MMCM unlocked), sync deassert.
    logic ep_rst_n_raw;
    assign ep_rst_n_raw = aresetn & ep_locked;
    (* ASYNC_REG = "TRUE" *) logic r_ep_rst_meta;
    (* ASYNC_REG = "TRUE" *) logic r_ep_rst_sync;
    `ALWAYS_FF_RST(ep_clk, ep_rst_n_raw,
        if (`RST_ASSERTED(ep_rst_n_raw)) begin
            r_ep_rst_meta <= 1'b0;
            r_ep_rst_sync <= 1'b0;
        end else begin
            r_ep_rst_meta <= 1'b1;
            r_ep_rst_sync <= r_ep_rst_meta;
        end
    )
    wire ep_aresetn = r_ep_rst_sync;

    // =========================================================================
    // Harness -- the leg is whichever fb_data_fabric the filelist compiled
    // =========================================================================
    logic w_timer_done, w_timer_pass, w_stream_irq;

    fb_harness #(
        .FPGA_CLK_HZ (FPGA_CLK_HZ),
        .UART_BAUD   (UART_BAUD)
    ) u_harness (
        .aclk, .aresetn, .ep_clk, .ep_aresetn,
        .i_uart_rx (uart_tx_in),
        .o_uart_tx (uart_rx_out),
        .ddr_awid, .ddr_awaddr, .ddr_awlen, .ddr_awsize, .ddr_awburst,
        .ddr_awlock, .ddr_awcache, .ddr_awprot, .ddr_awqos, .ddr_awvalid,
        .ddr_awready,
        .ddr_wdata, .ddr_wstrb, .ddr_wlast, .ddr_wvalid, .ddr_wready,
        .ddr_bid, .ddr_bresp, .ddr_bvalid, .ddr_bready,
        .ddr_arid, .ddr_araddr, .ddr_arlen, .ddr_arsize, .ddr_arburst,
        .ddr_arlock, .ddr_arcache, .ddr_arprot, .ddr_arqos, .ddr_arvalid,
        .ddr_arready,
        .ddr_rid, .ddr_rdata, .ddr_rresp, .ddr_rlast, .ddr_rvalid, .ddr_rready,
        .o_timer_done (w_timer_done),
        .o_timer_pass (w_timer_pass),
        .o_stream_irq (w_stream_irq)
    );

    // =========================================================================
    // LEDs (slow-domain CDC driver shared with the STREAM boards)
    // =========================================================================
    localparam logic [7:0] LED_PATTERN_PASS = 8'h23;
    localparam logic [7:0] LED_PATTERN_FAIL = 8'h99;
    logic [7:0] w_led_status;
    assign w_led_status = w_timer_done
        ? (w_timer_pass ? LED_PATTERN_PASS : LED_PATTERN_FAIL)
        : {init_calib_complete, mig_mmcm_locked, ep_locked, 4'h0, w_stream_irq};

    led_status_driver #(
        .FPGA_CLK_HZ  (FPGA_CLK_HZ),
        .LED_UPDATE_HZ(200),
        .NUM_LEDS     (8),
        .SYNC_STAGES  (3)
    ) u_led_status_driver (
        .aclk     (aclk),
        .aresetn  (aresetn),
        .i_status (w_led_status),
        .o_led    (led)
    );

endmodule : fb_genesys2_top
