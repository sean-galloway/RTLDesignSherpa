// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
// Module: fb_genesys2_top
// Purpose: Genesys 2 board top of the fabric benchmark: fb_harness on the
//          LiteDRAM DDR3 controller's user_clk, the endpoint clock from a second
//          MMCM, UART to the host, status on the LEDs.
// Documentation: projects/fpga-systems/Genesys2/fabric-benchmark/PRD.md
// Author: sean galloway
// Created: 2026-10-15
//==============================================================================
// S0 controller: fb_litedram (rtl/litedram/fb_litedram.yml, bin/gen_litedram.sh)
//   -- the board-proven LiteDRAM memtest configuration (K7DDRPHY, DDR3-800 at
//   1:4) with a 128-bit / ID-10 AXI port. Its VexRiscv BIOS calibrates the PHY
//   at boot; init_done (and not init_error) is "S0 ready". It replaced MIG on
//   2026-10-16 (MIG's read path returned no data on this board; PRD §6).
// Clocks
//   sys_clk_p/n  200 MHz LVDS (AD12/AD11) -> IBUFDS -> fb_litedram's PLL
//   aclk         fb_litedram user_clk, 100 MHz: STREAM, the fabric under test,
//                the harness -- and S0 needs no clock crossing
//   ep_clk       125 MHz from u_ep_mmcm (aclk x10 / 8), the endpoints' clock
//                (fb_endpoints crosses into it through axi4_cdc_{rd,wr}). The
//                K0 sim ran the same 100 / 125 MHz pair.
// Reset
//   cpu_resetn (R19) resets the controller (rst, active high inside). The
//   harness leaves reset with user_rst, NOT on calibration: W2 runs need no
//   DDR, and a calibration problem then shows on LED 7 / fb_ctl STATUS
//   instead of a dead board.
// LEDs
//   run finished: 0x23 PASS / 0x99 FAIL (the STREAM boards' patterns)
//   otherwise:    [0] stream_irq  [4] DDR init error  [5] ep MMCM locked
//                 [6] DDR PLL locked  [7] DDR init done
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module fb_genesys2_top #(
    parameter int FPGA_CLK_HZ = 100_000_000,   // user_clk
    parameter int UART_BAUD   = 115_200
) (
    input  logic        sys_clk_p,
    input  logic        sys_clk_n,
    input  logic        cpu_resetn,

    input  logic        uart_tx_in,     // host -> FPGA (Y20)
    output logic        uart_rx_out,    // FPGA -> host (Y23)
    output logic [7:0]  led,

    // DDR3 (2 x MT41J256M16, 32-bit) -- names and pins are the generated
    // Genesys 2 pin file's (mem-ctrl-ip/scoria/build-litedram/.../ddr3_pins.xdc)
    output logic [14:0] ddram_a,
    output logic [2:0]  ddram_ba,
    output logic        ddram_ras_n,
    output logic        ddram_cas_n,
    output logic        ddram_we_n,
    output logic        ddram_cs_n,
    output logic [3:0]  ddram_dm,
    inout  wire  [31:0] ddram_dq,
    inout  wire  [3:0]  ddram_dqs_p,
    inout  wire  [3:0]  ddram_dqs_n,
    output logic        ddram_clk_p,
    output logic        ddram_clk_n,
    output logic        ddram_cke,
    output logic        ddram_odt,
    output logic        ddram_reset_n
);

    // =========================================================================
    // DDR3 controller (S0) and the fabric clock
    // =========================================================================
    logic         w_clk200;
    logic         user_clk, user_rst, ddr_pll_locked, ddr_init_done, ddr_init_error;

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

    IBUFDS #(
        .DIFF_TERM    ("FALSE"),
        .IBUF_LOW_PWR ("TRUE"),
        .IOSTANDARD   ("LVDS")
    ) u_clk200_ibufds (
        .I  (sys_clk_p),
        .IB (sys_clk_n),
        .O  (w_clk200)
    );

    fb_litedram u_litedram (
        .clk            (w_clk200),
        .rst            (~cpu_resetn),       // board button is active LOW
        .pll_locked     (ddr_pll_locked),
        .init_done      (ddr_init_done),
        .init_error     (ddr_init_error),
        // The BIOS console is not brought out: the board has one host UART and
        // it is the harness's. The BIOS calibrates and idles without a host.
        .uart_rx        (1'b1),
        .uart_tx        (),
        .user_clk       (user_clk),
        .user_rst       (user_rst),
        // The fabric's slave port is 32-bit addressed; S0's window is 1 GB, so
        // the controller sees the low 30 bits. LiteDRAM's AXI port carries no
        // lock/cache/prot/qos (dropped here, as MIG ignored them).
        .user_port_axi_0_awvalid (ddr_awvalid), .user_port_axi_0_awready (ddr_awready),
        .user_port_axi_0_awaddr  (ddr_awaddr[29:0]),
        .user_port_axi_0_awburst (ddr_awburst), .user_port_axi_0_awlen   (ddr_awlen),
        .user_port_axi_0_awsize  (ddr_awsize),  .user_port_axi_0_awid    (ddr_awid),
        .user_port_axi_0_wvalid  (ddr_wvalid),  .user_port_axi_0_wready  (ddr_wready),
        .user_port_axi_0_wdata   (ddr_wdata),   .user_port_axi_0_wstrb   (ddr_wstrb),
        .user_port_axi_0_wlast   (ddr_wlast),
        .user_port_axi_0_bvalid  (ddr_bvalid),  .user_port_axi_0_bready  (ddr_bready),
        .user_port_axi_0_bresp   (ddr_bresp),   .user_port_axi_0_bid     (ddr_bid),
        .user_port_axi_0_arvalid (ddr_arvalid), .user_port_axi_0_arready (ddr_arready),
        .user_port_axi_0_araddr  (ddr_araddr[29:0]),
        .user_port_axi_0_arburst (ddr_arburst), .user_port_axi_0_arlen   (ddr_arlen),
        .user_port_axi_0_arsize  (ddr_arsize),  .user_port_axi_0_arid    (ddr_arid),
        .user_port_axi_0_rvalid  (ddr_rvalid),  .user_port_axi_0_rready  (ddr_rready),
        .user_port_axi_0_rdata   (ddr_rdata),   .user_port_axi_0_rresp   (ddr_rresp),
        .user_port_axi_0_rlast   (ddr_rlast),   .user_port_axi_0_rid     (ddr_rid),
        .ddram_a, .ddram_ba, .ddram_ras_n, .ddram_cas_n, .ddram_we_n, .ddram_cs_n,
        .ddram_dm, .ddram_dq, .ddram_dqs_p, .ddram_dqs_n, .ddram_clk_p, .ddram_clk_n,
        .ddram_cke, .ddram_odt, .ddram_reset_n
    );
    wire unused_ddr_attr = ^{ddr_awaddr[31:30], ddr_araddr[31:30], ddr_awlock, ddr_arlock,
                             ddr_awcache, ddr_arcache, ddr_awprot, ddr_arprot,
                             ddr_awqos, ddr_arqos};

    // Fabric reset: user_rst is synchronous to user_clk. Assert with it,
    // release one cycle later from a flop, so the fan-out starts clean.
    logic r_aresetn;
    wire  w_user_rst_n = ~user_rst;
    `ALWAYS_FF_RST(user_clk, w_user_rst_n,
        if (`RST_ASSERTED(w_user_rst_n)) r_aresetn <= 1'b0;
        else                             r_aresetn <= 1'b1;
    )
    wire aclk    = user_clk;
    wire aresetn = r_aresetn;

    // =========================================================================
    // Endpoint clock: 125 MHz from aclk (VCO 1000 MHz)
    // =========================================================================
    logic ep_clkfb, ep_clkfb_buf, ep_clk_unbuf, ep_clk, ep_locked;
    MMCME2_BASE #(
        .CLKIN1_PERIOD    (10.000),
        .CLKFBOUT_MULT_F  (10.000),
        .DIVCLK_DIVIDE    (1),
        .CLKOUT0_DIVIDE_F (8.000)
    ) u_ep_mmcm (
        .CLKIN1   (aclk),
        .CLKFBIN  (ep_clkfb_buf),
        .CLKFBOUT (ep_clkfb),
        .CLKFBOUTB(),
        .CLKOUT0  (ep_clk_unbuf),
        .CLKOUT0B (), .CLKOUT1 (), .CLKOUT1B(), .CLKOUT2 (), .CLKOUT2B(),
        .CLKOUT3  (), .CLKOUT3B(), .CLKOUT4 (), .CLKOUT5 (), .CLKOUT6 (),
        .LOCKED   (ep_locked),
        .RST      (user_rst),
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
        .i_ddr_init_done  (ddr_init_done),
        .i_ddr_init_error (ddr_init_error),
        .i_ddr_pll_locked (ddr_pll_locked),
        .i_ep_mmcm_locked (ep_locked),
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
        : {ddr_init_done, ddr_pll_locked, ep_locked, ddr_init_error, 3'h0, w_stream_irq};

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
