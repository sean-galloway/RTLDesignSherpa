// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: bs_genesys2_xil_top
// Purpose: Genesys 2 board top of the bridge stress model's third-party
//          build (build-xil): the bridge_bs_xil harness with third-party IP
//          on its vendor ports -- LiteDRAM DDR3 and an AMD/Xilinx BRAM
//          controller as memories, the AXI Traffic Generator and AXI Central
//          DMA as masters, an AXI Protocol Checker on each memory link.
// build-xmix (`define BS_XMIX, its filelist): the same board top around the
//          bridge_bs_xmix harness -- AXI3, AXI4 and AXI5 stress ports -- whose
//          bram slave port is AXI3: AMD's AXI Protocol Converter (bs_axi3_conv,
//          AXI3 in, AXI4 out) carries it to the BRAM controller, and the bram
//          link's protocol checker (bs_pc_bram3) judges the bridge's AXI3.
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Author: sean galloway
// Created: 2026-10-20
//==============================================================================
// Clocks
//   sys_clk_p/n  200 MHz LVDS -> IBUFDS -> u_litedram's PLL (and its IDELAYCTRL)
//   aclk         u_litedram user_clk, 100 MHz: the bridge, the configuration
//                path, the vendor IP and every non-cdc port
//   cclk          75 MHz from u_mmcm (aclk x9 / 12): the cdc ports
// Reset
//   cpu_resetn (R19) resets LiteDRAM. Both domains leave reset once user_clk
//   is up (user_rst low, u_mmcm locked), NOT on calibration: the stress
//   slaves need no DDR, and the host waits for EXT_STS0 [0] (init_done)
//   before it touches the ddr window.
// Vendor control (AXI4-Lite out of the configuration bridge)
//   ext0 0x0010_0000  u_atg's programming slave (an AXI4 slave, driven one
//                     beat at a time)
//   ext1 0x0011_0000  u_cdma's register slave (it waits for W before AW)
// EXT_STS (control block)
//   EXT_STS0  [0] DDR3 init_done  [1] LiteDRAM PLL locked  [2] cclk MMCM
//             locked  [3] ddr link protocol violation  [4] bram link
//             protocol violation  [5] ATG irq_out  [6] ATG err_out
//             [7] CDMA cdma_introut  [8] ddr link stall (2048 idle cycles
//             with work pending)  [9] bram link stall  [10] DDR3 init_error
//             [11] traffic generator link protocol violation
//             [31:16] ddr writes outstanding
//   EXT_STS1  bs_pc_ddr pc_status[31:0]    EXT_STS2  bs_pc_ddr pc_status[63:32]
//   EXT_STS3  bs_pc_bram pc_status[31:0]
//   (pc_asserted and pc_status are sticky in the checker until reset)
// LEDs
//   [0] heartbeat  [1] clocks locked  [2] run busy  [3] all done
//   [4] any error  [5] done and no error  [6] protocol violation
//   [7] DDR3 calibrated
//==============================================================================

`timescale 1ns / 1ps

module bs_genesys2_xil_top #(
    parameter int FPGA_CLK_HZ = 100_000_000,   // user_clk
    parameter int UART_BAUD   = 115_200
) (
    input  logic       sys_clk_p,
    input  logic       sys_clk_n,
    input  logic       cpu_resetn,

    input  logic       uart_tx_in,     // host -> FPGA (Y20)
    output logic       uart_rx_out,    // FPGA -> host (Y23)
    output logic [7:0] led,

    // DDR3 (2 x MT41J256M16, 32-bit) -- the board-proven LiteDRAM pin file
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

    // ---- clocks and resets -------------------------------------------------------
    logic w_clk200, user_clk, user_rst, ddr_pll_locked, ddr_init_done, ddr_init_error;
    logic aclk, aresetn, cclk, cresetn;
    logic w_clkfb, w_clkfb_buf, w_cclk_unbuf, w_c_locked;

    assign aclk = user_clk;

    IBUFDS #(.DIFF_TERM ("FALSE"), .IBUF_LOW_PWR ("TRUE"), .IOSTANDARD ("LVDS")) u_clk200_ibufds (
        .I (sys_clk_p), .IB (sys_clk_n), .O (w_clk200)
    );

    MMCME2_BASE #(
        .CLKIN1_PERIOD    (10.000),
        .CLKFBOUT_MULT_F  (9.000),
        .DIVCLK_DIVIDE    (1),
        .CLKOUT0_DIVIDE_F (12.000)
    ) u_mmcm (
        .CLKIN1   (user_clk),
        .CLKFBIN  (w_clkfb_buf),
        .CLKFBOUT (w_clkfb),
        .CLKFBOUTB(),
        .CLKOUT0  (w_cclk_unbuf),
        .CLKOUT0B (), .CLKOUT1 (), .CLKOUT1B(), .CLKOUT2 (), .CLKOUT2B(),
        .CLKOUT3  (), .CLKOUT3B(), .CLKOUT4 (), .CLKOUT5 (), .CLKOUT6 (),
        .LOCKED   (w_c_locked),
        .PWRDWN   (1'b0),
        .RST      (user_rst)
    );
    BUFG u_bufg_fb (.I(w_clkfb),      .O(w_clkfb_buf));
    BUFG u_bufg_c  (.I(w_cclk_unbuf), .O(cclk));

    logic w_rst_n;
    assign w_rst_n = !user_rst && w_c_locked;
    reset_sync #(.N(3)) u_rst_a (.clk(aclk), .rst_n(w_rst_n), .sync_rst_n(aresetn));
    reset_sync #(.N(3)) u_rst_c (.clk(cclk), .rst_n(w_rst_n), .sync_rst_n(cresetn));

    // ---- the harness ---------------------------------------------------------------
    logic w_all_done, w_any_err, w_busy;
    logic [127:0] w_ext_sts;

    logic [31:0] ext0_axil_awaddr, ext0_axil_wdata, ext0_axil_araddr, ext0_axil_rdata;
    logic [31:0] ext1_axil_awaddr, ext1_axil_wdata, ext1_axil_araddr, ext1_axil_rdata;
    logic [2:0]  ext0_axil_awprot, ext0_axil_arprot, ext1_axil_awprot, ext1_axil_arprot;
    logic [3:0]  ext0_axil_wstrb, ext1_axil_wstrb;
    logic [1:0]  ext0_axil_bresp, ext0_axil_rresp, ext1_axil_bresp, ext1_axil_rresp;
    logic        ext0_axil_awvalid, ext0_axil_awready, ext0_axil_wvalid, ext0_axil_wready;
    logic        ext0_axil_bvalid, ext0_axil_bready, ext0_axil_arvalid, ext0_axil_arready;
    logic        ext0_axil_rvalid, ext0_axil_rready;
    logic        ext1_axil_awvalid, ext1_axil_awready, ext1_axil_wvalid, ext1_axil_wready;
    logic        ext1_axil_bvalid, ext1_axil_bready, ext1_axil_arvalid, ext1_axil_arready;
    logic        ext1_axil_rvalid, ext1_axil_rready;

    // one AXI4 port per vendor block, named as the harness names them
    logic [1:0]   atg_axi_awid, atg_axi_arid, atg_axi_bid, atg_axi_rid;
    logic [31:0]  atg_axi_awaddr, atg_axi_araddr;
    logic [7:0]   atg_axi_awlen, atg_axi_arlen;
    logic [2:0]   atg_axi_awsize, atg_axi_arsize, atg_axi_awprot, atg_axi_arprot;
    logic [1:0]   atg_axi_awburst, atg_axi_arburst, atg_axi_bresp, atg_axi_rresp;
    logic         atg_axi_awlock, atg_axi_arlock;
    logic [3:0]   atg_axi_awcache, atg_axi_arcache, atg_axi_awqos, atg_axi_arqos, atg_axi_awregion, atg_axi_arregion;
    logic         atg_axi_awuser, atg_axi_aruser, atg_axi_wuser, atg_axi_buser, atg_axi_ruser;
    logic         atg_axi_awvalid, atg_axi_awready, atg_axi_wvalid, atg_axi_wready, atg_axi_bvalid, atg_axi_bready;
    logic         atg_axi_arvalid, atg_axi_arready, atg_axi_rvalid, atg_axi_rready, atg_axi_wlast, atg_axi_rlast;
    logic [63:0]  atg_axi_wdata, atg_axi_rdata;
    logic [7:0]   atg_axi_wstrb;
    logic [0:0]   cdma_axi_awid, cdma_axi_arid, cdma_axi_bid, cdma_axi_rid;
    logic [31:0]  cdma_axi_awaddr, cdma_axi_araddr;
    logic [7:0]   cdma_axi_awlen, cdma_axi_arlen;
    logic [2:0]   cdma_axi_awsize, cdma_axi_arsize, cdma_axi_awprot, cdma_axi_arprot;
    logic [1:0]   cdma_axi_awburst, cdma_axi_arburst, cdma_axi_bresp, cdma_axi_rresp;
    logic         cdma_axi_awlock, cdma_axi_arlock;
    logic [3:0]   cdma_axi_awcache, cdma_axi_arcache, cdma_axi_awqos, cdma_axi_arqos, cdma_axi_awregion, cdma_axi_arregion;
    logic         cdma_axi_awuser, cdma_axi_aruser, cdma_axi_wuser, cdma_axi_buser, cdma_axi_ruser;
    logic         cdma_axi_awvalid, cdma_axi_awready, cdma_axi_wvalid, cdma_axi_wready, cdma_axi_bvalid, cdma_axi_bready;
    logic         cdma_axi_arvalid, cdma_axi_arready, cdma_axi_rvalid, cdma_axi_rready, cdma_axi_wlast, cdma_axi_rlast;
    logic [63:0]  cdma_axi_wdata, cdma_axi_rdata;
    logic [7:0]   cdma_axi_wstrb;
    logic [6:0]   bram_axi_awid, bram_axi_arid, bram_axi_bid, bram_axi_rid;
    logic [31:0]  bram_axi_awaddr, bram_axi_araddr;
    logic [7:0]   bram_axi_awlen, bram_axi_arlen;
    logic [2:0]   bram_axi_awsize, bram_axi_arsize, bram_axi_awprot, bram_axi_arprot;
    logic [1:0]   bram_axi_awburst, bram_axi_arburst, bram_axi_bresp, bram_axi_rresp;
    logic         bram_axi_awlock, bram_axi_arlock;
    logic [3:0]   bram_axi_awcache, bram_axi_arcache, bram_axi_awqos, bram_axi_arqos, bram_axi_awregion, bram_axi_arregion;
    logic         bram_axi_awuser, bram_axi_aruser, bram_axi_wuser, bram_axi_buser, bram_axi_ruser;
    logic         bram_axi_awvalid, bram_axi_awready, bram_axi_wvalid, bram_axi_wready, bram_axi_bvalid, bram_axi_bready;
    logic         bram_axi_arvalid, bram_axi_arready, bram_axi_rvalid, bram_axi_rready, bram_axi_wlast, bram_axi_rlast;
    logic [63:0]  bram_axi_wdata, bram_axi_rdata;
    logic [7:0]   bram_axi_wstrb;
`ifdef BS_XMIX
    // build-xmix: the harness's AXI3 bram port, ahead of bs_axi3_conv
    logic [6:0]   b3_axi_awid, b3_axi_arid, b3_axi_wid, b3_axi_bid, b3_axi_rid;
    logic [31:0]  b3_axi_awaddr, b3_axi_araddr;
    logic [3:0]   b3_axi_awlen, b3_axi_arlen, b3_axi_awcache, b3_axi_arcache;
    logic [2:0]   b3_axi_awsize, b3_axi_arsize, b3_axi_awprot, b3_axi_arprot;
    logic [1:0]   b3_axi_awburst, b3_axi_arburst, b3_axi_awlock, b3_axi_arlock;
    logic [1:0]   b3_axi_bresp, b3_axi_rresp;
    logic         b3_axi_awuser, b3_axi_aruser, b3_axi_wuser, b3_axi_buser, b3_axi_ruser;
    logic         b3_axi_awvalid, b3_axi_awready, b3_axi_wvalid, b3_axi_wready, b3_axi_bvalid, b3_axi_bready;
    logic         b3_axi_arvalid, b3_axi_arready, b3_axi_rvalid, b3_axi_rready, b3_axi_wlast, b3_axi_rlast;
    logic [63:0]  b3_axi_wdata, b3_axi_rdata;
    logic [7:0]   b3_axi_wstrb;
`endif
    logic [6:0]   ddr_axi_awid, ddr_axi_arid, ddr_axi_bid, ddr_axi_rid;
    logic [31:0]  ddr_axi_awaddr, ddr_axi_araddr;
    logic [7:0]   ddr_axi_awlen, ddr_axi_arlen;
    logic [2:0]   ddr_axi_awsize, ddr_axi_arsize, ddr_axi_awprot, ddr_axi_arprot;
    logic [1:0]   ddr_axi_awburst, ddr_axi_arburst, ddr_axi_bresp, ddr_axi_rresp;
    logic         ddr_axi_awlock, ddr_axi_arlock;
    logic [3:0]   ddr_axi_awcache, ddr_axi_arcache, ddr_axi_awqos, ddr_axi_arqos, ddr_axi_awregion, ddr_axi_arregion;
    logic         ddr_axi_awuser, ddr_axi_aruser, ddr_axi_wuser, ddr_axi_buser, ddr_axi_ruser;
    logic         ddr_axi_awvalid, ddr_axi_awready, ddr_axi_wvalid, ddr_axi_wready, ddr_axi_bvalid, ddr_axi_bready;
    logic         ddr_axi_arvalid, ddr_axi_arready, ddr_axi_rvalid, ddr_axi_rready, ddr_axi_wlast, ddr_axi_rlast;
    logic [127:0] ddr_axi_wdata, ddr_axi_rdata;
    logic [15:0]  ddr_axi_wstrb;

        
`ifdef BS_XMIX
    bs_harness_bridge_bs_xmix #(
`else
    bs_harness_bridge_bs_xil #(
`endif
        .CLKS_PER_BIT (FPGA_CLK_HZ / UART_BAUD)
    ) u_harness (
        .aclk, .aresetn, .cclk, .cresetn,
        .i_uart_rx  (uart_tx_in),
        .o_uart_tx  (uart_rx_out),
        .o_all_done (w_all_done),
        .o_any_err  (w_any_err),
        .o_busy     (w_busy),
        .ext0_axil_awaddr, .ext0_axil_awprot, .ext0_axil_awvalid, .ext0_axil_awready,
        .ext0_axil_wdata, .ext0_axil_wstrb, .ext0_axil_wvalid, .ext0_axil_wready,
        .ext0_axil_bresp, .ext0_axil_bvalid, .ext0_axil_bready, .ext0_axil_araddr,
        .ext0_axil_arprot, .ext0_axil_arvalid, .ext0_axil_arready, .ext0_axil_rdata,
        .ext0_axil_rresp, .ext0_axil_rvalid, .ext0_axil_rready,
        .ext1_axil_awaddr, .ext1_axil_awprot, .ext1_axil_awvalid, .ext1_axil_awready,
        .ext1_axil_wdata, .ext1_axil_wstrb, .ext1_axil_wvalid, .ext1_axil_wready,
        .ext1_axil_bresp, .ext1_axil_bvalid, .ext1_axil_bready, .ext1_axil_araddr,
        .ext1_axil_arprot, .ext1_axil_arvalid, .ext1_axil_arready, .ext1_axil_rdata,
        .ext1_axil_rresp, .ext1_axil_rvalid, .ext1_axil_rready,
        .i_ext_sts  (w_ext_sts),
        .atg_axi_awid, .atg_axi_awaddr, .atg_axi_awlen, .atg_axi_awsize, .atg_axi_awburst,
        .atg_axi_awlock, .atg_axi_awcache, .atg_axi_awprot, .atg_axi_awqos,
        .atg_axi_awregion, .atg_axi_awuser, .atg_axi_awvalid, .atg_axi_awready,
        .atg_axi_wdata, .atg_axi_wstrb, .atg_axi_wlast, .atg_axi_wuser, .atg_axi_wvalid,
        .atg_axi_wready, .atg_axi_bid, .atg_axi_bresp, .atg_axi_buser, .atg_axi_bvalid,
        .atg_axi_bready, .atg_axi_arid, .atg_axi_araddr, .atg_axi_arlen, .atg_axi_arsize,
        .atg_axi_arburst, .atg_axi_arlock, .atg_axi_arcache, .atg_axi_arprot, .atg_axi_arqos,
        .atg_axi_arregion, .atg_axi_aruser, .atg_axi_arvalid, .atg_axi_arready, .atg_axi_rid,
        .atg_axi_rdata, .atg_axi_rresp, .atg_axi_rlast, .atg_axi_ruser, .atg_axi_rvalid,
        .atg_axi_rready,
        .cdma_axi_awid, .cdma_axi_awaddr, .cdma_axi_awlen, .cdma_axi_awsize,
        .cdma_axi_awburst, .cdma_axi_awlock, .cdma_axi_awcache, .cdma_axi_awprot,
        .cdma_axi_awqos, .cdma_axi_awregion, .cdma_axi_awuser, .cdma_axi_awvalid,
        .cdma_axi_awready, .cdma_axi_wdata, .cdma_axi_wstrb, .cdma_axi_wlast,
        .cdma_axi_wuser, .cdma_axi_wvalid, .cdma_axi_wready, .cdma_axi_bid, .cdma_axi_bresp,
        .cdma_axi_buser, .cdma_axi_bvalid, .cdma_axi_bready, .cdma_axi_arid,
        .cdma_axi_araddr, .cdma_axi_arlen, .cdma_axi_arsize, .cdma_axi_arburst,
        .cdma_axi_arlock, .cdma_axi_arcache, .cdma_axi_arprot, .cdma_axi_arqos,
        .cdma_axi_arregion, .cdma_axi_aruser, .cdma_axi_arvalid, .cdma_axi_arready,
        .cdma_axi_rid, .cdma_axi_rdata, .cdma_axi_rresp, .cdma_axi_rlast, .cdma_axi_ruser,
        .cdma_axi_rvalid, .cdma_axi_rready,
`ifdef BS_XMIX
        // bram is AXI3 here: b3_axi_* into bs_axi3_conv
        .bram_axi_awid (b3_axi_awid), .bram_axi_awaddr (b3_axi_awaddr), .bram_axi_awlen (b3_axi_awlen),
        .bram_axi_awsize (b3_axi_awsize), .bram_axi_awburst (b3_axi_awburst), .bram_axi_awlock (b3_axi_awlock),
        .bram_axi_awcache (b3_axi_awcache), .bram_axi_awprot (b3_axi_awprot), .bram_axi_awuser (b3_axi_awuser),
        .bram_axi_awvalid (b3_axi_awvalid), .bram_axi_awready (b3_axi_awready), .bram_axi_wid (b3_axi_wid),
        .bram_axi_wdata (b3_axi_wdata), .bram_axi_wstrb (b3_axi_wstrb), .bram_axi_wlast (b3_axi_wlast),
        .bram_axi_wuser (b3_axi_wuser), .bram_axi_wvalid (b3_axi_wvalid), .bram_axi_wready (b3_axi_wready),
        .bram_axi_bid (b3_axi_bid), .bram_axi_bresp (b3_axi_bresp), .bram_axi_buser (b3_axi_buser),
        .bram_axi_bvalid (b3_axi_bvalid), .bram_axi_bready (b3_axi_bready), .bram_axi_arid (b3_axi_arid),
        .bram_axi_araddr (b3_axi_araddr), .bram_axi_arlen (b3_axi_arlen), .bram_axi_arsize (b3_axi_arsize),
        .bram_axi_arburst (b3_axi_arburst), .bram_axi_arlock (b3_axi_arlock), .bram_axi_arcache (b3_axi_arcache),
        .bram_axi_arprot (b3_axi_arprot), .bram_axi_aruser (b3_axi_aruser), .bram_axi_arvalid (b3_axi_arvalid),
        .bram_axi_arready (b3_axi_arready), .bram_axi_rid (b3_axi_rid), .bram_axi_rdata (b3_axi_rdata),
        .bram_axi_rresp (b3_axi_rresp), .bram_axi_rlast (b3_axi_rlast), .bram_axi_ruser (b3_axi_ruser),
        .bram_axi_rvalid (b3_axi_rvalid), .bram_axi_rready (b3_axi_rready),
`else
        .bram_axi_awid, .bram_axi_awaddr, .bram_axi_awlen, .bram_axi_awsize,
        .bram_axi_awburst, .bram_axi_awlock, .bram_axi_awcache, .bram_axi_awprot,
        .bram_axi_awqos, .bram_axi_awregion, .bram_axi_awuser, .bram_axi_awvalid,
        .bram_axi_awready, .bram_axi_wdata, .bram_axi_wstrb, .bram_axi_wlast,
        .bram_axi_wuser, .bram_axi_wvalid, .bram_axi_wready, .bram_axi_bid, .bram_axi_bresp,
        .bram_axi_buser, .bram_axi_bvalid, .bram_axi_bready, .bram_axi_arid,
        .bram_axi_araddr, .bram_axi_arlen, .bram_axi_arsize, .bram_axi_arburst,
        .bram_axi_arlock, .bram_axi_arcache, .bram_axi_arprot, .bram_axi_arqos,
        .bram_axi_arregion, .bram_axi_aruser, .bram_axi_arvalid, .bram_axi_arready,
        .bram_axi_rid, .bram_axi_rdata, .bram_axi_rresp, .bram_axi_rlast, .bram_axi_ruser,
        .bram_axi_rvalid, .bram_axi_rready,
`endif
        .ddr_axi_awid, .ddr_axi_awaddr, .ddr_axi_awlen, .ddr_axi_awsize, .ddr_axi_awburst,
        .ddr_axi_awlock, .ddr_axi_awcache, .ddr_axi_awprot, .ddr_axi_awqos,
        .ddr_axi_awregion, .ddr_axi_awuser, .ddr_axi_awvalid, .ddr_axi_awready,
        .ddr_axi_wdata, .ddr_axi_wstrb, .ddr_axi_wlast, .ddr_axi_wuser, .ddr_axi_wvalid,
        .ddr_axi_wready, .ddr_axi_bid, .ddr_axi_bresp, .ddr_axi_buser, .ddr_axi_bvalid,
        .ddr_axi_bready, .ddr_axi_arid, .ddr_axi_araddr, .ddr_axi_arlen, .ddr_axi_arsize,
        .ddr_axi_arburst, .ddr_axi_arlock, .ddr_axi_arcache, .ddr_axi_arprot, .ddr_axi_arqos,
        .ddr_axi_arregion, .ddr_axi_aruser, .ddr_axi_arvalid, .ddr_axi_arready, .ddr_axi_rid,
        .ddr_axi_rdata, .ddr_axi_rresp, .ddr_axi_rlast, .ddr_axi_ruser, .ddr_axi_rvalid,
        .ddr_axi_rready
    );


    // ---- LiteDRAM DDR3 (slave ddr) ----------------------------------------------------
    // The board-proven LiteDRAM configuration (rtl/litedram/bs_litedram.yml): its
    // VexRiscv + BIOS calibrate the PHY at boot, then idle. Its AXI port has no
    // lock / cache / prot / qos / region or user signals; the window is 1 GB, so
    // it takes the low 30 address bits.
    bs_litedram u_litedram (
        .clk            (w_clk200),
        .rst            (~cpu_resetn),          // board button is active LOW
        .pll_locked     (ddr_pll_locked),
        .init_done      (ddr_init_done),
        .init_error     (ddr_init_error),
        // the BIOS console stays inside: the board's one host UART is the harness's
        .uart_rx        (1'b1),
        .uart_tx        (),
        .user_clk       (user_clk),
        .user_rst       (user_rst),
        .user_port_axi_0_awvalid (ddr_axi_awvalid), .user_port_axi_0_awready (ddr_axi_awready),
        .user_port_axi_0_awaddr  (ddr_axi_awaddr[29:0]),
        .user_port_axi_0_awburst (ddr_axi_awburst), .user_port_axi_0_awlen   (ddr_axi_awlen),
        .user_port_axi_0_awsize  (ddr_axi_awsize),  .user_port_axi_0_awid    (ddr_axi_awid),
        .user_port_axi_0_wvalid  (ddr_axi_wvalid),  .user_port_axi_0_wready  (ddr_axi_wready),
        .user_port_axi_0_wdata   (ddr_axi_wdata),   .user_port_axi_0_wstrb   (ddr_axi_wstrb),
        .user_port_axi_0_wlast   (ddr_axi_wlast),
        .user_port_axi_0_bvalid  (ddr_axi_bvalid),  .user_port_axi_0_bready  (ddr_axi_bready),
        .user_port_axi_0_bresp   (ddr_axi_bresp),   .user_port_axi_0_bid     (ddr_axi_bid),
        .user_port_axi_0_arvalid (ddr_axi_arvalid), .user_port_axi_0_arready (ddr_axi_arready),
        .user_port_axi_0_araddr  (ddr_axi_araddr[29:0]),
        .user_port_axi_0_arburst (ddr_axi_arburst), .user_port_axi_0_arlen   (ddr_axi_arlen),
        .user_port_axi_0_arsize  (ddr_axi_arsize),  .user_port_axi_0_arid    (ddr_axi_arid),
        .user_port_axi_0_rvalid  (ddr_axi_rvalid),  .user_port_axi_0_rready  (ddr_axi_rready),
        .user_port_axi_0_rdata   (ddr_axi_rdata),   .user_port_axi_0_rresp   (ddr_axi_rresp),
        .user_port_axi_0_rlast   (ddr_axi_rlast),   .user_port_axi_0_rid     (ddr_axi_rid),
        .ddram_a, .ddram_ba, .ddram_ras_n, .ddram_cas_n, .ddram_we_n, .ddram_cs_n,
        .ddram_dm, .ddram_dq, .ddram_dqs_p, .ddram_dqs_n, .ddram_clk_p, .ddram_clk_n,
        .ddram_cke, .ddram_odt, .ddram_reset_n
    );
    assign ddr_axi_buser = 1'b0;
    assign ddr_axi_ruser = 1'b0;
    wire unused_ddr = ^{ddr_axi_awaddr[31:30], ddr_axi_araddr[31:30], ddr_axi_awlock,
                        ddr_axi_arlock, ddr_axi_awcache, ddr_axi_arcache, ddr_axi_awprot,
                        ddr_axi_arprot, ddr_axi_awqos, ddr_axi_arqos, ddr_axi_awregion,
                        ddr_axi_arregion, ddr_axi_awuser, ddr_axi_aruser, ddr_axi_wuser};

    // ---- BRAM controller + block memory (slave bram) ----------------------------------
    // dual port: the controller writes on A and reads on B at once
    logic        w_bram_rst, w_bram_clk, w_bram_en, w_bramb_rst, w_bramb_clk, w_bramb_en;
    logic [7:0]  w_bram_we, w_bramb_we;
    logic [15:0] w_bram_addr, w_bramb_addr;
    logic [63:0] w_bram_wrdata, w_bram_rddata, w_bramb_wrdata, w_bramb_rddata;

`ifdef BS_XMIX
    // AXI3 bram port -> AXI4 BRAM controller (AMD AXI Protocol Converter)
    bs_axi3_conv u_axi3_conv (
        .aclk, .aresetn,
        .s_axi_awid (b3_axi_awid), .s_axi_awaddr (b3_axi_awaddr), .s_axi_awlen (b3_axi_awlen),
        .s_axi_awsize (b3_axi_awsize), .s_axi_awburst (b3_axi_awburst), .s_axi_awlock (b3_axi_awlock),
        .s_axi_awcache (b3_axi_awcache), .s_axi_awprot (b3_axi_awprot), .s_axi_awqos (4'd0),
        .s_axi_awvalid (b3_axi_awvalid), .s_axi_awready (b3_axi_awready),
        .s_axi_wid (b3_axi_wid), .s_axi_wdata (b3_axi_wdata), .s_axi_wstrb (b3_axi_wstrb),
        .s_axi_wlast (b3_axi_wlast), .s_axi_wvalid (b3_axi_wvalid), .s_axi_wready (b3_axi_wready),
        .s_axi_bid (b3_axi_bid), .s_axi_bresp (b3_axi_bresp), .s_axi_bvalid (b3_axi_bvalid),
        .s_axi_bready (b3_axi_bready),
        .s_axi_arid (b3_axi_arid), .s_axi_araddr (b3_axi_araddr), .s_axi_arlen (b3_axi_arlen),
        .s_axi_arsize (b3_axi_arsize), .s_axi_arburst (b3_axi_arburst), .s_axi_arlock (b3_axi_arlock),
        .s_axi_arcache (b3_axi_arcache), .s_axi_arprot (b3_axi_arprot), .s_axi_arqos (4'd0),
        .s_axi_arvalid (b3_axi_arvalid), .s_axi_arready (b3_axi_arready),
        .s_axi_rid (b3_axi_rid), .s_axi_rdata (b3_axi_rdata), .s_axi_rresp (b3_axi_rresp),
        .s_axi_rlast (b3_axi_rlast), .s_axi_rvalid (b3_axi_rvalid), .s_axi_rready (b3_axi_rready),
        .m_axi_awid (bram_axi_awid), .m_axi_awaddr (bram_axi_awaddr), .m_axi_awlen (bram_axi_awlen),
        .m_axi_awsize (bram_axi_awsize), .m_axi_awburst (bram_axi_awburst),
        .m_axi_awlock (bram_axi_awlock), .m_axi_awcache (bram_axi_awcache),
        .m_axi_awprot (bram_axi_awprot), .m_axi_awregion (bram_axi_awregion),
        .m_axi_awqos (bram_axi_awqos), .m_axi_awvalid (bram_axi_awvalid),
        .m_axi_awready (bram_axi_awready),
        .m_axi_wdata (bram_axi_wdata), .m_axi_wstrb (bram_axi_wstrb), .m_axi_wlast (bram_axi_wlast),
        .m_axi_wvalid (bram_axi_wvalid), .m_axi_wready (bram_axi_wready),
        .m_axi_bid (bram_axi_bid), .m_axi_bresp (bram_axi_bresp), .m_axi_bvalid (bram_axi_bvalid),
        .m_axi_bready (bram_axi_bready),
        .m_axi_arid (bram_axi_arid), .m_axi_araddr (bram_axi_araddr), .m_axi_arlen (bram_axi_arlen),
        .m_axi_arsize (bram_axi_arsize), .m_axi_arburst (bram_axi_arburst),
        .m_axi_arlock (bram_axi_arlock), .m_axi_arcache (bram_axi_arcache),
        .m_axi_arprot (bram_axi_arprot), .m_axi_arregion (bram_axi_arregion),
        .m_axi_arqos (bram_axi_arqos), .m_axi_arvalid (bram_axi_arvalid),
        .m_axi_arready (bram_axi_arready),
        .m_axi_rid (bram_axi_rid), .m_axi_rdata (bram_axi_rdata), .m_axi_rresp (bram_axi_rresp),
        .m_axi_rlast (bram_axi_rlast), .m_axi_rvalid (bram_axi_rvalid), .m_axi_rready (bram_axi_rready)
    );
    assign b3_axi_buser = 1'b0;
    assign b3_axi_ruser = 1'b0;
    assign {bram_axi_awuser, bram_axi_aruser, bram_axi_wuser} = '0;   // the AXI3 port carries no user
    wire unused_b3_user = ^{b3_axi_awuser, b3_axi_aruser, b3_axi_wuser, bram_axi_buser, bram_axi_ruser};
`endif

    bs_bram_ctrl u_bram_ctrl (
        .s_axi_aclk    (aclk),            .s_axi_aresetn (aresetn),
        .s_axi_awid    (bram_axi_awid),   .s_axi_awaddr  (bram_axi_awaddr[15:0]),
        .s_axi_awlen   (bram_axi_awlen),  .s_axi_awsize  (bram_axi_awsize),
        .s_axi_awburst (bram_axi_awburst), .s_axi_awlock (bram_axi_awlock),
        .s_axi_awcache (bram_axi_awcache), .s_axi_awprot (bram_axi_awprot),
        .s_axi_awvalid (bram_axi_awvalid), .s_axi_awready (bram_axi_awready),
        .s_axi_wdata   (bram_axi_wdata),  .s_axi_wstrb   (bram_axi_wstrb),
        .s_axi_wlast   (bram_axi_wlast),  .s_axi_wvalid  (bram_axi_wvalid),
        .s_axi_wready  (bram_axi_wready),
        .s_axi_bid     (bram_axi_bid),    .s_axi_bresp   (bram_axi_bresp),
        .s_axi_bvalid  (bram_axi_bvalid), .s_axi_bready  (bram_axi_bready),
        .s_axi_arid    (bram_axi_arid),   .s_axi_araddr  (bram_axi_araddr[15:0]),
        .s_axi_arlen   (bram_axi_arlen),  .s_axi_arsize  (bram_axi_arsize),
        .s_axi_arburst (bram_axi_arburst), .s_axi_arlock (bram_axi_arlock),
        .s_axi_arcache (bram_axi_arcache), .s_axi_arprot (bram_axi_arprot),
        .s_axi_arvalid (bram_axi_arvalid), .s_axi_arready (bram_axi_arready),
        .s_axi_rid     (bram_axi_rid),    .s_axi_rdata   (bram_axi_rdata),
        .s_axi_rresp   (bram_axi_rresp),  .s_axi_rlast   (bram_axi_rlast),
        .s_axi_rvalid  (bram_axi_rvalid), .s_axi_rready  (bram_axi_rready),
        .bram_rst_a    (w_bram_rst),      .bram_clk_a    (w_bram_clk),
        .bram_en_a     (w_bram_en),       .bram_we_a     (w_bram_we),
        .bram_addr_a   (w_bram_addr),     .bram_wrdata_a (w_bram_wrdata),
        .bram_rddata_a (w_bram_rddata),
        .bram_rst_b    (w_bramb_rst),     .bram_clk_b    (w_bramb_clk),
        .bram_en_b     (w_bramb_en),      .bram_we_b     (w_bramb_we),
        .bram_addr_b   (w_bramb_addr),    .bram_wrdata_b (w_bramb_wrdata),
        .bram_rddata_b (w_bramb_rddata)
    );
    assign bram_axi_buser = 1'b0;
    assign bram_axi_ruser = 1'b0;

    bs_bram u_bram (
        .clka  (w_bram_clk), .rsta (w_bram_rst), .ena (w_bram_en), .wea (w_bram_we),
        .addra ({16'd0, w_bram_addr}), .dina (w_bram_wrdata), .douta (w_bram_rddata),
        .clkb  (w_bramb_clk), .rstb (w_bramb_rst), .enb (w_bramb_en), .web (w_bramb_we),
        .addrb ({16'd0, w_bramb_addr}), .dinb (w_bramb_wrdata), .doutb (w_bramb_rddata),
        .rsta_busy (), .rstb_busy ()
    );

    // ---- AXI Traffic Generator (master atg; programmed through ext0) -----------------
    logic w_atg_irq, w_atg_err;
    logic [7:0] w_atg_awuser, w_atg_aruser;

    bs_atg u_atg (
        .s_axi_aclk    (aclk), .s_axi_aresetn (aresetn), .core_ext_start (1'b0),
        // programming slave: one 32-bit beat per AXI4-Lite access
        .s_axi_awid    (1'b0),             .s_axi_awaddr  (ext0_axil_awaddr),
        .s_axi_awlen   (8'd0),             .s_axi_awsize  (3'd2),
        .s_axi_awburst (2'b01),            .s_axi_awlock  (1'b0),
        .s_axi_awcache (4'd0),             .s_axi_awprot  (ext0_axil_awprot),
        .s_axi_awqos   (4'd0),             .s_axi_awuser  (8'd0),
        .s_axi_awvalid (ext0_axil_awvalid), .s_axi_awready (ext0_axil_awready),
        .s_axi_wlast   (1'b1),             .s_axi_wdata   (ext0_axil_wdata),
        .s_axi_wstrb   (ext0_axil_wstrb),  .s_axi_wvalid  (ext0_axil_wvalid),
        .s_axi_wready  (ext0_axil_wready),
        .s_axi_bid     (),                 .s_axi_bresp   (ext0_axil_bresp),
        .s_axi_bvalid  (ext0_axil_bvalid), .s_axi_bready  (ext0_axil_bready),
        .s_axi_arid    (1'b0),             .s_axi_araddr  (ext0_axil_araddr),
        .s_axi_arlen   (8'd0),             .s_axi_arsize  (3'd2),
        .s_axi_arburst (2'b01),            .s_axi_arlock  (1'b0),
        .s_axi_arcache (4'd0),             .s_axi_arprot  (ext0_axil_arprot),
        .s_axi_arqos   (4'd0),             .s_axi_aruser  (8'd0),
        .s_axi_arvalid (ext0_axil_arvalid), .s_axi_arready (ext0_axil_arready),
        .s_axi_rid     (),                 .s_axi_rlast   (),
        .s_axi_rdata   (ext0_axil_rdata),  .s_axi_rresp   (ext0_axil_rresp),
        .s_axi_rvalid  (ext0_axil_rvalid), .s_axi_rready  (ext0_axil_rready),
        // the traffic it makes
        .m_axi_awid    (atg_axi_awid),     .m_axi_awaddr  (atg_axi_awaddr),
        .m_axi_awlen   (atg_axi_awlen),    .m_axi_awsize  (atg_axi_awsize),
        .m_axi_awburst (atg_axi_awburst),  .m_axi_awlock  (atg_axi_awlock),
        .m_axi_awcache (atg_axi_awcache),  .m_axi_awprot  (atg_axi_awprot),
        .m_axi_awqos   (atg_axi_awqos),    .m_axi_awuser  (w_atg_awuser),
        .m_axi_awvalid (atg_axi_awvalid),  .m_axi_awready (atg_axi_awready),
        .m_axi_wlast   (atg_axi_wlast),    .m_axi_wdata   (atg_axi_wdata),
        .m_axi_wstrb   (atg_axi_wstrb),    .m_axi_wvalid  (atg_axi_wvalid),
        .m_axi_wready  (atg_axi_wready),
        .m_axi_bid     (atg_axi_bid),      .m_axi_bresp   (atg_axi_bresp),
        .m_axi_bvalid  (atg_axi_bvalid),   .m_axi_bready  (atg_axi_bready),
        .m_axi_arid    (atg_axi_arid),     .m_axi_araddr  (atg_axi_araddr),
        .m_axi_arlen   (atg_axi_arlen),    .m_axi_arsize  (atg_axi_arsize),
        .m_axi_arburst (atg_axi_arburst),  .m_axi_arlock  (atg_axi_arlock),
        .m_axi_arcache (atg_axi_arcache),  .m_axi_arprot  (atg_axi_arprot),
        .m_axi_arqos   (atg_axi_arqos),    .m_axi_aruser  (w_atg_aruser),
        .m_axi_arvalid (atg_axi_arvalid),  .m_axi_arready (atg_axi_arready),
        .m_axi_rid     (atg_axi_rid),      .m_axi_rlast   (atg_axi_rlast),
        .m_axi_rdata   (atg_axi_rdata),    .m_axi_rresp   (atg_axi_rresp),
        .m_axi_rvalid  (atg_axi_rvalid),   .m_axi_rready  (atg_axi_rready),
        .irq_out       (w_atg_irq),        .err_out       (w_atg_err)
    );
    assign atg_axi_awregion = 4'd0;
    assign atg_axi_arregion = 4'd0;
    assign atg_axi_awuser   = 1'b0;
    assign atg_axi_aruser   = 1'b0;
    assign atg_axi_wuser    = 1'b0;
    wire unused_atg = ^{w_atg_awuser, w_atg_aruser, atg_axi_buser, atg_axi_ruser};

    // ---- AXI Central DMA (master cdma; registers through ext1) ------------------------
    logic w_cdma_irq;

    // The DMA's register slave takes AW only with W (AXI A3.3.1). It sits
    // directly on ext1: the AXI4-to-AXI4-Lite converter in the configuration
    // bridge offers W without waiting for AWREADY since bridge BUG-020 was
    // fixed (an AW skid stood here until then).
    bs_cdma u_cdma (
        .m_axi_aclk (aclk), .s_axi_lite_aclk (aclk), .s_axi_lite_aresetn (aresetn),
        .cdma_introut (w_cdma_irq),
        .s_axi_lite_awready (ext1_axil_awready), .s_axi_lite_awvalid (ext1_axil_awvalid),
        .s_axi_lite_awaddr  (ext1_axil_awaddr[5:0]),
        .s_axi_lite_wready  (ext1_axil_wready),  .s_axi_lite_wvalid  (ext1_axil_wvalid),
        .s_axi_lite_wdata   (ext1_axil_wdata),
        .s_axi_lite_bready  (ext1_axil_bready),  .s_axi_lite_bvalid  (ext1_axil_bvalid),
        .s_axi_lite_bresp   (ext1_axil_bresp),
        .s_axi_lite_arready (ext1_axil_arready), .s_axi_lite_arvalid (ext1_axil_arvalid),
        .s_axi_lite_araddr  (ext1_axil_araddr[5:0]),
        .s_axi_lite_rready  (ext1_axil_rready),  .s_axi_lite_rvalid  (ext1_axil_rvalid),
        .s_axi_lite_rdata   (ext1_axil_rdata),   .s_axi_lite_rresp   (ext1_axil_rresp),
        .m_axi_arready (cdma_axi_arready), .m_axi_arvalid (cdma_axi_arvalid),
        .m_axi_araddr  (cdma_axi_araddr),  .m_axi_arlen   (cdma_axi_arlen),
        .m_axi_arsize  (cdma_axi_arsize),  .m_axi_arburst (cdma_axi_arburst),
        .m_axi_arprot  (cdma_axi_arprot),  .m_axi_arcache (cdma_axi_arcache),
        .m_axi_rready  (cdma_axi_rready),  .m_axi_rvalid  (cdma_axi_rvalid),
        .m_axi_rdata   (cdma_axi_rdata),   .m_axi_rresp   (cdma_axi_rresp),
        .m_axi_rlast   (cdma_axi_rlast),
        .m_axi_awready (cdma_axi_awready), .m_axi_awvalid (cdma_axi_awvalid),
        .m_axi_awaddr  (cdma_axi_awaddr),  .m_axi_awlen   (cdma_axi_awlen),
        .m_axi_awsize  (cdma_axi_awsize),  .m_axi_awburst (cdma_axi_awburst),
        .m_axi_awprot  (cdma_axi_awprot),  .m_axi_awcache (cdma_axi_awcache),
        .m_axi_wready  (cdma_axi_wready),  .m_axi_wvalid  (cdma_axi_wvalid),
        .m_axi_wdata   (cdma_axi_wdata),   .m_axi_wstrb   (cdma_axi_wstrb),
        .m_axi_wlast   (cdma_axi_wlast),
        .m_axi_bready  (cdma_axi_bready),  .m_axi_bvalid  (cdma_axi_bvalid),
        .m_axi_bresp   (cdma_axi_bresp),
        .cdma_tvect_out ()
    );
    // the DMA has no ID, lock, QoS, region or user signals: one ID, all zero
    assign cdma_axi_awid = 1'b0;     assign cdma_axi_arid = 1'b0;
    assign cdma_axi_awlock = 1'b0;   assign cdma_axi_arlock = 1'b0;
    assign cdma_axi_awqos = 4'd0;    assign cdma_axi_arqos = 4'd0;
    assign cdma_axi_awregion = 4'd0; assign cdma_axi_arregion = 4'd0;
    assign cdma_axi_awuser = 1'b0;   assign cdma_axi_aruser = 1'b0;
    assign cdma_axi_wuser = 1'b0;
    wire unused_cdma = ^{cdma_axi_bid, cdma_axi_rid, cdma_axi_buser, cdma_axi_ruser};

    // ---- protocol checkers on the two memory links -------------------------------------
    logic [159:0] w_pc_ddr_status, w_pc_bram_status;
    // pc_ddr / pc_bram asserted are ILA triggers too (capture_ila.tcl ILA_TRIG=pc)
    (* mark_debug = "true" *) logic w_pc_ddr_asserted;
    (* mark_debug = "true" *) logic w_pc_bram_asserted;
    logic         w_pc_atg_asserted;
    logic [159:0] w_pc_atg_status;

    
    bs_pc_ddr u_pc_ddr (
        .pc_status (w_pc_ddr_status), .pc_asserted (w_pc_ddr_asserted),
        .aclk, .aresetn,
        .pc_axi_awid (ddr_axi_awid), .pc_axi_awaddr (ddr_axi_awaddr),
        .pc_axi_awlen (ddr_axi_awlen), .pc_axi_awsize (ddr_axi_awsize),
        .pc_axi_awburst (ddr_axi_awburst), .pc_axi_awlock (ddr_axi_awlock),
        .pc_axi_awcache (ddr_axi_awcache), .pc_axi_awprot (ddr_axi_awprot),
        .pc_axi_awqos (ddr_axi_awqos), .pc_axi_awregion (ddr_axi_awregion),
        .pc_axi_awvalid (ddr_axi_awvalid), .pc_axi_awready (ddr_axi_awready),
        .pc_axi_wlast (ddr_axi_wlast), .pc_axi_wdata (ddr_axi_wdata),
        .pc_axi_wstrb (ddr_axi_wstrb), .pc_axi_wvalid (ddr_axi_wvalid),
        .pc_axi_wready (ddr_axi_wready), .pc_axi_bid (ddr_axi_bid),
        .pc_axi_bresp (ddr_axi_bresp), .pc_axi_bvalid (ddr_axi_bvalid),
        .pc_axi_bready (ddr_axi_bready), .pc_axi_arid (ddr_axi_arid),
        .pc_axi_araddr (ddr_axi_araddr), .pc_axi_arlen (ddr_axi_arlen),
        .pc_axi_arsize (ddr_axi_arsize), .pc_axi_arburst (ddr_axi_arburst),
        .pc_axi_arlock (ddr_axi_arlock), .pc_axi_arcache (ddr_axi_arcache),
        .pc_axi_arprot (ddr_axi_arprot), .pc_axi_arqos (ddr_axi_arqos),
        .pc_axi_arregion (ddr_axi_arregion), .pc_axi_arvalid (ddr_axi_arvalid),
        .pc_axi_arready (ddr_axi_arready), .pc_axi_rid (ddr_axi_rid),
        .pc_axi_rlast (ddr_axi_rlast), .pc_axi_rdata (ddr_axi_rdata),
        .pc_axi_rresp (ddr_axi_rresp), .pc_axi_rvalid (ddr_axi_rvalid),
        .pc_axi_rready (ddr_axi_rready)
    );
`ifdef BS_XMIX
    // the bridge's AXI3 output is what is judged (the AXI4 side is the converter's)
    bs_pc_bram3 u_pc_bram (
        .pc_status (w_pc_bram_status), .pc_asserted (w_pc_bram_asserted),
        .aclk, .aresetn,
        .pc_axi_awid (b3_axi_awid), .pc_axi_awaddr (b3_axi_awaddr),
        .pc_axi_awlen (b3_axi_awlen), .pc_axi_awsize (b3_axi_awsize),
        .pc_axi_awburst (b3_axi_awburst), .pc_axi_awlock (b3_axi_awlock),
        .pc_axi_awcache (b3_axi_awcache), .pc_axi_awprot (b3_axi_awprot),
        .pc_axi_awqos (4'd0),
        .pc_axi_awvalid (b3_axi_awvalid), .pc_axi_awready (b3_axi_awready),
        .pc_axi_wid (b3_axi_wid), .pc_axi_wlast (b3_axi_wlast), .pc_axi_wdata (b3_axi_wdata),
        .pc_axi_wstrb (b3_axi_wstrb), .pc_axi_wvalid (b3_axi_wvalid),
        .pc_axi_wready (b3_axi_wready), .pc_axi_bid (b3_axi_bid),
        .pc_axi_bresp (b3_axi_bresp), .pc_axi_bvalid (b3_axi_bvalid),
        .pc_axi_bready (b3_axi_bready), .pc_axi_arid (b3_axi_arid),
        .pc_axi_araddr (b3_axi_araddr), .pc_axi_arlen (b3_axi_arlen),
        .pc_axi_arsize (b3_axi_arsize), .pc_axi_arburst (b3_axi_arburst),
        .pc_axi_arlock (b3_axi_arlock), .pc_axi_arcache (b3_axi_arcache),
        .pc_axi_arprot (b3_axi_arprot), .pc_axi_arqos (4'd0),
        .pc_axi_arvalid (b3_axi_arvalid),
        .pc_axi_arready (b3_axi_arready), .pc_axi_rid (b3_axi_rid),
        .pc_axi_rlast (b3_axi_rlast), .pc_axi_rdata (b3_axi_rdata),
        .pc_axi_rresp (b3_axi_rresp), .pc_axi_rvalid (b3_axi_rvalid),
        .pc_axi_rready (b3_axi_rready)
    );
`else
    bs_pc_bram u_pc_bram (
        .pc_status (w_pc_bram_status), .pc_asserted (w_pc_bram_asserted),
        .aclk, .aresetn,
        .pc_axi_awid (bram_axi_awid), .pc_axi_awaddr (bram_axi_awaddr),
        .pc_axi_awlen (bram_axi_awlen), .pc_axi_awsize (bram_axi_awsize),
        .pc_axi_awburst (bram_axi_awburst), .pc_axi_awlock (bram_axi_awlock),
        .pc_axi_awcache (bram_axi_awcache), .pc_axi_awprot (bram_axi_awprot),
        .pc_axi_awqos (bram_axi_awqos), .pc_axi_awregion (bram_axi_awregion),
        .pc_axi_awvalid (bram_axi_awvalid), .pc_axi_awready (bram_axi_awready),
        .pc_axi_wlast (bram_axi_wlast), .pc_axi_wdata (bram_axi_wdata),
        .pc_axi_wstrb (bram_axi_wstrb), .pc_axi_wvalid (bram_axi_wvalid),
        .pc_axi_wready (bram_axi_wready), .pc_axi_bid (bram_axi_bid),
        .pc_axi_bresp (bram_axi_bresp), .pc_axi_bvalid (bram_axi_bvalid),
        .pc_axi_bready (bram_axi_bready), .pc_axi_arid (bram_axi_arid),
        .pc_axi_araddr (bram_axi_araddr), .pc_axi_arlen (bram_axi_arlen),
        .pc_axi_arsize (bram_axi_arsize), .pc_axi_arburst (bram_axi_arburst),
        .pc_axi_arlock (bram_axi_arlock), .pc_axi_arcache (bram_axi_arcache),
        .pc_axi_arprot (bram_axi_arprot), .pc_axi_arqos (bram_axi_arqos),
        .pc_axi_arregion (bram_axi_arregion), .pc_axi_arvalid (bram_axi_arvalid),
        .pc_axi_arready (bram_axi_arready), .pc_axi_rid (bram_axi_rid),
        .pc_axi_rlast (bram_axi_rlast), .pc_axi_rdata (bram_axi_rdata),
        .pc_axi_rresp (bram_axi_rresp), .pc_axi_rvalid (bram_axi_rvalid),
        .pc_axi_rready (bram_axi_rready)
    );
`endif
    bs_pc_atg u_pc_atg (
        .pc_status (w_pc_atg_status), .pc_asserted (w_pc_atg_asserted),
        .aclk, .aresetn,
        .pc_axi_awid (atg_axi_awid), .pc_axi_awaddr (atg_axi_awaddr),
        .pc_axi_awlen (atg_axi_awlen), .pc_axi_awsize (atg_axi_awsize),
        .pc_axi_awburst (atg_axi_awburst), .pc_axi_awlock (atg_axi_awlock),
        .pc_axi_awcache (atg_axi_awcache), .pc_axi_awprot (atg_axi_awprot),
        .pc_axi_awqos (atg_axi_awqos), .pc_axi_awregion (atg_axi_awregion),
        .pc_axi_awvalid (atg_axi_awvalid), .pc_axi_awready (atg_axi_awready),
        .pc_axi_wlast (atg_axi_wlast), .pc_axi_wdata (atg_axi_wdata),
        .pc_axi_wstrb (atg_axi_wstrb), .pc_axi_wvalid (atg_axi_wvalid),
        .pc_axi_wready (atg_axi_wready), .pc_axi_bid (atg_axi_bid),
        .pc_axi_bresp (atg_axi_bresp), .pc_axi_bvalid (atg_axi_bvalid),
        .pc_axi_bready (atg_axi_bready), .pc_axi_arid (atg_axi_arid),
        .pc_axi_araddr (atg_axi_araddr), .pc_axi_arlen (atg_axi_arlen),
        .pc_axi_arsize (atg_axi_arsize), .pc_axi_arburst (atg_axi_arburst),
        .pc_axi_arlock (atg_axi_arlock), .pc_axi_arcache (atg_axi_arcache),
        .pc_axi_arprot (atg_axi_arprot), .pc_axi_arqos (atg_axi_arqos),
        .pc_axi_arregion (atg_axi_arregion), .pc_axi_arvalid (atg_axi_arvalid),
        .pc_axi_arready (atg_axi_arready), .pc_axi_rid (atg_axi_rid),
        .pc_axi_rlast (atg_axi_rlast), .pc_axi_rdata (atg_axi_rdata),
        .pc_axi_rresp (atg_axi_rresp), .pc_axi_rvalid (atg_axi_rvalid),
        .pc_axi_rready (atg_axi_rready)
    );

    // ---- link stall detectors (the ILA's triggers) ---------------------------------
    // Work pending on a memory link -- a VALID up, or a write / read accepted and
    // not yet answered -- and no handshake on any of its channels for 2048
    // cycles. Sticky until reset. The ILA build (fpga/tcl/build_ila.tcl)
    // triggers on it, so a capture shows the cycles that led into a stall.
    logic [15:0] r_ddr_wr_out, r_ddr_rd_out;
    logic [11:0] r_ddr_idle;
    (* mark_debug = "true" *) logic r_ddr_stall;
    logic w_ddr_any_hs, w_ddr_pending;
    assign w_ddr_any_hs  = (ddr_axi_awvalid && ddr_axi_awready) || (ddr_axi_wvalid && ddr_axi_wready)
                        || (ddr_axi_bvalid && ddr_axi_bready) || (ddr_axi_arvalid && ddr_axi_arready)
                        || (ddr_axi_rvalid && ddr_axi_rready);
    assign w_ddr_pending = ddr_axi_awvalid || ddr_axi_wvalid || ddr_axi_arvalid
                        || ddr_axi_bvalid || ddr_axi_rvalid
                        || (r_ddr_wr_out != '0) || (r_ddr_rd_out != '0);
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_ddr_wr_out <= '0;
            r_ddr_rd_out <= '0;
            r_ddr_idle   <= '0;
            r_ddr_stall  <= 1'b0;
        end else begin
            r_ddr_wr_out <= r_ddr_wr_out + 16'(ddr_axi_awvalid && ddr_axi_awready)
                                         - 16'(ddr_axi_bvalid && ddr_axi_bready);
            r_ddr_rd_out <= r_ddr_rd_out + 16'(ddr_axi_arvalid && ddr_axi_arready)
                                         - 16'(ddr_axi_rvalid && ddr_axi_rready && ddr_axi_rlast);
            if (w_ddr_any_hs || !w_ddr_pending) r_ddr_idle <= '0;
            else if (r_ddr_idle != '1)          r_ddr_idle <= r_ddr_idle + 12'd1;
            if (r_ddr_idle == '1)               r_ddr_stall <= 1'b1;
        end
    end

    // the same on the bram link
    logic [15:0] r_bram_wr_out, r_bram_rd_out;
    logic [11:0] r_bram_idle;
    (* mark_debug = "true" *) logic r_bram_stall;
    logic w_bram_any_hs, w_bram_pending;
    assign w_bram_any_hs  = (bram_axi_awvalid && bram_axi_awready) || (bram_axi_wvalid && bram_axi_wready)
                        || (bram_axi_bvalid && bram_axi_bready) || (bram_axi_arvalid && bram_axi_arready)
                        || (bram_axi_rvalid && bram_axi_rready);
    assign w_bram_pending = bram_axi_awvalid || bram_axi_wvalid || bram_axi_arvalid
                        || bram_axi_bvalid || bram_axi_rvalid
                        || (r_bram_wr_out != '0) || (r_bram_rd_out != '0);
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_bram_wr_out <= '0;
            r_bram_rd_out <= '0;
            r_bram_idle   <= '0;
            r_bram_stall  <= 1'b0;
        end else begin
            r_bram_wr_out <= r_bram_wr_out + 16'(bram_axi_awvalid && bram_axi_awready)
                                         - 16'(bram_axi_bvalid && bram_axi_bready);
            r_bram_rd_out <= r_bram_rd_out + 16'(bram_axi_arvalid && bram_axi_arready)
                                         - 16'(bram_axi_rvalid && bram_axi_rready && bram_axi_rlast);
            if (w_bram_any_hs || !w_bram_pending) r_bram_idle <= '0;
            else if (r_bram_idle != '1)          r_bram_idle <= r_bram_idle + 12'd1;
            if (r_bram_idle == '1)               r_bram_stall <= 1'b1;
        end
    end

    // the same on the traffic generator's port (a response it waits for that
    // never comes shows here, not on a memory link)
    logic [15:0] r_atg_wr_out, r_atg_rd_out;
    logic [11:0] r_atg_idle;
    (* mark_debug = "true" *) logic r_atg_stall;
    logic w_atg_any_hs, w_atg_pending;
    assign w_atg_any_hs  = (atg_axi_awvalid && atg_axi_awready) || (atg_axi_wvalid && atg_axi_wready)
                        || (atg_axi_bvalid && atg_axi_bready) || (atg_axi_arvalid && atg_axi_arready)
                        || (atg_axi_rvalid && atg_axi_rready);
    assign w_atg_pending = atg_axi_awvalid || atg_axi_wvalid || atg_axi_arvalid
                        || atg_axi_bvalid || atg_axi_rvalid
                        || (r_atg_wr_out != '0) || (r_atg_rd_out != '0);
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_atg_wr_out <= '0;
            r_atg_rd_out <= '0;
            r_atg_idle   <= '0;
            r_atg_stall  <= 1'b0;
        end else begin
            r_atg_wr_out <= r_atg_wr_out + 16'(atg_axi_awvalid && atg_axi_awready)
                                         - 16'(atg_axi_bvalid && atg_axi_bready);
            r_atg_rd_out <= r_atg_rd_out + 16'(atg_axi_arvalid && atg_axi_arready)
                                         - 16'(atg_axi_rvalid && atg_axi_rready && atg_axi_rlast);
            if (w_atg_any_hs || !w_atg_pending) r_atg_idle <= '0;
            else if (r_atg_idle != '1)          r_atg_idle <= r_atg_idle + 12'd1;
            if (r_atg_idle == '1)               r_atg_stall <= 1'b1;
        end
    end

    // ---- status ----------------------------------------------------------------------
    // Everything below is on aclk except the cclk MMCM lock, which is quasi-
    // static (it falls only with user_clk, which resets everything).
    always_ff @(posedge aclk) begin
        w_ext_sts[31:0]   <= {r_ddr_wr_out, 4'd0, w_pc_atg_asserted, ddr_init_error, r_bram_stall, r_ddr_stall, w_cdma_irq, w_atg_err, w_atg_irq,
                              w_pc_bram_asserted, w_pc_ddr_asserted, w_c_locked,
                              ddr_pll_locked, ddr_init_done};
        w_ext_sts[63:32]  <= w_pc_ddr_status[31:0];
        w_ext_sts[95:64]  <= w_pc_ddr_status[63:32];
        w_ext_sts[127:96] <= w_pc_bram_status[31:0];
    end
    wire unused_pc = ^{w_pc_ddr_status[159:64], w_pc_bram_status[159:32], w_pc_atg_status};

    logic [25:0] r_beat;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) r_beat <= '0;
        else          r_beat <= r_beat + 26'd1;
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) led <= '0;
        else led <= {ddr_init_done && !ddr_init_error, w_pc_ddr_asserted || w_pc_bram_asserted,
                     w_all_done && !w_any_err, w_any_err, w_all_done, w_busy,
                     ddr_pll_locked && w_c_locked, r_beat[25]};
    end

endmodule : bs_genesys2_xil_top
