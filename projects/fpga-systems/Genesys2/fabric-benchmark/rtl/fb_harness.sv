// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: fb_harness
// Purpose: The Genesys 2 fabric benchmark harness (K0): STREAM moving data
//          through the data fabric under test, controlled over the UART.
//
// Documentation: projects/fpga-systems/Genesys2/fabric-benchmark/PRD.md
//
// Author: sean galloway
// Created: 2026-10-15
//
//==============================================================================
// What is here, and why it is the same in every leg
//==============================================================================
//   Control (aclk):  UART -> uart_axil_bridge -> bridge_fb_cfg (generated) ->
//     stream_apb   0x0000_0000  STREAM registers
//     harness_csr  0x0001_0000  the STREAM harness's CSR block, unchanged
//     desc_ram     0x0002_0000  descriptor preload (write port)
//     stream_err   0x0003_0000  STREAM error FIFO
//     slvmon_apb   0x0018_0000  slave-side observer window: stubbed until that
//                               observer lands (fb_apb_stub reads 0 = absent)
//     obs_apb      0x0019_0000  master-side observer (STREAM's rd/wr port): bus
//                               meters + latency histograms, read by the host's
//                               bus_meters exactly as in the STREAM build
//   The offsets are the Genesys 2 STREAM harness's, so its host stack (the
//   characterization runner, stream_addrs, harness_addrs) drives this harness
//   unchanged; only the descriptor builder learns the data map below.
//
//   Data (aclk): the fabric under test, fb_data_fabric -- whichever leg the
//   filelist compiled (bridge / Xilinx AXI Crossbar / SmartConnect):
//     M0 stream_desc  STREAM m_axi_desc 256 -> axi4_dwidth_converter_rd -> 128
//     M1 stream_rd    STREAM m_axi_rd
//     M2 stream_wr    STREAM m_axi_wr
//     M3 inj_wr       W3 injector; held idle in K0 (fabric-only mode, W2)
//     S0 ddr          0x0000_0000  1 GB  -> the ddr_* ports (MIG on the board,
//                                          a memory model in sim)
//     S1 desc_ram     0x8000_0000  64 KB -> the descriptor RAM's read port
//     S2 lfsr_src     0x9000_0000  256 MB-> fb_endpoints (LFSR source)
//     S3 crc_snk      0xA000_0000  256 MB-> fb_endpoints (CRC sink)
//
//   Channels: the endpoints take a burst's channel from address bits
//   [CH_ADDR_LSB +: 3] (fb_endpoints CH_SEL_ADDR=1), because SmartConnect
//   delivers no ID to its slaves. CH_ADDR_LSB = 25: channel N owns the 32 MB
//   at window base + N x 32 MB, which holds the largest chain the host builds
//   (16 descriptors x 1 MB). The host places channel N's buffers there.
//
//   Run timer and verdict: char_run_timer (utility-ip/misc), as in the STREAM
//   and RAPIDS harnesses. START is the first STREAM descriptor AR (taken on
//   STREAM's side of the converter, before any fabric); STOP is the sink's
//   write-beat count reaching TIMER_EXPECTED_BEATS. The counts and CRCs come
//   back from the endpoint clock as periodic snapshots, so SETTLE is 32 cycles
//   to span the next snapshot after STOP, and STOP itself lands a snapshot
//   period (a few cycles) after the last beat -- the same in every leg.
//
//   Soft reset (harness_csr CTRL.SOFT_RESET) resets STREAM, the fabric, the
//   descriptor RAM and the observer. It does NOT reset fb_endpoints, whose
//   clock-crossing FIFOs would be left half reset; it and CLEAR_STATS both
//   clear the endpoints' CRC state instead. The UART, the configuration bridge and the
//   CSR block stay on the hardware reset so the host link survives it.
//==============================================================================

`timescale 1ns / 1ps

`include "reset_defs.svh"

module fb_harness #(
    parameter int FPGA_CLK_HZ  = 100_000_000,
    parameter int UART_BAUD    = 115_200,
    parameter int NUM_CHANNELS = stream_char_cfg_pkg::CFG_NUM_CHANNELS,
    parameter int SRAM_DEPTH   = stream_char_cfg_pkg::CFG_SRAM_DEPTH,
    parameter int AR_MAX_OUTSTANDING = stream_char_cfg_pkg::CFG_AR_MAX_OUTSTANDING,
    parameter int AW_MAX_OUTSTANDING = stream_char_cfg_pkg::CFG_AW_MAX_OUTSTANDING,
    parameter int USE_ROW_COL_MAJOR_ADDRESSING =
                      stream_char_cfg_pkg::CFG_USE_ROW_COL_MAJOR_ADDRESSING,
    parameter int CH_ADDR_LSB  = 25
) (
    input  logic          aclk,
    input  logic          aresetn,
    input  logic          ep_clk,
    input  logic          ep_aresetn,

    input  logic          i_uart_rx,
    output logic          o_uart_tx,

    // S0: DDR3 window, 128-bit AXI4, slave-side ID {slot, id}
    output logic [9:0]    ddr_awid,
    output logic [31:0]   ddr_awaddr,
    output logic [7:0]    ddr_awlen,
    output logic [2:0]    ddr_awsize,
    output logic [1:0]    ddr_awburst,
    output logic          ddr_awlock,
    output logic [3:0]    ddr_awcache,
    output logic [2:0]    ddr_awprot,
    output logic [3:0]    ddr_awqos,
    output logic          ddr_awvalid,
    input  logic          ddr_awready,
    output logic [127:0]  ddr_wdata,
    output logic [15:0]   ddr_wstrb,
    output logic          ddr_wlast,
    output logic          ddr_wvalid,
    input  logic          ddr_wready,
    input  logic [9:0]    ddr_bid,
    input  logic [1:0]    ddr_bresp,
    input  logic          ddr_bvalid,
    output logic          ddr_bready,
    output logic [9:0]    ddr_arid,
    output logic [31:0]   ddr_araddr,
    output logic [7:0]    ddr_arlen,
    output logic [2:0]    ddr_arsize,
    output logic [1:0]    ddr_arburst,
    output logic          ddr_arlock,
    output logic [3:0]    ddr_arcache,
    output logic [2:0]    ddr_arprot,
    output logic [3:0]    ddr_arqos,
    output logic          ddr_arvalid,
    input  logic          ddr_arready,
    input  logic [9:0]    ddr_rid,
    input  logic [127:0]  ddr_rdata,
    input  logic [1:0]    ddr_rresp,
    input  logic          ddr_rlast,
    input  logic          ddr_rvalid,
    output logic          ddr_rready,

    // Board status (LEDs)
    output logic          o_timer_done,
    output logic          o_timer_pass,
    output logic          o_stream_irq
);

    localparam int DATA_WIDTH     = 128;   // every fabric port (PRD section 4)
    localparam int DESC_WIDTH     = 256;   // STREAM's descriptor master
    localparam int ADDR_WIDTH     = 32;
    localparam int AXI_ID_WIDTH   = 8;     // master-side ID
    localparam int SID            = 10;    // slave-side ID {slot, id}
    localparam int AXI_USER_WIDTH = $clog2(NUM_CHANNELS) > 0 ? $clog2(NUM_CHANNELS) : 1;
    localparam int APB_ADDR_WIDTH = 13;
    localparam int CLKS_PER_BIT   = FPGA_CLK_HZ / UART_BAUD;
    // 512 x 128 b = 8 KB: the STREAM harness's 256 descriptors of 32 B
    localparam int DESC_RAM_DEPTH = 512;

    // =========================================================================
    // Data-fabric port wires, named exactly as fb_data_fabric's ports so the
    // fabric instance connects by .* (ddr_* are this module's own ports).
    // =========================================================================
    // stream_desc (rd, ID 8)
    logic [7:0] stream_desc_arid;
    logic [31:0] stream_desc_araddr;
    logic [7:0] stream_desc_arlen;
    logic [2:0] stream_desc_arsize;
    logic [1:0] stream_desc_arburst;
    logic stream_desc_arlock;
    logic [3:0] stream_desc_arcache;
    logic [2:0] stream_desc_arprot;
    logic [3:0] stream_desc_arqos;
    logic stream_desc_arvalid;
    logic stream_desc_arready;
    logic [7:0] stream_desc_rid;
    logic [127:0] stream_desc_rdata;
    logic [1:0] stream_desc_rresp;
    logic stream_desc_rlast;
    logic stream_desc_rvalid;
    logic stream_desc_rready;
    // stream_rd (rd, ID 8)
    logic [7:0] stream_rd_arid;
    logic [31:0] stream_rd_araddr;
    logic [7:0] stream_rd_arlen;
    logic [2:0] stream_rd_arsize;
    logic [1:0] stream_rd_arburst;
    logic stream_rd_arlock;
    logic [3:0] stream_rd_arcache;
    logic [2:0] stream_rd_arprot;
    logic [3:0] stream_rd_arqos;
    logic stream_rd_arvalid;
    logic stream_rd_arready;
    logic [7:0] stream_rd_rid;
    logic [127:0] stream_rd_rdata;
    logic [1:0] stream_rd_rresp;
    logic stream_rd_rlast;
    logic stream_rd_rvalid;
    logic stream_rd_rready;
    // stream_wr (wr, ID 8)
    logic [7:0] stream_wr_awid;
    logic [31:0] stream_wr_awaddr;
    logic [7:0] stream_wr_awlen;
    logic [2:0] stream_wr_awsize;
    logic [1:0] stream_wr_awburst;
    logic stream_wr_awlock;
    logic [3:0] stream_wr_awcache;
    logic [2:0] stream_wr_awprot;
    logic [3:0] stream_wr_awqos;
    logic stream_wr_awvalid;
    logic stream_wr_awready;
    logic [127:0] stream_wr_wdata;
    logic [15:0] stream_wr_wstrb;
    logic stream_wr_wlast;
    logic stream_wr_wvalid;
    logic stream_wr_wready;
    logic [7:0] stream_wr_bid;
    logic [1:0] stream_wr_bresp;
    logic stream_wr_bvalid;
    logic stream_wr_bready;
    // inj_wr (wr, ID 8)
    logic [7:0] inj_wr_awid;
    logic [31:0] inj_wr_awaddr;
    logic [7:0] inj_wr_awlen;
    logic [2:0] inj_wr_awsize;
    logic [1:0] inj_wr_awburst;
    logic inj_wr_awlock;
    logic [3:0] inj_wr_awcache;
    logic [2:0] inj_wr_awprot;
    logic [3:0] inj_wr_awqos;
    logic inj_wr_awvalid;
    logic inj_wr_awready;
    logic [127:0] inj_wr_wdata;
    logic [15:0] inj_wr_wstrb;
    logic inj_wr_wlast;
    logic inj_wr_wvalid;
    logic inj_wr_wready;
    logic [7:0] inj_wr_bid;
    logic [1:0] inj_wr_bresp;
    logic inj_wr_bvalid;
    logic inj_wr_bready;
    // desc_ram (rd, ID 10)
    logic [9:0] desc_ram_arid;
    logic [31:0] desc_ram_araddr;
    logic [7:0] desc_ram_arlen;
    logic [2:0] desc_ram_arsize;
    logic [1:0] desc_ram_arburst;
    logic desc_ram_arlock;
    logic [3:0] desc_ram_arcache;
    logic [2:0] desc_ram_arprot;
    logic [3:0] desc_ram_arqos;
    logic desc_ram_arvalid;
    logic desc_ram_arready;
    logic [9:0] desc_ram_rid;
    logic [127:0] desc_ram_rdata;
    logic [1:0] desc_ram_rresp;
    logic desc_ram_rlast;
    logic desc_ram_rvalid;
    logic desc_ram_rready;
    // lfsr_src (rd, ID 10)
    logic [9:0] lfsr_src_arid;
    logic [31:0] lfsr_src_araddr;
    logic [7:0] lfsr_src_arlen;
    logic [2:0] lfsr_src_arsize;
    logic [1:0] lfsr_src_arburst;
    logic lfsr_src_arlock;
    logic [3:0] lfsr_src_arcache;
    logic [2:0] lfsr_src_arprot;
    logic [3:0] lfsr_src_arqos;
    logic lfsr_src_arvalid;
    logic lfsr_src_arready;
    logic [9:0] lfsr_src_rid;
    logic [127:0] lfsr_src_rdata;
    logic [1:0] lfsr_src_rresp;
    logic lfsr_src_rlast;
    logic lfsr_src_rvalid;
    logic lfsr_src_rready;
    // crc_snk (wr, ID 10)
    logic [9:0] crc_snk_awid;
    logic [31:0] crc_snk_awaddr;
    logic [7:0] crc_snk_awlen;
    logic [2:0] crc_snk_awsize;
    logic [1:0] crc_snk_awburst;
    logic crc_snk_awlock;
    logic [3:0] crc_snk_awcache;
    logic [2:0] crc_snk_awprot;
    logic [3:0] crc_snk_awqos;
    logic crc_snk_awvalid;
    logic crc_snk_awready;
    logic [127:0] crc_snk_wdata;
    logic [15:0] crc_snk_wstrb;
    logic crc_snk_wlast;
    logic crc_snk_wvalid;
    logic crc_snk_wready;
    logic [9:0] crc_snk_bid;
    logic [1:0] crc_snk_bresp;
    logic crc_snk_bvalid;
    logic crc_snk_bready;

    // =========================================================================
    // Host link: UART -> AXI4-Lite -> configuration bridge
    // =========================================================================
    logic [31:0] host_axi_awaddr, host_axi_wdata, host_axi_araddr, host_axi_rdata;
    logic [2:0]  host_axi_awprot, host_axi_arprot;
    logic [3:0]  host_axi_wstrb;
    logic [1:0]  host_axi_bresp, host_axi_rresp;
    logic        host_axi_awvalid, host_axi_awready, host_axi_wvalid, host_axi_wready;
    logic        host_axi_bvalid, host_axi_bready, host_axi_arvalid, host_axi_arready;
    logic        host_axi_rvalid, host_axi_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH (32),
        .AXIL_DATA_WIDTH (32),
        .CLKS_PER_BIT    (CLKS_PER_BIT)
    ) u_uart (
        .aclk(aclk), .aresetn(aresetn),
        .i_uart_rx(i_uart_rx), .o_uart_tx(o_uart_tx),
        .m_axil_awaddr(host_axi_awaddr), .m_axil_awprot(host_axi_awprot),
        .m_axil_awvalid(host_axi_awvalid), .m_axil_awready(host_axi_awready),
        .m_axil_wdata(host_axi_wdata), .m_axil_wstrb(host_axi_wstrb),
        .m_axil_wvalid(host_axi_wvalid), .m_axil_wready(host_axi_wready),
        .m_axil_bresp(host_axi_bresp), .m_axil_bvalid(host_axi_bvalid),
        .m_axil_bready(host_axi_bready),
        .m_axil_araddr(host_axi_araddr), .m_axil_arprot(host_axi_arprot),
        .m_axil_arvalid(host_axi_arvalid), .m_axil_arready(host_axi_arready),
        .m_axil_rdata(host_axi_rdata), .m_axil_rresp(host_axi_rresp),
        .m_axil_rvalid(host_axi_rvalid), .m_axil_rready(host_axi_rready)
    );

    // Configuration-bridge slave-side wires (bridge_fb_cfg port names)
    logic        stream_apb_PSEL, stream_apb_PENABLE, stream_apb_PWRITE;
    logic [31:0] stream_apb_PADDR, stream_apb_PWDATA, stream_apb_PRDATA;
    logic [3:0]  stream_apb_PSTRB;
    logic [2:0]  stream_apb_PPROT;
    logic        stream_apb_PREADY, stream_apb_PSLVERR;

    logic [31:0] harness_csr_axi_awaddr, harness_csr_axi_wdata, harness_csr_axi_araddr, harness_csr_axi_rdata;
    logic [2:0]  harness_csr_axi_awprot, harness_csr_axi_arprot;
    logic [3:0]  harness_csr_axi_wstrb;
    logic [1:0]  harness_csr_axi_bresp, harness_csr_axi_rresp;
    logic        harness_csr_axi_awvalid, harness_csr_axi_awready, harness_csr_axi_wvalid, harness_csr_axi_wready;
    logic        harness_csr_axi_bvalid, harness_csr_axi_bready, harness_csr_axi_arvalid, harness_csr_axi_arready;
    logic        harness_csr_axi_rvalid, harness_csr_axi_rready;

    logic        cfg_desc_awid, cfg_desc_wvalid, cfg_desc_wready, cfg_desc_wlast;
    logic [31:0] cfg_desc_awaddr;
    logic [7:0]  cfg_desc_awlen;
    logic [2:0]  cfg_desc_awsize, cfg_desc_awprot;
    logic [1:0]  cfg_desc_awburst, cfg_desc_bresp;
    logic        cfg_desc_awlock, cfg_desc_awvalid, cfg_desc_awready;
    logic [3:0]  cfg_desc_awcache, cfg_desc_awqos, cfg_desc_awregion;
    logic        cfg_desc_awuser, cfg_desc_wuser, cfg_desc_bid, cfg_desc_buser;
    logic [127:0] cfg_desc_wdata;
    logic [15:0] cfg_desc_wstrb;
    logic        cfg_desc_bvalid, cfg_desc_bready;
    logic        cfg_desc_arid, cfg_desc_arlock, cfg_desc_aruser, cfg_desc_arvalid, cfg_desc_arready;
    logic [31:0] cfg_desc_araddr;
    logic [7:0]  cfg_desc_arlen;
    logic [2:0]  cfg_desc_arsize, cfg_desc_arprot;
    logic [1:0]  cfg_desc_arburst, cfg_desc_rresp;
    logic [3:0]  cfg_desc_arcache, cfg_desc_arqos, cfg_desc_arregion;
    logic        cfg_desc_rid, cfg_desc_rlast, cfg_desc_ruser, cfg_desc_rvalid, cfg_desc_rready;
    logic [127:0] cfg_desc_rdata;

    logic [31:0] stream_err_axi_awaddr, stream_err_axi_wdata, stream_err_axi_araddr, stream_err_axi_rdata;
    logic [2:0]  stream_err_axi_awprot, stream_err_axi_arprot;
    logic [3:0]  stream_err_axi_wstrb;
    logic [1:0]  stream_err_axi_bresp, stream_err_axi_rresp;
    logic        stream_err_axi_awvalid, stream_err_axi_awready, stream_err_axi_wvalid, stream_err_axi_wready;
    logic        stream_err_axi_bvalid, stream_err_axi_bready, stream_err_axi_arvalid, stream_err_axi_arready;
    logic        stream_err_axi_rvalid, stream_err_axi_rready;

    logic        slvmon_apb_PSEL, slvmon_apb_PENABLE, slvmon_apb_PWRITE, slvmon_apb_PREADY, slvmon_apb_PSLVERR;
    logic [31:0] slvmon_apb_PADDR, slvmon_apb_PWDATA, slvmon_apb_PRDATA;
    logic [3:0]  slvmon_apb_PSTRB;
    logic [2:0]  slvmon_apb_PPROT;
    logic        obs_apb_PSEL, obs_apb_PENABLE, obs_apb_PWRITE, obs_apb_PREADY, obs_apb_PSLVERR;
    logic [31:0] obs_apb_PADDR, obs_apb_PWDATA, obs_apb_PRDATA;
    logic [3:0]  obs_apb_PSTRB;
    logic [2:0]  obs_apb_PPROT;

    bridge_fb_cfg u_cfg (
        .aclk(aclk), .aresetn(aresetn),
        .host_axi_awaddr(host_axi_awaddr), .host_axi_awprot(host_axi_awprot),
        .host_axi_awvalid(host_axi_awvalid), .host_axi_awready(host_axi_awready),
        .host_axi_wdata(host_axi_wdata), .host_axi_wstrb(host_axi_wstrb),
        .host_axi_wvalid(host_axi_wvalid), .host_axi_wready(host_axi_wready),
        .host_axi_bresp(host_axi_bresp), .host_axi_bvalid(host_axi_bvalid),
        .host_axi_bready(host_axi_bready),
        .host_axi_araddr(host_axi_araddr), .host_axi_arprot(host_axi_arprot),
        .host_axi_arvalid(host_axi_arvalid), .host_axi_arready(host_axi_arready),
        .host_axi_rdata(host_axi_rdata), .host_axi_rresp(host_axi_rresp),
        .host_axi_rvalid(host_axi_rvalid), .host_axi_rready(host_axi_rready),
        .stream_apb_PSEL(stream_apb_PSEL), .stream_apb_PADDR(stream_apb_PADDR),
        .stream_apb_PENABLE(stream_apb_PENABLE), .stream_apb_PWRITE(stream_apb_PWRITE),
        .stream_apb_PWDATA(stream_apb_PWDATA), .stream_apb_PSTRB(stream_apb_PSTRB),
        .stream_apb_PPROT(stream_apb_PPROT), .stream_apb_PRDATA(stream_apb_PRDATA),
        .stream_apb_PREADY(stream_apb_PREADY), .stream_apb_PSLVERR(stream_apb_PSLVERR),
        .harness_csr_axi_awaddr(harness_csr_axi_awaddr), .harness_csr_axi_awprot(harness_csr_axi_awprot),
        .harness_csr_axi_awvalid(harness_csr_axi_awvalid), .harness_csr_axi_awready(harness_csr_axi_awready),
        .harness_csr_axi_wdata(harness_csr_axi_wdata), .harness_csr_axi_wstrb(harness_csr_axi_wstrb),
        .harness_csr_axi_wvalid(harness_csr_axi_wvalid), .harness_csr_axi_wready(harness_csr_axi_wready),
        .harness_csr_axi_bresp(harness_csr_axi_bresp), .harness_csr_axi_bvalid(harness_csr_axi_bvalid),
        .harness_csr_axi_bready(harness_csr_axi_bready),
        .harness_csr_axi_araddr(harness_csr_axi_araddr), .harness_csr_axi_arprot(harness_csr_axi_arprot),
        .harness_csr_axi_arvalid(harness_csr_axi_arvalid), .harness_csr_axi_arready(harness_csr_axi_arready),
        .harness_csr_axi_rdata(harness_csr_axi_rdata), .harness_csr_axi_rresp(harness_csr_axi_rresp),
        .harness_csr_axi_rvalid(harness_csr_axi_rvalid), .harness_csr_axi_rready(harness_csr_axi_rready),
        .desc_ram_axi_awid(cfg_desc_awid), .desc_ram_axi_awaddr(cfg_desc_awaddr),
        .desc_ram_axi_awlen(cfg_desc_awlen), .desc_ram_axi_awsize(cfg_desc_awsize),
        .desc_ram_axi_awburst(cfg_desc_awburst), .desc_ram_axi_awlock(cfg_desc_awlock),
        .desc_ram_axi_awcache(cfg_desc_awcache), .desc_ram_axi_awprot(cfg_desc_awprot),
        .desc_ram_axi_awqos(cfg_desc_awqos), .desc_ram_axi_awregion(cfg_desc_awregion),
        .desc_ram_axi_awuser(cfg_desc_awuser), .desc_ram_axi_awvalid(cfg_desc_awvalid),
        .desc_ram_axi_awready(cfg_desc_awready),
        .desc_ram_axi_wdata(cfg_desc_wdata), .desc_ram_axi_wstrb(cfg_desc_wstrb),
        .desc_ram_axi_wlast(cfg_desc_wlast), .desc_ram_axi_wuser(cfg_desc_wuser),
        .desc_ram_axi_wvalid(cfg_desc_wvalid), .desc_ram_axi_wready(cfg_desc_wready),
        .desc_ram_axi_bid(cfg_desc_bid), .desc_ram_axi_bresp(cfg_desc_bresp),
        .desc_ram_axi_buser(cfg_desc_buser), .desc_ram_axi_bvalid(cfg_desc_bvalid),
        .desc_ram_axi_bready(cfg_desc_bready),
        .desc_ram_axi_arid(cfg_desc_arid), .desc_ram_axi_araddr(cfg_desc_araddr),
        .desc_ram_axi_arlen(cfg_desc_arlen), .desc_ram_axi_arsize(cfg_desc_arsize),
        .desc_ram_axi_arburst(cfg_desc_arburst), .desc_ram_axi_arlock(cfg_desc_arlock),
        .desc_ram_axi_arcache(cfg_desc_arcache), .desc_ram_axi_arprot(cfg_desc_arprot),
        .desc_ram_axi_arqos(cfg_desc_arqos), .desc_ram_axi_arregion(cfg_desc_arregion),
        .desc_ram_axi_aruser(cfg_desc_aruser), .desc_ram_axi_arvalid(cfg_desc_arvalid),
        .desc_ram_axi_arready(cfg_desc_arready),
        .desc_ram_axi_rid(cfg_desc_rid), .desc_ram_axi_rdata(cfg_desc_rdata),
        .desc_ram_axi_rresp(cfg_desc_rresp), .desc_ram_axi_rlast(cfg_desc_rlast),
        .desc_ram_axi_ruser(cfg_desc_ruser), .desc_ram_axi_rvalid(cfg_desc_rvalid),
        .desc_ram_axi_rready(cfg_desc_rready),
        .stream_err_axi_awaddr(stream_err_axi_awaddr), .stream_err_axi_awprot(stream_err_axi_awprot),
        .stream_err_axi_awvalid(stream_err_axi_awvalid), .stream_err_axi_awready(stream_err_axi_awready),
        .stream_err_axi_wdata(stream_err_axi_wdata), .stream_err_axi_wstrb(stream_err_axi_wstrb),
        .stream_err_axi_wvalid(stream_err_axi_wvalid), .stream_err_axi_wready(stream_err_axi_wready),
        .stream_err_axi_bresp(stream_err_axi_bresp), .stream_err_axi_bvalid(stream_err_axi_bvalid),
        .stream_err_axi_bready(stream_err_axi_bready),
        .stream_err_axi_araddr(stream_err_axi_araddr), .stream_err_axi_arprot(stream_err_axi_arprot),
        .stream_err_axi_arvalid(stream_err_axi_arvalid), .stream_err_axi_arready(stream_err_axi_arready),
        .stream_err_axi_rdata(stream_err_axi_rdata), .stream_err_axi_rresp(stream_err_axi_rresp),
        .stream_err_axi_rvalid(stream_err_axi_rvalid), .stream_err_axi_rready(stream_err_axi_rready),
        .slvmon_apb_PSEL(slvmon_apb_PSEL), .slvmon_apb_PADDR(slvmon_apb_PADDR),
        .slvmon_apb_PENABLE(slvmon_apb_PENABLE), .slvmon_apb_PWRITE(slvmon_apb_PWRITE),
        .slvmon_apb_PWDATA(slvmon_apb_PWDATA), .slvmon_apb_PSTRB(slvmon_apb_PSTRB),
        .slvmon_apb_PPROT(slvmon_apb_PPROT), .slvmon_apb_PRDATA(slvmon_apb_PRDATA),
        .slvmon_apb_PREADY(slvmon_apb_PREADY), .slvmon_apb_PSLVERR(slvmon_apb_PSLVERR),
        .obs_apb_PSEL(obs_apb_PSEL), .obs_apb_PADDR(obs_apb_PADDR),
        .obs_apb_PENABLE(obs_apb_PENABLE), .obs_apb_PWRITE(obs_apb_PWRITE),
        .obs_apb_PWDATA(obs_apb_PWDATA), .obs_apb_PSTRB(obs_apb_PSTRB),
        .obs_apb_PPROT(obs_apb_PPROT), .obs_apb_PRDATA(obs_apb_PRDATA),
        .obs_apb_PREADY(obs_apb_PREADY), .obs_apb_PSLVERR(obs_apb_PSLVERR),
        .unmapped_irq(), .unmapped_addr(), .unmapped_count(), .unmapped_clear(1'b0)
    );

    // Slave-side observer window: present in the map, nothing behind it yet.
    fb_apb_stub u_slvmon_stub (
        .psel(slvmon_apb_PSEL), .penable(slvmon_apb_PENABLE), .pwrite(slvmon_apb_PWRITE),
        .paddr(slvmon_apb_PADDR), .pwdata(slvmon_apb_PWDATA), .pstrb(slvmon_apb_PSTRB),
        .pprot(slvmon_apb_PPROT), .prdata(slvmon_apb_PRDATA), .pready(slvmon_apb_PREADY),
        .pslverr(slvmon_apb_PSLVERR));
    // (obs_apb: the master-side observer, u_dma_observer, below)
    wire unused_obs_pprot = ^obs_apb_PPROT;

    // =========================================================================
    // Harness CSR (the STREAM harness's block) and the unit soft reset
    // =========================================================================
    logic        csr_clear_pulse, csr_soft_reset, csr_cam_clear;
    logic        csr_timer_clear_pulse;
    logic [31:0] csr_timer_expected_beats;
    logic        stream_irq;

    // Soft reset: pulse-extended to 16 cycles and ANDed with the hardware
    // reset, exactly as in the STREAM harness.
    localparam int SOFT_RST_PULSE_CYCLES = 16;
    logic [4:0] r_soft_rst_cnt;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))            r_soft_rst_cnt <= '0;
        else if (csr_soft_reset)               r_soft_rst_cnt <= 5'(SOFT_RST_PULSE_CYCLES);
        else if (r_soft_rst_cnt != 5'd0)       r_soft_rst_cnt <= r_soft_rst_cnt - 5'd1;
    )
    wire unit_aresetn = aresetn & (r_soft_rst_cnt == 5'd0);

    // Endpoint status (aclk snapshot from fb_endpoints) and the timer verdict
    logic [NUM_CHANNELS-1:0][31:0] read_crc_value, write_crc_value;
    logic [NUM_CHANNELS-1:0]       read_crc_valid, write_crc_valid;
    logic [31:0]                   read_beat_count, write_beat_count;
    logic [NUM_CHANNELS-1:0]       crc_match_per_ch, crc_valid_per_ch;
    logic                          crc_match, crc_both_valid;
    logic                          timer_done, timer_running, timer_pass;
    logic [63:0]                   timer_cycles, timer_r_first, timer_r_last;
    logic [63:0]                   timer_w_first, timer_w_last;

    harness_csr #(
        .AW(32), .DW(32), .NUM_CHANNELS(NUM_CHANNELS),
        .BUILD_ERROR_FLAVOR(0),
        .BUILD_MAIN_CONES  (0),
        .BUILD_CLK_HZ      (FPGA_CLK_HZ),
        .BUILD_NUM_CHANNELS(NUM_CHANNELS),
        .BUILD_DATA_WIDTH_B(DATA_WIDTH / 8),
        .BUILD_USE_MONITORS(0),
        .BUILD_GEN_MON     (0)
    ) u_csr (
        .aclk(aclk), .aresetn(aresetn),
        .s_awaddr(harness_csr_axi_awaddr), .s_awprot(harness_csr_axi_awprot),
        .s_awvalid(harness_csr_axi_awvalid), .s_awready(harness_csr_axi_awready),
        .s_wdata(harness_csr_axi_wdata), .s_wstrb(harness_csr_axi_wstrb),
        .s_wvalid(harness_csr_axi_wvalid), .s_wready(harness_csr_axi_wready),
        .s_bresp(harness_csr_axi_bresp), .s_bvalid(harness_csr_axi_bvalid),
        .s_bready(harness_csr_axi_bready),
        .s_araddr(harness_csr_axi_araddr), .s_arprot(harness_csr_axi_arprot),
        .s_arvalid(harness_csr_axi_arvalid), .s_arready(harness_csr_axi_arready),
        .s_rdata(harness_csr_axi_rdata), .s_rresp(harness_csr_axi_rresp),
        .s_rvalid(harness_csr_axi_rvalid), .s_rready(harness_csr_axi_rready),
        .o_start_pulse      (),
        .o_clear_stats_pulse(csr_clear_pulse),
        .o_freeze_trace     (),
        .o_soft_reset_pulse (csr_soft_reset),
        .o_cam_clear_pulse  (csr_cam_clear),
        .i_stream_irq       (stream_irq),
        .i_any_error        (1'b0),
        .i_dbg_wr_ptr       (32'd0),
        .i_dbg_overflow     (1'b0),
        .i_dbg_clear_busy   (1'b0),
        .i_mon_comp_tier1_a (32'd0), .i_mon_comp_tier1_b (32'd0),
        .i_mon_comp_tier1_c (32'd0), .i_mon_comp_tier0   (32'd0),
        .i_mon_comp_cam_miss(32'd0), .i_mon_comp_delta_ts_ovf(32'd0),
        .i_mon_comp_event_data_ovf(32'd0), .i_mon_comp_ed_delta_ovf(32'd0),
        .i_crc_rd_expected  (read_crc_value[0]),
        .i_crc_wr_expected  (read_crc_value[0]),
        .i_crc_wr_computed  (write_crc_value[0]),
        .i_crc_valid        (crc_both_valid),
        .i_crc_match        (crc_match),
        .i_crc_rd_per_ch    (read_crc_value),
        .i_crc_wr_per_ch    (write_crc_value),
        .i_crc_valid_mask   (crc_valid_per_ch),
        .i_crc_match_mask   (crc_match_per_ch),
        .o_timer_clear_pulse   (csr_timer_clear_pulse),
        .o_timer_expected_beats(csr_timer_expected_beats),
        .i_timer_done          (timer_done),
        .i_timer_running       (timer_running),
        .i_timer_pass          (timer_pass),
        .i_timer_cycles        (timer_cycles),
        .i_timer_r_first       (timer_r_first),
        .i_timer_r_last        (timer_r_last),
        .i_timer_w_first       (timer_w_first),
        .i_timer_w_last        (timer_w_last),
        .o_rd_resp_delay_cyc   (),
        .o_wr_resp_delay_cyc   (),
        .i_desc_sram_ar_hs (32'd0), .i_desc_sram_r_hs (32'd0),
        .i_desc_ar_hs      (32'd0), .i_desc_ar_stall  (32'd0),
        .i_desc_r_hs       (32'd0), .i_desc_r_stall   (32'd0),
        .i_desc_aw_hs      (32'd0), .i_desc_w_hs      (32'd0),
        .i_desc_b_hs       (32'd0), .i_desc_vr_live   (16'd0)
    );

    // =========================================================================
    // STREAM: the Genesys 2 geometry from stream_char_cfg_pkg (channels,
    // outstanding, SRAM depth), in-core monitors compiled out -- the
    // master-side observer below is what the host reads utilization and
    // latency from, as in the STREAM perf build. Identical in every leg.
    // =========================================================================
    // Descriptor master, 256-bit
    logic [AXI_ID_WIDTH-1:0]   sd_arid, sd_rid;
    logic [ADDR_WIDTH-1:0]     sd_araddr;
    logic [7:0]                sd_arlen;
    logic [2:0]                sd_arsize, sd_arprot;
    logic [1:0]                sd_arburst, sd_rresp;
    logic                      sd_arlock, sd_arvalid, sd_arready, sd_rlast, sd_rvalid, sd_rready;
    logic [3:0]                sd_arcache, sd_arqos, sd_arregion;
    logic [AXI_USER_WIDTH-1:0] sd_aruser, sd_ruser;
    logic [DESC_WIDTH-1:0]     sd_rdata;
    // Data read / write masters: unused USER and REGION outputs
    logic [3:0]                sr_arregion, sw_awregion;
    logic [AXI_USER_WIDTH-1:0] sr_aruser, sw_awuser, sw_wuser;

    logic        mon_awvalid, mon_awready, mon_wvalid, mon_wready, mon_bvalid, mon_bready;
    logic [31:0] mon_awaddr;
    logic [2:0]  mon_awprot;
    logic [63:0] mon_wdata;
    logic [7:0]  mon_wstrb;
    logic [1:0]  mon_bresp;

    stream_top_ch8 #(
        .NUM_CHANNELS       (NUM_CHANNELS),
        .DATA_WIDTH         (DATA_WIDTH),
        .ADDR_WIDTH         (ADDR_WIDTH),
        .USE_ROW_COL_MAJOR_ADDRESSING (USE_ROW_COL_MAJOR_ADDRESSING),
        .SRAM_DEPTH         (SRAM_DEPTH),
        .APB_ADDR_WIDTH     (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH     (32),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .AXI_USER_WIDTH     (AXI_USER_WIDTH),
        .USE_AXI_MONITORS   (0),
        .MON_N_ADDR_RANGES  (0),
        .USE_MON_COMPRESSION(0),
        .USE_MON_HALFBEAT   (0),
        .CDC_ENABLE         (0),
        .AR_MAX_OUTSTANDING (AR_MAX_OUTSTANDING),
        .AW_MAX_OUTSTANDING (AW_MAX_OUTSTANDING),
        .GEN_MON            (1'b0),
        .DESC_MON_ENABLE_ERROR_LOGIC     (1'b0),
        .DESC_MON_ENABLE_TIMEOUT_LOGIC   (1'b0),
        .DESC_MON_ENABLE_COMPL_LOGIC     (1'b0),
        .DESC_MON_ENABLE_THRESHOLD_LOGIC (1'b0),
        .DESC_MON_ENABLE_PERF_LOGIC      (1'b1),
        .DESC_MON_ENABLE_DEBUG_LOGIC     (1'b0),
        .DATA_MON_ENABLE_ERROR_LOGIC     (1'b0),
        .DATA_MON_ENABLE_TIMEOUT_LOGIC   (1'b0),
        .DATA_MON_ENABLE_COMPL_LOGIC     (1'b0),
        .DATA_MON_ENABLE_THRESHOLD_LOGIC (1'b0),
        .DATA_MON_ENABLE_PERF_LOGIC      (1'b1),
        .DATA_MON_ENABLE_DEBUG_LOGIC     (1'b0)
    ) u_stream (
        .aclk(aclk), .aresetn(unit_aresetn),
        .pclk(aclk), .presetn(aresetn),
        .cam_clear(csr_cam_clear),
        .s_apb_paddr  (stream_apb_PADDR[APB_ADDR_WIDTH-1:0]),
        .s_apb_psel   (stream_apb_PSEL),
        .s_apb_penable(stream_apb_PENABLE),
        .s_apb_pwrite (stream_apb_PWRITE),
        .s_apb_pwdata (stream_apb_PWDATA),
        .s_apb_pstrb  (stream_apb_PSTRB),
        .s_apb_prdata (stream_apb_PRDATA),
        .s_apb_pready (stream_apb_PREADY),
        .s_apb_pslverr(stream_apb_PSLVERR),
        .m_axi_desc_arid(sd_arid), .m_axi_desc_araddr(sd_araddr),
        .m_axi_desc_arlen(sd_arlen), .m_axi_desc_arsize(sd_arsize),
        .m_axi_desc_arburst(sd_arburst), .m_axi_desc_arlock(sd_arlock),
        .m_axi_desc_arcache(sd_arcache), .m_axi_desc_arprot(sd_arprot),
        .m_axi_desc_arqos(sd_arqos), .m_axi_desc_arregion(sd_arregion),
        .m_axi_desc_aruser(sd_aruser), .m_axi_desc_arvalid(sd_arvalid),
        .m_axi_desc_arready(sd_arready),
        .m_axi_desc_rid(sd_rid), .m_axi_desc_rdata(sd_rdata),
        .m_axi_desc_rresp(sd_rresp), .m_axi_desc_rlast(sd_rlast),
        .m_axi_desc_ruser(sd_ruser), .m_axi_desc_rvalid(sd_rvalid),
        .m_axi_desc_rready(sd_rready),
        .m_axi_rd_arid(stream_rd_arid), .m_axi_rd_araddr(stream_rd_araddr),
        .m_axi_rd_arlen(stream_rd_arlen), .m_axi_rd_arsize(stream_rd_arsize),
        .m_axi_rd_arburst(stream_rd_arburst), .m_axi_rd_arlock(stream_rd_arlock),
        .m_axi_rd_arcache(stream_rd_arcache), .m_axi_rd_arprot(stream_rd_arprot),
        .m_axi_rd_arqos(stream_rd_arqos), .m_axi_rd_arregion(sr_arregion),
        .m_axi_rd_aruser(sr_aruser), .m_axi_rd_arvalid(stream_rd_arvalid),
        .m_axi_rd_arready(stream_rd_arready),
        .m_axi_rd_rid(stream_rd_rid), .m_axi_rd_rdata(stream_rd_rdata),
        .m_axi_rd_rresp(stream_rd_rresp), .m_axi_rd_rlast(stream_rd_rlast),
        .m_axi_rd_ruser('0), .m_axi_rd_rvalid(stream_rd_rvalid),
        .m_axi_rd_rready(stream_rd_rready),
        .m_axi_wr_awid(stream_wr_awid), .m_axi_wr_awaddr(stream_wr_awaddr),
        .m_axi_wr_awlen(stream_wr_awlen), .m_axi_wr_awsize(stream_wr_awsize),
        .m_axi_wr_awburst(stream_wr_awburst), .m_axi_wr_awlock(stream_wr_awlock),
        .m_axi_wr_awcache(stream_wr_awcache), .m_axi_wr_awprot(stream_wr_awprot),
        .m_axi_wr_awqos(stream_wr_awqos), .m_axi_wr_awregion(sw_awregion),
        .m_axi_wr_awuser(sw_awuser), .m_axi_wr_awvalid(stream_wr_awvalid),
        .m_axi_wr_awready(stream_wr_awready),
        .m_axi_wr_wdata(stream_wr_wdata), .m_axi_wr_wstrb(stream_wr_wstrb),
        .m_axi_wr_wlast(stream_wr_wlast), .m_axi_wr_wuser(sw_wuser),
        .m_axi_wr_wvalid(stream_wr_wvalid), .m_axi_wr_wready(stream_wr_wready),
        .m_axi_wr_bid(stream_wr_bid), .m_axi_wr_bresp(stream_wr_bresp),
        .m_axi_wr_buser('0), .m_axi_wr_bvalid(stream_wr_bvalid),
        .m_axi_wr_bready(stream_wr_bready),
        .s_axil_err_arvalid(stream_err_axi_arvalid), .s_axil_err_arready(stream_err_axi_arready),
        .s_axil_err_araddr (stream_err_axi_araddr),  .s_axil_err_arprot (stream_err_axi_arprot),
        .s_axil_err_rvalid (stream_err_axi_rvalid),  .s_axil_err_rready (stream_err_axi_rready),
        .s_axil_err_rdata  (stream_err_axi_rdata),   .s_axil_err_rresp  (stream_err_axi_rresp),
        .m_axil_mon_awvalid(mon_awvalid), .m_axil_mon_awready(mon_awready),
        .m_axil_mon_awaddr (mon_awaddr),  .m_axil_mon_awprot (mon_awprot),
        .m_axil_mon_wvalid (mon_wvalid),  .m_axil_mon_wready (mon_wready),
        .m_axil_mon_wdata  (mon_wdata),   .m_axil_mon_wstrb  (mon_wstrb),
        .m_axil_mon_bvalid (mon_bvalid),  .m_axil_mon_bready (mon_bready),
        .m_axil_mon_bresp  (mon_bresp),
        .stream_irq        (stream_irq),
        .mon_compressor_stat_tier1_a(), .mon_compressor_stat_tier1_b(),
        .mon_compressor_stat_tier1_c(), .mon_compressor_stat_tier0(),
        .mon_compressor_stat_cam_miss(), .mon_compressor_stat_delta_ts_ovf(),
        .mon_compressor_stat_event_data_ovf(), .mon_compressor_stat_ed_delta_ovf(),
        .debug_hwif_scheduler_idle(), .debug_hwif_desc_engine_idle(),
        .debug_hwif_channel_idle(), .debug_regblk_req(), .debug_regblk_req_is_wr(),
        .debug_regblk_addr(), .debug_regblk_rd_data(), .debug_regblk_rd_ack(),
        .debug_peakrdl_cmd_valid(), .debug_peakrdl_cmd_paddr(),
        .debug_peakrdl_rsp_valid(), .debug_peakrdl_rsp_prdata(),
        .debug_last_cpuif_addr(), .debug_last_cpuif_rd_data(), .debug_last_cpuif_rd_ack(),
        .debug_apb_cmd_valid(), .debug_apb_cmd_ready(), .debug_apb_cmd_pwrite(),
        .debug_apb_cmd_paddr(), .debug_apb_rsp_valid(), .debug_apb_rsp_ready(),
        .debug_apb_rsp_prdata(), .debug_apb_rd_cmd_seen(), .debug_apb_rd_cmd_addr(),
        .debug_apb_rsp_prdata_captured(), .debug_apb_rd_count(),
        .debug_peakrdl_rd_count(), .debug_regblk_rd_count()
    );

    // MonBus egress (monitors compiled out) and writes to the error-FIFO
    // window: accepted and dropped, so neither can stall.
    fb_axil_wr_sink #(.AW(32), .DW(64)) u_mon_sink (
        .aclk(aclk), .aresetn(unit_aresetn),
        .s_awaddr(mon_awaddr), .s_awprot(mon_awprot), .s_awvalid(mon_awvalid),
        .s_awready(mon_awready), .s_wdata(mon_wdata), .s_wstrb(mon_wstrb),
        .s_wvalid(mon_wvalid), .s_wready(mon_wready), .s_bresp(mon_bresp),
        .s_bvalid(mon_bvalid), .s_bready(mon_bready));
    fb_axil_wr_sink #(.AW(32), .DW(32)) u_err_wr_sink (
        .aclk(aclk), .aresetn(aresetn),
        .s_awaddr(stream_err_axi_awaddr), .s_awprot(stream_err_axi_awprot),
        .s_awvalid(stream_err_axi_awvalid), .s_awready(stream_err_axi_awready),
        .s_wdata(stream_err_axi_wdata), .s_wstrb(stream_err_axi_wstrb),
        .s_wvalid(stream_err_axi_wvalid), .s_wready(stream_err_axi_wready),
        .s_bresp(stream_err_axi_bresp), .s_bvalid(stream_err_axi_bvalid),
        .s_bready(stream_err_axi_bready));


    // =========================================================================
    // Master-side observer on STREAM's own rd/wr port (before the fabric):
    // the STREAM perf build's instrument, configured the same way -- bus
    // meters and latency histograms on, monitor taps OFF so it can never gate
    // the DMA. A pure snoop: every AXI port is an input.
    // =========================================================================
    localparam int OBS_NUM_CHANNELS    = 8;     // fixed: one register layout for every build
    localparam int OBS_CW              = $clog2(OBS_NUM_CHANNELS);
    localparam int OBS_MAX_OUTSTANDING = (AR_MAX_OUTSTANDING > AW_MAX_OUTSTANDING)
                                         ? AR_MAX_OUTSTANDING : AW_MAX_OUTSTANDING;
    localparam int OBS_ACLK_MHZ        = FPGA_CLK_HZ / 1_000_000;

    // Measurement window: opens on the first STREAM rd/wr activity after a
    // soft reset, closes 16 idle cycles after the last (the STREAM harness's
    // controller, unchanged).
    logic       obs_busy, obs_win_active, obs_started, obs_meter_clear, obs_meter_freeze;
    logic [4:0] obs_settle;
    assign obs_busy = stream_rd_arvalid | stream_rd_rvalid | stream_wr_awvalid |
                      stream_wr_wvalid | stream_wr_bvalid;
    `ALWAYS_FF_RST(aclk, unit_aresetn,
        if (`RST_ASSERTED(unit_aresetn)) begin
            obs_win_active <= 1'b0; obs_started <= 1'b0; obs_settle <= 5'd0;
        end else if (obs_busy && !obs_win_active && !obs_started) begin
            obs_win_active <= 1'b1; obs_started <= 1'b1; obs_settle <= 5'd0;
        end else if (obs_win_active) begin
            if (obs_busy)                    obs_settle     <= 5'd0;
            else if (obs_settle != 5'd16)    obs_settle     <= obs_settle + 5'd1;
            else                             obs_win_active <= 1'b0;
        end
    )
    assign obs_meter_clear  = obs_busy && !obs_win_active && !obs_started;
    assign obs_meter_freeze = ~obs_win_active;

    // STREAM drives arid/awid = channel
    logic [AXI_ID_WIDTH-1:0] obs_cfg_rd_rid       [1][OBS_NUM_CHANNELS];
    logic                    obs_cfg_rd_rid_valid [1][OBS_NUM_CHANNELS];
    always_comb begin
        for (int c = 0; c < OBS_NUM_CHANNELS; c++) begin
            obs_cfg_rd_rid[0][c]       = AXI_ID_WIDTH'(c);
            obs_cfg_rd_rid_valid[0][c] = (c < NUM_CHANNELS);
        end
    end
    logic [OBS_CW-1:0] obs_wr_active_ch_id    [1];
    logic              obs_wr_active_ch_valid [1];
    assign obs_wr_active_ch_id[0]    = '0;
    assign obs_wr_active_ch_valid[0] = 1'b0;

    logic        dmamon_awvalid, dmamon_awready, dmamon_wvalid, dmamon_wready;
    logic        dmamon_bvalid, dmamon_bready;
    logic [31:0] dmamon_awaddr;
    logic [2:0]  dmamon_awprot;
    logic [63:0] dmamon_wdata;
    logic [7:0]  dmamon_wstrb;
    logic [1:0]  dmamon_bresp;

    axi4_intf_master_observer #(
        .NUM_RD_PORTS        (1),
        .NUM_WR_PORTS        (1),
        .ADDR_WIDTH          (ADDR_WIDTH),
        .DATA_WIDTH          (DATA_WIDTH),
        .AXI_ID_WIDTH        (AXI_ID_WIDTH),
        .AXI_USER_WIDTH      (AXI_USER_WIDTH),
        .OBS_AXI_ID_WIDTH    (4),
        .MAX_BURST_BEATS     (64),
        .USE_COMPRESSION     (0),
        .EGRESS_AXIL         (1'b1),
        .ENABLE_MON_TAPS     (1'b0),
        .TAP_ENABLE_ERROR_LOGIC     (1'b0),
        .TAP_ENABLE_TIMEOUT_LOGIC   (1'b0),
        .TAP_ENABLE_COMPL_LOGIC     (1'b0),
        .TAP_ENABLE_THRESHOLD_LOGIC (1'b0),
        .TAP_ENABLE_DEBUG_LOGIC     (1'b0),
        .MAX_TRANSACTIONS    (stream_char_cfg_pkg::CFG_OBS_MAX_TRANSACTIONS),
        .NUM_BANKS           (stream_char_cfg_pkg::CFG_OBS_NUM_BANKS),
        .USE_WDATA_ORDER_Q   (stream_char_cfg_pkg::CFG_OBS_USE_WDATA_ORDER_Q),
        .ACLK_MHZ            (OBS_ACLK_MHZ),
        .ENABLE_BUS_METER    (1),
        .WR_CH_FROM_AWID     (1),
        .NUM_CHANNELS        (OBS_NUM_CHANNELS),
        .ENABLE_LATENCY_HIST (1),
        .HIST_NUM_BINS       (16),
        .HIST_MAX_OUTSTANDING(OBS_MAX_OUTSTANDING),
        .N_ADDR_RANGES       (0)
    ) u_dma_observer (
        .aclk(aclk), .aresetn(unit_aresetn), .cam_clear(1'b0),
        .obs_rd_arid(stream_rd_arid), .obs_rd_araddr(stream_rd_araddr),
        .obs_rd_arlen(stream_rd_arlen), .obs_rd_arsize(stream_rd_arsize),
        .obs_rd_arburst(stream_rd_arburst), .obs_rd_arlock(stream_rd_arlock),
        .obs_rd_arcache(stream_rd_arcache), .obs_rd_arprot(stream_rd_arprot),
        .obs_rd_arqos(stream_rd_arqos), .obs_rd_arregion(sr_arregion),
        .obs_rd_aruser(sr_aruser), .obs_rd_arvalid(stream_rd_arvalid),
        .obs_rd_arready(stream_rd_arready),
        .obs_rd_rid(stream_rd_rid), .obs_rd_rdata(stream_rd_rdata),
        .obs_rd_rresp(stream_rd_rresp), .obs_rd_rlast(stream_rd_rlast),
        .obs_rd_ruser('0), .obs_rd_rvalid(stream_rd_rvalid),
        .obs_rd_rready(stream_rd_rready),
        .obs_wr_awid(stream_wr_awid), .obs_wr_awaddr(stream_wr_awaddr),
        .obs_wr_awlen(stream_wr_awlen), .obs_wr_awsize(stream_wr_awsize),
        .obs_wr_awburst(stream_wr_awburst), .obs_wr_awlock(stream_wr_awlock),
        .obs_wr_awcache(stream_wr_awcache), .obs_wr_awprot(stream_wr_awprot),
        .obs_wr_awqos(stream_wr_awqos), .obs_wr_awregion(sw_awregion),
        .obs_wr_awuser(sw_awuser), .obs_wr_awvalid(stream_wr_awvalid),
        .obs_wr_wdata(stream_wr_wdata), .obs_wr_wstrb(stream_wr_wstrb),
        .obs_wr_wlast(stream_wr_wlast), .obs_wr_wuser(sw_wuser),
        .obs_wr_wvalid(stream_wr_wvalid),
        .obs_wr_awready(stream_wr_awready), .obs_wr_wready(stream_wr_wready),
        .obs_wr_bid(stream_wr_bid), .obs_wr_bresp(stream_wr_bresp),
        .obs_wr_buser('0), .obs_wr_bvalid(stream_wr_bvalid),
        .obs_wr_bready(stream_wr_bready),
        .obs_wr_active_ch_id(obs_wr_active_ch_id),
        .obs_wr_active_ch_valid(obs_wr_active_ch_valid),
        .s_axil_arvalid(1'b0), .s_axil_arready(), .s_axil_araddr('0), .s_axil_arprot('0),
        .s_axil_rvalid(), .s_axil_rready(1'b0), .s_axil_rdata(), .s_axil_rresp(),
        .m_axi_awid(), .m_axi_awaddr(), .m_axi_awlen(), .m_axi_awsize(), .m_axi_awburst(),
        .m_axi_awlock(), .m_axi_awcache(), .m_axi_awprot(), .m_axi_awqos(),
        .m_axi_awregion(), .m_axi_awuser(), .m_axi_awvalid(), .m_axi_awready(1'b0),
        .m_axi_wdata(), .m_axi_wstrb(), .m_axi_wlast(), .m_axi_wuser(), .m_axi_wvalid(),
        .m_axi_wready(1'b0), .m_axi_bid('0), .m_axi_bresp('0), .m_axi_buser(1'b0),
        .m_axi_bvalid(1'b0), .m_axi_bready(),
        .irq_out(),
        .s_apb_psel(obs_apb_PSEL), .s_apb_penable(obs_apb_PENABLE),
        .s_apb_pready(obs_apb_PREADY), .s_apb_paddr(obs_apb_PADDR[11:0]),
        .s_apb_pwrite(obs_apb_PWRITE), .s_apb_pwdata(obs_apb_PWDATA),
        .s_apb_pstrb(obs_apb_PSTRB), .s_apb_prdata(obs_apb_PRDATA),
        .s_apb_pslverr(obs_apb_PSLVERR),
        .i_meter_clear(obs_meter_clear), .i_meter_freeze(obs_meter_freeze),
        .cfg_rd_rid_per_channel(obs_cfg_rd_rid),
        .cfg_rd_rid_per_channel_valid(obs_cfg_rd_rid_valid),
        .m_axil_awaddr(dmamon_awaddr), .m_axil_awprot(dmamon_awprot),
        .m_axil_awready(dmamon_awready), .m_axil_awvalid(dmamon_awvalid),
        .m_axil_bready(dmamon_bready), .m_axil_bresp(dmamon_bresp),
        .m_axil_bvalid(dmamon_bvalid), .m_axil_wdata(dmamon_wdata),
        .m_axil_wready(dmamon_wready), .m_axil_wstrb(dmamon_wstrb),
        .m_axil_wvalid(dmamon_wvalid)
    );
    // Its MonBus egress (taps off: nothing is ever sent) still needs an answer.
    fb_axil_wr_sink #(.AW(32), .DW(64)) u_dmamon_sink (
        .aclk(aclk), .aresetn(unit_aresetn),
        .s_awaddr(dmamon_awaddr), .s_awprot(dmamon_awprot), .s_awvalid(dmamon_awvalid),
        .s_awready(dmamon_awready), .s_wdata(dmamon_wdata), .s_wstrb(dmamon_wstrb),
        .s_wvalid(dmamon_wvalid), .s_wready(dmamon_wready), .s_bresp(dmamon_bresp),
        .s_bvalid(dmamon_bvalid), .s_bready(dmamon_bready));

    // =========================================================================
    // M0: STREAM's 256-bit descriptor fetch, narrowed to the fabric's 128 bits
    // OUTSIDE the fabric (the same converter in every leg). USER (STREAM's
    // channel) is not on the fabric port set.
    // =========================================================================
    logic [AXI_USER_WIDTH-1:0] m0_aruser_unused;
    axi4_dwidth_converter_rd #(
        .S_AXI_DATA_WIDTH     (DESC_WIDTH),
        .M_AXI_DATA_WIDTH     (DATA_WIDTH),
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH       (ADDR_WIDTH),
        .AXI_USER_WIDTH       (AXI_USER_WIDTH),
        // The converter's contract: RASM_DEPTH covers a 256-beat burst (its
        // default). STREAM fetches one descriptor per AR -- 2 beats at 128 --
        // so few bursts are ever in reassembly; 4 bounds the pool.
        .RASM_DEPTH           (272),
        .RASM_MAX_OUTSTANDING (4)
    ) u_desc_narrow (
        .aclk(aclk), .aresetn(unit_aresetn),
        .s_axi_arid(sd_arid), .s_axi_araddr(sd_araddr), .s_axi_arlen(sd_arlen),
        .s_axi_arsize(sd_arsize), .s_axi_arburst(sd_arburst), .s_axi_arlock(sd_arlock),
        .s_axi_arcache(sd_arcache), .s_axi_arprot(sd_arprot), .s_axi_arqos(sd_arqos),
        .s_axi_arregion(sd_arregion), .s_axi_aruser(sd_aruser),
        .s_axi_arvalid(sd_arvalid), .s_axi_arready(sd_arready),
        .s_axi_rid(sd_rid), .s_axi_rdata(sd_rdata), .s_axi_rresp(sd_rresp),
        .s_axi_rlast(sd_rlast), .s_axi_ruser(sd_ruser),
        .s_axi_rvalid(sd_rvalid), .s_axi_rready(sd_rready),
        .m_axi_arid(stream_desc_arid), .m_axi_araddr(stream_desc_araddr),
        .m_axi_arlen(stream_desc_arlen), .m_axi_arsize(stream_desc_arsize),
        .m_axi_arburst(stream_desc_arburst), .m_axi_arlock(stream_desc_arlock),
        .m_axi_arcache(stream_desc_arcache), .m_axi_arprot(stream_desc_arprot),
        .m_axi_arqos(stream_desc_arqos), .m_axi_arregion(),
        .m_axi_aruser(m0_aruser_unused),
        .m_axi_arvalid(stream_desc_arvalid), .m_axi_arready(stream_desc_arready),
        .m_axi_rid(stream_desc_rid), .m_axi_rdata(stream_desc_rdata),
        .m_axi_rresp(stream_desc_rresp), .m_axi_rlast(stream_desc_rlast),
        .m_axi_ruser('0), .m_axi_rvalid(stream_desc_rvalid),
        .m_axi_rready(stream_desc_rready)
    );

    // M3: the W3 injector is K3 work; in fabric-only mode the port is idle.
    assign inj_wr_awid    = '0;
    assign inj_wr_awaddr  = '0;
    assign inj_wr_awlen   = '0;
    assign inj_wr_awsize  = 3'd4;
    assign inj_wr_awburst = 2'b01;
    assign inj_wr_awlock  = 1'b0;
    assign inj_wr_awcache = '0;
    assign inj_wr_awprot  = '0;
    assign inj_wr_awqos   = '0;
    assign inj_wr_awvalid = 1'b0;
    assign inj_wr_wdata   = '0;
    assign inj_wr_wstrb   = '0;
    assign inj_wr_wlast   = 1'b0;
    assign inj_wr_wvalid  = 1'b0;
    assign inj_wr_bready  = 1'b1;

    // =========================================================================
    // The data fabric under test
    // =========================================================================
    fb_data_fabric u_fabric (
        .aclk(aclk), .aresetn(unit_aresetn),
        .*
    );

    // =========================================================================
    // S1: descriptor RAM. Write port: the host, through the configuration
    // bridge (0x2_0000). Read port: STREAM, through the fabric (0x8000_0000).
    // =========================================================================
    logic [SID-1:0] w_desc_bid;
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH (SID),
        .ADDR_WIDTH   (32),
        .DATA_WIDTH   (DATA_WIDTH),
        .USER_WIDTH   (1),
        .MEM_DEPTH    (DESC_RAM_DEPTH)
    ) u_desc_ram (
        .aclk(aclk), .aresetn(unit_aresetn),
        .s_axi_awid(SID'(cfg_desc_awid)), .s_axi_awaddr(cfg_desc_awaddr),
        .s_axi_awlen(cfg_desc_awlen), .s_axi_awsize(cfg_desc_awsize),
        .s_axi_awburst(cfg_desc_awburst), .s_axi_awlock(cfg_desc_awlock),
        .s_axi_awcache(cfg_desc_awcache), .s_axi_awprot(cfg_desc_awprot),
        .s_axi_awqos(cfg_desc_awqos), .s_axi_awregion(cfg_desc_awregion),
        .s_axi_awuser(cfg_desc_awuser),
        .s_axi_awvalid(cfg_desc_awvalid), .s_axi_awready(cfg_desc_awready),
        .s_axi_wdata(cfg_desc_wdata), .s_axi_wstrb(cfg_desc_wstrb),
        .s_axi_wlast(cfg_desc_wlast), .s_axi_wuser(cfg_desc_wuser),
        .s_axi_wvalid(cfg_desc_wvalid), .s_axi_wready(cfg_desc_wready),
        .s_axi_bid(w_desc_bid), .s_axi_bresp(cfg_desc_bresp),
        .s_axi_buser(cfg_desc_buser),
        .s_axi_bvalid(cfg_desc_bvalid), .s_axi_bready(cfg_desc_bready),
        .s_axi_arid(desc_ram_arid), .s_axi_araddr(desc_ram_araddr),
        .s_axi_arlen(desc_ram_arlen), .s_axi_arsize(desc_ram_arsize),
        .s_axi_arburst(desc_ram_arburst), .s_axi_arlock(desc_ram_arlock),
        .s_axi_arcache(desc_ram_arcache), .s_axi_arprot(desc_ram_arprot),
        .s_axi_arqos(desc_ram_arqos), .s_axi_arregion(4'd0),
        .s_axi_aruser(1'b0),
        .s_axi_arvalid(desc_ram_arvalid), .s_axi_arready(desc_ram_arready),
        .s_axi_rid(desc_ram_rid), .s_axi_rdata(desc_ram_rdata),
        .s_axi_rresp(desc_ram_rresp), .s_axi_rlast(desc_ram_rlast),
        .s_axi_ruser(),
        .s_axi_rvalid(desc_ram_rvalid), .s_axi_rready(desc_ram_rready),
        .i_cfg_start_clear(1'b0), .o_cfg_done_clear(),
        .o_dbg_vr(), .o_dbg_fub_vr(), .o_dbg_bram_wr(), .o_dbg_bram_rd(),
        .o_dbg_busy_wr(), .o_dbg_busy_rd()
    );
    assign cfg_desc_bid = w_desc_bid[0];

    // A host READ of the descriptor window has no RAM port to reach: answer it.
    fb_axi4_rd_stub #(.IW(1), .AW(32), .DW(128)) u_desc_rd_stub (
        .aclk(aclk), .aresetn(aresetn),
        .s_arid(cfg_desc_arid), .s_araddr(cfg_desc_araddr), .s_arlen(cfg_desc_arlen),
        .s_arvalid(cfg_desc_arvalid), .s_arready(cfg_desc_arready),
        .s_rid(cfg_desc_rid), .s_rdata(cfg_desc_rdata), .s_rresp(cfg_desc_rresp),
        .s_rlast(cfg_desc_rlast), .s_rvalid(cfg_desc_rvalid), .s_rready(cfg_desc_rready));
    assign cfg_desc_ruser = 1'b0;

    // =========================================================================
    // S2 / S3: LFSR source and CRC sink on their own clock (fb_endpoints)
    // =========================================================================
    fb_endpoints #(
        .NUM_CHANNELS  (NUM_CHANNELS),
        .AXI_ID_WIDTH  (SID),
        .AXI_ADDR_WIDTH(ADDR_WIDTH),
        .AXI_DATA_WIDTH(DATA_WIDTH),
        .CH_SEL_ADDR   (1'b1),
        .CH_ADDR_LSB   (CH_ADDR_LSB)
    ) u_endpoints (
        // HARDWARE reset, not the unit soft reset: fb_endpoints spans two
        // clocks through async FIFOs, and the soft reset reaches only the
        // aclk side -- resetting one side of a CDC FIFO leaves its pointers
        // disagreeing, and the next run's first burst never crosses (found
        // as a hang on every run after the first). Its only per-run state,
        // the CRC/LFSR, is cleared by i_clear below.
        .aclk(aclk), .aresetn(aresetn),
        .ep_clk(ep_clk), .ep_aresetn(ep_aresetn),
        .i_clear(csr_clear_pulse | csr_soft_reset),
        .s_rd_arid(lfsr_src_arid), .s_rd_araddr(lfsr_src_araddr), .s_rd_arlen(lfsr_src_arlen),
        .s_rd_arsize(lfsr_src_arsize), .s_rd_arburst(lfsr_src_arburst),
        .s_rd_arlock(lfsr_src_arlock), .s_rd_arcache(lfsr_src_arcache),
        .s_rd_arprot(lfsr_src_arprot), .s_rd_arqos(lfsr_src_arqos),
        .s_rd_arvalid(lfsr_src_arvalid), .s_rd_arready(lfsr_src_arready),
        .s_rd_rid(lfsr_src_rid), .s_rd_rdata(lfsr_src_rdata), .s_rd_rresp(lfsr_src_rresp),
        .s_rd_rlast(lfsr_src_rlast), .s_rd_rvalid(lfsr_src_rvalid), .s_rd_rready(lfsr_src_rready),
        .s_wr_awid(crc_snk_awid), .s_wr_awaddr(crc_snk_awaddr), .s_wr_awlen(crc_snk_awlen),
        .s_wr_awsize(crc_snk_awsize), .s_wr_awburst(crc_snk_awburst),
        .s_wr_awlock(crc_snk_awlock), .s_wr_awcache(crc_snk_awcache),
        .s_wr_awprot(crc_snk_awprot), .s_wr_awqos(crc_snk_awqos),
        .s_wr_awvalid(crc_snk_awvalid), .s_wr_awready(crc_snk_awready),
        .s_wr_wdata(crc_snk_wdata), .s_wr_wstrb(crc_snk_wstrb), .s_wr_wlast(crc_snk_wlast),
        .s_wr_wvalid(crc_snk_wvalid), .s_wr_wready(crc_snk_wready),
        .s_wr_bid(crc_snk_bid), .s_wr_bresp(crc_snk_bresp),
        .s_wr_bvalid(crc_snk_bvalid), .s_wr_bready(crc_snk_bready),
        .o_read_crc_value(read_crc_value), .o_read_crc_valid(read_crc_valid),
        .o_read_beat_count(read_beat_count),
        .o_write_crc_value(write_crc_value), .o_write_crc_valid(write_crc_valid),
        .o_write_beat_count(write_beat_count)
    );

    // =========================================================================
    // Run timer + per-channel CRC verdict (utility-ip/misc char_run_timer)
    // =========================================================================
    char_run_timer #(
        .NUM_CHANNELS  (NUM_CHANNELS),
        .CRC_WIDTH     (32),
        .COUNT_WIDTH   (32),
        .SETTLE_CYCLES (32)
    ) u_char_run_timer (
        .aclk             (aclk),
        .aresetn          (aresetn),
        .i_clear          (csr_timer_clear_pulse),
        .i_start          (sd_arvalid & sd_arready),
        .i_expected_beats (csr_timer_expected_beats),
        .i_rd_beat_count  (read_beat_count),
        .i_wr_beat_count  (write_beat_count),
        .i_rd_crc_value   (read_crc_value),
        .i_rd_crc_valid   (read_crc_valid),
        .i_wr_crc_value   (write_crc_value),
        .i_wr_crc_valid   (write_crc_valid),
        .o_crc_valid_mask (crc_valid_per_ch),
        .o_crc_match_mask (crc_match_per_ch),
        .o_crc_any_valid  (crc_both_valid),
        .o_crc_match      (crc_match),
        .o_running        (timer_running),
        .o_done           (timer_done),
        .o_pass           (timer_pass),
        .o_cycles         (timer_cycles),
        .o_r_first        (timer_r_first),
        .o_r_last         (timer_r_last),
        .o_w_first        (timer_w_first),
        .o_w_last         (timer_w_last)
    );

    assign o_timer_done = timer_done;
    assign o_timer_pass = timer_pass;
    assign o_stream_irq = stream_irq;

    // Outputs nothing here reads
    wire unused_ok = ^{sr_arregion, sw_awregion, sr_aruser, sw_awuser, sw_wuser,
                       m0_aruser_unused, w_desc_bid};

endmodule : fb_harness
