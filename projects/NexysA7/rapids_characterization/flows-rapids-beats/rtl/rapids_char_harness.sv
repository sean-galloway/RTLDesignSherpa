// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: rapids_char_harness
// Purpose: Synthesizable characterization harness that wraps the split
//          rapids_beats_top DUT with on-chip pattern generators/checkers and
//          memories, mirroring the STREAM characterization harness structure.
//
// Instantiates:
//   - rapids_beats_top          (DUT: split SOURCE + SINK beats DMA)
//   - axis4_master_pattern_gen  (drives DUT s_axis_* : sink-ingress stimulus)
//   - axis4_slave_pattern_check (consumes DUT m_axis_*: source-egress check)
//   - axi4_slave_rd_pattern_gen (backs DUT m_axi_rd_*  : 512b source data source)
//   - axi4_slave_wr_crc_check   (backs DUT m_axi_wr_*  : 512b sink data verify)
//   - sdpram_slave_axi4_axi4 x2 (descriptor RAM per half; DUT reads port A via
//                                {src,snk}_m_axi_desc_*, host writes descriptors
//                                via the exposed write/port-B boundary)
//   - sdpram_slave_axi4_axi4 x2 (control semaphore RAM per half; the ctrlwr
//                                master WRITES and the ctrlrd master READS the
//                                same backing store, so a doorbell write is
//                                observable by a gate read)
//   - always-accept AXIL write responder for m_axil_mon_* (monitor egress never
//                                stalls); s_axil_err_* quiesced.
//
// The cocotb TB drives s_apb_* + the control ports directly. A UART/AXIL bridge
// + CSR + trace observer are intentionally NOT part of this stage; the harness
// is structured so they can be layered on later (a board top would wrap this).
//
// Author: sean galloway
// Created: 2026-07-03

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rapids_char_harness #(
    // ---- DUT geometry (NUM_CHANNELS / DATA_WIDTH overridable) ----
    parameter int NUM_CHANNELS    = 8,
    parameter int DATA_WIDTH      = 512,
    parameter int ADDR_WIDTH      = 64,
    parameter int AXI_ID_WIDTH    = 8,
    parameter int SRAM_DEPTH      = 4096,
    parameter int APB_ADDR_WIDTH  = 13,
    parameter int APB_DATA_WIDTH  = 32,
    // AXIS network-interface parameters (tid carries the channel id)
    parameter int AXIS_ID_WIDTH   = 8,
    parameter int AXIS_DEST_WIDTH = 4,
    parameter int AXIS_USER_WIDTH = 1,
    // ---- Harness memory sizing ----
    parameter int DESC_RAM_ENTRIES = 2048,  // 2048 x 256b descriptors per half
    parameter int CTRL_RAM_DEPTH   = 256,   // control semaphore words per half
    // RD/WR data "memory" depth. The pattern gen / CRC check are stateless LFSR
    // engines (no backing array), so these are advisory sizing knobs only.
    parameter int RD_MEM_DEPTH     = 4096,
    parameter int WR_MEM_DEPTH     = 4096,
    // ---- Derived ----
    parameter int SW  = DATA_WIDTH / 8,
    parameter int CIW = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1,
    // Descriptor fetch is fixed 256-bit end-to-end (DUT src/snk desc rdata).
    parameter int DESC_DATA_WIDTH = 256
) (
    //-------------------------------------------------------------------------
    // Clock / Reset / CAM clear
    //-------------------------------------------------------------------------
    input  logic                                    aclk,
    input  logic                                    aresetn,
    input  logic                                    cam_clear,

    //-------------------------------------------------------------------------
    // APB4 config (straight through to the DUT; host config/kick)
    //-------------------------------------------------------------------------
    input  logic [APB_ADDR_WIDTH-1:0]               s_apb_paddr,
    input  logic                                    s_apb_psel,
    input  logic                                    s_apb_penable,
    input  logic                                    s_apb_pwrite,
    input  logic [APB_DATA_WIDTH-1:0]               s_apb_pwdata,
    input  logic [(APB_DATA_WIDTH/8)-1:0]           s_apb_pstrb,
    output logic [APB_DATA_WIDTH-1:0]               s_apb_prdata,
    output logic                                    s_apb_pready,
    output logic                                    s_apb_pslverr,

    //-------------------------------------------------------------------------
    // Monitor egress window config (pass-through to DUT cfg_mon_*)
    //-------------------------------------------------------------------------
    input  logic [31:0]                             cfg_mon_base_addr,
    input  logic [31:0]                             cfg_mon_limit_addr,
    input  logic [15:0]                             cfg_mon_flush_watermark,

    //-------------------------------------------------------------------------
    // AXIS pattern generator control/status (sink-ingress stimulus -> s_axis)
    //-------------------------------------------------------------------------
    input  logic                                    cfg_gen_start,
    input  logic [31:0]                             cfg_gen_lfsr_seed,
    input  logic [31:0]                             cfg_gen_num_beats,      // beats PER CHANNEL
    input  logic [31:0]                             cfg_gen_beats_per_pkt,
    input  logic [NUM_CHANNELS-1:0]                 cfg_gen_channel_mask,   // 0 => all channels
    input  logic [AXIS_DEST_WIDTH-1:0]              cfg_gen_tdest,
    output logic                                    gen_busy,
    output logic                                    gen_done,
    output logic [NUM_CHANNELS-1:0][31:0]           o_gen_expected_crc,
    output logic [NUM_CHANNELS-1:0]                 o_gen_expected_crc_valid,
    output logic [31:0]                             o_gen_beat_count_total,

    //-------------------------------------------------------------------------
    // AXIS pattern checker control/status (source-egress check <- m_axis)
    //-------------------------------------------------------------------------
    input  logic                                    chk_cfg_start,
    input  logic [31:0]                             chk_cfg_lfsr_seed,
    input  logic                                    chk_ready_en,
    output logic [NUM_CHANNELS-1:0][31:0]           o_chk_actual_crc,
    output logic [NUM_CHANNELS-1:0]                 o_chk_actual_crc_valid,
    output logic                                    o_data_error,
    output logic [31:0]                             o_chk_beat_count_total,
    output logic [31:0]                             o_pkt_count,

    //-------------------------------------------------------------------------
    // Source-data memory (LFSR pattern gen backing DUT m_axi_rd_*)
    //-------------------------------------------------------------------------
    input  logic                                    rd_crc_lfsr_reset,
    output logic [NUM_CHANNELS-1:0][31:0]           rd_crc_value,
    output logic [NUM_CHANNELS-1:0]                 rd_crc_valid,
    output logic [31:0]                             rd_beat_count_total,
    output logic                                    rd_mem_busy,

    //-------------------------------------------------------------------------
    // Sink-data memory (CRC check backing DUT m_axi_wr_*)
    //-------------------------------------------------------------------------
    input  logic                                    wr_crc_reset,
    output logic [NUM_CHANNELS-1:0][31:0]           wr_crc_value,
    output logic [NUM_CHANNELS-1:0]                 wr_crc_valid,
    output logic [31:0]                             wr_beat_count_total,
    output logic                                    wr_mem_busy,

    //-------------------------------------------------------------------------
    // Per-direction AXI bus-meter buckets (axi_bus_meter, aggregate-only).
    // Auto-windowed in hardware: opened+cleared on first DMA activity, frozen
    // 16 idle cycles after the last beat, so the frozen buckets bracket exactly
    // one workload. PROD/BP/STARV/IDLE sum to the window length; utilization =
    // prod / (prod+bp+starv+idle). Read back by read_bus_meters.py.
    //-------------------------------------------------------------------------
    output logic [31:0]                             obs_rd_prod,   // source read R-channel
    output logic [31:0]                             obs_rd_bp,
    output logic [31:0]                             obs_rd_starv,
    output logic [31:0]                             obs_rd_idle,
    output logic [31:0]                             obs_wr_prod,   // sink write W-channel
    output logic [31:0]                             obs_wr_bp,
    output logic [31:0]                             obs_wr_starv,
    output logic [31:0]                             obs_wr_idle,

    //-------------------------------------------------------------------------
    // SOURCE descriptor-RAM host write port (port B: descriptor loading)
    //-------------------------------------------------------------------------
    input  logic [AXI_ID_WIDTH-1:0]                 desc_src_awid,
    input  logic [ADDR_WIDTH-1:0]                   desc_src_awaddr,
    input  logic [7:0]                              desc_src_awlen,
    input  logic [2:0]                              desc_src_awsize,
    input  logic [1:0]                              desc_src_awburst,
    input  logic                                    desc_src_awvalid,
    output logic                                    desc_src_awready,
    input  logic [DESC_DATA_WIDTH-1:0]              desc_src_wdata,
    input  logic [(DESC_DATA_WIDTH/8)-1:0]          desc_src_wstrb,
    input  logic                                    desc_src_wlast,
    input  logic                                    desc_src_wvalid,
    output logic                                    desc_src_wready,
    output logic [AXI_ID_WIDTH-1:0]                 desc_src_bid,
    output logic [1:0]                              desc_src_bresp,
    output logic                                    desc_src_bvalid,
    input  logic                                    desc_src_bready,

    //-------------------------------------------------------------------------
    // SINK descriptor-RAM host write port (port B: descriptor loading)
    //-------------------------------------------------------------------------
    input  logic [AXI_ID_WIDTH-1:0]                 desc_snk_awid,
    input  logic [ADDR_WIDTH-1:0]                   desc_snk_awaddr,
    input  logic [7:0]                              desc_snk_awlen,
    input  logic [2:0]                              desc_snk_awsize,
    input  logic [1:0]                              desc_snk_awburst,
    input  logic                                    desc_snk_awvalid,
    output logic                                    desc_snk_awready,
    input  logic [DESC_DATA_WIDTH-1:0]              desc_snk_wdata,
    input  logic [(DESC_DATA_WIDTH/8)-1:0]          desc_snk_wstrb,
    input  logic                                    desc_snk_wlast,
    input  logic                                    desc_snk_wvalid,
    output logic                                    desc_snk_wready,
    output logic [AXI_ID_WIDTH-1:0]                 desc_snk_bid,
    output logic [1:0]                              desc_snk_bresp,
    output logic                                    desc_snk_bvalid,
    input  logic                                    desc_snk_bready,

    //-------------------------------------------------------------------------
    // Status rollups
    //-------------------------------------------------------------------------
    output logic                                    src_system_idle,
    output logic [NUM_CHANNELS-1:0]                 src_sched_error,
    output logic                                    snk_system_idle,
    output logic [NUM_CHANNELS-1:0]                 snk_sched_error,
    output logic                                    mon_irq
);

    //=========================================================================
    // Internal wires between the DUT masters and the harness slaves/memories
    //=========================================================================

    // ---- SOURCE descriptor fetch master (AR/R, 256-bit) ----
    logic [AXI_ID_WIDTH-1:0]   src_desc_arid;
    logic [ADDR_WIDTH-1:0]     src_desc_araddr;
    logic [7:0]                src_desc_arlen;
    logic [2:0]                src_desc_arsize;
    logic [1:0]                src_desc_arburst;
    logic                      src_desc_arlock;
    logic [3:0]                src_desc_arcache;
    logic [2:0]                src_desc_arprot;
    logic [3:0]                src_desc_arqos;
    logic [3:0]                src_desc_arregion;
    logic                      src_desc_arvalid, src_desc_arready;
    logic [AXI_ID_WIDTH-1:0]   src_desc_rid;
    logic [DESC_DATA_WIDTH-1:0] src_desc_rdata;
    logic [1:0]                src_desc_rresp;
    logic                      src_desc_rlast, src_desc_rvalid, src_desc_rready;

    // ---- SINK descriptor fetch master (AR/R, 256-bit) ----
    logic [AXI_ID_WIDTH-1:0]   snk_desc_arid;
    logic [ADDR_WIDTH-1:0]     snk_desc_araddr;
    logic [7:0]                snk_desc_arlen;
    logic [2:0]                snk_desc_arsize;
    logic [1:0]                snk_desc_arburst;
    logic                      snk_desc_arlock;
    logic [3:0]                snk_desc_arcache;
    logic [2:0]                snk_desc_arprot;
    logic [3:0]                snk_desc_arqos;
    logic [3:0]                snk_desc_arregion;
    logic                      snk_desc_arvalid, snk_desc_arready;
    logic [AXI_ID_WIDTH-1:0]   snk_desc_rid;
    logic [DESC_DATA_WIDTH-1:0] snk_desc_rdata;
    logic [1:0]                snk_desc_rresp;
    logic                      snk_desc_rlast, snk_desc_rvalid, snk_desc_rready;

    // ---- SOURCE control read master (AR/R, 32-bit) ----
    logic                      src_crd_arvalid, src_crd_arready;
    logic [ADDR_WIDTH-1:0]     src_crd_araddr;
    logic [7:0]                src_crd_arlen;
    logic [2:0]                src_crd_arsize;
    logic [1:0]                src_crd_arburst;
    logic [AXI_ID_WIDTH-1:0]   src_crd_arid;
    logic                      src_crd_arlock;
    logic [3:0]                src_crd_arcache;
    logic [2:0]                src_crd_arprot;
    logic [3:0]                src_crd_arqos;
    logic [3:0]                src_crd_arregion;
    logic                      src_crd_rvalid, src_crd_rready;
    logic [31:0]               src_crd_rdata;
    logic [1:0]                src_crd_rresp;
    logic                      src_crd_rlast;
    logic [AXI_ID_WIDTH-1:0]   src_crd_rid;

    // ---- SOURCE control write master (AW/W/B, 32-bit) ----
    logic                      src_cwr_awvalid, src_cwr_awready;
    logic [ADDR_WIDTH-1:0]     src_cwr_awaddr;
    logic [7:0]                src_cwr_awlen;
    logic [2:0]                src_cwr_awsize;
    logic [1:0]                src_cwr_awburst;
    logic [AXI_ID_WIDTH-1:0]   src_cwr_awid;
    logic                      src_cwr_awlock;
    logic [3:0]                src_cwr_awcache;
    logic [2:0]                src_cwr_awprot;
    logic [3:0]                src_cwr_awqos;
    logic [3:0]                src_cwr_awregion;
    logic                      src_cwr_wvalid, src_cwr_wready;
    logic [31:0]               src_cwr_wdata;
    logic [3:0]                src_cwr_wstrb;
    logic                      src_cwr_wlast;
    logic                      src_cwr_bvalid, src_cwr_bready;
    logic [AXI_ID_WIDTH-1:0]   src_cwr_bid;
    logic [1:0]                src_cwr_bresp;

    // ---- SINK control read master (AR/R, 32-bit) ----
    logic                      snk_crd_arvalid, snk_crd_arready;
    logic [ADDR_WIDTH-1:0]     snk_crd_araddr;
    logic [7:0]                snk_crd_arlen;
    logic [2:0]                snk_crd_arsize;
    logic [1:0]                snk_crd_arburst;
    logic [AXI_ID_WIDTH-1:0]   snk_crd_arid;
    logic                      snk_crd_arlock;
    logic [3:0]                snk_crd_arcache;
    logic [2:0]                snk_crd_arprot;
    logic [3:0]                snk_crd_arqos;
    logic [3:0]                snk_crd_arregion;
    logic                      snk_crd_rvalid, snk_crd_rready;
    logic [31:0]               snk_crd_rdata;
    logic [1:0]                snk_crd_rresp;
    logic                      snk_crd_rlast;
    logic [AXI_ID_WIDTH-1:0]   snk_crd_rid;

    // ---- SINK control write master (AW/W/B, 32-bit) ----
    logic                      snk_cwr_awvalid, snk_cwr_awready;
    logic [ADDR_WIDTH-1:0]     snk_cwr_awaddr;
    logic [7:0]                snk_cwr_awlen;
    logic [2:0]                snk_cwr_awsize;
    logic [1:0]                snk_cwr_awburst;
    logic [AXI_ID_WIDTH-1:0]   snk_cwr_awid;
    logic                      snk_cwr_awlock;
    logic [3:0]                snk_cwr_awcache;
    logic [2:0]                snk_cwr_awprot;
    logic [3:0]                snk_cwr_awqos;
    logic [3:0]                snk_cwr_awregion;
    logic                      snk_cwr_wvalid, snk_cwr_wready;
    logic [31:0]               snk_cwr_wdata;
    logic [3:0]                snk_cwr_wstrb;
    logic                      snk_cwr_wlast;
    logic                      snk_cwr_bvalid, snk_cwr_bready;
    logic [AXI_ID_WIDTH-1:0]   snk_cwr_bid;
    logic [1:0]                snk_cwr_bresp;

    // ---- SOURCE data read master (AR/R, 512-bit) ----
    logic [AXI_ID_WIDTH-1:0]   rd_arid;
    logic [ADDR_WIDTH-1:0]     rd_araddr;
    logic [7:0]                rd_arlen;
    logic [2:0]                rd_arsize;
    logic [1:0]                rd_arburst;
    logic                      rd_arvalid, rd_arready;
    logic [AXI_ID_WIDTH-1:0]   rd_rid;
    logic [DATA_WIDTH-1:0]     rd_rdata;
    logic [1:0]                rd_rresp;
    logic                      rd_rlast, rd_rvalid, rd_rready;

    // ---- SINK data write master (AW/W/B, 512-bit) ----
    logic [AXI_ID_WIDTH-1:0]   wr_awid;
    logic [ADDR_WIDTH-1:0]     wr_awaddr;
    logic [7:0]                wr_awlen;
    logic [2:0]                wr_awsize;
    logic [1:0]                wr_awburst;
    logic                      wr_awlock;
    logic [3:0]                wr_awcache;
    logic [2:0]                wr_awprot;
    logic [3:0]                wr_awqos;
    logic [3:0]                wr_awregion;
    logic                      wr_awvalid, wr_awready;
    logic [DATA_WIDTH-1:0]     wr_wdata;
    logic [SW-1:0]             wr_wstrb;
    logic                      wr_wlast, wr_wvalid, wr_wready;
    logic [AXI_ID_WIDTH-1:0]   wr_bid;
    logic [1:0]                wr_bresp;
    logic                      wr_bvalid, wr_bready;

    // ---- AXIS ingress (harness gen -> DUT s_axis) ----
    logic [DATA_WIDTH-1:0]     s_axis_tdata;
    logic [SW-1:0]             s_axis_tstrb;
    logic                      s_axis_tlast;
    logic [AXIS_ID_WIDTH-1:0]  s_axis_tid;
    logic [AXIS_DEST_WIDTH-1:0] s_axis_tdest;
    logic [AXIS_USER_WIDTH-1:0] s_axis_tuser;
    logic                      s_axis_tvalid, s_axis_tready;

    // ---- AXIS egress (DUT m_axis -> harness check) ----
    logic [DATA_WIDTH-1:0]     m_axis_tdata;
    logic [SW-1:0]             m_axis_tstrb;
    logic                      m_axis_tlast;
    logic [AXIS_ID_WIDTH-1:0]  m_axis_tid;
    logic [AXIS_DEST_WIDTH-1:0] m_axis_tdest;
    logic [AXIS_USER_WIDTH-1:0] m_axis_tuser;
    logic                      m_axis_tvalid, m_axis_tready;

    // ---- MonBus AXIL capture master (DUT -> always-accept responder) ----
    logic                      mon_awvalid, mon_awready;
    logic [31:0]               mon_awaddr;
    logic [2:0]                mon_awprot;
    logic                      mon_wvalid, mon_wready;
    logic [63:0]               mon_wdata;
    logic [7:0]                mon_wstrb;
    logic                      mon_bvalid, mon_bready;
    logic [1:0]                mon_bresp;

    //=========================================================================
    // DUT: rapids_beats_top
    //=========================================================================
    rapids_beats_top #(
        .NUM_CHANNELS   (NUM_CHANNELS),
        .DATA_WIDTH     (DATA_WIDTH),
        .ADDR_WIDTH     (ADDR_WIDTH),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .SRAM_DEPTH     (SRAM_DEPTH),
        .APB_ADDR_WIDTH (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH (APB_DATA_WIDTH),
        .AXIS_ID_WIDTH  (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH(AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH(AXIS_USER_WIDTH)
    ) u_dut (
        .aclk    (aclk),
        .aresetn (aresetn),
        .cam_clear(cam_clear),

        // APB
        .s_apb_paddr   (s_apb_paddr),
        .s_apb_psel    (s_apb_psel),
        .s_apb_penable (s_apb_penable),
        .s_apb_pwrite  (s_apb_pwrite),
        .s_apb_pwdata  (s_apb_pwdata),
        .s_apb_pstrb   (s_apb_pstrb),
        .s_apb_prdata  (s_apb_prdata),
        .s_apb_pready  (s_apb_pready),
        .s_apb_pslverr (s_apb_pslverr),

        // SOURCE descriptor master
        .src_m_axi_desc_arid    (src_desc_arid),
        .src_m_axi_desc_araddr  (src_desc_araddr),
        .src_m_axi_desc_arlen   (src_desc_arlen),
        .src_m_axi_desc_arsize  (src_desc_arsize),
        .src_m_axi_desc_arburst (src_desc_arburst),
        .src_m_axi_desc_arlock  (src_desc_arlock),
        .src_m_axi_desc_arcache (src_desc_arcache),
        .src_m_axi_desc_arprot  (src_desc_arprot),
        .src_m_axi_desc_arqos   (src_desc_arqos),
        .src_m_axi_desc_arregion(src_desc_arregion),
        .src_m_axi_desc_arvalid (src_desc_arvalid),
        .src_m_axi_desc_arready (src_desc_arready),
        .src_m_axi_desc_rid     (src_desc_rid),
        .src_m_axi_desc_rdata   (src_desc_rdata),
        .src_m_axi_desc_rresp   (src_desc_rresp),
        .src_m_axi_desc_rlast   (src_desc_rlast),
        .src_m_axi_desc_rvalid  (src_desc_rvalid),
        .src_m_axi_desc_rready  (src_desc_rready),

        // SINK descriptor master
        .snk_m_axi_desc_arid    (snk_desc_arid),
        .snk_m_axi_desc_araddr  (snk_desc_araddr),
        .snk_m_axi_desc_arlen   (snk_desc_arlen),
        .snk_m_axi_desc_arsize  (snk_desc_arsize),
        .snk_m_axi_desc_arburst (snk_desc_arburst),
        .snk_m_axi_desc_arlock  (snk_desc_arlock),
        .snk_m_axi_desc_arcache (snk_desc_arcache),
        .snk_m_axi_desc_arprot  (snk_desc_arprot),
        .snk_m_axi_desc_arqos   (snk_desc_arqos),
        .snk_m_axi_desc_arregion(snk_desc_arregion),
        .snk_m_axi_desc_arvalid (snk_desc_arvalid),
        .snk_m_axi_desc_arready (snk_desc_arready),
        .snk_m_axi_desc_rid     (snk_desc_rid),
        .snk_m_axi_desc_rdata   (snk_desc_rdata),
        .snk_m_axi_desc_rresp   (snk_desc_rresp),
        .snk_m_axi_desc_rlast   (snk_desc_rlast),
        .snk_m_axi_desc_rvalid  (snk_desc_rvalid),
        .snk_m_axi_desc_rready  (snk_desc_rready),

        // SOURCE control read master
        .src_m_axi_ctrlrd_arvalid (src_crd_arvalid),
        .src_m_axi_ctrlrd_arready (src_crd_arready),
        .src_m_axi_ctrlrd_araddr  (src_crd_araddr),
        .src_m_axi_ctrlrd_arlen   (src_crd_arlen),
        .src_m_axi_ctrlrd_arsize  (src_crd_arsize),
        .src_m_axi_ctrlrd_arburst (src_crd_arburst),
        .src_m_axi_ctrlrd_arid    (src_crd_arid),
        .src_m_axi_ctrlrd_arlock  (src_crd_arlock),
        .src_m_axi_ctrlrd_arcache (src_crd_arcache),
        .src_m_axi_ctrlrd_arprot  (src_crd_arprot),
        .src_m_axi_ctrlrd_arqos   (src_crd_arqos),
        .src_m_axi_ctrlrd_arregion(src_crd_arregion),
        .src_m_axi_ctrlrd_rvalid  (src_crd_rvalid),
        .src_m_axi_ctrlrd_rready  (src_crd_rready),
        .src_m_axi_ctrlrd_rdata   (src_crd_rdata),
        .src_m_axi_ctrlrd_rresp   (src_crd_rresp),
        .src_m_axi_ctrlrd_rlast   (src_crd_rlast),
        .src_m_axi_ctrlrd_rid     (src_crd_rid),

        // SOURCE control write master
        .src_m_axi_ctrlwr_awvalid (src_cwr_awvalid),
        .src_m_axi_ctrlwr_awready (src_cwr_awready),
        .src_m_axi_ctrlwr_awaddr  (src_cwr_awaddr),
        .src_m_axi_ctrlwr_awlen   (src_cwr_awlen),
        .src_m_axi_ctrlwr_awsize  (src_cwr_awsize),
        .src_m_axi_ctrlwr_awburst (src_cwr_awburst),
        .src_m_axi_ctrlwr_awid    (src_cwr_awid),
        .src_m_axi_ctrlwr_awlock  (src_cwr_awlock),
        .src_m_axi_ctrlwr_awcache (src_cwr_awcache),
        .src_m_axi_ctrlwr_awprot  (src_cwr_awprot),
        .src_m_axi_ctrlwr_awqos   (src_cwr_awqos),
        .src_m_axi_ctrlwr_awregion(src_cwr_awregion),
        .src_m_axi_ctrlwr_wvalid  (src_cwr_wvalid),
        .src_m_axi_ctrlwr_wready  (src_cwr_wready),
        .src_m_axi_ctrlwr_wdata   (src_cwr_wdata),
        .src_m_axi_ctrlwr_wstrb   (src_cwr_wstrb),
        .src_m_axi_ctrlwr_wlast   (src_cwr_wlast),
        .src_m_axi_ctrlwr_bvalid  (src_cwr_bvalid),
        .src_m_axi_ctrlwr_bready  (src_cwr_bready),
        .src_m_axi_ctrlwr_bid     (src_cwr_bid),
        .src_m_axi_ctrlwr_bresp   (src_cwr_bresp),

        // SINK control read master
        .snk_m_axi_ctrlrd_arvalid (snk_crd_arvalid),
        .snk_m_axi_ctrlrd_arready (snk_crd_arready),
        .snk_m_axi_ctrlrd_araddr  (snk_crd_araddr),
        .snk_m_axi_ctrlrd_arlen   (snk_crd_arlen),
        .snk_m_axi_ctrlrd_arsize  (snk_crd_arsize),
        .snk_m_axi_ctrlrd_arburst (snk_crd_arburst),
        .snk_m_axi_ctrlrd_arid    (snk_crd_arid),
        .snk_m_axi_ctrlrd_arlock  (snk_crd_arlock),
        .snk_m_axi_ctrlrd_arcache (snk_crd_arcache),
        .snk_m_axi_ctrlrd_arprot  (snk_crd_arprot),
        .snk_m_axi_ctrlrd_arqos   (snk_crd_arqos),
        .snk_m_axi_ctrlrd_arregion(snk_crd_arregion),
        .snk_m_axi_ctrlrd_rvalid  (snk_crd_rvalid),
        .snk_m_axi_ctrlrd_rready  (snk_crd_rready),
        .snk_m_axi_ctrlrd_rdata   (snk_crd_rdata),
        .snk_m_axi_ctrlrd_rresp   (snk_crd_rresp),
        .snk_m_axi_ctrlrd_rlast   (snk_crd_rlast),
        .snk_m_axi_ctrlrd_rid     (snk_crd_rid),

        // SINK control write master
        .snk_m_axi_ctrlwr_awvalid (snk_cwr_awvalid),
        .snk_m_axi_ctrlwr_awready (snk_cwr_awready),
        .snk_m_axi_ctrlwr_awaddr  (snk_cwr_awaddr),
        .snk_m_axi_ctrlwr_awlen   (snk_cwr_awlen),
        .snk_m_axi_ctrlwr_awsize  (snk_cwr_awsize),
        .snk_m_axi_ctrlwr_awburst (snk_cwr_awburst),
        .snk_m_axi_ctrlwr_awid    (snk_cwr_awid),
        .snk_m_axi_ctrlwr_awlock  (snk_cwr_awlock),
        .snk_m_axi_ctrlwr_awcache (snk_cwr_awcache),
        .snk_m_axi_ctrlwr_awprot  (snk_cwr_awprot),
        .snk_m_axi_ctrlwr_awqos   (snk_cwr_awqos),
        .snk_m_axi_ctrlwr_awregion(snk_cwr_awregion),
        .snk_m_axi_ctrlwr_wvalid  (snk_cwr_wvalid),
        .snk_m_axi_ctrlwr_wready  (snk_cwr_wready),
        .snk_m_axi_ctrlwr_wdata   (snk_cwr_wdata),
        .snk_m_axi_ctrlwr_wstrb   (snk_cwr_wstrb),
        .snk_m_axi_ctrlwr_wlast   (snk_cwr_wlast),
        .snk_m_axi_ctrlwr_bvalid  (snk_cwr_bvalid),
        .snk_m_axi_ctrlwr_bready  (snk_cwr_bready),
        .snk_m_axi_ctrlwr_bid     (snk_cwr_bid),
        .snk_m_axi_ctrlwr_bresp   (snk_cwr_bresp),

        // SOURCE data read master
        .m_axi_rd_arid   (rd_arid),
        .m_axi_rd_araddr (rd_araddr),
        .m_axi_rd_arlen  (rd_arlen),
        .m_axi_rd_arsize (rd_arsize),
        .m_axi_rd_arburst(rd_arburst),
        .m_axi_rd_arvalid(rd_arvalid),
        .m_axi_rd_arready(rd_arready),
        .m_axi_rd_rid    (rd_rid),
        .m_axi_rd_rdata  (rd_rdata),
        .m_axi_rd_rresp  (rd_rresp),
        .m_axi_rd_rlast  (rd_rlast),
        .m_axi_rd_rvalid (rd_rvalid),
        .m_axi_rd_rready (rd_rready),

        // SINK data write master
        .m_axi_wr_awid   (wr_awid),
        .m_axi_wr_awaddr (wr_awaddr),
        .m_axi_wr_awlen  (wr_awlen),
        .m_axi_wr_awsize (wr_awsize),
        .m_axi_wr_awburst(wr_awburst),
        .m_axi_wr_awlock (wr_awlock),
        .m_axi_wr_awcache(wr_awcache),
        .m_axi_wr_awprot (wr_awprot),
        .m_axi_wr_awqos  (wr_awqos),
        .m_axi_wr_awregion(wr_awregion),
        .m_axi_wr_awvalid(wr_awvalid),
        .m_axi_wr_awready(wr_awready),
        .m_axi_wr_wdata  (wr_wdata),
        .m_axi_wr_wstrb  (wr_wstrb),
        .m_axi_wr_wlast  (wr_wlast),
        .m_axi_wr_wvalid (wr_wvalid),
        .m_axi_wr_wready (wr_wready),
        .m_axi_wr_bid    (wr_bid),
        .m_axi_wr_bresp  (wr_bresp),
        .m_axi_wr_bvalid (wr_bvalid),
        .m_axi_wr_bready (wr_bready),

        // AXIS ingress (sink)
        .s_axis_tdata  (s_axis_tdata),
        .s_axis_tstrb  (s_axis_tstrb),
        .s_axis_tlast  (s_axis_tlast),
        .s_axis_tid    (s_axis_tid),
        .s_axis_tdest  (s_axis_tdest),
        .s_axis_tuser  (s_axis_tuser),
        .s_axis_tvalid (s_axis_tvalid),
        .s_axis_tready (s_axis_tready),

        // AXIS egress (source)
        .m_axis_tdata  (m_axis_tdata),
        .m_axis_tstrb  (m_axis_tstrb),
        .m_axis_tlast  (m_axis_tlast),
        .m_axis_tid    (m_axis_tid),
        .m_axis_tdest  (m_axis_tdest),
        .m_axis_tuser  (m_axis_tuser),
        .m_axis_tvalid (m_axis_tvalid),
        .m_axis_tready (m_axis_tready),

        // MonBus AXIL error-drain slave (quiesced: no external reader)
        .s_axil_err_arvalid (1'b0),
        .s_axil_err_arready (),
        .s_axil_err_araddr  (32'h0),
        .s_axil_err_arprot  (3'h0),
        .s_axil_err_rvalid  (),
        .s_axil_err_rready  (1'b1),
        .s_axil_err_rdata   (),
        .s_axil_err_rresp   (),

        // MonBus AXIL capture master (always-accept responder below)
        .m_axil_mon_awvalid (mon_awvalid),
        .m_axil_mon_awready (mon_awready),
        .m_axil_mon_awaddr  (mon_awaddr),
        .m_axil_mon_awprot  (mon_awprot),
        .m_axil_mon_wvalid  (mon_wvalid),
        .m_axil_mon_wready  (mon_wready),
        .m_axil_mon_wdata   (mon_wdata),
        .m_axil_mon_wstrb   (mon_wstrb),
        .m_axil_mon_bvalid  (mon_bvalid),
        .m_axil_mon_bready  (mon_bready),
        .m_axil_mon_bresp   (mon_bresp),

        .mon_irq (mon_irq),

        .cfg_mon_base_addr       (cfg_mon_base_addr),
        .cfg_mon_limit_addr      (cfg_mon_limit_addr),
        .cfg_mon_flush_watermark (cfg_mon_flush_watermark),

        // Status
        .src_system_idle (src_system_idle),
        .src_sched_error (src_sched_error),
        .snk_system_idle (snk_system_idle),
        .snk_sched_error (snk_sched_error)
    );

    //=========================================================================
    // AXIS pattern generator -> DUT s_axis (sink-ingress stimulus)
    //=========================================================================
    // NOTE: LFSR/CRC params left at defaults, which are IDENTICAL across
    // axis4_master_pattern_gen, axis4_slave_pattern_check,
    // axi4_slave_rd_pattern_gen and axi4_slave_wr_crc_check (LFSR_SEED=DEADBEEF,
    // LFSR_TAPS={32,22,2,1}, CRC-32 Ethernet 0x04C11DB7). This keeps the on-chip
    // self-check (per-channel CRC) bit-consistent across all four blocks.
    axis4_master_pattern_gen #(
        .NUM_CHANNELS    (NUM_CHANNELS),
        .AXIS_DATA_WIDTH (DATA_WIDTH),
        .AXIS_ID_WIDTH   (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH (AXIS_USER_WIDTH)
    ) u_axis_gen (
        .clk   (aclk),
        .rst_n (aresetn),
        .cfg_start            (cfg_gen_start),
        .cfg_lfsr_seed        (cfg_gen_lfsr_seed),
        .cfg_channel_mask     (cfg_gen_channel_mask),
        .cfg_num_beats        (cfg_gen_num_beats),
        .cfg_beats_per_pkt    (cfg_gen_beats_per_pkt),
        .cfg_tdest            (cfg_gen_tdest),
        .cfg_busy             (gen_busy),
        .cfg_done             (gen_done),
        .o_expected_crc       (o_gen_expected_crc),
        .o_expected_crc_valid (o_gen_expected_crc_valid),
        .o_beat_count         (),
        .o_beat_count_total   (o_gen_beat_count_total),
        .m_axis_tvalid (s_axis_tvalid),
        .m_axis_tready (s_axis_tready),
        .m_axis_tdata  (s_axis_tdata),
        .m_axis_tstrb  (s_axis_tstrb),
        .m_axis_tlast  (s_axis_tlast),
        .m_axis_tid    (s_axis_tid),
        .m_axis_tdest  (s_axis_tdest),
        .m_axis_tuser  (s_axis_tuser)
    );

    //=========================================================================
    // AXIS pattern checker <- DUT m_axis (source-egress check)
    //=========================================================================
    axis4_slave_pattern_check #(
        .NUM_CHANNELS    (NUM_CHANNELS),
        .AXIS_DATA_WIDTH (DATA_WIDTH),
        .AXIS_ID_WIDTH   (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH (AXIS_USER_WIDTH)
    ) u_axis_chk (
        .clk   (aclk),
        .rst_n (aresetn),
        .cfg_start          (chk_cfg_start),
        .cfg_lfsr_seed      (chk_cfg_lfsr_seed),
        .ready_en           (chk_ready_en),
        .o_actual_crc       (o_chk_actual_crc),
        .o_actual_crc_valid (o_chk_actual_crc_valid),
        .o_data_error       (o_data_error),
        .o_beat_count       (),
        .o_beat_count_total (o_chk_beat_count_total),
        .o_pkt_count        (o_pkt_count),
        .s_axis_tvalid (m_axis_tvalid),
        .s_axis_tready (m_axis_tready),
        .s_axis_tdata  (m_axis_tdata),
        .s_axis_tstrb  (m_axis_tstrb),
        .s_axis_tlast  (m_axis_tlast),
        .s_axis_tid    (m_axis_tid),
        .s_axis_tdest  (m_axis_tdest),
        .s_axis_tuser  (m_axis_tuser)
    );

    //=========================================================================
    // Source-data memory: LFSR pattern generator backing DUT m_axi_rd_*
    //=========================================================================
    axi4_slave_rd_pattern_gen #(
        .NUM_CHANNELS   (NUM_CHANNELS),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (ADDR_WIDTH),
        .AXI_DATA_WIDTH (DATA_WIDTH)
    ) u_rd_mem (
        .aclk   (aclk),
        .aresetn(aresetn),
        .crc_lfsr_reset (rd_crc_lfsr_reset),
        .read_crc_value (rd_crc_value),
        .read_crc_valid (rd_crc_valid),
        .read_beat_count (),
        .read_beat_count_total (rd_beat_count_total),
        // AR (DUT m_axi_rd master -> slave); DUT drives no lock/cache/prot/
        // qos/region/user on this port, so tie the slave inputs quiescent.
        .s_axi_arid    (rd_arid),
        .s_axi_araddr  (rd_araddr),
        .s_axi_arlen   (rd_arlen),
        .s_axi_arsize  (rd_arsize),
        .s_axi_arburst (rd_arburst),
        .s_axi_arlock  (1'b0),
        .s_axi_arcache (4'h0),
        .s_axi_arprot  (3'h0),
        .s_axi_arqos   (4'h0),
        .s_axi_arregion(4'h0),
        .s_axi_aruser  (1'b0),
        .s_axi_arvalid (rd_arvalid),
        .s_axi_arready (rd_arready),
        // R
        .s_axi_rid     (rd_rid),
        .s_axi_rdata   (rd_rdata),
        .s_axi_rresp   (rd_rresp),
        .s_axi_rlast   (rd_rlast),
        .s_axi_ruser   (),
        .s_axi_rvalid  (rd_rvalid),
        .s_axi_rready  (rd_rready),
        .busy          (rd_mem_busy)
    );

    //=========================================================================
    // Sink-data memory: CRC checker backing DUT m_axi_wr_*
    //=========================================================================
    axi4_slave_wr_crc_check #(
        .NUM_CHANNELS   (NUM_CHANNELS),
        .AXI_ID_WIDTH   (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH (ADDR_WIDTH),
        .AXI_DATA_WIDTH (DATA_WIDTH)
    ) u_wr_mem (
        .aclk   (aclk),
        .aresetn(aresetn),
        .crc_reset (wr_crc_reset),
        .write_crc_value (wr_crc_value),
        .write_crc_valid (wr_crc_valid),
        .write_beat_count (),
        .write_beat_count_total (wr_beat_count_total),
        // AW (DUT m_axi_wr master -> slave); DUT drives no user on this port.
        .s_axi_awid    (wr_awid),
        .s_axi_awaddr  (wr_awaddr),
        .s_axi_awlen   (wr_awlen),
        .s_axi_awsize  (wr_awsize),
        .s_axi_awburst (wr_awburst),
        .s_axi_awlock  (wr_awlock),
        .s_axi_awcache (wr_awcache),
        .s_axi_awprot  (wr_awprot),
        .s_axi_awqos   (wr_awqos),
        .s_axi_awregion(wr_awregion),
        .s_axi_awuser  (1'b0),
        .s_axi_awvalid (wr_awvalid),
        .s_axi_awready (wr_awready),
        // W
        .s_axi_wdata   (wr_wdata),
        .s_axi_wstrb   (wr_wstrb),
        .s_axi_wlast   (wr_wlast),
        .s_axi_wuser   (1'b0),
        .s_axi_wvalid  (wr_wvalid),
        .s_axi_wready  (wr_wready),
        // B
        .s_axi_bid     (wr_bid),
        .s_axi_bresp   (wr_bresp),
        .s_axi_buser   (),
        .s_axi_bvalid  (wr_bvalid),
        .s_axi_bready  (wr_bready),
        .busy          (wr_mem_busy)
    );

    //=========================================================================
    // SOURCE descriptor RAM (256-bit): DUT reads (port A) / host writes (port B)
    //=========================================================================
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH (AXI_ID_WIDTH),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .DATA_WIDTH   (DESC_DATA_WIDTH),
        .USER_WIDTH   (1),
        .MEM_DEPTH    (DESC_RAM_ENTRIES)
    ) u_desc_ram_src (
        .aclk   (aclk),
        .aresetn(aresetn),
        // Port B: host descriptor write (exposed at harness boundary)
        .s_axi_awid    (desc_src_awid),
        .s_axi_awaddr  (desc_src_awaddr),
        .s_axi_awlen   (desc_src_awlen),
        .s_axi_awsize  (desc_src_awsize),
        .s_axi_awburst (desc_src_awburst),
        .s_axi_awlock  (1'b0),
        .s_axi_awcache (4'h0),
        .s_axi_awprot  (3'h0),
        .s_axi_awqos   (4'h0),
        .s_axi_awregion(4'h0),
        .s_axi_awuser  (1'b0),
        .s_axi_awvalid (desc_src_awvalid),
        .s_axi_awready (desc_src_awready),
        .s_axi_wdata   (desc_src_wdata),
        .s_axi_wstrb   (desc_src_wstrb),
        .s_axi_wlast   (desc_src_wlast),
        .s_axi_wuser   (1'b0),
        .s_axi_wvalid  (desc_src_wvalid),
        .s_axi_wready  (desc_src_wready),
        .s_axi_bid     (desc_src_bid),
        .s_axi_bresp   (desc_src_bresp),
        .s_axi_buser   (),
        .s_axi_bvalid  (desc_src_bvalid),
        .s_axi_bready  (desc_src_bready),
        // Port A: DUT source descriptor fetch (read-only)
        .s_axi_arid    (src_desc_arid),
        .s_axi_araddr  (src_desc_araddr),
        .s_axi_arlen   (src_desc_arlen),
        .s_axi_arsize  (src_desc_arsize),
        .s_axi_arburst (src_desc_arburst),
        .s_axi_arlock  (src_desc_arlock),
        .s_axi_arcache (src_desc_arcache),
        .s_axi_arprot  (src_desc_arprot),
        .s_axi_arqos   (src_desc_arqos),
        .s_axi_arregion(src_desc_arregion),
        .s_axi_aruser  (1'b0),
        .s_axi_arvalid (src_desc_arvalid),
        .s_axi_arready (src_desc_arready),
        .s_axi_rid     (src_desc_rid),
        .s_axi_rdata   (src_desc_rdata),
        .s_axi_rresp   (src_desc_rresp),
        .s_axi_rlast   (src_desc_rlast),
        .s_axi_ruser   (),
        .s_axi_rvalid  (src_desc_rvalid),
        .s_axi_rready  (src_desc_rready),
        .i_cfg_start_clear (1'b0),
        .o_cfg_done_clear  (),
        .o_dbg_vr      (),
        .o_dbg_fub_vr  (),
        .o_dbg_bram_wr (),
        .o_dbg_bram_rd (),
        .o_dbg_busy_wr (),
        .o_dbg_busy_rd ()
    );

    //=========================================================================
    // SINK descriptor RAM (256-bit): DUT reads (port A) / host writes (port B)
    //=========================================================================
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH (AXI_ID_WIDTH),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .DATA_WIDTH   (DESC_DATA_WIDTH),
        .USER_WIDTH   (1),
        .MEM_DEPTH    (DESC_RAM_ENTRIES)
    ) u_desc_ram_snk (
        .aclk   (aclk),
        .aresetn(aresetn),
        // Port B: host descriptor write (exposed at harness boundary)
        .s_axi_awid    (desc_snk_awid),
        .s_axi_awaddr  (desc_snk_awaddr),
        .s_axi_awlen   (desc_snk_awlen),
        .s_axi_awsize  (desc_snk_awsize),
        .s_axi_awburst (desc_snk_awburst),
        .s_axi_awlock  (1'b0),
        .s_axi_awcache (4'h0),
        .s_axi_awprot  (3'h0),
        .s_axi_awqos   (4'h0),
        .s_axi_awregion(4'h0),
        .s_axi_awuser  (1'b0),
        .s_axi_awvalid (desc_snk_awvalid),
        .s_axi_awready (desc_snk_awready),
        .s_axi_wdata   (desc_snk_wdata),
        .s_axi_wstrb   (desc_snk_wstrb),
        .s_axi_wlast   (desc_snk_wlast),
        .s_axi_wuser   (1'b0),
        .s_axi_wvalid  (desc_snk_wvalid),
        .s_axi_wready  (desc_snk_wready),
        .s_axi_bid     (desc_snk_bid),
        .s_axi_bresp   (desc_snk_bresp),
        .s_axi_buser   (),
        .s_axi_bvalid  (desc_snk_bvalid),
        .s_axi_bready  (desc_snk_bready),
        // Port A: DUT sink descriptor fetch (read-only)
        .s_axi_arid    (snk_desc_arid),
        .s_axi_araddr  (snk_desc_araddr),
        .s_axi_arlen   (snk_desc_arlen),
        .s_axi_arsize  (snk_desc_arsize),
        .s_axi_arburst (snk_desc_arburst),
        .s_axi_arlock  (snk_desc_arlock),
        .s_axi_arcache (snk_desc_arcache),
        .s_axi_arprot  (snk_desc_arprot),
        .s_axi_arqos   (snk_desc_arqos),
        .s_axi_arregion(snk_desc_arregion),
        .s_axi_aruser  (1'b0),
        .s_axi_arvalid (snk_desc_arvalid),
        .s_axi_arready (snk_desc_arready),
        .s_axi_rid     (snk_desc_rid),
        .s_axi_rdata   (snk_desc_rdata),
        .s_axi_rresp   (snk_desc_rresp),
        .s_axi_rlast   (snk_desc_rlast),
        .s_axi_ruser   (),
        .s_axi_rvalid  (snk_desc_rvalid),
        .s_axi_rready  (snk_desc_rready),
        .i_cfg_start_clear (1'b0),
        .o_cfg_done_clear  (),
        .o_dbg_vr      (),
        .o_dbg_fub_vr  (),
        .o_dbg_bram_wr (),
        .o_dbg_bram_rd (),
        .o_dbg_busy_wr (),
        .o_dbg_busy_rd ()
    );

    //=========================================================================
    // SOURCE control semaphore RAM (32-bit): shared backing store so a ctrlwr
    // doorbell write is observable by a ctrlrd gate read.
    //   write port <- src_m_axi_ctrlwr ; read port <- src_m_axi_ctrlrd
    //=========================================================================
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH (AXI_ID_WIDTH),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .DATA_WIDTH   (32),
        .USER_WIDTH   (1),
        .MEM_DEPTH    (CTRL_RAM_DEPTH)
    ) u_ctrl_ram_src (
        .aclk   (aclk),
        .aresetn(aresetn),
        // Write port <- SOURCE ctrlwr master
        .s_axi_awid    (src_cwr_awid),
        .s_axi_awaddr  (src_cwr_awaddr),
        .s_axi_awlen   (src_cwr_awlen),
        .s_axi_awsize  (src_cwr_awsize),
        .s_axi_awburst (src_cwr_awburst),
        .s_axi_awlock  (src_cwr_awlock),
        .s_axi_awcache (src_cwr_awcache),
        .s_axi_awprot  (src_cwr_awprot),
        .s_axi_awqos   (src_cwr_awqos),
        .s_axi_awregion(src_cwr_awregion),
        .s_axi_awuser  (1'b0),
        .s_axi_awvalid (src_cwr_awvalid),
        .s_axi_awready (src_cwr_awready),
        .s_axi_wdata   (src_cwr_wdata),
        .s_axi_wstrb   (src_cwr_wstrb),
        .s_axi_wlast   (src_cwr_wlast),
        .s_axi_wuser   (1'b0),
        .s_axi_wvalid  (src_cwr_wvalid),
        .s_axi_wready  (src_cwr_wready),
        .s_axi_bid     (src_cwr_bid),
        .s_axi_bresp   (src_cwr_bresp),
        .s_axi_buser   (),
        .s_axi_bvalid  (src_cwr_bvalid),
        .s_axi_bready  (src_cwr_bready),
        // Read port <- SOURCE ctrlrd master
        .s_axi_arid    (src_crd_arid),
        .s_axi_araddr  (src_crd_araddr),
        .s_axi_arlen   (src_crd_arlen),
        .s_axi_arsize  (src_crd_arsize),
        .s_axi_arburst (src_crd_arburst),
        .s_axi_arlock  (src_crd_arlock),
        .s_axi_arcache (src_crd_arcache),
        .s_axi_arprot  (src_crd_arprot),
        .s_axi_arqos   (src_crd_arqos),
        .s_axi_arregion(src_crd_arregion),
        .s_axi_aruser  (1'b0),
        .s_axi_arvalid (src_crd_arvalid),
        .s_axi_arready (src_crd_arready),
        .s_axi_rid     (src_crd_rid),
        .s_axi_rdata   (src_crd_rdata),
        .s_axi_rresp   (src_crd_rresp),
        .s_axi_rlast   (src_crd_rlast),
        .s_axi_ruser   (),
        .s_axi_rvalid  (src_crd_rvalid),
        .s_axi_rready  (src_crd_rready),
        .i_cfg_start_clear (1'b0),
        .o_cfg_done_clear  (),
        .o_dbg_vr      (),
        .o_dbg_fub_vr  (),
        .o_dbg_bram_wr (),
        .o_dbg_bram_rd (),
        .o_dbg_busy_wr (),
        .o_dbg_busy_rd ()
    );

    //=========================================================================
    // SINK control semaphore RAM (32-bit): shared backing store.
    //   write port <- snk_m_axi_ctrlwr ; read port <- snk_m_axi_ctrlrd
    //=========================================================================
    sdpram_slave_axi4_axi4 #(
        .AXI_ID_WIDTH (AXI_ID_WIDTH),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .DATA_WIDTH   (32),
        .USER_WIDTH   (1),
        .MEM_DEPTH    (CTRL_RAM_DEPTH)
    ) u_ctrl_ram_snk (
        .aclk   (aclk),
        .aresetn(aresetn),
        // Write port <- SINK ctrlwr master
        .s_axi_awid    (snk_cwr_awid),
        .s_axi_awaddr  (snk_cwr_awaddr),
        .s_axi_awlen   (snk_cwr_awlen),
        .s_axi_awsize  (snk_cwr_awsize),
        .s_axi_awburst (snk_cwr_awburst),
        .s_axi_awlock  (snk_cwr_awlock),
        .s_axi_awcache (snk_cwr_awcache),
        .s_axi_awprot  (snk_cwr_awprot),
        .s_axi_awqos   (snk_cwr_awqos),
        .s_axi_awregion(snk_cwr_awregion),
        .s_axi_awuser  (1'b0),
        .s_axi_awvalid (snk_cwr_awvalid),
        .s_axi_awready (snk_cwr_awready),
        .s_axi_wdata   (snk_cwr_wdata),
        .s_axi_wstrb   (snk_cwr_wstrb),
        .s_axi_wlast   (snk_cwr_wlast),
        .s_axi_wuser   (1'b0),
        .s_axi_wvalid  (snk_cwr_wvalid),
        .s_axi_wready  (snk_cwr_wready),
        .s_axi_bid     (snk_cwr_bid),
        .s_axi_bresp   (snk_cwr_bresp),
        .s_axi_buser   (),
        .s_axi_bvalid  (snk_cwr_bvalid),
        .s_axi_bready  (snk_cwr_bready),
        // Read port <- SINK ctrlrd master
        .s_axi_arid    (snk_crd_arid),
        .s_axi_araddr  (snk_crd_araddr),
        .s_axi_arlen   (snk_crd_arlen),
        .s_axi_arsize  (snk_crd_arsize),
        .s_axi_arburst (snk_crd_arburst),
        .s_axi_arlock  (snk_crd_arlock),
        .s_axi_arcache (snk_crd_arcache),
        .s_axi_arprot  (snk_crd_arprot),
        .s_axi_arqos   (snk_crd_arqos),
        .s_axi_arregion(snk_crd_arregion),
        .s_axi_aruser  (1'b0),
        .s_axi_arvalid (snk_crd_arvalid),
        .s_axi_arready (snk_crd_arready),
        .s_axi_rid     (snk_crd_rid),
        .s_axi_rdata   (snk_crd_rdata),
        .s_axi_rresp   (snk_crd_rresp),
        .s_axi_rlast   (snk_crd_rlast),
        .s_axi_ruser   (),
        .s_axi_rvalid  (snk_crd_rvalid),
        .s_axi_rready  (snk_crd_rready),
        .i_cfg_start_clear (1'b0),
        .o_cfg_done_clear  (),
        .o_dbg_vr      (),
        .o_dbg_fub_vr  (),
        .o_dbg_bram_wr (),
        .o_dbg_bram_rd (),
        .o_dbg_busy_wr (),
        .o_dbg_busy_rd ()
    );

    //=========================================================================
    // MonBus AXIL capture master: always-accept write responder.
    // aw/w are accepted every cycle (never stalls the always-on monitor
    // egress); a matched aw/w pair produces one OKAY B. Monotonic counters
    // compared mod-2^16 keep bvalid asserted while responses are owed.
    //=========================================================================
    assign mon_awready = 1'b1;
    assign mon_wready  = 1'b1;
    assign mon_bresp   = 2'b00;  // OKAY

    logic [15:0] r_mon_aw_cnt, r_mon_w_cnt, r_mon_b_cnt;
    wire mon_b_beat = mon_bvalid && mon_bready;
    assign mon_bvalid = (r_mon_aw_cnt != r_mon_b_cnt) && (r_mon_w_cnt != r_mon_b_cnt);

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_mon_aw_cnt <= '0;
            r_mon_w_cnt  <= '0;
            r_mon_b_cnt  <= '0;
        end else begin
            if (mon_awvalid && mon_awready) r_mon_aw_cnt <= r_mon_aw_cnt + 16'd1;
            if (mon_wvalid  && mon_wready)  r_mon_w_cnt  <= r_mon_w_cnt  + 16'd1;
            if (mon_b_beat)                 r_mon_b_cnt  <= r_mon_b_cnt  + 16'd1;
        end
    )

    //=========================================================================
    // AXI bus meters (per-direction utilization) -- reused, DMA-agnostic
    //
    // Two pure-snoop axi_bus_meter instances tap the DUT's source-read (rd_r*)
    // and sink-write (wr_w*) data masters. Each classifies every window cycle
    // into PRODUCTIVE (valid&ready), BACKPRESSURE (valid&!ready), STARVATION
    // (!valid&ready) or IDLE (!valid&!ready). Same instrument STREAM char uses;
    // RAPIDS has genuinely separate read/write masters so the split is real.
    //=========================================================================
    // Measurement-window controller: open+clear the meters on first bus
    // activity, freeze them 16 idle cycles after the last beat -> exactly one
    // frozen window per workload (the host reads the frozen buckets over CSR).
    logic obs_busy;
    assign obs_busy = rd_arvalid | rd_rvalid | wr_awvalid | wr_wvalid | wr_bvalid;
    logic       obs_win_active, obs_started;
    logic [4:0] obs_settle;
    logic       obs_meter_clear, obs_meter_freeze;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            obs_win_active <= 1'b0; obs_started <= 1'b0; obs_settle <= 5'd0;
        end else begin
            if (obs_busy && !obs_win_active && !obs_started) begin
                obs_win_active <= 1'b1; obs_started <= 1'b1; obs_settle <= 5'd0;
            end else if (obs_win_active) begin
                if (obs_busy)                    obs_settle <= 5'd0;
                else if (obs_settle != 5'd16)    obs_settle <= obs_settle + 5'd1;
                else                             obs_win_active <= 1'b0;  // close
            end
        end
    )
    assign obs_meter_clear  = obs_busy && !obs_win_active && !obs_started; // 1-cyc open
    assign obs_meter_freeze = ~obs_win_active;

    // Per-channel meter outputs unused (aggregate-only, NUM_CHANNELS=1).
    logic [15:0] obs_rd_ch_prod  [1], obs_rd_ch_bp  [1], obs_rd_ch_starv  [1], obs_rd_ch_idle  [1];
    logic [15:0] obs_wr_ch_prod  [1], obs_wr_ch_bp  [1], obs_wr_ch_starv  [1], obs_wr_ch_idle  [1];
    logic [3:0]  obs_rd_ch_ovf, obs_wr_ch_ovf;

    axi_bus_meter #(
        .NUM_CHANNELS (1)
    ) u_meter_rd (
        .aclk    (aclk),
        .aresetn (aresetn),
        .i_clear (obs_meter_clear),
        .i_freeze(obs_meter_freeze),
        // Snoop the source-read R channel (data returning from source memory).
        .i_valid        (rd_rvalid),
        .i_ready        (rd_rready),
        .i_channel_id   (1'b0),
        .i_channel_valid(rd_rvalid),
        .o_agg_productive  (obs_rd_prod),
        .o_agg_backpressure(obs_rd_bp),
        .o_agg_starvation  (obs_rd_starv),
        .o_agg_idle        (obs_rd_idle),
        .o_ch_productive   (obs_rd_ch_prod),
        .o_ch_backpressure (obs_rd_ch_bp),
        .o_ch_starvation   (obs_rd_ch_starv),
        .o_ch_idle         (obs_rd_ch_idle),
        .o_ch_overflow     (obs_rd_ch_ovf)
    );

    axi_bus_meter #(
        .NUM_CHANNELS (1)
    ) u_meter_wr (
        .aclk    (aclk),
        .aresetn (aresetn),
        .i_clear (obs_meter_clear),
        .i_freeze(obs_meter_freeze),
        // Snoop the sink-write W channel (data draining to sink memory).
        .i_valid        (wr_wvalid),
        .i_ready        (wr_wready),
        .i_channel_id   (1'b0),
        .i_channel_valid(wr_wvalid),
        .o_agg_productive  (obs_wr_prod),
        .o_agg_backpressure(obs_wr_bp),
        .o_agg_starvation  (obs_wr_starv),
        .o_agg_idle        (obs_wr_idle),
        .o_ch_productive   (obs_wr_ch_prod),
        .o_ch_backpressure (obs_wr_ch_bp),
        .o_ch_starvation   (obs_wr_ch_starv),
        .o_ch_idle         (obs_wr_ch_idle),
        .o_ch_overflow     (obs_wr_ch_ovf)
    );

endmodule : rapids_char_harness
