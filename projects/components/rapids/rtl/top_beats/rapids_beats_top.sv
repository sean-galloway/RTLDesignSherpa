// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_beats_top
// Purpose: Top-level wrapper for the RAPIDS "beats" DMA engine.
//
// Description:
//   Mirrors the structure of stream_top_ch8 for the RAPIDS beats core.
//
//   Integration hierarchy:
//     APB4 slave (s_apb_*)
//       -> apb_slave  (APB -> CMD/RSP, single clock domain: pclk = aclk)
//       -> cmdrsp_router (address-based routing)
//          -> apbtodescr           (0x000-0x03F : per-channel kick-off)
//          -> peakrdl_to_cmdrsp     (0x100+      : config registers)
//             -> rapids_regs        (PeakRDL passthrough register file)
//       -> rapids_config_block (hwif_out -> cfg_* mapping)
//       -> rapids_core_beats   (scheduler array + sink/source data paths)
//       -> rd/wr AXI monitor block (axi4_master_rd_mon + axi4_master_wr_mon,
//                                   USE_AXI_MONITORS=1) merged with the core's
//                                   64-bit MonBus via monbus_arbiter.
//
//   APB address map:
//     0x000-0x03F : channel kick-off (apbtodescr)
//     0x100+      : configuration registers (PeakRDL / rapids_regs)
//
// Monbus width reconciliation:
//   rapids_core_beats emits a 64-bit raw MonBus packet, while the AXI4
//   monitors (axi4_master_rd_mon / axi4_master_wr_mon) and monbus_arbiter
//   operate on the 128-bit monitor_common_pkg::monitor_packet_t (the
//   convention used by stream_top / axi4_dma_observer). The top-level
//   mon_packet output is therefore a 128-bit monitor_packet_t. The core's
//   64-bit packet is zero-extended into the low 64 bits when it is passed
//   through (USE_AXI_MONITORS=0) or fed into the arbiter (USE_AXI_MONITORS=1).
//
// Author: sean galloway
// Created: 2026-07-02

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module rapids_beats_top #(
    parameter int NUM_CHANNELS   = 8,
    parameter int DATA_WIDTH     = 512,
    parameter int ADDR_WIDTH     = 64,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int SRAM_DEPTH     = 4096,
    parameter int APB_ADDR_WIDTH = 12,
    parameter int APB_DATA_WIDTH = 32,
    parameter int USE_AXI_MONITORS = 0,  // 0 = disable AXI taps (core MonBus passthrough)
    // Monitor sizing (only meaningful when USE_AXI_MONITORS=1)
    parameter int MON_MAX_TRANSACTIONS = 16,
    parameter int AR_MAX_OUTSTANDING   = 8,
    parameter int AW_MAX_OUTSTANDING   = 8,
    // Short aliases / derived
    parameter int NC  = NUM_CHANNELS,
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1,
    parameter int SCW = $clog2(SRAM_DEPTH) + 1
) (
    //-------------------------------------------------------------------------
    // Clock and Reset
    //-------------------------------------------------------------------------
    input  logic                                    aclk,
    input  logic                                    aresetn,
    // Sync clear of the AXI monitor transaction CAMs (USE_AXI_MONITORS=1).
    input  logic                                    cam_clear,

    //-------------------------------------------------------------------------
    // APB4 Configuration Interface (single clock domain: pclk = aclk)
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
    // AXI4 Master - Descriptor Fetch (FIXED 256-bit read data)
    //-------------------------------------------------------------------------
    output logic [IW-1:0]                           m_axi_desc_arid,
    output logic [AW-1:0]                           m_axi_desc_araddr,
    output logic [7:0]                              m_axi_desc_arlen,
    output logic [2:0]                              m_axi_desc_arsize,
    output logic [1:0]                              m_axi_desc_arburst,
    output logic                                    m_axi_desc_arlock,
    output logic [3:0]                              m_axi_desc_arcache,
    output logic [2:0]                              m_axi_desc_arprot,
    output logic [3:0]                              m_axi_desc_arqos,
    output logic [3:0]                              m_axi_desc_arregion,
    output logic                                    m_axi_desc_arvalid,
    input  logic                                    m_axi_desc_arready,
    input  logic [IW-1:0]                           m_axi_desc_rid,
    input  logic [255:0]                            m_axi_desc_rdata,
    input  logic [1:0]                              m_axi_desc_rresp,
    input  logic                                    m_axi_desc_rlast,
    input  logic                                    m_axi_desc_rvalid,
    output logic                                    m_axi_desc_rready,

    //-------------------------------------------------------------------------
    // AXI4 Master - Data Read (Memory -> Source SRAM)
    //-------------------------------------------------------------------------
    output logic [IW-1:0]                           m_axi_rd_arid,
    output logic [AW-1:0]                           m_axi_rd_araddr,
    output logic [7:0]                              m_axi_rd_arlen,
    output logic [2:0]                              m_axi_rd_arsize,
    output logic [1:0]                              m_axi_rd_arburst,
    output logic                                    m_axi_rd_arvalid,
    input  logic                                    m_axi_rd_arready,
    input  logic [IW-1:0]                           m_axi_rd_rid,
    input  logic [DW-1:0]                           m_axi_rd_rdata,
    input  logic [1:0]                              m_axi_rd_rresp,
    input  logic                                    m_axi_rd_rlast,
    input  logic                                    m_axi_rd_rvalid,
    output logic                                    m_axi_rd_rready,

    //-------------------------------------------------------------------------
    // AXI4 Master - Data Write (Sink SRAM -> Memory)
    //-------------------------------------------------------------------------
    output logic [IW-1:0]                           m_axi_wr_awid,
    output logic [AW-1:0]                           m_axi_wr_awaddr,
    output logic [7:0]                              m_axi_wr_awlen,
    output logic [2:0]                              m_axi_wr_awsize,
    output logic [1:0]                              m_axi_wr_awburst,
    output logic                                    m_axi_wr_awlock,
    output logic [3:0]                              m_axi_wr_awcache,
    output logic [2:0]                              m_axi_wr_awprot,
    output logic [3:0]                              m_axi_wr_awqos,
    output logic [3:0]                              m_axi_wr_awregion,
    output logic                                    m_axi_wr_awvalid,
    input  logic                                    m_axi_wr_awready,
    output logic [DW-1:0]                           m_axi_wr_wdata,
    output logic [(DW/8)-1:0]                       m_axi_wr_wstrb,
    output logic                                    m_axi_wr_wlast,
    output logic                                    m_axi_wr_wvalid,
    input  logic                                    m_axi_wr_wready,
    input  logic [IW-1:0]                           m_axi_wr_bid,
    input  logic [1:0]                              m_axi_wr_bresp,
    input  logic                                    m_axi_wr_bvalid,
    output logic                                    m_axi_wr_bready,

    //-------------------------------------------------------------------------
    // Sink Path - Fill Interface (External network -> SRAM)
    //-------------------------------------------------------------------------
    input  logic                                    snk_fill_alloc_req,
    input  logic [7:0]                              snk_fill_alloc_size,
    input  logic [CIW-1:0]                          snk_fill_alloc_id,
    output logic [NC-1:0][SCW-1:0]                  snk_fill_space_free,
    input  logic                                    snk_fill_valid,
    output logic                                    snk_fill_ready,
    input  logic [CIW-1:0]                          snk_fill_id,
    input  logic [DW-1:0]                           snk_fill_data,

    //-------------------------------------------------------------------------
    // Source Path - Drain Interface (SRAM -> External network)
    //-------------------------------------------------------------------------
    output logic [NC-1:0][SCW-1:0]                  src_drain_data_avail,
    input  logic [NC-1:0]                           src_drain_req,
    input  logic [NC-1:0][7:0]                      src_drain_size,
    output logic [NC-1:0]                           src_drain_valid,
    input  logic                                    src_drain_read,
    input  logic [CIW-1:0]                          src_drain_id,
    output logic [DW-1:0]                           src_drain_data,

    //-------------------------------------------------------------------------
    // MonBus AXI-Lite Group (mirrors stream_top_ch8)
    //   - AXI-Lite error-drain slave (32-bit data): CPU reads err/IRQ FIFO
    //   - AXI-Lite capture master   (64-bit data): monitor bulk-trace writes
    //   - Single interrupt output (mon_irq from monbus_axil_axil_group)
    // Active only when USE_AXI_MONITORS==1; tied off otherwise.
    //-------------------------------------------------------------------------
    // AXI-Lite error-drain slave (32-bit)
    input  logic                                    s_axil_err_arvalid,
    output logic                                    s_axil_err_arready,
    input  logic [31:0]                             s_axil_err_araddr,
    input  logic [2:0]                              s_axil_err_arprot,
    output logic                                    s_axil_err_rvalid,
    input  logic                                    s_axil_err_rready,
    output logic [31:0]                             s_axil_err_rdata,
    output logic [1:0]                              s_axil_err_rresp,

    // AXI-Lite capture master (64-bit)
    output logic                                    m_axil_mon_awvalid,
    input  logic                                    m_axil_mon_awready,
    output logic [31:0]                             m_axil_mon_awaddr,
    output logic [2:0]                              m_axil_mon_awprot,
    output logic                                    m_axil_mon_wvalid,
    input  logic                                    m_axil_mon_wready,
    output logic [63:0]                             m_axil_mon_wdata,
    output logic [7:0]                              m_axil_mon_wstrb,
    input  logic                                    m_axil_mon_bvalid,
    output logic                                    m_axil_mon_bready,
    input  logic [1:0]                              m_axil_mon_bresp,

    // Interrupt output
    output logic                                    mon_irq,

    // Configuration (mirror stream_top_ch8)
    input  logic [31:0]                             cfg_mon_base_addr,
    input  logic [31:0]                             cfg_mon_limit_addr,
    input  logic [15:0]                             cfg_mon_flush_watermark,

    //-------------------------------------------------------------------------
    // Status (minimal top-level observation)
    //-------------------------------------------------------------------------
    output logic                                    system_idle,
    output logic [NC-1:0]                           sched_error
);

    //=========================================================================
    // APB -> CMD/RSP (single clock domain)
    //=========================================================================
    logic                          apb_cmd_valid;
    logic                          apb_cmd_ready;
    logic                          apb_cmd_pwrite;
    logic [APB_ADDR_WIDTH-1:0]     apb_cmd_paddr;
    logic [APB_DATA_WIDTH-1:0]     apb_cmd_pwdata;
    logic [(APB_DATA_WIDTH/8)-1:0] apb_cmd_pstrb;
    logic                          apb_rsp_valid;
    logic                          apb_rsp_ready;
    logic [APB_DATA_WIDTH-1:0]     apb_rsp_prdata;
    logic                          apb_rsp_pslverr;

    apb_slave #(
        .ADDR_WIDTH (APB_ADDR_WIDTH),
        .DATA_WIDTH (APB_DATA_WIDTH)
    ) u_apb_slave (
        .pclk           (aclk),
        .presetn        (aresetn),
        .s_apb_PSEL     (s_apb_psel),
        .s_apb_PENABLE  (s_apb_penable),
        .s_apb_PREADY   (s_apb_pready),
        .s_apb_PADDR    (s_apb_paddr),
        .s_apb_PWRITE   (s_apb_pwrite),
        .s_apb_PWDATA   (s_apb_pwdata),
        .s_apb_PSTRB    (s_apb_pstrb),
        .s_apb_PPROT    (3'b000),
        .s_apb_PRDATA   (s_apb_prdata),
        .s_apb_PSLVERR  (s_apb_pslverr),
        .cmd_valid      (apb_cmd_valid),
        .cmd_ready      (apb_cmd_ready),
        .cmd_pwrite     (apb_cmd_pwrite),
        .cmd_paddr      (apb_cmd_paddr),
        .cmd_pwdata     (apb_cmd_pwdata),
        .cmd_pstrb      (apb_cmd_pstrb),
        .cmd_pprot      (),
        .rsp_valid      (apb_rsp_valid),
        .rsp_ready      (apb_rsp_ready),
        .rsp_prdata     (apb_rsp_prdata),
        .rsp_pslverr    (apb_rsp_pslverr)
    );

    //=========================================================================
    // CMD/RSP Address Router
    //=========================================================================
    // Kick-off (m0) : 0x000-0x03F -> apbtodescr
    logic                          kickoff_cmd_valid;
    logic                          kickoff_cmd_ready;
    logic                          kickoff_cmd_pwrite;
    logic [APB_ADDR_WIDTH-1:0]     kickoff_cmd_paddr;
    logic [APB_DATA_WIDTH-1:0]     kickoff_cmd_pwdata;
    logic                          kickoff_rsp_valid;
    logic                          kickoff_rsp_ready;
    logic [APB_DATA_WIDTH-1:0]     kickoff_rsp_prdata;
    logic                          kickoff_rsp_pslverr;

    // Registers (m1) : 0x100+ -> peakrdl_to_cmdrsp
    logic                          peakrdl_cmd_valid;
    logic                          peakrdl_cmd_ready;
    logic                          peakrdl_cmd_pwrite;
    logic [APB_ADDR_WIDTH-1:0]     peakrdl_cmd_paddr;
    logic [APB_DATA_WIDTH-1:0]     peakrdl_cmd_pwdata;
    logic                          peakrdl_rsp_valid;
    logic                          peakrdl_rsp_ready;
    logic [APB_DATA_WIDTH-1:0]     peakrdl_rsp_prdata;
    logic                          peakrdl_rsp_pslverr;

    cmdrsp_router #(
        .ADDR_WIDTH (APB_ADDR_WIDTH),
        .DATA_WIDTH (APB_DATA_WIDTH)
    ) u_cmdrsp_router (
        .clk            (aclk),
        .rst_n          (aresetn),
        // Slave (from apb_slave)
        .s_cmd_valid    (apb_cmd_valid),
        .s_cmd_ready    (apb_cmd_ready),
        .s_cmd_pwrite   (apb_cmd_pwrite),
        .s_cmd_paddr    (apb_cmd_paddr),
        .s_cmd_pwdata   (apb_cmd_pwdata),
        .s_rsp_valid    (apb_rsp_valid),
        .s_rsp_ready    (apb_rsp_ready),
        .s_rsp_prdata   (apb_rsp_prdata),
        .s_rsp_pslverr  (apb_rsp_pslverr),
        // Master 0: apbtodescr (0x000-0x03F)
        .m0_cmd_valid   (kickoff_cmd_valid),
        .m0_cmd_ready   (kickoff_cmd_ready),
        .m0_cmd_pwrite  (kickoff_cmd_pwrite),
        .m0_cmd_paddr   (kickoff_cmd_paddr),
        .m0_cmd_pwdata  (kickoff_cmd_pwdata),
        .m0_rsp_valid   (kickoff_rsp_valid),
        .m0_rsp_ready   (kickoff_rsp_ready),
        .m0_rsp_prdata  (kickoff_rsp_prdata),
        .m0_rsp_pslverr (kickoff_rsp_pslverr),
        // Master 1: peakrdl_to_cmdrsp (0x100+)
        .m1_cmd_valid   (peakrdl_cmd_valid),
        .m1_cmd_ready   (peakrdl_cmd_ready),
        .m1_cmd_pwrite  (peakrdl_cmd_pwrite),
        .m1_cmd_paddr   (peakrdl_cmd_paddr),
        .m1_cmd_pwdata  (peakrdl_cmd_pwdata),
        .m1_rsp_valid   (peakrdl_rsp_valid),
        .m1_rsp_ready   (peakrdl_rsp_ready),
        .m1_rsp_prdata  (peakrdl_rsp_prdata),
        .m1_rsp_pslverr (peakrdl_rsp_pslverr),
        // Performance profiler region (0x040-0x0FF) - unused in beats core
        .perf_cfg_enable    (),
        .perf_cfg_mode      (),
        .perf_cfg_clear     (),
        .perf_fifo_data_low (32'h0),
        .perf_fifo_data_high(32'h0),
        .perf_fifo_empty    (1'b1),
        .perf_fifo_full     (1'b0),
        .perf_fifo_count    (16'h0),
        .perf_fifo_rd       ()
    );

    //=========================================================================
    // Channel Kick-off Router (apbtodescr) -> core.apb_valid/apb_addr
    //=========================================================================
    logic [NC-1:0]          apb_valid;
    logic [NC-1:0]          apb_ready;
    logic [NC-1:0][AW-1:0]  apb_addr;

    apbtodescr #(
        .ADDR_WIDTH      (APB_ADDR_WIDTH),
        .DATA_WIDTH      (APB_DATA_WIDTH),
        .NUM_CHANNELS    (NUM_CHANNELS),
        .DESC_ADDR_WIDTH (ADDR_WIDTH)
    ) u_apbtodescr (
        .clk            (aclk),
        .rst_n          (aresetn),
        .apb_cmd_valid  (kickoff_cmd_valid),
        .apb_cmd_ready  (kickoff_cmd_ready),
        .apb_cmd_addr   (kickoff_cmd_paddr),
        .apb_cmd_wdata  (kickoff_cmd_pwdata),
        .apb_cmd_write  (kickoff_cmd_pwrite),
        .apb_rsp_valid  (kickoff_rsp_valid),
        .apb_rsp_ready  (kickoff_rsp_ready),
        .apb_rsp_rdata  (kickoff_rsp_prdata),
        .apb_rsp_error  (kickoff_rsp_pslverr),
        .desc_apb_valid (apb_valid),
        .desc_apb_ready (apb_ready),
        .desc_apb_addr  (apb_addr),
        .apb_descriptor_kickoff_hit ()
    );

    //=========================================================================
    // PeakRDL passthrough adapter (peakrdl_to_cmdrsp)
    //=========================================================================
    logic                          regblk_req;
    logic                          regblk_req_is_wr;
    logic [APB_ADDR_WIDTH-1:0]     regblk_addr;
    logic [APB_DATA_WIDTH-1:0]     regblk_wr_data;
    logic [APB_DATA_WIDTH-1:0]     regblk_wr_biten;
    logic                          regblk_req_stall_wr;
    logic                          regblk_req_stall_rd;
    logic                          regblk_rd_ack;
    logic                          regblk_rd_err;
    logic [APB_DATA_WIDTH-1:0]     regblk_rd_data;
    logic                          regblk_wr_ack;
    logic                          regblk_wr_err;

    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH (APB_ADDR_WIDTH),
        .DATA_WIDTH (APB_DATA_WIDTH)
    ) u_peakrdl_adapter (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .cmd_valid          (peakrdl_cmd_valid),
        .cmd_ready          (peakrdl_cmd_ready),
        .cmd_pwrite         (peakrdl_cmd_pwrite),
        .cmd_paddr          (peakrdl_cmd_paddr),
        .cmd_pwdata         (peakrdl_cmd_pwdata),
        .cmd_pstrb          ({(APB_DATA_WIDTH/8){1'b1}}),
        .rsp_valid          (peakrdl_rsp_valid),
        .rsp_ready          (peakrdl_rsp_ready),
        .rsp_prdata         (peakrdl_rsp_prdata),
        .rsp_pslverr        (peakrdl_rsp_pslverr),
        .regblk_req         (regblk_req),
        .regblk_req_is_wr   (regblk_req_is_wr),
        .regblk_addr        (regblk_addr),
        .regblk_wr_data     (regblk_wr_data),
        .regblk_wr_biten    (regblk_wr_biten),
        .regblk_req_stall_wr(regblk_req_stall_wr),
        .regblk_req_stall_rd(regblk_req_stall_rd),
        .regblk_rd_ack      (regblk_rd_ack),
        .regblk_rd_err      (regblk_rd_err),
        .regblk_rd_data     (regblk_rd_data),
        .regblk_wr_ack      (regblk_wr_ack),
        .regblk_wr_err      (regblk_wr_err)
    );

    //=========================================================================
    // PeakRDL Register Block (rapids_regs)
    //=========================================================================
    import rapids_regs_pkg::*;

    rapids_regs_pkg::rapids_regs__in_t  hwif_in;
    rapids_regs_pkg::rapids_regs__out_t hwif_out;

    // hwif_in status returns are tied off minimally (no fields driven).
    assign hwif_in = '{default: '0};

    rapids_regs u_rapids_regs (
        .clk                    (aclk),
        .rst                    (~aresetn),  // PeakRDL uses active-high reset
        .s_cpuif_req            (regblk_req),
        .s_cpuif_req_is_wr      (regblk_req_is_wr),
        .s_cpuif_addr           (13'({1'b0, regblk_addr})),  // 12b -> 13b
        .s_cpuif_wr_data        (regblk_wr_data),
        .s_cpuif_wr_biten       (regblk_wr_biten),
        .s_cpuif_req_stall_wr   (regblk_req_stall_wr),
        .s_cpuif_req_stall_rd   (regblk_req_stall_rd),
        .s_cpuif_rd_ack         (regblk_rd_ack),
        .s_cpuif_rd_err         (regblk_rd_err),
        .s_cpuif_rd_data        (regblk_rd_data),
        .s_cpuif_wr_ack         (regblk_wr_ack),
        .s_cpuif_wr_err         (regblk_wr_err),
        .hwif_in                (hwif_in),
        .hwif_out               (hwif_out)
    );

    //=========================================================================
    // Configuration Mapping Block (hwif_out -> cfg_*)
    //=========================================================================
    // Base cfg -> core
    logic [NC-1:0]  cfg_channel_enable;
    logic [NC-1:0]  cfg_channel_reset;
    logic           cfg_sched_enable;
    logic [31:0]    cfg_sched_timeout_cycles;
    logic [7:0]     cfg_sched_timeout_limit;
    logic           cfg_sched_timeout_enable;
    logic           cfg_sched_err_enable;
    logic           cfg_sched_compl_enable;
    logic           cfg_sched_perf_enable;
    logic           cfg_desceng_enable;
    logic           cfg_desceng_prefetch;
    logic [3:0]     cfg_desceng_fifo_thresh;
    logic [AW-1:0]  cfg_desceng_addr0_base;
    logic [AW-1:0]  cfg_desceng_addr0_limit;
    logic [AW-1:0]  cfg_desceng_addr1_base;
    logic [AW-1:0]  cfg_desceng_addr1_limit;
    // Descriptor AXI monitor cfg -> core (in-core descriptor monitor)
    logic           cfg_desc_mon_enable;
    logic           cfg_desc_mon_err_enable;
    logic           cfg_desc_mon_perf_enable;
    logic           cfg_desc_mon_timeout_enable;
    logic [31:0]    cfg_desc_mon_timeout_cycles;
    logic [31:0]    cfg_desc_mon_latency_thresh;
    logic [15:0]    cfg_desc_mon_pkt_mask;
    logic [3:0]     cfg_desc_mon_err_select;
    logic [7:0]     cfg_desc_mon_err_mask;
    logic [7:0]     cfg_desc_mon_timeout_mask;
    logic [7:0]     cfg_desc_mon_compl_mask;
    logic [7:0]     cfg_desc_mon_thresh_mask;
    logic [7:0]     cfg_desc_mon_perf_mask;
    logic [7:0]     cfg_desc_mon_addr_mask;
    logic [7:0]     cfg_desc_mon_debug_mask;
    // Read engine AXI monitor cfg -> rd_mon tap
    logic           cfg_rdeng_mon_enable;
    logic           cfg_rdeng_mon_err_enable;
    logic           cfg_rdeng_mon_perf_enable;
    logic           cfg_rdeng_mon_timeout_enable;
    logic [31:0]    cfg_rdeng_mon_timeout_cycles;
    logic [31:0]    cfg_rdeng_mon_latency_thresh;
    logic [15:0]    cfg_rdeng_mon_pkt_mask;
    logic [3:0]     cfg_rdeng_mon_err_select;
    logic [7:0]     cfg_rdeng_mon_err_mask;
    logic [7:0]     cfg_rdeng_mon_timeout_mask;
    logic [7:0]     cfg_rdeng_mon_compl_mask;
    logic [7:0]     cfg_rdeng_mon_thresh_mask;
    logic [7:0]     cfg_rdeng_mon_perf_mask;
    logic [7:0]     cfg_rdeng_mon_addr_mask;
    logic [7:0]     cfg_rdeng_mon_debug_mask;
    // Write engine AXI monitor cfg -> wr_mon tap
    logic           cfg_wreng_mon_enable;
    logic           cfg_wreng_mon_err_enable;
    logic           cfg_wreng_mon_perf_enable;
    logic           cfg_wreng_mon_timeout_enable;
    logic [31:0]    cfg_wreng_mon_timeout_cycles;
    logic [31:0]    cfg_wreng_mon_latency_thresh;
    logic [15:0]    cfg_wreng_mon_pkt_mask;
    logic [3:0]     cfg_wreng_mon_err_select;
    logic [7:0]     cfg_wreng_mon_err_mask;
    logic [7:0]     cfg_wreng_mon_timeout_mask;
    logic [7:0]     cfg_wreng_mon_compl_mask;
    logic [7:0]     cfg_wreng_mon_thresh_mask;
    logic [7:0]     cfg_wreng_mon_perf_mask;
    logic [7:0]     cfg_wreng_mon_addr_mask;
    logic [7:0]     cfg_wreng_mon_debug_mask;
    // AXI transfer cfg -> core
    logic [7:0]     cfg_axi_rd_xfer_beats;
    logic [7:0]     cfg_axi_wr_xfer_beats;
    // Perf / obs (unused by beats core; left open)
    logic           cfg_perf_enable;
    logic           cfg_perf_mode;
    logic           cfg_perf_clear;
    logic [2:0]     cfg_obs_ch_sel;
    logic [1:0]     cfg_obs_cat_sel;

    rapids_config_block #(
        .NUM_CHANNELS (NUM_CHANNELS),
        .ADDR_WIDTH   (ADDR_WIDTH)
    ) u_config_block (
        .clk    (aclk),
        .rst_n  (aresetn),

        // Global Control
        .reg_global_ctrl_global_en          (hwif_out.GLOBAL_CTRL.GLOBAL_EN.value),
        .reg_global_ctrl_global_rst         (hwif_out.GLOBAL_CTRL.GLOBAL_RST.value),
        // Channel Control
        .reg_channel_enable_ch_en           (hwif_out.CHANNEL_ENABLE.CH_EN.value),
        .reg_channel_reset_ch_rst           (hwif_out.CHANNEL_RESET.CH_RST.value),
        // Scheduler Configuration
        .reg_sched_timeout_cycles_timeout_cycles (hwif_out.SCHED_TIMEOUT_CYCLES.TIMEOUT_CYCLES.value),
        .reg_sched_timeout_limit_limit           (hwif_out.SCHED_TIMEOUT_LIMIT.LIMIT.value),
        .reg_sched_config_sched_en               (hwif_out.SCHED_CONFIG.SCHED_EN.value),
        .reg_sched_config_timeout_en             (hwif_out.SCHED_CONFIG.TIMEOUT_EN.value),
        .reg_sched_config_err_en                 (hwif_out.SCHED_CONFIG.ERR_EN.value),
        .reg_sched_config_compl_en               (hwif_out.SCHED_CONFIG.COMPL_EN.value),
        .reg_sched_config_perf_en                (hwif_out.SCHED_CONFIG.PERF_EN.value),
        // Descriptor Engine Configuration
        .reg_desceng_config_desceng_en           (hwif_out.DESCENG_CONFIG.DESCENG_EN.value),
        .reg_desceng_config_prefetch_en          (hwif_out.DESCENG_CONFIG.PREFETCH_EN.value),
        .reg_desceng_config_fifo_thresh          (hwif_out.DESCENG_CONFIG.FIFO_THRESH.value),
        .reg_desceng_addr0_base_addr0_base       (hwif_out.DESCENG_ADDR0_BASE.ADDR0_BASE.value),
        .reg_desceng_addr0_limit_addr0_limit     (hwif_out.DESCENG_ADDR0_LIMIT.ADDR0_LIMIT.value),
        .reg_desceng_addr1_base_addr1_base       (hwif_out.DESCENG_ADDR1_BASE.ADDR1_BASE.value),
        .reg_desceng_addr1_limit_addr1_limit     (hwif_out.DESCENG_ADDR1_LIMIT.ADDR1_LIMIT.value),
        // Descriptor AXI Monitor Configuration (MON regfile instance)
        .reg_daxmon_enable_mon_en                (hwif_out.MON.DAXMON_ENABLE.MON_EN.value),
        .reg_daxmon_enable_err_en                (hwif_out.MON.DAXMON_ENABLE.ERR_EN.value),
        .reg_daxmon_enable_compl_en              (hwif_out.MON.DAXMON_ENABLE.COMPL_EN.value),
        .reg_daxmon_enable_timeout_en            (hwif_out.MON.DAXMON_ENABLE.TIMEOUT_EN.value),
        .reg_daxmon_enable_perf_en               (hwif_out.MON.DAXMON_ENABLE.PERF_EN.value),
        .reg_daxmon_timeout_timeout_cycles       (hwif_out.MON.DAXMON_TIMEOUT.TIMEOUT_CYCLES.value),
        .reg_daxmon_latency_thresh_latency_thresh(hwif_out.MON.DAXMON_LATENCY_THRESH.LATENCY_THRESH.value),
        .reg_daxmon_pkt_mask_pkt_mask            (hwif_out.MON.DAXMON_PKT_MASK.PKT_MASK.value),
        .reg_daxmon_err_cfg_err_select           (hwif_out.MON.DAXMON_ERR_CFG.ERR_SELECT.value),
        .reg_daxmon_err_cfg_err_mask             (hwif_out.MON.DAXMON_ERR_CFG.ERR_MASK.value),
        .reg_daxmon_mask1_timeout_mask           (hwif_out.MON.DAXMON_MASK1.TIMEOUT_MASK.value),
        .reg_daxmon_mask1_compl_mask             (hwif_out.MON.DAXMON_MASK1.COMPL_MASK.value),
        .reg_daxmon_mask2_thresh_mask            (hwif_out.MON.DAXMON_MASK2.THRESH_MASK.value),
        .reg_daxmon_mask2_perf_mask              (hwif_out.MON.DAXMON_MASK2.PERF_MASK.value),
        .reg_daxmon_mask3_addr_mask              (hwif_out.MON.DAXMON_MASK3.ADDR_MASK.value),
        .reg_daxmon_mask3_debug_mask             (hwif_out.MON.DAXMON_MASK3.DEBUG_MASK.value),
        // Read Engine AXI Monitor Configuration
        .reg_rdmon_enable_mon_en                 (hwif_out.MON.RDMON_ENABLE.MON_EN.value),
        .reg_rdmon_enable_err_en                 (hwif_out.MON.RDMON_ENABLE.ERR_EN.value),
        .reg_rdmon_enable_compl_en               (hwif_out.MON.RDMON_ENABLE.COMPL_EN.value),
        .reg_rdmon_enable_timeout_en             (hwif_out.MON.RDMON_ENABLE.TIMEOUT_EN.value),
        .reg_rdmon_enable_perf_en                (hwif_out.MON.RDMON_ENABLE.PERF_EN.value),
        .reg_rdmon_timeout_timeout_cycles        (hwif_out.MON.RDMON_TIMEOUT.TIMEOUT_CYCLES.value),
        .reg_rdmon_latency_thresh_latency_thresh (hwif_out.MON.RDMON_LATENCY_THRESH.LATENCY_THRESH.value),
        .reg_rdmon_pkt_mask_pkt_mask             (hwif_out.MON.RDMON_PKT_MASK.PKT_MASK.value),
        .reg_rdmon_err_cfg_err_select            (hwif_out.MON.RDMON_ERR_CFG.ERR_SELECT.value),
        .reg_rdmon_err_cfg_err_mask              (hwif_out.MON.RDMON_ERR_CFG.ERR_MASK.value),
        .reg_rdmon_mask1_timeout_mask            (hwif_out.MON.RDMON_MASK1.TIMEOUT_MASK.value),
        .reg_rdmon_mask1_compl_mask              (hwif_out.MON.RDMON_MASK1.COMPL_MASK.value),
        .reg_rdmon_mask2_thresh_mask             (hwif_out.MON.RDMON_MASK2.THRESH_MASK.value),
        .reg_rdmon_mask2_perf_mask               (hwif_out.MON.RDMON_MASK2.PERF_MASK.value),
        .reg_rdmon_mask3_addr_mask               (hwif_out.MON.RDMON_MASK3.ADDR_MASK.value),
        .reg_rdmon_mask3_debug_mask              (hwif_out.MON.RDMON_MASK3.DEBUG_MASK.value),
        // Write Engine AXI Monitor Configuration
        .reg_wrmon_enable_mon_en                 (hwif_out.MON.WRMON_ENABLE.MON_EN.value),
        .reg_wrmon_enable_err_en                 (hwif_out.MON.WRMON_ENABLE.ERR_EN.value),
        .reg_wrmon_enable_compl_en               (hwif_out.MON.WRMON_ENABLE.COMPL_EN.value),
        .reg_wrmon_enable_timeout_en             (hwif_out.MON.WRMON_ENABLE.TIMEOUT_EN.value),
        .reg_wrmon_enable_perf_en                (hwif_out.MON.WRMON_ENABLE.PERF_EN.value),
        .reg_wrmon_timeout_timeout_cycles        (hwif_out.MON.WRMON_TIMEOUT.TIMEOUT_CYCLES.value),
        .reg_wrmon_latency_thresh_latency_thresh (hwif_out.MON.WRMON_LATENCY_THRESH.LATENCY_THRESH.value),
        .reg_wrmon_pkt_mask_pkt_mask             (hwif_out.MON.WRMON_PKT_MASK.PKT_MASK.value),
        .reg_wrmon_err_cfg_err_select            (hwif_out.MON.WRMON_ERR_CFG.ERR_SELECT.value),
        .reg_wrmon_err_cfg_err_mask              (hwif_out.MON.WRMON_ERR_CFG.ERR_MASK.value),
        .reg_wrmon_mask1_timeout_mask            (hwif_out.MON.WRMON_MASK1.TIMEOUT_MASK.value),
        .reg_wrmon_mask1_compl_mask              (hwif_out.MON.WRMON_MASK1.COMPL_MASK.value),
        .reg_wrmon_mask2_thresh_mask             (hwif_out.MON.WRMON_MASK2.THRESH_MASK.value),
        .reg_wrmon_mask2_perf_mask               (hwif_out.MON.WRMON_MASK2.PERF_MASK.value),
        .reg_wrmon_mask3_addr_mask               (hwif_out.MON.WRMON_MASK3.ADDR_MASK.value),
        .reg_wrmon_mask3_debug_mask              (hwif_out.MON.WRMON_MASK3.DEBUG_MASK.value),
        // AXI Transfer Configuration
        .reg_axi_xfer_config_rd_xfer_beats       (hwif_out.AXI_XFER_CONFIG.RD_XFER_BEATS.value),
        .reg_axi_xfer_config_wr_xfer_beats       (hwif_out.AXI_XFER_CONFIG.WR_XFER_BEATS.value),
        // Performance Profiler Configuration
        .reg_perf_config_perf_en                 (hwif_out.PERF_CONFIG.PERF_EN.value),
        .reg_perf_config_perf_mode               (hwif_out.PERF_CONFIG.PERF_MODE.value),
        .reg_perf_config_perf_clear              (hwif_out.PERF_CONFIG.PERF_CLEAR.value),
        // Observation mux selector
        .reg_obs_ctrl_ch_sel                     (hwif_out.OBS_CTRL.CH_SEL.value),
        .reg_obs_ctrl_cat_sel                    (hwif_out.OBS_CTRL.CAT_SEL.value),
        // Observation mux status (no core source in beats; tie to 0)
        .i_obs_flags                             (32'h0),
        .i_obs_data0                             (32'h0),
        .i_obs_data1                             (32'h0),

        // Outputs to core (base cfg)
        .cfg_channel_enable          (cfg_channel_enable),
        .cfg_channel_reset           (cfg_channel_reset),
        .cfg_sched_enable            (cfg_sched_enable),
        .cfg_sched_timeout_cycles    (cfg_sched_timeout_cycles),
        .cfg_sched_timeout_limit     (cfg_sched_timeout_limit),
        .cfg_sched_timeout_enable    (cfg_sched_timeout_enable),
        .cfg_sched_err_enable        (cfg_sched_err_enable),
        .cfg_sched_compl_enable      (cfg_sched_compl_enable),
        .cfg_sched_perf_enable       (cfg_sched_perf_enable),
        .cfg_desceng_enable          (cfg_desceng_enable),
        .cfg_desceng_prefetch        (cfg_desceng_prefetch),
        .cfg_desceng_fifo_thresh     (cfg_desceng_fifo_thresh),
        .cfg_desceng_addr0_base      (cfg_desceng_addr0_base),
        .cfg_desceng_addr0_limit     (cfg_desceng_addr0_limit),
        .cfg_desceng_addr1_base      (cfg_desceng_addr1_base),
        .cfg_desceng_addr1_limit     (cfg_desceng_addr1_limit),
        .cfg_desc_mon_enable         (cfg_desc_mon_enable),
        .cfg_desc_mon_err_enable     (cfg_desc_mon_err_enable),
        .cfg_desc_mon_perf_enable    (cfg_desc_mon_perf_enable),
        .cfg_desc_mon_timeout_enable (cfg_desc_mon_timeout_enable),
        .cfg_desc_mon_timeout_cycles (cfg_desc_mon_timeout_cycles),
        .cfg_desc_mon_latency_thresh (cfg_desc_mon_latency_thresh),
        .cfg_desc_mon_pkt_mask       (cfg_desc_mon_pkt_mask),
        .cfg_desc_mon_err_select     (cfg_desc_mon_err_select),
        .cfg_desc_mon_err_mask       (cfg_desc_mon_err_mask),
        .cfg_desc_mon_timeout_mask   (cfg_desc_mon_timeout_mask),
        .cfg_desc_mon_compl_mask     (cfg_desc_mon_compl_mask),
        .cfg_desc_mon_thresh_mask    (cfg_desc_mon_thresh_mask),
        .cfg_desc_mon_perf_mask      (cfg_desc_mon_perf_mask),
        .cfg_desc_mon_addr_mask      (cfg_desc_mon_addr_mask),
        .cfg_desc_mon_debug_mask     (cfg_desc_mon_debug_mask),
        // Outputs to rd/wr monitor block
        .cfg_rdeng_mon_enable        (cfg_rdeng_mon_enable),
        .cfg_rdeng_mon_err_enable    (cfg_rdeng_mon_err_enable),
        .cfg_rdeng_mon_perf_enable   (cfg_rdeng_mon_perf_enable),
        .cfg_rdeng_mon_timeout_enable(cfg_rdeng_mon_timeout_enable),
        .cfg_rdeng_mon_timeout_cycles(cfg_rdeng_mon_timeout_cycles),
        .cfg_rdeng_mon_latency_thresh(cfg_rdeng_mon_latency_thresh),
        .cfg_rdeng_mon_pkt_mask      (cfg_rdeng_mon_pkt_mask),
        .cfg_rdeng_mon_err_select    (cfg_rdeng_mon_err_select),
        .cfg_rdeng_mon_err_mask      (cfg_rdeng_mon_err_mask),
        .cfg_rdeng_mon_timeout_mask  (cfg_rdeng_mon_timeout_mask),
        .cfg_rdeng_mon_compl_mask    (cfg_rdeng_mon_compl_mask),
        .cfg_rdeng_mon_thresh_mask   (cfg_rdeng_mon_thresh_mask),
        .cfg_rdeng_mon_perf_mask     (cfg_rdeng_mon_perf_mask),
        .cfg_rdeng_mon_addr_mask     (cfg_rdeng_mon_addr_mask),
        .cfg_rdeng_mon_debug_mask    (cfg_rdeng_mon_debug_mask),
        .cfg_wreng_mon_enable        (cfg_wreng_mon_enable),
        .cfg_wreng_mon_err_enable    (cfg_wreng_mon_err_enable),
        .cfg_wreng_mon_perf_enable   (cfg_wreng_mon_perf_enable),
        .cfg_wreng_mon_timeout_enable(cfg_wreng_mon_timeout_enable),
        .cfg_wreng_mon_timeout_cycles(cfg_wreng_mon_timeout_cycles),
        .cfg_wreng_mon_latency_thresh(cfg_wreng_mon_latency_thresh),
        .cfg_wreng_mon_pkt_mask      (cfg_wreng_mon_pkt_mask),
        .cfg_wreng_mon_err_select    (cfg_wreng_mon_err_select),
        .cfg_wreng_mon_err_mask      (cfg_wreng_mon_err_mask),
        .cfg_wreng_mon_timeout_mask  (cfg_wreng_mon_timeout_mask),
        .cfg_wreng_mon_compl_mask    (cfg_wreng_mon_compl_mask),
        .cfg_wreng_mon_thresh_mask   (cfg_wreng_mon_thresh_mask),
        .cfg_wreng_mon_perf_mask     (cfg_wreng_mon_perf_mask),
        .cfg_wreng_mon_addr_mask     (cfg_wreng_mon_addr_mask),
        .cfg_wreng_mon_debug_mask    (cfg_wreng_mon_debug_mask),
        // AXI transfer cfg
        .cfg_axi_rd_xfer_beats       (cfg_axi_rd_xfer_beats),
        .cfg_axi_wr_xfer_beats       (cfg_axi_wr_xfer_beats),
        // Perf / obs (unused downstream)
        .cfg_perf_enable             (cfg_perf_enable),
        .cfg_perf_mode               (cfg_perf_mode),
        .cfg_perf_clear              (cfg_perf_clear),
        .cfg_obs_ch_sel              (cfg_obs_ch_sel),
        .cfg_obs_cat_sel             (cfg_obs_cat_sel),
        .obs_flags_to_regs           (),
        .obs_data0_to_regs           (),
        .obs_data1_to_regs           ()
    );

    //=========================================================================
    // Core-side AXI signals (rd/wr routed to top ports either directly or
    // through the AXI monitor taps depending on USE_AXI_MONITORS)
    //=========================================================================
    // Data read (core master)
    logic [IW-1:0]  core_rd_arid;
    logic [AW-1:0]  core_rd_araddr;
    logic [7:0]     core_rd_arlen;
    logic [2:0]     core_rd_arsize;
    logic [1:0]     core_rd_arburst;
    logic           core_rd_arvalid;
    logic           core_rd_arready;
    logic [IW-1:0]  core_rd_rid;
    logic [DW-1:0]  core_rd_rdata;
    logic [1:0]     core_rd_rresp;
    logic           core_rd_rlast;
    logic           core_rd_rvalid;
    logic           core_rd_rready;
    // Data write (core master)
    logic [IW-1:0]  core_wr_awid;
    logic [AW-1:0]  core_wr_awaddr;
    logic [7:0]     core_wr_awlen;
    logic [2:0]     core_wr_awsize;
    logic [1:0]     core_wr_awburst;
    logic           core_wr_awlock;
    logic [3:0]     core_wr_awcache;
    logic [2:0]     core_wr_awprot;
    logic [3:0]     core_wr_awqos;
    logic [3:0]     core_wr_awregion;
    logic           core_wr_awvalid;
    logic           core_wr_awready;
    logic [DW-1:0]  core_wr_wdata;
    logic [(DW/8)-1:0] core_wr_wstrb;
    logic           core_wr_wlast;
    logic           core_wr_wvalid;
    logic           core_wr_wready;
    logic [IW-1:0]  core_wr_bid;
    logic [1:0]     core_wr_bresp;
    logic           core_wr_bvalid;
    logic           core_wr_bready;

    // Core status (mostly discarded; a couple surfaced at top)
    logic [NC-1:0]        descriptor_engine_idle;
    logic [NC-1:0]        scheduler_idle;
    logic [NC-1:0][6:0]   scheduler_state;
    logic                 cfg_sts_desc_mon_busy;
    logic [7:0]           cfg_sts_desc_mon_active_txns;
    logic [15:0]          cfg_sts_desc_mon_error_count;
    logic [31:0]          cfg_sts_desc_mon_txn_count;
    logic                 cfg_sts_desc_mon_conflict_error;

    // Core raw 64-bit MonBus
    logic          core_mon_valid;
    logic          core_mon_ready;
    logic [63:0]   core_mon_packet;

    //=========================================================================
    // RAPIDS Beats Core
    //=========================================================================
    rapids_core_beats #(
        .NUM_CHANNELS         (NUM_CHANNELS),
        .ADDR_WIDTH           (ADDR_WIDTH),
        .DATA_WIDTH           (DATA_WIDTH),
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .SRAM_DEPTH           (SRAM_DEPTH),
        .AR_MAX_OUTSTANDING   (AR_MAX_OUTSTANDING),
        .AW_MAX_OUTSTANDING   (AW_MAX_OUTSTANDING),
        .MON_MAX_TRANSACTIONS (MON_MAX_TRANSACTIONS)
    ) u_core (
        .clk    (aclk),
        .rst_n  (aresetn),

        // APB kick-off
        .apb_valid (apb_valid),
        .apb_ready (apb_ready),
        .apb_addr  (apb_addr),

        // Configuration
        .cfg_channel_enable         (cfg_channel_enable),
        .cfg_channel_reset          (cfg_channel_reset),
        .cfg_sched_enable           (cfg_sched_enable),
        .cfg_sched_timeout_cycles   (cfg_sched_timeout_cycles),
        .cfg_sched_timeout_limit    (cfg_sched_timeout_limit),
        .cfg_sched_timeout_enable   (cfg_sched_timeout_enable),
        .cfg_sched_err_enable       (cfg_sched_err_enable),
        .cfg_sched_compl_enable     (cfg_sched_compl_enable),
        .cfg_sched_perf_enable      (cfg_sched_perf_enable),
        .cfg_desceng_enable         (cfg_desceng_enable),
        .cfg_desceng_prefetch       (cfg_desceng_prefetch),
        .cfg_desceng_fifo_thresh    (cfg_desceng_fifo_thresh),
        .cfg_desceng_addr0_base     (cfg_desceng_addr0_base),
        .cfg_desceng_addr0_limit    (cfg_desceng_addr0_limit),
        .cfg_desceng_addr1_base     (cfg_desceng_addr1_base),
        .cfg_desceng_addr1_limit    (cfg_desceng_addr1_limit),
        .cfg_desc_mon_enable        (cfg_desc_mon_enable),
        .cfg_desc_mon_err_enable    (cfg_desc_mon_err_enable),
        .cfg_desc_mon_perf_enable   (cfg_desc_mon_perf_enable),
        .cfg_desc_mon_timeout_enable(cfg_desc_mon_timeout_enable),
        .cfg_desc_mon_timeout_cycles(cfg_desc_mon_timeout_cycles),
        .cfg_desc_mon_latency_thresh(cfg_desc_mon_latency_thresh),
        .cfg_desc_mon_pkt_mask      (cfg_desc_mon_pkt_mask),
        .cfg_desc_mon_err_select    (cfg_desc_mon_err_select),
        .cfg_desc_mon_err_mask      (cfg_desc_mon_err_mask),
        .cfg_desc_mon_timeout_mask  (cfg_desc_mon_timeout_mask),
        .cfg_desc_mon_compl_mask    (cfg_desc_mon_compl_mask),
        .cfg_desc_mon_thresh_mask   (cfg_desc_mon_thresh_mask),
        .cfg_desc_mon_perf_mask     (cfg_desc_mon_perf_mask),
        .cfg_desc_mon_addr_mask     (cfg_desc_mon_addr_mask),
        .cfg_desc_mon_debug_mask    (cfg_desc_mon_debug_mask),
        .cfg_axi_rd_xfer_beats      (cfg_axi_rd_xfer_beats),
        .cfg_axi_wr_xfer_beats      (cfg_axi_wr_xfer_beats),

        // Status
        .system_idle                    (system_idle),
        .descriptor_engine_idle         (descriptor_engine_idle),
        .scheduler_idle                 (scheduler_idle),
        .scheduler_state                (scheduler_state),
        .sched_error                    (sched_error),
        .cfg_sts_desc_mon_busy          (cfg_sts_desc_mon_busy),
        .cfg_sts_desc_mon_active_txns   (cfg_sts_desc_mon_active_txns),
        .cfg_sts_desc_mon_error_count   (cfg_sts_desc_mon_error_count),
        .cfg_sts_desc_mon_txn_count     (cfg_sts_desc_mon_txn_count),
        .cfg_sts_desc_mon_conflict_error(cfg_sts_desc_mon_conflict_error),

        // Sink fill interface (straight to top ports)
        .snk_fill_alloc_req  (snk_fill_alloc_req),
        .snk_fill_alloc_size (snk_fill_alloc_size),
        .snk_fill_alloc_id   (snk_fill_alloc_id),
        .snk_fill_space_free (snk_fill_space_free),
        .snk_fill_valid      (snk_fill_valid),
        .snk_fill_ready      (snk_fill_ready),
        .snk_fill_id         (snk_fill_id),
        .snk_fill_data       (snk_fill_data),

        // Source drain interface (straight to top ports)
        .src_drain_data_avail (src_drain_data_avail),
        .src_drain_req        (src_drain_req),
        .src_drain_size       (src_drain_size),
        .src_drain_valid      (src_drain_valid),
        .src_drain_read       (src_drain_read),
        .src_drain_id         (src_drain_id),
        .src_drain_data       (src_drain_data),

        // Descriptor AXI master (straight to top ports)
        .m_axi_desc_arvalid (m_axi_desc_arvalid),
        .m_axi_desc_arready (m_axi_desc_arready),
        .m_axi_desc_araddr  (m_axi_desc_araddr),
        .m_axi_desc_arlen   (m_axi_desc_arlen),
        .m_axi_desc_arsize  (m_axi_desc_arsize),
        .m_axi_desc_arburst (m_axi_desc_arburst),
        .m_axi_desc_arid    (m_axi_desc_arid),
        .m_axi_desc_arlock  (m_axi_desc_arlock),
        .m_axi_desc_arcache (m_axi_desc_arcache),
        .m_axi_desc_arprot  (m_axi_desc_arprot),
        .m_axi_desc_arqos   (m_axi_desc_arqos),
        .m_axi_desc_arregion(m_axi_desc_arregion),
        .m_axi_desc_rvalid  (m_axi_desc_rvalid),
        .m_axi_desc_rready  (m_axi_desc_rready),
        .m_axi_desc_rdata   (m_axi_desc_rdata),
        .m_axi_desc_rresp   (m_axi_desc_rresp),
        .m_axi_desc_rlast   (m_axi_desc_rlast),
        .m_axi_desc_rid     (m_axi_desc_rid),

        // Data read AXI master (core side -> monitor tap or top)
        .m_axi_rd_arid    (core_rd_arid),
        .m_axi_rd_araddr  (core_rd_araddr),
        .m_axi_rd_arlen   (core_rd_arlen),
        .m_axi_rd_arsize  (core_rd_arsize),
        .m_axi_rd_arburst (core_rd_arburst),
        .m_axi_rd_arvalid (core_rd_arvalid),
        .m_axi_rd_arready (core_rd_arready),
        .m_axi_rd_rid     (core_rd_rid),
        .m_axi_rd_rdata   (core_rd_rdata),
        .m_axi_rd_rresp   (core_rd_rresp),
        .m_axi_rd_rlast   (core_rd_rlast),
        .m_axi_rd_rvalid  (core_rd_rvalid),
        .m_axi_rd_rready  (core_rd_rready),

        // Data write AXI master (core side -> monitor tap or top)
        .m_axi_wr_awid    (core_wr_awid),
        .m_axi_wr_awaddr  (core_wr_awaddr),
        .m_axi_wr_awlen   (core_wr_awlen),
        .m_axi_wr_awsize  (core_wr_awsize),
        .m_axi_wr_awburst (core_wr_awburst),
        .m_axi_wr_awlock  (core_wr_awlock),
        .m_axi_wr_awcache (core_wr_awcache),
        .m_axi_wr_awprot  (core_wr_awprot),
        .m_axi_wr_awqos   (core_wr_awqos),
        .m_axi_wr_awregion(core_wr_awregion),
        .m_axi_wr_awvalid (core_wr_awvalid),
        .m_axi_wr_awready (core_wr_awready),
        .m_axi_wr_wdata   (core_wr_wdata),
        .m_axi_wr_wstrb   (core_wr_wstrb),
        .m_axi_wr_wlast   (core_wr_wlast),
        .m_axi_wr_wvalid  (core_wr_wvalid),
        .m_axi_wr_wready  (core_wr_wready),
        .m_axi_wr_bid     (core_wr_bid),
        .m_axi_wr_bresp   (core_wr_bresp),
        .m_axi_wr_bvalid  (core_wr_bvalid),
        .m_axi_wr_bready  (core_wr_bready),

        // Core raw MonBus (64-bit)
        .mon_valid  (core_mon_valid),
        .mon_ready  (core_mon_ready),
        .mon_packet (core_mon_packet),

        // Debug (discarded)
        .dbg_rd_all_complete          (),
        .dbg_r_beats_rcvd             (),
        .dbg_sram_writes              (),
        .dbg_arb_request              (),
        .dbg_snk_sram_bridge_pending  (),
        .dbg_snk_sram_bridge_out_valid(),
        .dbg_src_sram_bridge_pending  (),
        .dbg_src_sram_bridge_out_valid()
    );

    //=========================================================================
    // rd/wr AXI Monitor Block + MonBus arbiter (USE_AXI_MONITORS)
    //=========================================================================
    generate
        if (USE_AXI_MONITORS == 1) begin : g_axi_monitors
            localparam int NUM_MON_SOURCES = 3;  // core, rd tap, wr tap
            monitor_common_pkg::monbus_timestamp_t mon_time_w;
            assign mon_time_w = '0;

            logic                                  mon_v  [NUM_MON_SOURCES];
            logic                                  mon_r  [NUM_MON_SOURCES];
            monitor_common_pkg::monitor_packet_t   mon_p  [NUM_MON_SOURCES];
            monitor_common_pkg::monbus_timestamp_t mon_t  [NUM_MON_SOURCES];

            // Slot 0: core raw 64-bit packet, zero-extended into 128-bit slot.
            assign mon_v[0]      = core_mon_valid;
            assign core_mon_ready = mon_r[0];
            assign mon_p[0]      = {{(monitor_common_pkg::MONBUS_PKT_WIDTH-64){1'b0}}, core_mon_packet};
            assign mon_t[0]      = '0;

            //---------------------------------------------------------------
            // Read tap: core_rd (fub side) -> top m_axi_rd (fabric side)
            //---------------------------------------------------------------
            axi4_master_rd_mon #(
                .AXI_ID_WIDTH    (AXI_ID_WIDTH),
                .AXI_ADDR_WIDTH  (ADDR_WIDTH),
                .AXI_DATA_WIDTH  (DATA_WIDTH),
                .AXI_USER_WIDTH  (1),
                .USE_MONITOR     (1'b1),
                .UNIT_ID         (8'h01),
                .AGENT_ID        (16'h0020),
                .MAX_TRANSACTIONS(MON_MAX_TRANSACTIONS)
            ) u_rd_mon (
                .aclk    (aclk),
                .aresetn (aresetn),
                .cam_clear(cam_clear),
                // fub side (from core)
                .fub_axi_arid    (core_rd_arid),
                .fub_axi_araddr  (core_rd_araddr),
                .fub_axi_arlen   (core_rd_arlen),
                .fub_axi_arsize  (core_rd_arsize),
                .fub_axi_arburst (core_rd_arburst),
                .fub_axi_arlock  (1'b0),
                .fub_axi_arcache (4'b0011),
                .fub_axi_arprot  (3'b000),
                .fub_axi_arqos   (4'b0000),
                .fub_axi_arregion(4'b0000),
                .fub_axi_aruser  (1'b0),
                .fub_axi_arvalid (core_rd_arvalid),
                .fub_axi_arready (core_rd_arready),
                .fub_axi_rid     (core_rd_rid),
                .fub_axi_rdata   (core_rd_rdata),
                .fub_axi_rresp   (core_rd_rresp),
                .fub_axi_rlast   (core_rd_rlast),
                .fub_axi_ruser   (),
                .fub_axi_rvalid  (core_rd_rvalid),
                .fub_axi_rready  (core_rd_rready),
                // m_axi side (to top)
                .m_axi_arid      (m_axi_rd_arid),
                .m_axi_araddr    (m_axi_rd_araddr),
                .m_axi_arlen     (m_axi_rd_arlen),
                .m_axi_arsize    (m_axi_rd_arsize),
                .m_axi_arburst   (m_axi_rd_arburst),
                .m_axi_arlock    (),
                .m_axi_arcache   (),
                .m_axi_arprot    (),
                .m_axi_arqos     (),
                .m_axi_arregion  (),
                .m_axi_aruser    (),
                .m_axi_arvalid   (m_axi_rd_arvalid),
                .m_axi_arready   (m_axi_rd_arready),
                .m_axi_rid       (m_axi_rd_rid),
                .m_axi_rdata     (m_axi_rd_rdata),
                .m_axi_rresp     (m_axi_rd_rresp),
                .m_axi_rlast     (m_axi_rd_rlast),
                .m_axi_ruser     (1'b0),
                .m_axi_rvalid    (m_axi_rd_rvalid),
                .m_axi_rready    (m_axi_rd_rready),
                // Config (from config block; masks tied 0 = leaf pass-through)
                .cfg_monitor_enable   (cfg_rdeng_mon_enable),
                .cfg_error_enable     (cfg_rdeng_mon_err_enable),
                .cfg_timeout_enable   (cfg_rdeng_mon_timeout_enable),
                .cfg_perf_enable      (cfg_rdeng_mon_perf_enable),
                .cfg_compl_enable     (1'b1),
                .cfg_threshold_enable (1'b0),
                .cfg_debug_enable     (1'b0),
                .cfg_timeout_cycles   (cfg_rdeng_mon_timeout_cycles[15:0]),
                .cfg_latency_threshold(cfg_rdeng_mon_latency_thresh),
                .cfg_axi_pkt_mask    ({8'h00, cfg_rdeng_mon_pkt_mask[7:0]}),
                .cfg_axi_err_select  ({12'h000, cfg_rdeng_mon_err_select}),
                .cfg_axi_error_mask  ({8'h00, cfg_rdeng_mon_err_mask}),
                .cfg_axi_timeout_mask({8'h00, cfg_rdeng_mon_timeout_mask}),
                .cfg_axi_compl_mask  ({8'h00, cfg_rdeng_mon_compl_mask}),
                .cfg_axi_thresh_mask ({8'h00, cfg_rdeng_mon_thresh_mask}),
                .cfg_axi_perf_mask   ({8'h00, cfg_rdeng_mon_perf_mask}),
                .cfg_axi_addr_mask   ({8'h00, cfg_rdeng_mon_addr_mask}),
                .cfg_axi_debug_mask  ({8'h00, cfg_rdeng_mon_debug_mask}),
                .cfg_addr_check_enable (1'b0),
                .cfg_addr_range_enable ('0),
                .cfg_addr_range_low    ('0),
                .cfg_addr_range_high   ('0),
                .cfg_start_event_sel   (3'd0),
                .cfg_end_event_sel     (3'd0),
                .cfg_start_trigger     (1'b0),
                .cfg_end_trigger       (1'b0),
                .cfg_window_force_close(1'b0),
                .i_mon_time      (mon_time_w),
                // Monbus output -> arbiter slot 1
                .monbus_valid    (mon_v[1]),
                .monbus_ready    (mon_r[1]),
                .monbus_packet   (mon_p[1]),
                .monbus_timestamp(mon_t[1]),
                .busy                  (),
                .active_transactions   (),
                .error_count           (),
                .transaction_count     (),
                .window_active         (),
                .window_cycles         (),
                .perf_prod_cycles      (),
                .perf_bp_cycles        (),
                .perf_starv_cycles     (),
                .perf_idle_cycles      (),
                .perf_beat_count       (),
                .perf_byte_count       (),
                .perf_burst_count      (),
                .cfg_conflict_error    ()
            );

            //---------------------------------------------------------------
            // Write tap: core_wr (fub side) -> top m_axi_wr (fabric side)
            //---------------------------------------------------------------
            axi4_master_wr_mon #(
                .AXI_ID_WIDTH    (AXI_ID_WIDTH),
                .AXI_ADDR_WIDTH  (ADDR_WIDTH),
                .AXI_DATA_WIDTH  (DATA_WIDTH),
                .AXI_USER_WIDTH  (1),
                .USE_MONITOR     (1'b1),
                .UNIT_ID         (8'h01),
                .AGENT_ID        (16'h0040),
                .MAX_TRANSACTIONS(MON_MAX_TRANSACTIONS)
            ) u_wr_mon (
                .aclk    (aclk),
                .aresetn (aresetn),
                .cam_clear(cam_clear),
                // fub side (from core)
                .fub_axi_awid    (core_wr_awid),
                .fub_axi_awaddr  (core_wr_awaddr),
                .fub_axi_awlen   (core_wr_awlen),
                .fub_axi_awsize  (core_wr_awsize),
                .fub_axi_awburst (core_wr_awburst),
                .fub_axi_awlock  (core_wr_awlock),
                .fub_axi_awcache (core_wr_awcache),
                .fub_axi_awprot  (core_wr_awprot),
                .fub_axi_awqos   (core_wr_awqos),
                .fub_axi_awregion(core_wr_awregion),
                .fub_axi_awuser  (1'b0),
                .fub_axi_awvalid (core_wr_awvalid),
                .fub_axi_awready (core_wr_awready),
                .fub_axi_wdata   (core_wr_wdata),
                .fub_axi_wstrb   (core_wr_wstrb),
                .fub_axi_wlast   (core_wr_wlast),
                .fub_axi_wuser   (1'b0),
                .fub_axi_wvalid  (core_wr_wvalid),
                .fub_axi_wready  (core_wr_wready),
                .fub_axi_bid     (core_wr_bid),
                .fub_axi_bresp   (core_wr_bresp),
                .fub_axi_buser   (),
                .fub_axi_bvalid  (core_wr_bvalid),
                .fub_axi_bready  (core_wr_bready),
                // m_axi side (to top)
                .m_axi_awid      (m_axi_wr_awid),
                .m_axi_awaddr    (m_axi_wr_awaddr),
                .m_axi_awlen     (m_axi_wr_awlen),
                .m_axi_awsize    (m_axi_wr_awsize),
                .m_axi_awburst   (m_axi_wr_awburst),
                .m_axi_awlock    (m_axi_wr_awlock),
                .m_axi_awcache   (m_axi_wr_awcache),
                .m_axi_awprot    (m_axi_wr_awprot),
                .m_axi_awqos     (m_axi_wr_awqos),
                .m_axi_awregion  (m_axi_wr_awregion),
                .m_axi_awuser    (),
                .m_axi_awvalid   (m_axi_wr_awvalid),
                .m_axi_awready   (m_axi_wr_awready),
                .m_axi_wdata     (m_axi_wr_wdata),
                .m_axi_wstrb     (m_axi_wr_wstrb),
                .m_axi_wlast     (m_axi_wr_wlast),
                .m_axi_wuser     (),
                .m_axi_wvalid    (m_axi_wr_wvalid),
                .m_axi_wready    (m_axi_wr_wready),
                .m_axi_bid       (m_axi_wr_bid),
                .m_axi_bresp     (m_axi_wr_bresp),
                .m_axi_buser     (1'b0),
                .m_axi_bvalid    (m_axi_wr_bvalid),
                .m_axi_bready    (m_axi_wr_bready),
                // Config
                .cfg_monitor_enable   (cfg_wreng_mon_enable),
                .cfg_error_enable     (cfg_wreng_mon_err_enable),
                .cfg_timeout_enable   (cfg_wreng_mon_timeout_enable),
                .cfg_perf_enable      (cfg_wreng_mon_perf_enable),
                .cfg_compl_enable     (1'b1),
                .cfg_threshold_enable (1'b0),
                .cfg_debug_enable     (1'b0),
                .cfg_timeout_cycles   (cfg_wreng_mon_timeout_cycles[15:0]),
                .cfg_latency_threshold(cfg_wreng_mon_latency_thresh),
                .cfg_axi_pkt_mask    ({8'h00, cfg_wreng_mon_pkt_mask[7:0]}),
                .cfg_axi_err_select  ({12'h000, cfg_wreng_mon_err_select}),
                .cfg_axi_error_mask  ({8'h00, cfg_wreng_mon_err_mask}),
                .cfg_axi_timeout_mask({8'h00, cfg_wreng_mon_timeout_mask}),
                .cfg_axi_compl_mask  ({8'h00, cfg_wreng_mon_compl_mask}),
                .cfg_axi_thresh_mask ({8'h00, cfg_wreng_mon_thresh_mask}),
                .cfg_axi_perf_mask   ({8'h00, cfg_wreng_mon_perf_mask}),
                .cfg_axi_addr_mask   ({8'h00, cfg_wreng_mon_addr_mask}),
                .cfg_axi_debug_mask  ({8'h00, cfg_wreng_mon_debug_mask}),
                .cfg_addr_check_enable (1'b0),
                .cfg_addr_range_enable ('0),
                .cfg_addr_range_low    ('0),
                .cfg_addr_range_high   ('0),
                .cfg_start_event_sel   (3'd0),
                .cfg_end_event_sel     (3'd0),
                .cfg_start_trigger     (1'b0),
                .cfg_end_trigger       (1'b0),
                .cfg_window_force_close(1'b0),
                .i_mon_time      (mon_time_w),
                // Monbus output -> arbiter slot 2
                .monbus_valid    (mon_v[2]),
                .monbus_ready    (mon_r[2]),
                .monbus_packet   (mon_p[2]),
                .monbus_timestamp(mon_t[2]),
                .busy                  (),
                .active_transactions   (),
                .error_count           (),
                .transaction_count     (),
                .window_active         (),
                .window_cycles         (),
                .perf_prod_cycles      (),
                .perf_bp_cycles        (),
                .perf_starv_cycles     (),
                .perf_idle_cycles      (),
                .perf_beat_count       (),
                .perf_byte_count       (),
                .perf_burst_count      (),
                .cfg_conflict_error    ()
            );

            //---------------------------------------------------------------
            // Merge the three MonBus sources.
            //---------------------------------------------------------------
            monitor_common_pkg::monbus_timestamp_t arb_ts;
            // Combined 128-bit MonBus stream: arbiter -> monbus_axil_axil_group
            logic                                mon_c_valid;
            logic                                mon_c_ready;
            monitor_common_pkg::monitor_packet_t mon_c_packet;
            monbus_arbiter #(
                .CLIENTS            (NUM_MON_SOURCES),
                .INPUT_SKID_ENABLE  (1),
                .OUTPUT_SKID_ENABLE (1),
                .INPUT_SKID_DEPTH   (2),
                .OUTPUT_SKID_DEPTH  (2)
            ) u_arbiter (
                .axi_aclk            (aclk),
                .axi_aresetn         (aresetn),
                .block_arb           (1'b0),
                .monbus_valid_in     (mon_v),
                .monbus_ready_in     (mon_r),
                .monbus_packet_in    (mon_p),
                .monbus_timestamp_in (mon_t),
                .monbus_valid        (mon_c_valid),
                .monbus_ready        (mon_c_ready),
                .monbus_packet       (mon_c_packet),
                .monbus_timestamp    (arb_ts),
                .grant_valid         (),
                .grant               (),
                .grant_id            (),
                .last_grant          ()
            );

            //---------------------------------------------------------------
            // MonBus AXI-Lite Group: combined stream -> AXI-Lite err-drain
            // slave + bulk-capture master + IRQ (mirrors stream_top_ch8).
            //---------------------------------------------------------------
            monitor_common_pkg::monbus_timestamp_t mon_grp_time_w;
            monbus_axil_axil_group #(
                .FIFO_DEPTH_ERR     (64),
                .FIFO_DEPTH_WRITE   (96),
                .ADDR_WIDTH         (32),
                .S_AXIL_DATA_WIDTH  (32),
                .NUM_PROTOCOLS      (3),
                .USE_COMPRESSION    (0),
                .HALF_BEAT_EN       (0)
            ) u_monbus_axil_group (
                .axi_aclk           (aclk),
                .axi_aresetn        (aresetn),
                .cam_clear          (cam_clear),

                // Combined MonBus input (from arbiter)
                .monbus_valid       (mon_c_valid),
                .monbus_ready       (mon_c_ready),
                .monbus_packet      (mon_c_packet),
                .monbus_timestamp   ('0),
                .mon_time_out       (mon_grp_time_w),

                // Error/Interrupt FIFO - AXI-Lite slave read (32-bit)
                .s_axil_arvalid     (s_axil_err_arvalid),
                .s_axil_arready     (s_axil_err_arready),
                .s_axil_araddr      (s_axil_err_araddr),
                .s_axil_arprot      (s_axil_err_arprot),
                .s_axil_rvalid      (s_axil_err_rvalid),
                .s_axil_rready      (s_axil_err_rready),
                .s_axil_rdata       (s_axil_err_rdata),
                .s_axil_rresp       (s_axil_err_rresp),

                // Bulk-capture - AXI-Lite master write (64-bit)
                .m_axil_awvalid     (m_axil_mon_awvalid),
                .m_axil_awready     (m_axil_mon_awready),
                .m_axil_awaddr      (m_axil_mon_awaddr),
                .m_axil_awprot      (m_axil_mon_awprot),
                .m_axil_wvalid      (m_axil_mon_wvalid),
                .m_axil_wready      (m_axil_mon_wready),
                .m_axil_wdata       (m_axil_mon_wdata),
                .m_axil_wstrb       (m_axil_mon_wstrb),
                .m_axil_bvalid      (m_axil_mon_bvalid),
                .m_axil_bready      (m_axil_mon_bready),
                .m_axil_bresp       (m_axil_mon_bresp),

                .irq_out            (mon_irq),

                // Config (base/limit/watermark from top-level inputs;
                // compression enable from WRMON_ENABLE.COMPRESS_EN).
                .cfg_base_addr      (cfg_mon_base_addr),
                .cfg_limit_addr     (cfg_mon_limit_addr),
                .cfg_flush_watermark(cfg_mon_flush_watermark),
                .cfg_compress_en    (hwif_out.MON.WRMON_ENABLE.COMPRESS_EN.value),

                //-------------------------------------------------------------
                // Protocol 0 - Descriptor AXI Monitor (DAXMON). Group masks are
                // 16-bit; the rapids MON fields are narrower (PKT=16, ERR_SEL=4,
                // others=8) so zero-extend to 16 to match the leaf-monitor style.
                //-------------------------------------------------------------
                .cfg_axi_pkt_mask     (hwif_out.MON.DAXMON_PKT_MASK.PKT_MASK.value),
                .cfg_axi_err_select   ({12'h000, hwif_out.MON.DAXMON_ERR_CFG.ERR_SELECT.value}),
                .cfg_axi_error_mask   ({8'h00,   hwif_out.MON.DAXMON_ERR_CFG.ERR_MASK.value}),
                .cfg_axi_timeout_mask ({8'h00,   hwif_out.MON.DAXMON_MASK1.TIMEOUT_MASK.value}),
                .cfg_axi_compl_mask   ({8'h00,   hwif_out.MON.DAXMON_MASK1.COMPL_MASK.value}),
                .cfg_axi_thresh_mask  ({8'h00,   hwif_out.MON.DAXMON_MASK2.THRESH_MASK.value}),
                .cfg_axi_perf_mask    ({8'h00,   hwif_out.MON.DAXMON_MASK2.PERF_MASK.value}),
                .cfg_axi_addr_mask    ({8'h00,   hwif_out.MON.DAXMON_MASK3.ADDR_MASK.value}),
                .cfg_axi_debug_mask   ({8'h00,   hwif_out.MON.DAXMON_MASK3.DEBUG_MASK.value}),

                //-------------------------------------------------------------
                // Protocol 1 - Read Engine Monitor (RDMON). AXIS ports reused
                // (Thresh->Credit, Perf->Channel, Addr->Stream), mirroring stream.
                //-------------------------------------------------------------
                .cfg_axis_pkt_mask    (hwif_out.MON.RDMON_PKT_MASK.PKT_MASK.value),
                .cfg_axis_err_select  ({12'h000, hwif_out.MON.RDMON_ERR_CFG.ERR_SELECT.value}),
                .cfg_axis_error_mask  ({8'h00,   hwif_out.MON.RDMON_ERR_CFG.ERR_MASK.value}),
                .cfg_axis_timeout_mask({8'h00,   hwif_out.MON.RDMON_MASK1.TIMEOUT_MASK.value}),
                .cfg_axis_compl_mask  ({8'h00,   hwif_out.MON.RDMON_MASK1.COMPL_MASK.value}),
                .cfg_axis_credit_mask ({8'h00,   hwif_out.MON.RDMON_MASK2.THRESH_MASK.value}),
                .cfg_axis_channel_mask({8'h00,   hwif_out.MON.RDMON_MASK2.PERF_MASK.value}),
                .cfg_axis_stream_mask ({8'h00,   hwif_out.MON.RDMON_MASK3.ADDR_MASK.value}),

                //-------------------------------------------------------------
                // Protocol 2 - Write Engine Monitor (WRMON). CORE ports reused,
                // mirroring stream.
                //-------------------------------------------------------------
                .cfg_core_pkt_mask    (hwif_out.MON.WRMON_PKT_MASK.PKT_MASK.value),
                .cfg_core_err_select  ({12'h000, hwif_out.MON.WRMON_ERR_CFG.ERR_SELECT.value}),
                .cfg_core_error_mask  ({8'h00,   hwif_out.MON.WRMON_ERR_CFG.ERR_MASK.value}),
                .cfg_core_timeout_mask({8'h00,   hwif_out.MON.WRMON_MASK1.TIMEOUT_MASK.value}),
                .cfg_core_compl_mask  ({8'h00,   hwif_out.MON.WRMON_MASK1.COMPL_MASK.value}),
                .cfg_core_thresh_mask ({8'h00,   hwif_out.MON.WRMON_MASK2.THRESH_MASK.value}),
                .cfg_core_perf_mask   ({8'h00,   hwif_out.MON.WRMON_MASK2.PERF_MASK.value}),
                .cfg_core_debug_mask  ({8'h00,   hwif_out.MON.WRMON_MASK3.DEBUG_MASK.value}),

                // Status / compressor stats: unused at this level.
                /* verilator lint_off PINCONNECTEMPTY */
                .err_fifo_full      (),
                .write_fifo_full    (),
                .err_fifo_count     (),
                .write_fifo_count   (),
                .mon_compressor_stat_tier1_a        (),
                .mon_compressor_stat_tier1_b        (),
                .mon_compressor_stat_tier1_c        (),
                .mon_compressor_stat_tier0          (),
                .mon_compressor_stat_cam_miss       (),
                .mon_compressor_stat_delta_ts_ovf   (),
                .mon_compressor_stat_event_data_ovf (),
                .mon_compressor_stat_ed_delta_ovf   ()
                /* verilator lint_on PINCONNECTEMPTY */
            );
        end else begin : g_no_axi_monitors
            // No AXI taps: core rd/wr AXI connect directly to top ports, and
            // the core's raw 64-bit MonBus is zero-extended and passed through.
            // Read
            assign m_axi_rd_arid    = core_rd_arid;
            assign m_axi_rd_araddr  = core_rd_araddr;
            assign m_axi_rd_arlen   = core_rd_arlen;
            assign m_axi_rd_arsize  = core_rd_arsize;
            assign m_axi_rd_arburst = core_rd_arburst;
            assign m_axi_rd_arvalid = core_rd_arvalid;
            assign core_rd_arready  = m_axi_rd_arready;
            assign core_rd_rid      = m_axi_rd_rid;
            assign core_rd_rdata    = m_axi_rd_rdata;
            assign core_rd_rresp    = m_axi_rd_rresp;
            assign core_rd_rlast    = m_axi_rd_rlast;
            assign core_rd_rvalid   = m_axi_rd_rvalid;
            assign m_axi_rd_rready  = core_rd_rready;
            // Write
            assign m_axi_wr_awid     = core_wr_awid;
            assign m_axi_wr_awaddr   = core_wr_awaddr;
            assign m_axi_wr_awlen    = core_wr_awlen;
            assign m_axi_wr_awsize   = core_wr_awsize;
            assign m_axi_wr_awburst  = core_wr_awburst;
            assign m_axi_wr_awlock   = core_wr_awlock;
            assign m_axi_wr_awcache  = core_wr_awcache;
            assign m_axi_wr_awprot   = core_wr_awprot;
            assign m_axi_wr_awqos    = core_wr_awqos;
            assign m_axi_wr_awregion = core_wr_awregion;
            assign m_axi_wr_awvalid  = core_wr_awvalid;
            assign core_wr_awready   = m_axi_wr_awready;
            assign m_axi_wr_wdata    = core_wr_wdata;
            assign m_axi_wr_wstrb    = core_wr_wstrb;
            assign m_axi_wr_wlast    = core_wr_wlast;
            assign m_axi_wr_wvalid   = core_wr_wvalid;
            assign core_wr_wready    = m_axi_wr_wready;
            assign core_wr_bid       = m_axi_wr_bid;
            assign core_wr_bresp     = m_axi_wr_bresp;
            assign core_wr_bvalid    = m_axi_wr_bvalid;
            assign m_axi_wr_bready   = core_wr_bready;
            // MonBus disabled: drop the core's MonBus and tie off the
            // AXI-Lite group interfaces (mirrors stream_top_ch8 g_monbus_tieoff).
            assign core_mon_ready = 1'b1;   // Always ready (backpressure disabled)
            assign mon_irq        = 1'b0;   // No interrupts

            // AXI-Lite error-drain slave outputs
            assign s_axil_err_arready = 1'b1;
            assign s_axil_err_rvalid  = 1'b0;
            assign s_axil_err_rdata   = 32'h0;
            assign s_axil_err_rresp   = 2'b00;

            // AXI-Lite capture master outputs
            assign m_axil_mon_awvalid = 1'b0;
            assign m_axil_mon_awaddr  = 32'h0;
            assign m_axil_mon_awprot  = 3'b000;
            assign m_axil_mon_wvalid  = 1'b0;
            assign m_axil_mon_wdata   = 64'h0;
            assign m_axil_mon_wstrb   = 8'h0;
            assign m_axil_mon_bready  = 1'b0;
        end
    endgenerate

endmodule : rapids_beats_top
