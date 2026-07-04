// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_beats_top
// Purpose: Top-level wrapper for the RAPIDS "beats" DMA engine (SPLIT core).
//
// Description:
//   Integrates the now-split RAPIDS beats core (rapids_core_beats), which is a
//   thin wrapper over two WHOLLY INDEPENDENT half engines:
//     - SOURCE half (memory -> AXIS, read-only)
//     - SINK   half (AXIS -> memory, write-only)
//
//   Each half owns its own scheduler array, descriptor engine, data path and
//   monitor arbiter. The core exposes the shared-infrastructure ports twice
//   (src_ / snk_ prefixed), direction-unique data ports once, and a SINGLE
//   merged monitor stream (arbitration lives inside the core).
//
//   Integration hierarchy:
//     APB4 slave (s_apb_*)
//       -> apb_slave  (APB -> CMD/RSP, single clock domain: pclk = aclk)
//       -> cmd demux (hand-written, 3-way):
//            0x000-0x03F  -> apbtodescr (u_kick_src)  -> core.src_apb_*
//            0x1000-0x103F-> apbtodescr (u_kick_snk)  -> core.snk_apb_*
//            all others   -> peakrdl_to_cmdrsp -> rapids_regs
//       -> rapids_config_block x2 (u_cfg_src <- hwif_out.SRC.*,
//                                  u_cfg_snk <- hwif_out.SNK.*)
//       -> rapids_core_beats (two independent halves)
//       -> monbus_axil_axil_group (single merged MonBus -> AXI-Lite drain /
//                                  bulk-capture master / IRQ)
//
//   APB address map (13-bit APB address; bit[12] selects SRC(0)/SNK(1)):
//     0x0000-0x003F : SOURCE channel kick-off (apbtodescr u_kick_src)
//     0x0040-0x0FFF : SOURCE configuration registers (rapids_regs SRC)
//     0x1000-0x103F : SINK   channel kick-off (apbtodescr u_kick_snk)
//     0x1040-0x1FFF : SINK   configuration registers (rapids_regs SNK)
//
//   NOTE on the single MonBus egress config: the two halves each emit their own
//   monitor stream; the core merges them into ONE stream. The downstream
//   monbus_axil_axil_group packet-filter/compression config is therefore a
//   single shared egress config, sourced from hwif_out.SRC.MON.* (the SNK.MON.*
//   filter fields exist in the register block but are not wired to the shared
//   egress; per-half egress splitting is a later stage).
//
// Author: sean galloway
// Created: 2026-07-02
// Rewritten for split core: 2026-07-03

`timescale 1ns / 1ps

`include "rapids_imports.svh"
`include "reset_defs.svh"

module rapids_beats_top #(
    parameter int NUM_CHANNELS   = 8,
    parameter int DATA_WIDTH     = 512,
    parameter int ADDR_WIDTH     = 64,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int SRAM_DEPTH     = 4096,
    // APB is now 13-bit: bit[12] selects the SRC(0) / SNK(1) half.
    parameter int APB_ADDR_WIDTH = 13,
    parameter int APB_DATA_WIDTH = 32,
    // Monitor sizing (in-core descriptor AXI monitors)
    parameter int MON_MAX_TRANSACTIONS = 16,
    parameter int AR_MAX_OUTSTANDING   = 8,
    parameter int AW_MAX_OUTSTANDING   = 8,
    // AXIS network-interface parameters (tid carries the channel id)
    parameter int AXIS_ID_WIDTH   = 8,
    parameter int AXIS_DEST_WIDTH = 4,
    parameter int AXIS_USER_WIDTH = 1,
    // Short aliases / derived
    parameter int NC  = NUM_CHANNELS,
    parameter int AW  = ADDR_WIDTH,
    parameter int DW  = DATA_WIDTH,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int CIW = (NC > 1) ? $clog2(NC) : 1,
    parameter int SCW = $clog2(SRAM_DEPTH) + 1,
    parameter int SW  = DW / 8
) (
    //-------------------------------------------------------------------------
    // Clock and Reset
    //-------------------------------------------------------------------------
    input  logic                                    aclk,
    input  logic                                    aresetn,
    // Sync clear of the MonBus AXI-Lite group transaction CAMs.
    input  logic                                    cam_clear,

    //-------------------------------------------------------------------------
    // APB4 Configuration Interface (single clock domain: pclk = aclk)
    //   13-bit address: bit[12] selects SRC(0)/SNK(1) half.
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

    //=========================================================================
    // SOURCE half - Descriptor Fetch AXI Master (FIXED 256-bit read data)
    //=========================================================================
    output logic [IW-1:0]                           src_m_axi_desc_arid,
    output logic [AW-1:0]                           src_m_axi_desc_araddr,
    output logic [7:0]                              src_m_axi_desc_arlen,
    output logic [2:0]                              src_m_axi_desc_arsize,
    output logic [1:0]                              src_m_axi_desc_arburst,
    output logic                                    src_m_axi_desc_arlock,
    output logic [3:0]                              src_m_axi_desc_arcache,
    output logic [2:0]                              src_m_axi_desc_arprot,
    output logic [3:0]                              src_m_axi_desc_arqos,
    output logic [3:0]                              src_m_axi_desc_arregion,
    output logic                                    src_m_axi_desc_arvalid,
    input  logic                                    src_m_axi_desc_arready,
    input  logic [IW-1:0]                           src_m_axi_desc_rid,
    input  logic [255:0]                            src_m_axi_desc_rdata,
    input  logic [1:0]                              src_m_axi_desc_rresp,
    input  logic                                    src_m_axi_desc_rlast,
    input  logic                                    src_m_axi_desc_rvalid,
    output logic                                    src_m_axi_desc_rready,

    //=========================================================================
    // SINK half - Descriptor Fetch AXI Master (FIXED 256-bit read data)
    //=========================================================================
    output logic [IW-1:0]                           snk_m_axi_desc_arid,
    output logic [AW-1:0]                           snk_m_axi_desc_araddr,
    output logic [7:0]                              snk_m_axi_desc_arlen,
    output logic [2:0]                              snk_m_axi_desc_arsize,
    output logic [1:0]                              snk_m_axi_desc_arburst,
    output logic                                    snk_m_axi_desc_arlock,
    output logic [3:0]                              snk_m_axi_desc_arcache,
    output logic [2:0]                              snk_m_axi_desc_arprot,
    output logic [3:0]                              snk_m_axi_desc_arqos,
    output logic [3:0]                              snk_m_axi_desc_arregion,
    output logic                                    snk_m_axi_desc_arvalid,
    input  logic                                    snk_m_axi_desc_arready,
    input  logic [IW-1:0]                           snk_m_axi_desc_rid,
    input  logic [255:0]                            snk_m_axi_desc_rdata,
    input  logic [1:0]                              snk_m_axi_desc_rresp,
    input  logic                                    snk_m_axi_desc_rlast,
    input  logic                                    snk_m_axi_desc_rvalid,
    output logic                                    snk_m_axi_desc_rready,

    //=========================================================================
    // SOURCE half - Control Read / Write AXI Master (32-bit) [Phase 2]
    //=========================================================================
    output logic                                    src_m_axi_ctrlrd_arvalid,
    input  logic                                    src_m_axi_ctrlrd_arready,
    output logic [AW-1:0]                           src_m_axi_ctrlrd_araddr,
    output logic [7:0]                              src_m_axi_ctrlrd_arlen,
    output logic [2:0]                              src_m_axi_ctrlrd_arsize,
    output logic [1:0]                              src_m_axi_ctrlrd_arburst,
    output logic [IW-1:0]                           src_m_axi_ctrlrd_arid,
    output logic                                    src_m_axi_ctrlrd_arlock,
    output logic [3:0]                              src_m_axi_ctrlrd_arcache,
    output logic [2:0]                              src_m_axi_ctrlrd_arprot,
    output logic [3:0]                              src_m_axi_ctrlrd_arqos,
    output logic [3:0]                              src_m_axi_ctrlrd_arregion,
    input  logic                                    src_m_axi_ctrlrd_rvalid,
    output logic                                    src_m_axi_ctrlrd_rready,
    input  logic [31:0]                             src_m_axi_ctrlrd_rdata,
    input  logic [1:0]                              src_m_axi_ctrlrd_rresp,
    input  logic                                    src_m_axi_ctrlrd_rlast,
    input  logic [IW-1:0]                           src_m_axi_ctrlrd_rid,

    output logic                                    src_m_axi_ctrlwr_awvalid,
    input  logic                                    src_m_axi_ctrlwr_awready,
    output logic [AW-1:0]                           src_m_axi_ctrlwr_awaddr,
    output logic [7:0]                              src_m_axi_ctrlwr_awlen,
    output logic [2:0]                              src_m_axi_ctrlwr_awsize,
    output logic [1:0]                              src_m_axi_ctrlwr_awburst,
    output logic [IW-1:0]                           src_m_axi_ctrlwr_awid,
    output logic                                    src_m_axi_ctrlwr_awlock,
    output logic [3:0]                              src_m_axi_ctrlwr_awcache,
    output logic [2:0]                              src_m_axi_ctrlwr_awprot,
    output logic [3:0]                              src_m_axi_ctrlwr_awqos,
    output logic [3:0]                              src_m_axi_ctrlwr_awregion,
    output logic                                    src_m_axi_ctrlwr_wvalid,
    input  logic                                    src_m_axi_ctrlwr_wready,
    output logic [31:0]                             src_m_axi_ctrlwr_wdata,
    output logic [3:0]                              src_m_axi_ctrlwr_wstrb,
    output logic                                    src_m_axi_ctrlwr_wlast,
    input  logic                                    src_m_axi_ctrlwr_bvalid,
    output logic                                    src_m_axi_ctrlwr_bready,
    input  logic [IW-1:0]                           src_m_axi_ctrlwr_bid,
    input  logic [1:0]                              src_m_axi_ctrlwr_bresp,

    //=========================================================================
    // SINK half - Control Read / Write AXI Master (32-bit) [Phase 2]
    //=========================================================================
    output logic                                    snk_m_axi_ctrlrd_arvalid,
    input  logic                                    snk_m_axi_ctrlrd_arready,
    output logic [AW-1:0]                           snk_m_axi_ctrlrd_araddr,
    output logic [7:0]                              snk_m_axi_ctrlrd_arlen,
    output logic [2:0]                              snk_m_axi_ctrlrd_arsize,
    output logic [1:0]                              snk_m_axi_ctrlrd_arburst,
    output logic [IW-1:0]                           snk_m_axi_ctrlrd_arid,
    output logic                                    snk_m_axi_ctrlrd_arlock,
    output logic [3:0]                              snk_m_axi_ctrlrd_arcache,
    output logic [2:0]                              snk_m_axi_ctrlrd_arprot,
    output logic [3:0]                              snk_m_axi_ctrlrd_arqos,
    output logic [3:0]                              snk_m_axi_ctrlrd_arregion,
    input  logic                                    snk_m_axi_ctrlrd_rvalid,
    output logic                                    snk_m_axi_ctrlrd_rready,
    input  logic [31:0]                             snk_m_axi_ctrlrd_rdata,
    input  logic [1:0]                              snk_m_axi_ctrlrd_rresp,
    input  logic                                    snk_m_axi_ctrlrd_rlast,
    input  logic [IW-1:0]                           snk_m_axi_ctrlrd_rid,

    output logic                                    snk_m_axi_ctrlwr_awvalid,
    input  logic                                    snk_m_axi_ctrlwr_awready,
    output logic [AW-1:0]                           snk_m_axi_ctrlwr_awaddr,
    output logic [7:0]                              snk_m_axi_ctrlwr_awlen,
    output logic [2:0]                              snk_m_axi_ctrlwr_awsize,
    output logic [1:0]                              snk_m_axi_ctrlwr_awburst,
    output logic [IW-1:0]                           snk_m_axi_ctrlwr_awid,
    output logic                                    snk_m_axi_ctrlwr_awlock,
    output logic [3:0]                              snk_m_axi_ctrlwr_awcache,
    output logic [2:0]                              snk_m_axi_ctrlwr_awprot,
    output logic [3:0]                              snk_m_axi_ctrlwr_awqos,
    output logic [3:0]                              snk_m_axi_ctrlwr_awregion,
    output logic                                    snk_m_axi_ctrlwr_wvalid,
    input  logic                                    snk_m_axi_ctrlwr_wready,
    output logic [31:0]                             snk_m_axi_ctrlwr_wdata,
    output logic [3:0]                              snk_m_axi_ctrlwr_wstrb,
    output logic                                    snk_m_axi_ctrlwr_wlast,
    input  logic                                    snk_m_axi_ctrlwr_bvalid,
    output logic                                    snk_m_axi_ctrlwr_bready,
    input  logic [IW-1:0]                           snk_m_axi_ctrlwr_bid,
    input  logic [1:0]                              snk_m_axi_ctrlwr_bresp,

    //-------------------------------------------------------------------------
    // SOURCE data - AXI4 Master Data Read (Memory -> Source SRAM)
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
    // SINK data - AXI4 Master Data Write (Sink SRAM -> Memory)
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
    // Sink Path - AXIS Slave Interface (External network -> SRAM); tid = channel
    //-------------------------------------------------------------------------
    input  logic [DW-1:0]                           s_axis_tdata,
    input  logic [SW-1:0]                           s_axis_tstrb,
    input  logic                                    s_axis_tlast,
    input  logic [AXIS_ID_WIDTH-1:0]                s_axis_tid,
    input  logic [AXIS_DEST_WIDTH-1:0]              s_axis_tdest,
    input  logic [AXIS_USER_WIDTH-1:0]              s_axis_tuser,
    input  logic                                    s_axis_tvalid,
    output logic                                    s_axis_tready,

    //-------------------------------------------------------------------------
    // Source Path - AXIS Master Interface (SRAM -> External network); tid = channel
    //-------------------------------------------------------------------------
    output logic [DW-1:0]                           m_axis_tdata,
    output logic [SW-1:0]                           m_axis_tstrb,
    output logic                                    m_axis_tlast,
    output logic [AXIS_ID_WIDTH-1:0]                m_axis_tid,
    output logic [AXIS_DEST_WIDTH-1:0]              m_axis_tdest,
    output logic [AXIS_USER_WIDTH-1:0]              m_axis_tuser,
    output logic                                    m_axis_tvalid,
    input  logic                                    m_axis_tready,

    //-------------------------------------------------------------------------
    // MonBus AXI-Lite Group (single merged egress; mirrors stream_top_ch8)
    //   - AXI-Lite error-drain slave (32-bit data): CPU reads err/IRQ FIFO
    //   - AXI-Lite capture master   (64-bit data): monitor bulk-trace writes
    //   - Single interrupt output (mon_irq)
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
    // Status (per-half top-level observation)
    //-------------------------------------------------------------------------
    output logic                                    src_system_idle,
    output logic [NC-1:0]                           src_sched_error,
    output logic                                    snk_system_idle,
    output logic [NC-1:0]                           snk_sched_error
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
    // Hand-written CMD/RSP 3-way demux
    //   - SRC kick   : 0x000-0x03F   (paddr[12:6] == 0)
    //   - SNK kick   : 0x1000-0x103F (paddr[12]==1, paddr[11:6] == 0)
    //   - Registers  : everything else -> peakrdl register chain
    //
    // APB is single-outstanding (apb_slave issues one CMD and waits for its
    // RSP), so a combinational demux on the address is safe: exactly one sink
    // sees CMD.valid at a time, and exactly one sink asserts RSP.valid.
    //=========================================================================
    localparam int KICK_WIN_LSB = 6;  // 0x40-byte kick window per half

    logic sel_kick_src, sel_kick_snk, sel_regs;
    assign sel_kick_src = (apb_cmd_paddr[APB_ADDR_WIDTH-1:KICK_WIN_LSB] == '0);
    assign sel_kick_snk = (apb_cmd_paddr[APB_ADDR_WIDTH-1] == 1'b1) &&
                          (apb_cmd_paddr[APB_ADDR_WIDTH-2:KICK_WIN_LSB] == '0);
    assign sel_regs     = ~(sel_kick_src | sel_kick_snk);

    // ---- SRC kick-off CMD/RSP ----
    logic                          kick_src_cmd_valid;
    logic                          kick_src_cmd_ready;
    logic                          kick_src_rsp_valid;
    logic [APB_DATA_WIDTH-1:0]     kick_src_rsp_prdata;
    logic                          kick_src_rsp_pslverr;

    // ---- SNK kick-off CMD/RSP ----
    logic                          kick_snk_cmd_valid;
    logic                          kick_snk_cmd_ready;
    logic                          kick_snk_rsp_valid;
    logic [APB_DATA_WIDTH-1:0]     kick_snk_rsp_prdata;
    logic                          kick_snk_rsp_pslverr;

    // ---- Register chain CMD/RSP ----
    logic                          peakrdl_cmd_valid;
    logic                          peakrdl_cmd_ready;
    logic                          peakrdl_rsp_valid;
    logic                          peakrdl_rsp_ready;
    logic [APB_DATA_WIDTH-1:0]     peakrdl_rsp_prdata;
    logic                          peakrdl_rsp_pslverr;

    // CMD valid steering
    assign kick_src_cmd_valid = apb_cmd_valid & sel_kick_src;
    assign kick_snk_cmd_valid = apb_cmd_valid & sel_kick_snk;
    assign peakrdl_cmd_valid  = apb_cmd_valid & sel_regs;

    // CMD ready mux back to apb_slave
    assign apb_cmd_ready = sel_kick_src ? kick_src_cmd_ready :
                           sel_kick_snk ? kick_snk_cmd_ready :
                                          peakrdl_cmd_ready;

    // RSP mux (only one sink responds per outstanding transaction)
    assign apb_rsp_valid   = kick_src_rsp_valid | kick_snk_rsp_valid | peakrdl_rsp_valid;
    assign apb_rsp_prdata  = kick_src_rsp_valid ? kick_src_rsp_prdata  :
                             kick_snk_rsp_valid ? kick_snk_rsp_prdata  :
                                                  peakrdl_rsp_prdata;
    assign apb_rsp_pslverr = kick_src_rsp_valid ? kick_src_rsp_pslverr :
                             kick_snk_rsp_valid ? kick_snk_rsp_pslverr :
                                                  peakrdl_rsp_pslverr;
    // RSP ready fanout
    assign peakrdl_rsp_ready = apb_rsp_ready;

    //=========================================================================
    // SOURCE channel kick-off (apbtodescr) -> core.src_apb_*
    //=========================================================================
    logic [NC-1:0]          src_apb_valid;
    logic [NC-1:0]          src_apb_ready;
    logic [NC-1:0][AW-1:0]  src_apb_addr;

    apbtodescr #(
        .ADDR_WIDTH      (APB_ADDR_WIDTH),
        .DATA_WIDTH      (APB_DATA_WIDTH),
        .NUM_CHANNELS    (NUM_CHANNELS),
        .DESC_ADDR_WIDTH (ADDR_WIDTH)
    ) u_kick_src (
        .clk            (aclk),
        .rst_n          (aresetn),
        .apb_cmd_valid  (kick_src_cmd_valid),
        .apb_cmd_ready  (kick_src_cmd_ready),
        .apb_cmd_addr   (apb_cmd_paddr),
        .apb_cmd_wdata  (apb_cmd_pwdata),
        .apb_cmd_write  (apb_cmd_pwrite),
        .apb_rsp_valid  (kick_src_rsp_valid),
        .apb_rsp_ready  (apb_rsp_ready),
        .apb_rsp_rdata  (kick_src_rsp_prdata),
        .apb_rsp_error  (kick_src_rsp_pslverr),
        .desc_apb_valid (src_apb_valid),
        .desc_apb_ready (src_apb_ready),
        .desc_apb_addr  (src_apb_addr),
        .apb_descriptor_kickoff_hit ()
    );

    //=========================================================================
    // SINK channel kick-off (apbtodescr) -> core.snk_apb_*
    //=========================================================================
    logic [NC-1:0]          snk_apb_valid;
    logic [NC-1:0]          snk_apb_ready;
    logic [NC-1:0][AW-1:0]  snk_apb_addr;

    apbtodescr #(
        .ADDR_WIDTH      (APB_ADDR_WIDTH),
        .DATA_WIDTH      (APB_DATA_WIDTH),
        .NUM_CHANNELS    (NUM_CHANNELS),
        .DESC_ADDR_WIDTH (ADDR_WIDTH)
    ) u_kick_snk (
        .clk            (aclk),
        .rst_n          (aresetn),
        .apb_cmd_valid  (kick_snk_cmd_valid),
        .apb_cmd_ready  (kick_snk_cmd_ready),
        .apb_cmd_addr   (apb_cmd_paddr),
        .apb_cmd_wdata  (apb_cmd_pwdata),
        .apb_cmd_write  (apb_cmd_pwrite),
        .apb_rsp_valid  (kick_snk_rsp_valid),
        .apb_rsp_ready  (apb_rsp_ready),
        .apb_rsp_rdata  (kick_snk_rsp_prdata),
        .apb_rsp_error  (kick_snk_rsp_pslverr),
        .desc_apb_valid (snk_apb_valid),
        .desc_apb_ready (snk_apb_ready),
        .desc_apb_addr  (snk_apb_addr),
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
        .cmd_pwrite         (apb_cmd_pwrite),
        .cmd_paddr          (apb_cmd_paddr),
        .cmd_pwdata         (apb_cmd_pwdata),
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
    // PeakRDL Register Block (rapids_regs) - split SRC / SNK
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
        .s_cpuif_addr           (regblk_addr),  // 13-bit
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
    // Configuration for the SOURCE half (u_cfg_src <- hwif_out.SRC.*)
    //=========================================================================
    logic [NC-1:0]  src_cfg_channel_enable;
    logic [NC-1:0]  src_cfg_channel_reset;
    logic           src_cfg_sched_enable;
    logic [31:0]    src_cfg_sched_timeout_cycles;
    logic [7:0]     src_cfg_sched_timeout_limit;
    logic           src_cfg_sched_timeout_enable;
    logic           src_cfg_sched_err_enable;
    logic           src_cfg_sched_compl_enable;
    logic           src_cfg_sched_perf_enable;
    logic           src_cfg_desceng_enable;
    logic           src_cfg_desceng_prefetch;
    logic [3:0]     src_cfg_desceng_fifo_thresh;
    logic [8:0]     src_cfg_ctrlrd_max_try;
    logic [AW-1:0]  src_cfg_desceng_addr0_base;
    logic [AW-1:0]  src_cfg_desceng_addr0_limit;
    logic [AW-1:0]  src_cfg_desceng_addr1_base;
    logic [AW-1:0]  src_cfg_desceng_addr1_limit;
    logic           src_cfg_desc_mon_enable;
    logic           src_cfg_desc_mon_err_enable;
    logic           src_cfg_desc_mon_perf_enable;
    logic           src_cfg_desc_mon_timeout_enable;
    logic [31:0]    src_cfg_desc_mon_timeout_cycles;
    logic [31:0]    src_cfg_desc_mon_latency_thresh;
    logic [15:0]    src_cfg_desc_mon_pkt_mask;
    logic [3:0]     src_cfg_desc_mon_err_select;
    logic [7:0]     src_cfg_desc_mon_err_mask;
    logic [7:0]     src_cfg_desc_mon_timeout_mask;
    logic [7:0]     src_cfg_desc_mon_compl_mask;
    logic [7:0]     src_cfg_desc_mon_thresh_mask;
    logic [7:0]     src_cfg_desc_mon_perf_mask;
    logic [7:0]     src_cfg_desc_mon_addr_mask;
    logic [7:0]     src_cfg_desc_mon_debug_mask;
    logic [7:0]     src_cfg_axi_rd_xfer_beats;  // used by source half
    logic [7:0]     src_cfg_drain_size;         // used by source half

    //=========================================================================
    // Configuration for the SINK half (u_cfg_snk <- hwif_out.SNK.*)
    //=========================================================================
    logic [NC-1:0]  snk_cfg_channel_enable;
    logic [NC-1:0]  snk_cfg_channel_reset;
    logic           snk_cfg_sched_enable;
    logic [31:0]    snk_cfg_sched_timeout_cycles;
    logic [7:0]     snk_cfg_sched_timeout_limit;
    logic           snk_cfg_sched_timeout_enable;
    logic           snk_cfg_sched_err_enable;
    logic           snk_cfg_sched_compl_enable;
    logic           snk_cfg_sched_perf_enable;
    logic           snk_cfg_desceng_enable;
    logic           snk_cfg_desceng_prefetch;
    logic [3:0]     snk_cfg_desceng_fifo_thresh;
    logic [8:0]     snk_cfg_ctrlrd_max_try;
    logic [AW-1:0]  snk_cfg_desceng_addr0_base;
    logic [AW-1:0]  snk_cfg_desceng_addr0_limit;
    logic [AW-1:0]  snk_cfg_desceng_addr1_base;
    logic [AW-1:0]  snk_cfg_desceng_addr1_limit;
    logic           snk_cfg_desc_mon_enable;
    logic           snk_cfg_desc_mon_err_enable;
    logic           snk_cfg_desc_mon_perf_enable;
    logic           snk_cfg_desc_mon_timeout_enable;
    logic [31:0]    snk_cfg_desc_mon_timeout_cycles;
    logic [31:0]    snk_cfg_desc_mon_latency_thresh;
    logic [15:0]    snk_cfg_desc_mon_pkt_mask;
    logic [3:0]     snk_cfg_desc_mon_err_select;
    logic [7:0]     snk_cfg_desc_mon_err_mask;
    logic [7:0]     snk_cfg_desc_mon_timeout_mask;
    logic [7:0]     snk_cfg_desc_mon_compl_mask;
    logic [7:0]     snk_cfg_desc_mon_thresh_mask;
    logic [7:0]     snk_cfg_desc_mon_perf_mask;
    logic [7:0]     snk_cfg_desc_mon_addr_mask;
    logic [7:0]     snk_cfg_desc_mon_debug_mask;
    logic [7:0]     snk_cfg_axi_wr_xfer_beats;  // used by sink half
    logic [7:0]     snk_cfg_alloc_size;         // used by sink half

    // tick_1us shared by both halves (Phase 2 ctrlrd retry pacing).
    logic           tick_1us;

    // ------------------------------------------------------------------------
    // tick_1us generator (paces ctrlrd poll retries). Free-running 1-cycle pulse
    // every TICK_1US_CYCLES aclk cycles (100 => ~1us at 100 MHz). The exact
    // period only affects retry cadence, not correctness.
    // ------------------------------------------------------------------------
    localparam int TICK_1US_CYCLES = 100;
    logic [$clog2(TICK_1US_CYCLES)-1:0] r_tick_cnt;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            r_tick_cnt <= '0;
            tick_1us   <= 1'b0;
        end else if (r_tick_cnt == TICK_1US_CYCLES[$clog2(TICK_1US_CYCLES)-1:0] - 1) begin
            r_tick_cnt <= '0;
            tick_1us   <= 1'b1;
        end else begin
            r_tick_cnt <= r_tick_cnt + 1'b1;
            tick_1us   <= 1'b0;
        end
    end

    //=========================================================================
    // Config mapping block - SOURCE half
    //=========================================================================
    rapids_config_block #(
        .NUM_CHANNELS (NUM_CHANNELS),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .USE_MON_REGS (1)
    ) u_cfg_src (
        .clk    (aclk),
        .rst_n  (aresetn),
        .reg_global_ctrl_global_en          (hwif_out.SRC.GLOBAL_CTRL.GLOBAL_EN.value),
        .reg_global_ctrl_global_rst         (hwif_out.SRC.GLOBAL_CTRL.GLOBAL_RST.value),
        .reg_channel_enable_ch_en           (hwif_out.SRC.CHANNEL_ENABLE.CH_EN.value),
        .reg_channel_reset_ch_rst           (hwif_out.SRC.CHANNEL_RESET.CH_RST.value),
        .reg_sched_timeout_cycles_timeout_cycles (hwif_out.SRC.SCHED_TIMEOUT_CYCLES.TIMEOUT_CYCLES.value),
        .reg_sched_timeout_limit_limit           (hwif_out.SRC.SCHED_TIMEOUT_LIMIT.LIMIT.value),
        .reg_sched_config_sched_en               (hwif_out.SRC.SCHED_CONFIG.SCHED_EN.value),
        .reg_sched_config_timeout_en             (hwif_out.SRC.SCHED_CONFIG.TIMEOUT_EN.value),
        .reg_sched_config_err_en                 (hwif_out.SRC.SCHED_CONFIG.ERR_EN.value),
        .reg_sched_config_compl_en               (hwif_out.SRC.SCHED_CONFIG.COMPL_EN.value),
        .reg_sched_config_perf_en                (hwif_out.SRC.SCHED_CONFIG.PERF_EN.value),
        .reg_desceng_config_desceng_en           (hwif_out.SRC.DESCENG_CONFIG.DESCENG_EN.value),
        .reg_desceng_config_prefetch_en          (hwif_out.SRC.DESCENG_CONFIG.PREFETCH_EN.value),
        .reg_desceng_config_fifo_thresh          (hwif_out.SRC.DESCENG_CONFIG.FIFO_THRESH.value),
        .reg_ctrl_config_ctrlrd_max_try          (hwif_out.SRC.CTRL_CONFIG.CTRLRD_MAX_TRY.value),
        .reg_desceng_addr0_base_addr0_base       (hwif_out.SRC.DESCENG_ADDR0_BASE.ADDR0_BASE.value),
        .reg_desceng_addr0_limit_addr0_limit     (hwif_out.SRC.DESCENG_ADDR0_LIMIT.ADDR0_LIMIT.value),
        .reg_desceng_addr1_base_addr1_base       (hwif_out.SRC.DESCENG_ADDR1_BASE.ADDR1_BASE.value),
        .reg_desceng_addr1_limit_addr1_limit     (hwif_out.SRC.DESCENG_ADDR1_LIMIT.ADDR1_LIMIT.value),
        .reg_daxmon_enable_mon_en                (hwif_out.SRC.MON.DAXMON_ENABLE.MON_EN.value),
        .reg_daxmon_enable_err_en                (hwif_out.SRC.MON.DAXMON_ENABLE.ERR_EN.value),
        .reg_daxmon_enable_compl_en              (hwif_out.SRC.MON.DAXMON_ENABLE.COMPL_EN.value),
        .reg_daxmon_enable_timeout_en            (hwif_out.SRC.MON.DAXMON_ENABLE.TIMEOUT_EN.value),
        .reg_daxmon_enable_perf_en               (hwif_out.SRC.MON.DAXMON_ENABLE.PERF_EN.value),
        .reg_daxmon_timeout_timeout_cycles       (hwif_out.SRC.MON.DAXMON_TIMEOUT.TIMEOUT_CYCLES.value),
        .reg_daxmon_latency_thresh_latency_thresh(hwif_out.SRC.MON.DAXMON_LATENCY_THRESH.LATENCY_THRESH.value),
        .reg_daxmon_pkt_mask_pkt_mask            (hwif_out.SRC.MON.DAXMON_PKT_MASK.PKT_MASK.value),
        .reg_daxmon_err_cfg_err_select           (hwif_out.SRC.MON.DAXMON_ERR_CFG.ERR_SELECT.value),
        .reg_daxmon_err_cfg_err_mask             (hwif_out.SRC.MON.DAXMON_ERR_CFG.ERR_MASK.value),
        .reg_daxmon_mask1_timeout_mask           (hwif_out.SRC.MON.DAXMON_MASK1.TIMEOUT_MASK.value),
        .reg_daxmon_mask1_compl_mask             (hwif_out.SRC.MON.DAXMON_MASK1.COMPL_MASK.value),
        .reg_daxmon_mask2_thresh_mask            (hwif_out.SRC.MON.DAXMON_MASK2.THRESH_MASK.value),
        .reg_daxmon_mask2_perf_mask              (hwif_out.SRC.MON.DAXMON_MASK2.PERF_MASK.value),
        .reg_daxmon_mask3_addr_mask              (hwif_out.SRC.MON.DAXMON_MASK3.ADDR_MASK.value),
        .reg_daxmon_mask3_debug_mask             (hwif_out.SRC.MON.DAXMON_MASK3.DEBUG_MASK.value),
        .reg_rdmon_enable_mon_en                 (hwif_out.SRC.MON.RDMON_ENABLE.MON_EN.value),
        .reg_rdmon_enable_err_en                 (hwif_out.SRC.MON.RDMON_ENABLE.ERR_EN.value),
        .reg_rdmon_enable_compl_en               (hwif_out.SRC.MON.RDMON_ENABLE.COMPL_EN.value),
        .reg_rdmon_enable_timeout_en             (hwif_out.SRC.MON.RDMON_ENABLE.TIMEOUT_EN.value),
        .reg_rdmon_enable_perf_en                (hwif_out.SRC.MON.RDMON_ENABLE.PERF_EN.value),
        .reg_rdmon_timeout_timeout_cycles        (hwif_out.SRC.MON.RDMON_TIMEOUT.TIMEOUT_CYCLES.value),
        .reg_rdmon_latency_thresh_latency_thresh (hwif_out.SRC.MON.RDMON_LATENCY_THRESH.LATENCY_THRESH.value),
        .reg_rdmon_pkt_mask_pkt_mask             (hwif_out.SRC.MON.RDMON_PKT_MASK.PKT_MASK.value),
        .reg_rdmon_err_cfg_err_select            (hwif_out.SRC.MON.RDMON_ERR_CFG.ERR_SELECT.value),
        .reg_rdmon_err_cfg_err_mask              (hwif_out.SRC.MON.RDMON_ERR_CFG.ERR_MASK.value),
        .reg_rdmon_mask1_timeout_mask            (hwif_out.SRC.MON.RDMON_MASK1.TIMEOUT_MASK.value),
        .reg_rdmon_mask1_compl_mask              (hwif_out.SRC.MON.RDMON_MASK1.COMPL_MASK.value),
        .reg_rdmon_mask2_thresh_mask             (hwif_out.SRC.MON.RDMON_MASK2.THRESH_MASK.value),
        .reg_rdmon_mask2_perf_mask               (hwif_out.SRC.MON.RDMON_MASK2.PERF_MASK.value),
        .reg_rdmon_mask3_addr_mask               (hwif_out.SRC.MON.RDMON_MASK3.ADDR_MASK.value),
        .reg_rdmon_mask3_debug_mask              (hwif_out.SRC.MON.RDMON_MASK3.DEBUG_MASK.value),
        .reg_wrmon_enable_mon_en                 (hwif_out.SRC.MON.WRMON_ENABLE.MON_EN.value),
        .reg_wrmon_enable_err_en                 (hwif_out.SRC.MON.WRMON_ENABLE.ERR_EN.value),
        .reg_wrmon_enable_compl_en               (hwif_out.SRC.MON.WRMON_ENABLE.COMPL_EN.value),
        .reg_wrmon_enable_timeout_en             (hwif_out.SRC.MON.WRMON_ENABLE.TIMEOUT_EN.value),
        .reg_wrmon_enable_perf_en                (hwif_out.SRC.MON.WRMON_ENABLE.PERF_EN.value),
        .reg_wrmon_timeout_timeout_cycles        (hwif_out.SRC.MON.WRMON_TIMEOUT.TIMEOUT_CYCLES.value),
        .reg_wrmon_latency_thresh_latency_thresh (hwif_out.SRC.MON.WRMON_LATENCY_THRESH.LATENCY_THRESH.value),
        .reg_wrmon_pkt_mask_pkt_mask             (hwif_out.SRC.MON.WRMON_PKT_MASK.PKT_MASK.value),
        .reg_wrmon_err_cfg_err_select            (hwif_out.SRC.MON.WRMON_ERR_CFG.ERR_SELECT.value),
        .reg_wrmon_err_cfg_err_mask              (hwif_out.SRC.MON.WRMON_ERR_CFG.ERR_MASK.value),
        .reg_wrmon_mask1_timeout_mask            (hwif_out.SRC.MON.WRMON_MASK1.TIMEOUT_MASK.value),
        .reg_wrmon_mask1_compl_mask              (hwif_out.SRC.MON.WRMON_MASK1.COMPL_MASK.value),
        .reg_wrmon_mask2_thresh_mask             (hwif_out.SRC.MON.WRMON_MASK2.THRESH_MASK.value),
        .reg_wrmon_mask2_perf_mask               (hwif_out.SRC.MON.WRMON_MASK2.PERF_MASK.value),
        .reg_wrmon_mask3_addr_mask               (hwif_out.SRC.MON.WRMON_MASK3.ADDR_MASK.value),
        .reg_wrmon_mask3_debug_mask              (hwif_out.SRC.MON.WRMON_MASK3.DEBUG_MASK.value),
        .reg_axi_xfer_config_rd_xfer_beats       (hwif_out.SRC.AXI_XFER_CONFIG.RD_XFER_BEATS.value),
        .reg_axi_xfer_config_wr_xfer_beats       (hwif_out.SRC.AXI_XFER_CONFIG.WR_XFER_BEATS.value),
        .reg_perf_config_perf_en                 (hwif_out.SRC.PERF_CONFIG.PERF_EN.value),
        .reg_perf_config_perf_mode               (hwif_out.SRC.PERF_CONFIG.PERF_MODE.value),
        .reg_perf_config_perf_clear              (hwif_out.SRC.PERF_CONFIG.PERF_CLEAR.value),
        .reg_obs_ctrl_ch_sel                     (hwif_out.SRC.OBS_CTRL.CH_SEL.value),
        .reg_obs_ctrl_cat_sel                    (hwif_out.SRC.OBS_CTRL.CAT_SEL.value),
        .i_obs_flags                             (32'h0),
        .i_obs_data0                             (32'h0),
        .i_obs_data1                             (32'h0),
        // Outputs to source half
        .cfg_channel_enable          (src_cfg_channel_enable),
        .cfg_channel_reset           (src_cfg_channel_reset),
        .cfg_sched_enable            (src_cfg_sched_enable),
        .cfg_sched_timeout_cycles    (src_cfg_sched_timeout_cycles),
        .cfg_sched_timeout_limit     (src_cfg_sched_timeout_limit),
        .cfg_sched_timeout_enable    (src_cfg_sched_timeout_enable),
        .cfg_sched_err_enable        (src_cfg_sched_err_enable),
        .cfg_sched_compl_enable      (src_cfg_sched_compl_enable),
        .cfg_sched_perf_enable       (src_cfg_sched_perf_enable),
        .cfg_desceng_enable          (src_cfg_desceng_enable),
        .cfg_desceng_prefetch        (src_cfg_desceng_prefetch),
        .cfg_desceng_fifo_thresh     (src_cfg_desceng_fifo_thresh),
        .cfg_ctrlrd_max_try          (src_cfg_ctrlrd_max_try),
        .cfg_desceng_addr0_base      (src_cfg_desceng_addr0_base),
        .cfg_desceng_addr0_limit     (src_cfg_desceng_addr0_limit),
        .cfg_desceng_addr1_base      (src_cfg_desceng_addr1_base),
        .cfg_desceng_addr1_limit     (src_cfg_desceng_addr1_limit),
        .cfg_desc_mon_enable         (src_cfg_desc_mon_enable),
        .cfg_desc_mon_err_enable     (src_cfg_desc_mon_err_enable),
        .cfg_desc_mon_perf_enable    (src_cfg_desc_mon_perf_enable),
        .cfg_desc_mon_timeout_enable (src_cfg_desc_mon_timeout_enable),
        .cfg_desc_mon_timeout_cycles (src_cfg_desc_mon_timeout_cycles),
        .cfg_desc_mon_latency_thresh (src_cfg_desc_mon_latency_thresh),
        .cfg_desc_mon_pkt_mask       (src_cfg_desc_mon_pkt_mask),
        .cfg_desc_mon_err_select     (src_cfg_desc_mon_err_select),
        .cfg_desc_mon_err_mask       (src_cfg_desc_mon_err_mask),
        .cfg_desc_mon_timeout_mask   (src_cfg_desc_mon_timeout_mask),
        .cfg_desc_mon_compl_mask     (src_cfg_desc_mon_compl_mask),
        .cfg_desc_mon_thresh_mask    (src_cfg_desc_mon_thresh_mask),
        .cfg_desc_mon_perf_mask      (src_cfg_desc_mon_perf_mask),
        .cfg_desc_mon_addr_mask      (src_cfg_desc_mon_addr_mask),
        .cfg_desc_mon_debug_mask     (src_cfg_desc_mon_debug_mask),
        // rd/wr engine monitor cfg outputs unused (taps live in halves later)
        .cfg_rdeng_mon_enable        (),
        .cfg_rdeng_mon_err_enable    (),
        .cfg_rdeng_mon_perf_enable   (),
        .cfg_rdeng_mon_timeout_enable(),
        .cfg_rdeng_mon_timeout_cycles(),
        .cfg_rdeng_mon_latency_thresh(),
        .cfg_rdeng_mon_pkt_mask      (),
        .cfg_rdeng_mon_err_select    (),
        .cfg_rdeng_mon_err_mask      (),
        .cfg_rdeng_mon_timeout_mask  (),
        .cfg_rdeng_mon_compl_mask    (),
        .cfg_rdeng_mon_thresh_mask   (),
        .cfg_rdeng_mon_perf_mask     (),
        .cfg_rdeng_mon_addr_mask     (),
        .cfg_rdeng_mon_debug_mask    (),
        .cfg_wreng_mon_enable        (),
        .cfg_wreng_mon_err_enable    (),
        .cfg_wreng_mon_perf_enable   (),
        .cfg_wreng_mon_timeout_enable(),
        .cfg_wreng_mon_timeout_cycles(),
        .cfg_wreng_mon_latency_thresh(),
        .cfg_wreng_mon_pkt_mask      (),
        .cfg_wreng_mon_err_select    (),
        .cfg_wreng_mon_err_mask      (),
        .cfg_wreng_mon_timeout_mask  (),
        .cfg_wreng_mon_compl_mask    (),
        .cfg_wreng_mon_thresh_mask   (),
        .cfg_wreng_mon_perf_mask     (),
        .cfg_wreng_mon_addr_mask     (),
        .cfg_wreng_mon_debug_mask    (),
        // AXI transfer cfg (source half consumes rd_xfer_beats + drain_size)
        .reg_axi_xfer_config_alloc_size (hwif_out.SRC.AXI_XFER_CONFIG.ALLOC_SIZE.value),
        .reg_axi_xfer_config_drain_size (hwif_out.SRC.AXI_XFER_CONFIG.DRAIN_SIZE.value),
        .cfg_axi_rd_xfer_beats       (src_cfg_axi_rd_xfer_beats),
        .cfg_axi_wr_xfer_beats       (),  // unused on source
        .cfg_alloc_size              (),  // unused on source
        .cfg_drain_size              (src_cfg_drain_size),
        .cfg_perf_enable             (),
        .cfg_perf_mode               (),
        .cfg_perf_clear              (),
        .cfg_obs_ch_sel              (),
        .cfg_obs_cat_sel             (),
        .obs_flags_to_regs           (),
        .obs_data0_to_regs           (),
        .obs_data1_to_regs           ()
    );

    //=========================================================================
    // Config mapping block - SINK half
    //=========================================================================
    rapids_config_block #(
        .NUM_CHANNELS (NUM_CHANNELS),
        .ADDR_WIDTH   (ADDR_WIDTH),
        .USE_MON_REGS (1)
    ) u_cfg_snk (
        .clk    (aclk),
        .rst_n  (aresetn),
        .reg_global_ctrl_global_en          (hwif_out.SNK.GLOBAL_CTRL.GLOBAL_EN.value),
        .reg_global_ctrl_global_rst         (hwif_out.SNK.GLOBAL_CTRL.GLOBAL_RST.value),
        .reg_channel_enable_ch_en           (hwif_out.SNK.CHANNEL_ENABLE.CH_EN.value),
        .reg_channel_reset_ch_rst           (hwif_out.SNK.CHANNEL_RESET.CH_RST.value),
        .reg_sched_timeout_cycles_timeout_cycles (hwif_out.SNK.SCHED_TIMEOUT_CYCLES.TIMEOUT_CYCLES.value),
        .reg_sched_timeout_limit_limit           (hwif_out.SNK.SCHED_TIMEOUT_LIMIT.LIMIT.value),
        .reg_sched_config_sched_en               (hwif_out.SNK.SCHED_CONFIG.SCHED_EN.value),
        .reg_sched_config_timeout_en             (hwif_out.SNK.SCHED_CONFIG.TIMEOUT_EN.value),
        .reg_sched_config_err_en                 (hwif_out.SNK.SCHED_CONFIG.ERR_EN.value),
        .reg_sched_config_compl_en               (hwif_out.SNK.SCHED_CONFIG.COMPL_EN.value),
        .reg_sched_config_perf_en                (hwif_out.SNK.SCHED_CONFIG.PERF_EN.value),
        .reg_desceng_config_desceng_en           (hwif_out.SNK.DESCENG_CONFIG.DESCENG_EN.value),
        .reg_desceng_config_prefetch_en          (hwif_out.SNK.DESCENG_CONFIG.PREFETCH_EN.value),
        .reg_desceng_config_fifo_thresh          (hwif_out.SNK.DESCENG_CONFIG.FIFO_THRESH.value),
        .reg_ctrl_config_ctrlrd_max_try          (hwif_out.SNK.CTRL_CONFIG.CTRLRD_MAX_TRY.value),
        .reg_desceng_addr0_base_addr0_base       (hwif_out.SNK.DESCENG_ADDR0_BASE.ADDR0_BASE.value),
        .reg_desceng_addr0_limit_addr0_limit     (hwif_out.SNK.DESCENG_ADDR0_LIMIT.ADDR0_LIMIT.value),
        .reg_desceng_addr1_base_addr1_base       (hwif_out.SNK.DESCENG_ADDR1_BASE.ADDR1_BASE.value),
        .reg_desceng_addr1_limit_addr1_limit     (hwif_out.SNK.DESCENG_ADDR1_LIMIT.ADDR1_LIMIT.value),
        .reg_daxmon_enable_mon_en                (hwif_out.SNK.MON.DAXMON_ENABLE.MON_EN.value),
        .reg_daxmon_enable_err_en                (hwif_out.SNK.MON.DAXMON_ENABLE.ERR_EN.value),
        .reg_daxmon_enable_compl_en              (hwif_out.SNK.MON.DAXMON_ENABLE.COMPL_EN.value),
        .reg_daxmon_enable_timeout_en            (hwif_out.SNK.MON.DAXMON_ENABLE.TIMEOUT_EN.value),
        .reg_daxmon_enable_perf_en               (hwif_out.SNK.MON.DAXMON_ENABLE.PERF_EN.value),
        .reg_daxmon_timeout_timeout_cycles       (hwif_out.SNK.MON.DAXMON_TIMEOUT.TIMEOUT_CYCLES.value),
        .reg_daxmon_latency_thresh_latency_thresh(hwif_out.SNK.MON.DAXMON_LATENCY_THRESH.LATENCY_THRESH.value),
        .reg_daxmon_pkt_mask_pkt_mask            (hwif_out.SNK.MON.DAXMON_PKT_MASK.PKT_MASK.value),
        .reg_daxmon_err_cfg_err_select           (hwif_out.SNK.MON.DAXMON_ERR_CFG.ERR_SELECT.value),
        .reg_daxmon_err_cfg_err_mask             (hwif_out.SNK.MON.DAXMON_ERR_CFG.ERR_MASK.value),
        .reg_daxmon_mask1_timeout_mask           (hwif_out.SNK.MON.DAXMON_MASK1.TIMEOUT_MASK.value),
        .reg_daxmon_mask1_compl_mask             (hwif_out.SNK.MON.DAXMON_MASK1.COMPL_MASK.value),
        .reg_daxmon_mask2_thresh_mask            (hwif_out.SNK.MON.DAXMON_MASK2.THRESH_MASK.value),
        .reg_daxmon_mask2_perf_mask              (hwif_out.SNK.MON.DAXMON_MASK2.PERF_MASK.value),
        .reg_daxmon_mask3_addr_mask              (hwif_out.SNK.MON.DAXMON_MASK3.ADDR_MASK.value),
        .reg_daxmon_mask3_debug_mask             (hwif_out.SNK.MON.DAXMON_MASK3.DEBUG_MASK.value),
        .reg_rdmon_enable_mon_en                 (hwif_out.SNK.MON.RDMON_ENABLE.MON_EN.value),
        .reg_rdmon_enable_err_en                 (hwif_out.SNK.MON.RDMON_ENABLE.ERR_EN.value),
        .reg_rdmon_enable_compl_en               (hwif_out.SNK.MON.RDMON_ENABLE.COMPL_EN.value),
        .reg_rdmon_enable_timeout_en             (hwif_out.SNK.MON.RDMON_ENABLE.TIMEOUT_EN.value),
        .reg_rdmon_enable_perf_en                (hwif_out.SNK.MON.RDMON_ENABLE.PERF_EN.value),
        .reg_rdmon_timeout_timeout_cycles        (hwif_out.SNK.MON.RDMON_TIMEOUT.TIMEOUT_CYCLES.value),
        .reg_rdmon_latency_thresh_latency_thresh (hwif_out.SNK.MON.RDMON_LATENCY_THRESH.LATENCY_THRESH.value),
        .reg_rdmon_pkt_mask_pkt_mask             (hwif_out.SNK.MON.RDMON_PKT_MASK.PKT_MASK.value),
        .reg_rdmon_err_cfg_err_select            (hwif_out.SNK.MON.RDMON_ERR_CFG.ERR_SELECT.value),
        .reg_rdmon_err_cfg_err_mask              (hwif_out.SNK.MON.RDMON_ERR_CFG.ERR_MASK.value),
        .reg_rdmon_mask1_timeout_mask            (hwif_out.SNK.MON.RDMON_MASK1.TIMEOUT_MASK.value),
        .reg_rdmon_mask1_compl_mask              (hwif_out.SNK.MON.RDMON_MASK1.COMPL_MASK.value),
        .reg_rdmon_mask2_thresh_mask             (hwif_out.SNK.MON.RDMON_MASK2.THRESH_MASK.value),
        .reg_rdmon_mask2_perf_mask               (hwif_out.SNK.MON.RDMON_MASK2.PERF_MASK.value),
        .reg_rdmon_mask3_addr_mask               (hwif_out.SNK.MON.RDMON_MASK3.ADDR_MASK.value),
        .reg_rdmon_mask3_debug_mask              (hwif_out.SNK.MON.RDMON_MASK3.DEBUG_MASK.value),
        .reg_wrmon_enable_mon_en                 (hwif_out.SNK.MON.WRMON_ENABLE.MON_EN.value),
        .reg_wrmon_enable_err_en                 (hwif_out.SNK.MON.WRMON_ENABLE.ERR_EN.value),
        .reg_wrmon_enable_compl_en               (hwif_out.SNK.MON.WRMON_ENABLE.COMPL_EN.value),
        .reg_wrmon_enable_timeout_en             (hwif_out.SNK.MON.WRMON_ENABLE.TIMEOUT_EN.value),
        .reg_wrmon_enable_perf_en                (hwif_out.SNK.MON.WRMON_ENABLE.PERF_EN.value),
        .reg_wrmon_timeout_timeout_cycles        (hwif_out.SNK.MON.WRMON_TIMEOUT.TIMEOUT_CYCLES.value),
        .reg_wrmon_latency_thresh_latency_thresh (hwif_out.SNK.MON.WRMON_LATENCY_THRESH.LATENCY_THRESH.value),
        .reg_wrmon_pkt_mask_pkt_mask             (hwif_out.SNK.MON.WRMON_PKT_MASK.PKT_MASK.value),
        .reg_wrmon_err_cfg_err_select            (hwif_out.SNK.MON.WRMON_ERR_CFG.ERR_SELECT.value),
        .reg_wrmon_err_cfg_err_mask              (hwif_out.SNK.MON.WRMON_ERR_CFG.ERR_MASK.value),
        .reg_wrmon_mask1_timeout_mask            (hwif_out.SNK.MON.WRMON_MASK1.TIMEOUT_MASK.value),
        .reg_wrmon_mask1_compl_mask              (hwif_out.SNK.MON.WRMON_MASK1.COMPL_MASK.value),
        .reg_wrmon_mask2_thresh_mask             (hwif_out.SNK.MON.WRMON_MASK2.THRESH_MASK.value),
        .reg_wrmon_mask2_perf_mask               (hwif_out.SNK.MON.WRMON_MASK2.PERF_MASK.value),
        .reg_wrmon_mask3_addr_mask               (hwif_out.SNK.MON.WRMON_MASK3.ADDR_MASK.value),
        .reg_wrmon_mask3_debug_mask              (hwif_out.SNK.MON.WRMON_MASK3.DEBUG_MASK.value),
        .reg_axi_xfer_config_rd_xfer_beats       (hwif_out.SNK.AXI_XFER_CONFIG.RD_XFER_BEATS.value),
        .reg_axi_xfer_config_wr_xfer_beats       (hwif_out.SNK.AXI_XFER_CONFIG.WR_XFER_BEATS.value),
        .reg_perf_config_perf_en                 (hwif_out.SNK.PERF_CONFIG.PERF_EN.value),
        .reg_perf_config_perf_mode               (hwif_out.SNK.PERF_CONFIG.PERF_MODE.value),
        .reg_perf_config_perf_clear              (hwif_out.SNK.PERF_CONFIG.PERF_CLEAR.value),
        .reg_obs_ctrl_ch_sel                     (hwif_out.SNK.OBS_CTRL.CH_SEL.value),
        .reg_obs_ctrl_cat_sel                    (hwif_out.SNK.OBS_CTRL.CAT_SEL.value),
        .i_obs_flags                             (32'h0),
        .i_obs_data0                             (32'h0),
        .i_obs_data1                             (32'h0),
        // Outputs to sink half
        .cfg_channel_enable          (snk_cfg_channel_enable),
        .cfg_channel_reset           (snk_cfg_channel_reset),
        .cfg_sched_enable            (snk_cfg_sched_enable),
        .cfg_sched_timeout_cycles    (snk_cfg_sched_timeout_cycles),
        .cfg_sched_timeout_limit     (snk_cfg_sched_timeout_limit),
        .cfg_sched_timeout_enable    (snk_cfg_sched_timeout_enable),
        .cfg_sched_err_enable        (snk_cfg_sched_err_enable),
        .cfg_sched_compl_enable      (snk_cfg_sched_compl_enable),
        .cfg_sched_perf_enable       (snk_cfg_sched_perf_enable),
        .cfg_desceng_enable          (snk_cfg_desceng_enable),
        .cfg_desceng_prefetch        (snk_cfg_desceng_prefetch),
        .cfg_desceng_fifo_thresh     (snk_cfg_desceng_fifo_thresh),
        .cfg_ctrlrd_max_try          (snk_cfg_ctrlrd_max_try),
        .cfg_desceng_addr0_base      (snk_cfg_desceng_addr0_base),
        .cfg_desceng_addr0_limit     (snk_cfg_desceng_addr0_limit),
        .cfg_desceng_addr1_base      (snk_cfg_desceng_addr1_base),
        .cfg_desceng_addr1_limit     (snk_cfg_desceng_addr1_limit),
        .cfg_desc_mon_enable         (snk_cfg_desc_mon_enable),
        .cfg_desc_mon_err_enable     (snk_cfg_desc_mon_err_enable),
        .cfg_desc_mon_perf_enable    (snk_cfg_desc_mon_perf_enable),
        .cfg_desc_mon_timeout_enable (snk_cfg_desc_mon_timeout_enable),
        .cfg_desc_mon_timeout_cycles (snk_cfg_desc_mon_timeout_cycles),
        .cfg_desc_mon_latency_thresh (snk_cfg_desc_mon_latency_thresh),
        .cfg_desc_mon_pkt_mask       (snk_cfg_desc_mon_pkt_mask),
        .cfg_desc_mon_err_select     (snk_cfg_desc_mon_err_select),
        .cfg_desc_mon_err_mask       (snk_cfg_desc_mon_err_mask),
        .cfg_desc_mon_timeout_mask   (snk_cfg_desc_mon_timeout_mask),
        .cfg_desc_mon_compl_mask     (snk_cfg_desc_mon_compl_mask),
        .cfg_desc_mon_thresh_mask    (snk_cfg_desc_mon_thresh_mask),
        .cfg_desc_mon_perf_mask      (snk_cfg_desc_mon_perf_mask),
        .cfg_desc_mon_addr_mask      (snk_cfg_desc_mon_addr_mask),
        .cfg_desc_mon_debug_mask     (snk_cfg_desc_mon_debug_mask),
        .cfg_rdeng_mon_enable        (),
        .cfg_rdeng_mon_err_enable    (),
        .cfg_rdeng_mon_perf_enable   (),
        .cfg_rdeng_mon_timeout_enable(),
        .cfg_rdeng_mon_timeout_cycles(),
        .cfg_rdeng_mon_latency_thresh(),
        .cfg_rdeng_mon_pkt_mask      (),
        .cfg_rdeng_mon_err_select    (),
        .cfg_rdeng_mon_err_mask      (),
        .cfg_rdeng_mon_timeout_mask  (),
        .cfg_rdeng_mon_compl_mask    (),
        .cfg_rdeng_mon_thresh_mask   (),
        .cfg_rdeng_mon_perf_mask     (),
        .cfg_rdeng_mon_addr_mask     (),
        .cfg_rdeng_mon_debug_mask    (),
        .cfg_wreng_mon_enable        (),
        .cfg_wreng_mon_err_enable    (),
        .cfg_wreng_mon_perf_enable   (),
        .cfg_wreng_mon_timeout_enable(),
        .cfg_wreng_mon_timeout_cycles(),
        .cfg_wreng_mon_latency_thresh(),
        .cfg_wreng_mon_pkt_mask      (),
        .cfg_wreng_mon_err_select    (),
        .cfg_wreng_mon_err_mask      (),
        .cfg_wreng_mon_timeout_mask  (),
        .cfg_wreng_mon_compl_mask    (),
        .cfg_wreng_mon_thresh_mask   (),
        .cfg_wreng_mon_perf_mask     (),
        .cfg_wreng_mon_addr_mask     (),
        .cfg_wreng_mon_debug_mask    (),
        // AXI transfer cfg (sink half consumes wr_xfer_beats + alloc_size)
        .reg_axi_xfer_config_alloc_size (hwif_out.SNK.AXI_XFER_CONFIG.ALLOC_SIZE.value),
        .reg_axi_xfer_config_drain_size (hwif_out.SNK.AXI_XFER_CONFIG.DRAIN_SIZE.value),
        .cfg_axi_rd_xfer_beats       (),  // unused on sink
        .cfg_axi_wr_xfer_beats       (snk_cfg_axi_wr_xfer_beats),
        .cfg_alloc_size              (snk_cfg_alloc_size),
        .cfg_drain_size              (),  // unused on sink
        .cfg_perf_enable             (),
        .cfg_perf_mode               (),
        .cfg_perf_clear              (),
        .cfg_obs_ch_sel              (),
        .cfg_obs_cat_sel             (),
        .obs_flags_to_regs           (),
        .obs_data0_to_regs           (),
        .obs_data1_to_regs           ()
    );

    //=========================================================================
    // Single merged MonBus egress (from the core; arbitration is in-core)
    //=========================================================================
    logic                                    core_mon_valid;
    logic                                    core_mon_ready;
    monitor_common_pkg::monitor_packet_t     core_mon_packet;
    monitor_common_pkg::monbus_timestamp_t   core_mon_timestamp;

    //=========================================================================
    // RAPIDS Beats Core (two independent halves)
    //=========================================================================
    rapids_core_beats #(
        .NUM_CHANNELS         (NUM_CHANNELS),
        .ADDR_WIDTH           (ADDR_WIDTH),
        .DATA_WIDTH           (DATA_WIDTH),
        .AXI_ID_WIDTH         (AXI_ID_WIDTH),
        .SRAM_DEPTH           (SRAM_DEPTH),
        .AR_MAX_OUTSTANDING   (AR_MAX_OUTSTANDING),
        .AW_MAX_OUTSTANDING   (AW_MAX_OUTSTANDING),
        .AXIS_ID_WIDTH        (AXIS_ID_WIDTH),
        .AXIS_DEST_WIDTH      (AXIS_DEST_WIDTH),
        .AXIS_USER_WIDTH      (AXIS_USER_WIDTH),
        .MON_MAX_TRANSACTIONS (MON_MAX_TRANSACTIONS)
    ) u_core (
        .clk    (aclk),
        .rst_n  (aresetn),

        //---------------------------------------------------------------------
        // SOURCE half - shared-infra (src_ prefixed)
        //---------------------------------------------------------------------
        .src_apb_valid              (src_apb_valid),
        .src_apb_ready              (src_apb_ready),
        .src_apb_addr               (src_apb_addr),
        .src_cfg_channel_enable     (src_cfg_channel_enable),
        .src_cfg_channel_reset      (src_cfg_channel_reset),
        .src_cfg_sched_enable       (src_cfg_sched_enable),
        .src_cfg_sched_timeout_cycles(src_cfg_sched_timeout_cycles),
        .src_cfg_sched_timeout_limit(src_cfg_sched_timeout_limit),
        .src_cfg_sched_timeout_enable(src_cfg_sched_timeout_enable),
        .src_cfg_sched_err_enable   (src_cfg_sched_err_enable),
        .src_cfg_sched_compl_enable (src_cfg_sched_compl_enable),
        .src_cfg_sched_perf_enable  (src_cfg_sched_perf_enable),
        .src_cfg_desceng_enable     (src_cfg_desceng_enable),
        .src_cfg_desceng_prefetch   (src_cfg_desceng_prefetch),
        .src_cfg_desceng_fifo_thresh(src_cfg_desceng_fifo_thresh),
        .src_cfg_desceng_addr0_base (src_cfg_desceng_addr0_base),
        .src_cfg_desceng_addr0_limit(src_cfg_desceng_addr0_limit),
        .src_cfg_desceng_addr1_base (src_cfg_desceng_addr1_base),
        .src_cfg_desceng_addr1_limit(src_cfg_desceng_addr1_limit),
        .src_cfg_ctrlrd_max_try     (src_cfg_ctrlrd_max_try),
        .src_tick_1us               (tick_1us),
        .src_cfg_desc_mon_enable        (src_cfg_desc_mon_enable),
        .src_cfg_desc_mon_err_enable    (src_cfg_desc_mon_err_enable),
        .src_cfg_desc_mon_perf_enable   (src_cfg_desc_mon_perf_enable),
        .src_cfg_desc_mon_timeout_enable(src_cfg_desc_mon_timeout_enable),
        .src_cfg_desc_mon_timeout_cycles(src_cfg_desc_mon_timeout_cycles),
        .src_cfg_desc_mon_latency_thresh(src_cfg_desc_mon_latency_thresh),
        .src_cfg_desc_mon_pkt_mask      (src_cfg_desc_mon_pkt_mask),
        .src_cfg_desc_mon_err_select    (src_cfg_desc_mon_err_select),
        .src_cfg_desc_mon_err_mask      (src_cfg_desc_mon_err_mask),
        .src_cfg_desc_mon_timeout_mask  (src_cfg_desc_mon_timeout_mask),
        .src_cfg_desc_mon_compl_mask    (src_cfg_desc_mon_compl_mask),
        .src_cfg_desc_mon_thresh_mask   (src_cfg_desc_mon_thresh_mask),
        .src_cfg_desc_mon_perf_mask     (src_cfg_desc_mon_perf_mask),
        .src_cfg_desc_mon_addr_mask     (src_cfg_desc_mon_addr_mask),
        .src_cfg_desc_mon_debug_mask    (src_cfg_desc_mon_debug_mask),
        // Status (source)
        .src_system_idle                (src_system_idle),
        .src_descriptor_engine_idle     (),
        .src_scheduler_idle             (),
        .src_scheduler_state            (),
        .src_sched_error                (src_sched_error),
        .src_cfg_sts_desc_mon_busy          (),
        .src_cfg_sts_desc_mon_active_txns   (),
        .src_cfg_sts_desc_mon_error_count   (),
        .src_cfg_sts_desc_mon_txn_count     (),
        .src_cfg_sts_desc_mon_conflict_error(),
        // Source descriptor fetch master -> top src_m_axi_desc_*
        .src_m_axi_desc_arvalid     (src_m_axi_desc_arvalid),
        .src_m_axi_desc_arready     (src_m_axi_desc_arready),
        .src_m_axi_desc_araddr      (src_m_axi_desc_araddr),
        .src_m_axi_desc_arlen       (src_m_axi_desc_arlen),
        .src_m_axi_desc_arsize      (src_m_axi_desc_arsize),
        .src_m_axi_desc_arburst     (src_m_axi_desc_arburst),
        .src_m_axi_desc_arid        (src_m_axi_desc_arid),
        .src_m_axi_desc_arlock      (src_m_axi_desc_arlock),
        .src_m_axi_desc_arcache     (src_m_axi_desc_arcache),
        .src_m_axi_desc_arprot      (src_m_axi_desc_arprot),
        .src_m_axi_desc_arqos       (src_m_axi_desc_arqos),
        .src_m_axi_desc_arregion    (src_m_axi_desc_arregion),
        .src_m_axi_desc_rvalid      (src_m_axi_desc_rvalid),
        .src_m_axi_desc_rready      (src_m_axi_desc_rready),
        .src_m_axi_desc_rdata       (src_m_axi_desc_rdata),
        .src_m_axi_desc_rresp       (src_m_axi_desc_rresp),
        .src_m_axi_desc_rlast       (src_m_axi_desc_rlast),
        .src_m_axi_desc_rid         (src_m_axi_desc_rid),
        // Source control read master -> top src_m_axi_ctrlrd_*
        .src_m_axi_ctrlrd_arvalid   (src_m_axi_ctrlrd_arvalid),
        .src_m_axi_ctrlrd_arready   (src_m_axi_ctrlrd_arready),
        .src_m_axi_ctrlrd_araddr    (src_m_axi_ctrlrd_araddr),
        .src_m_axi_ctrlrd_arlen     (src_m_axi_ctrlrd_arlen),
        .src_m_axi_ctrlrd_arsize    (src_m_axi_ctrlrd_arsize),
        .src_m_axi_ctrlrd_arburst   (src_m_axi_ctrlrd_arburst),
        .src_m_axi_ctrlrd_arid      (src_m_axi_ctrlrd_arid),
        .src_m_axi_ctrlrd_arlock    (src_m_axi_ctrlrd_arlock),
        .src_m_axi_ctrlrd_arcache   (src_m_axi_ctrlrd_arcache),
        .src_m_axi_ctrlrd_arprot    (src_m_axi_ctrlrd_arprot),
        .src_m_axi_ctrlrd_arqos     (src_m_axi_ctrlrd_arqos),
        .src_m_axi_ctrlrd_arregion  (src_m_axi_ctrlrd_arregion),
        .src_m_axi_ctrlrd_rvalid    (src_m_axi_ctrlrd_rvalid),
        .src_m_axi_ctrlrd_rready    (src_m_axi_ctrlrd_rready),
        .src_m_axi_ctrlrd_rdata     (src_m_axi_ctrlrd_rdata),
        .src_m_axi_ctrlrd_rresp     (src_m_axi_ctrlrd_rresp),
        .src_m_axi_ctrlrd_rlast     (src_m_axi_ctrlrd_rlast),
        .src_m_axi_ctrlrd_rid       (src_m_axi_ctrlrd_rid),
        // Source control write master -> top src_m_axi_ctrlwr_*
        .src_m_axi_ctrlwr_awvalid   (src_m_axi_ctrlwr_awvalid),
        .src_m_axi_ctrlwr_awready   (src_m_axi_ctrlwr_awready),
        .src_m_axi_ctrlwr_awaddr    (src_m_axi_ctrlwr_awaddr),
        .src_m_axi_ctrlwr_awlen     (src_m_axi_ctrlwr_awlen),
        .src_m_axi_ctrlwr_awsize    (src_m_axi_ctrlwr_awsize),
        .src_m_axi_ctrlwr_awburst   (src_m_axi_ctrlwr_awburst),
        .src_m_axi_ctrlwr_awid      (src_m_axi_ctrlwr_awid),
        .src_m_axi_ctrlwr_awlock    (src_m_axi_ctrlwr_awlock),
        .src_m_axi_ctrlwr_awcache   (src_m_axi_ctrlwr_awcache),
        .src_m_axi_ctrlwr_awprot    (src_m_axi_ctrlwr_awprot),
        .src_m_axi_ctrlwr_awqos     (src_m_axi_ctrlwr_awqos),
        .src_m_axi_ctrlwr_awregion  (src_m_axi_ctrlwr_awregion),
        .src_m_axi_ctrlwr_wvalid    (src_m_axi_ctrlwr_wvalid),
        .src_m_axi_ctrlwr_wready    (src_m_axi_ctrlwr_wready),
        .src_m_axi_ctrlwr_wdata     (src_m_axi_ctrlwr_wdata),
        .src_m_axi_ctrlwr_wstrb     (src_m_axi_ctrlwr_wstrb),
        .src_m_axi_ctrlwr_wlast     (src_m_axi_ctrlwr_wlast),
        .src_m_axi_ctrlwr_bvalid    (src_m_axi_ctrlwr_bvalid),
        .src_m_axi_ctrlwr_bready    (src_m_axi_ctrlwr_bready),
        .src_m_axi_ctrlwr_bid       (src_m_axi_ctrlwr_bid),
        .src_m_axi_ctrlwr_bresp     (src_m_axi_ctrlwr_bresp),

        //---------------------------------------------------------------------
        // SOURCE half - direction-unique (no prefix)
        //---------------------------------------------------------------------
        .cfg_axi_rd_xfer_beats      (src_cfg_axi_rd_xfer_beats),
        .cfg_drain_size             (src_cfg_drain_size),
        .m_axis_tdata               (m_axis_tdata),
        .m_axis_tstrb               (m_axis_tstrb),
        .m_axis_tlast               (m_axis_tlast),
        .m_axis_tid                 (m_axis_tid),
        .m_axis_tdest               (m_axis_tdest),
        .m_axis_tuser               (m_axis_tuser),
        .m_axis_tvalid              (m_axis_tvalid),
        .m_axis_tready              (m_axis_tready),
        .m_axi_rd_arid              (m_axi_rd_arid),
        .m_axi_rd_araddr            (m_axi_rd_araddr),
        .m_axi_rd_arlen             (m_axi_rd_arlen),
        .m_axi_rd_arsize            (m_axi_rd_arsize),
        .m_axi_rd_arburst           (m_axi_rd_arburst),
        .m_axi_rd_arvalid           (m_axi_rd_arvalid),
        .m_axi_rd_arready           (m_axi_rd_arready),
        .m_axi_rd_rid               (m_axi_rd_rid),
        .m_axi_rd_rdata             (m_axi_rd_rdata),
        .m_axi_rd_rresp             (m_axi_rd_rresp),
        .m_axi_rd_rlast             (m_axi_rd_rlast),
        .m_axi_rd_rvalid            (m_axi_rd_rvalid),
        .m_axi_rd_rready            (m_axi_rd_rready),

        //---------------------------------------------------------------------
        // SINK half - shared-infra (snk_ prefixed)
        //---------------------------------------------------------------------
        .snk_apb_valid              (snk_apb_valid),
        .snk_apb_ready              (snk_apb_ready),
        .snk_apb_addr               (snk_apb_addr),
        .snk_cfg_channel_enable     (snk_cfg_channel_enable),
        .snk_cfg_channel_reset      (snk_cfg_channel_reset),
        .snk_cfg_sched_enable       (snk_cfg_sched_enable),
        .snk_cfg_sched_timeout_cycles(snk_cfg_sched_timeout_cycles),
        .snk_cfg_sched_timeout_limit(snk_cfg_sched_timeout_limit),
        .snk_cfg_sched_timeout_enable(snk_cfg_sched_timeout_enable),
        .snk_cfg_sched_err_enable   (snk_cfg_sched_err_enable),
        .snk_cfg_sched_compl_enable (snk_cfg_sched_compl_enable),
        .snk_cfg_sched_perf_enable  (snk_cfg_sched_perf_enable),
        .snk_cfg_desceng_enable     (snk_cfg_desceng_enable),
        .snk_cfg_desceng_prefetch   (snk_cfg_desceng_prefetch),
        .snk_cfg_desceng_fifo_thresh(snk_cfg_desceng_fifo_thresh),
        .snk_cfg_desceng_addr0_base (snk_cfg_desceng_addr0_base),
        .snk_cfg_desceng_addr0_limit(snk_cfg_desceng_addr0_limit),
        .snk_cfg_desceng_addr1_base (snk_cfg_desceng_addr1_base),
        .snk_cfg_desceng_addr1_limit(snk_cfg_desceng_addr1_limit),
        .snk_cfg_ctrlrd_max_try     (snk_cfg_ctrlrd_max_try),
        .snk_tick_1us               (tick_1us),
        .snk_cfg_desc_mon_enable        (snk_cfg_desc_mon_enable),
        .snk_cfg_desc_mon_err_enable    (snk_cfg_desc_mon_err_enable),
        .snk_cfg_desc_mon_perf_enable   (snk_cfg_desc_mon_perf_enable),
        .snk_cfg_desc_mon_timeout_enable(snk_cfg_desc_mon_timeout_enable),
        .snk_cfg_desc_mon_timeout_cycles(snk_cfg_desc_mon_timeout_cycles),
        .snk_cfg_desc_mon_latency_thresh(snk_cfg_desc_mon_latency_thresh),
        .snk_cfg_desc_mon_pkt_mask      (snk_cfg_desc_mon_pkt_mask),
        .snk_cfg_desc_mon_err_select    (snk_cfg_desc_mon_err_select),
        .snk_cfg_desc_mon_err_mask      (snk_cfg_desc_mon_err_mask),
        .snk_cfg_desc_mon_timeout_mask  (snk_cfg_desc_mon_timeout_mask),
        .snk_cfg_desc_mon_compl_mask    (snk_cfg_desc_mon_compl_mask),
        .snk_cfg_desc_mon_thresh_mask   (snk_cfg_desc_mon_thresh_mask),
        .snk_cfg_desc_mon_perf_mask     (snk_cfg_desc_mon_perf_mask),
        .snk_cfg_desc_mon_addr_mask     (snk_cfg_desc_mon_addr_mask),
        .snk_cfg_desc_mon_debug_mask    (snk_cfg_desc_mon_debug_mask),
        // Status (sink)
        .snk_system_idle                (snk_system_idle),
        .snk_descriptor_engine_idle     (),
        .snk_scheduler_idle             (),
        .snk_scheduler_state            (),
        .snk_sched_error                (snk_sched_error),
        .snk_cfg_sts_desc_mon_busy          (),
        .snk_cfg_sts_desc_mon_active_txns   (),
        .snk_cfg_sts_desc_mon_error_count   (),
        .snk_cfg_sts_desc_mon_txn_count     (),
        .snk_cfg_sts_desc_mon_conflict_error(),
        // Sink descriptor fetch master -> top snk_m_axi_desc_*
        .snk_m_axi_desc_arvalid     (snk_m_axi_desc_arvalid),
        .snk_m_axi_desc_arready     (snk_m_axi_desc_arready),
        .snk_m_axi_desc_araddr      (snk_m_axi_desc_araddr),
        .snk_m_axi_desc_arlen       (snk_m_axi_desc_arlen),
        .snk_m_axi_desc_arsize      (snk_m_axi_desc_arsize),
        .snk_m_axi_desc_arburst     (snk_m_axi_desc_arburst),
        .snk_m_axi_desc_arid        (snk_m_axi_desc_arid),
        .snk_m_axi_desc_arlock      (snk_m_axi_desc_arlock),
        .snk_m_axi_desc_arcache     (snk_m_axi_desc_arcache),
        .snk_m_axi_desc_arprot      (snk_m_axi_desc_arprot),
        .snk_m_axi_desc_arqos       (snk_m_axi_desc_arqos),
        .snk_m_axi_desc_arregion    (snk_m_axi_desc_arregion),
        .snk_m_axi_desc_rvalid      (snk_m_axi_desc_rvalid),
        .snk_m_axi_desc_rready      (snk_m_axi_desc_rready),
        .snk_m_axi_desc_rdata       (snk_m_axi_desc_rdata),
        .snk_m_axi_desc_rresp       (snk_m_axi_desc_rresp),
        .snk_m_axi_desc_rlast       (snk_m_axi_desc_rlast),
        .snk_m_axi_desc_rid         (snk_m_axi_desc_rid),
        // Sink control read master -> top snk_m_axi_ctrlrd_*
        .snk_m_axi_ctrlrd_arvalid   (snk_m_axi_ctrlrd_arvalid),
        .snk_m_axi_ctrlrd_arready   (snk_m_axi_ctrlrd_arready),
        .snk_m_axi_ctrlrd_araddr    (snk_m_axi_ctrlrd_araddr),
        .snk_m_axi_ctrlrd_arlen     (snk_m_axi_ctrlrd_arlen),
        .snk_m_axi_ctrlrd_arsize    (snk_m_axi_ctrlrd_arsize),
        .snk_m_axi_ctrlrd_arburst   (snk_m_axi_ctrlrd_arburst),
        .snk_m_axi_ctrlrd_arid      (snk_m_axi_ctrlrd_arid),
        .snk_m_axi_ctrlrd_arlock    (snk_m_axi_ctrlrd_arlock),
        .snk_m_axi_ctrlrd_arcache   (snk_m_axi_ctrlrd_arcache),
        .snk_m_axi_ctrlrd_arprot    (snk_m_axi_ctrlrd_arprot),
        .snk_m_axi_ctrlrd_arqos     (snk_m_axi_ctrlrd_arqos),
        .snk_m_axi_ctrlrd_arregion  (snk_m_axi_ctrlrd_arregion),
        .snk_m_axi_ctrlrd_rvalid    (snk_m_axi_ctrlrd_rvalid),
        .snk_m_axi_ctrlrd_rready    (snk_m_axi_ctrlrd_rready),
        .snk_m_axi_ctrlrd_rdata     (snk_m_axi_ctrlrd_rdata),
        .snk_m_axi_ctrlrd_rresp     (snk_m_axi_ctrlrd_rresp),
        .snk_m_axi_ctrlrd_rlast     (snk_m_axi_ctrlrd_rlast),
        .snk_m_axi_ctrlrd_rid       (snk_m_axi_ctrlrd_rid),
        // Sink control write master -> top snk_m_axi_ctrlwr_*
        .snk_m_axi_ctrlwr_awvalid   (snk_m_axi_ctrlwr_awvalid),
        .snk_m_axi_ctrlwr_awready   (snk_m_axi_ctrlwr_awready),
        .snk_m_axi_ctrlwr_awaddr    (snk_m_axi_ctrlwr_awaddr),
        .snk_m_axi_ctrlwr_awlen     (snk_m_axi_ctrlwr_awlen),
        .snk_m_axi_ctrlwr_awsize    (snk_m_axi_ctrlwr_awsize),
        .snk_m_axi_ctrlwr_awburst   (snk_m_axi_ctrlwr_awburst),
        .snk_m_axi_ctrlwr_awid      (snk_m_axi_ctrlwr_awid),
        .snk_m_axi_ctrlwr_awlock    (snk_m_axi_ctrlwr_awlock),
        .snk_m_axi_ctrlwr_awcache   (snk_m_axi_ctrlwr_awcache),
        .snk_m_axi_ctrlwr_awprot    (snk_m_axi_ctrlwr_awprot),
        .snk_m_axi_ctrlwr_awqos     (snk_m_axi_ctrlwr_awqos),
        .snk_m_axi_ctrlwr_awregion  (snk_m_axi_ctrlwr_awregion),
        .snk_m_axi_ctrlwr_wvalid    (snk_m_axi_ctrlwr_wvalid),
        .snk_m_axi_ctrlwr_wready    (snk_m_axi_ctrlwr_wready),
        .snk_m_axi_ctrlwr_wdata     (snk_m_axi_ctrlwr_wdata),
        .snk_m_axi_ctrlwr_wstrb     (snk_m_axi_ctrlwr_wstrb),
        .snk_m_axi_ctrlwr_wlast     (snk_m_axi_ctrlwr_wlast),
        .snk_m_axi_ctrlwr_bvalid    (snk_m_axi_ctrlwr_bvalid),
        .snk_m_axi_ctrlwr_bready    (snk_m_axi_ctrlwr_bready),
        .snk_m_axi_ctrlwr_bid       (snk_m_axi_ctrlwr_bid),
        .snk_m_axi_ctrlwr_bresp     (snk_m_axi_ctrlwr_bresp),

        //---------------------------------------------------------------------
        // SINK half - direction-unique (no prefix)
        //---------------------------------------------------------------------
        .cfg_axi_wr_xfer_beats      (snk_cfg_axi_wr_xfer_beats),
        .cfg_alloc_size             (snk_cfg_alloc_size),
        .s_axis_tdata               (s_axis_tdata),
        .s_axis_tstrb               (s_axis_tstrb),
        .s_axis_tlast               (s_axis_tlast),
        .s_axis_tid                 (s_axis_tid),
        .s_axis_tdest               (s_axis_tdest),
        .s_axis_tuser               (s_axis_tuser),
        .s_axis_tvalid              (s_axis_tvalid),
        .s_axis_tready              (s_axis_tready),
        .m_axi_wr_awid              (m_axi_wr_awid),
        .m_axi_wr_awaddr            (m_axi_wr_awaddr),
        .m_axi_wr_awlen             (m_axi_wr_awlen),
        .m_axi_wr_awsize            (m_axi_wr_awsize),
        .m_axi_wr_awburst           (m_axi_wr_awburst),
        .m_axi_wr_awlock            (m_axi_wr_awlock),
        .m_axi_wr_awcache           (m_axi_wr_awcache),
        .m_axi_wr_awprot            (m_axi_wr_awprot),
        .m_axi_wr_awqos             (m_axi_wr_awqos),
        .m_axi_wr_awregion          (m_axi_wr_awregion),
        .m_axi_wr_awvalid           (m_axi_wr_awvalid),
        .m_axi_wr_awready           (m_axi_wr_awready),
        .m_axi_wr_wdata             (m_axi_wr_wdata),
        .m_axi_wr_wstrb             (m_axi_wr_wstrb),
        .m_axi_wr_wlast             (m_axi_wr_wlast),
        .m_axi_wr_wvalid            (m_axi_wr_wvalid),
        .m_axi_wr_wready            (m_axi_wr_wready),
        .m_axi_wr_bid               (m_axi_wr_bid),
        .m_axi_wr_bresp             (m_axi_wr_bresp),
        .m_axi_wr_bvalid            (m_axi_wr_bvalid),
        .m_axi_wr_bready            (m_axi_wr_bready),

        //---------------------------------------------------------------------
        // Single merged MonBus egress
        //---------------------------------------------------------------------
        .mon_valid                  (core_mon_valid),
        .mon_ready                  (core_mon_ready),
        .mon_packet                 (core_mon_packet),
        .mon_timestamp              (core_mon_timestamp),

        //---------------------------------------------------------------------
        // Debug (discarded)
        //---------------------------------------------------------------------
        .src_dbg_rd_all_complete          (),
        .src_dbg_r_beats_rcvd             (),
        .src_dbg_sram_writes              (),
        .src_dbg_arb_request              (),
        .src_dbg_src_sram_bridge_pending  (),
        .src_dbg_src_sram_bridge_out_valid(),
        .src_dbg_axis_beats_sent          (),
        .src_dbg_axis_packets_sent        (),
        .snk_dbg_snk_sram_bridge_pending  (),
        .snk_dbg_snk_sram_bridge_out_valid(),
        .snk_dbg_axis_beats_received      (),
        .snk_dbg_axis_packets_received    ()
    );

    //=========================================================================
    // MonBus AXI-Lite Group: single merged stream -> AXI-Lite err-drain slave
    // + bulk-capture master + IRQ (mirrors stream_top_ch8).
    //
    // Egress packet-filter / compression config is a single SHARED egress cfg,
    // sourced from hwif_out.SRC.MON.* (SNK.MON.* filter fields exist but are
    // not wired here; per-half egress splitting is a later stage).
    //=========================================================================
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

        // Combined MonBus input (from the core's single merged egress)
        .monbus_valid       (core_mon_valid),
        .monbus_ready       (core_mon_ready),
        .monbus_packet      (core_mon_packet),
        .monbus_timestamp   (core_mon_timestamp),
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

        // Config (base/limit/watermark from top-level inputs; compression enable
        // from the shared SRC.MON egress config).
        .cfg_base_addr      (cfg_mon_base_addr),
        .cfg_limit_addr     (cfg_mon_limit_addr),
        .cfg_flush_watermark(cfg_mon_flush_watermark),
        .cfg_compress_en    (hwif_out.SRC.MON.WRMON_ENABLE.COMPRESS_EN.value),

        // Protocol 0 - Descriptor AXI Monitor (DAXMON), shared SRC.MON egress cfg
        .cfg_axi_pkt_mask     (hwif_out.SRC.MON.DAXMON_PKT_MASK.PKT_MASK.value),
        .cfg_axi_err_select   ({12'h000, hwif_out.SRC.MON.DAXMON_ERR_CFG.ERR_SELECT.value}),
        .cfg_axi_error_mask   ({8'h00,   hwif_out.SRC.MON.DAXMON_ERR_CFG.ERR_MASK.value}),
        .cfg_axi_timeout_mask ({8'h00,   hwif_out.SRC.MON.DAXMON_MASK1.TIMEOUT_MASK.value}),
        .cfg_axi_compl_mask   ({8'h00,   hwif_out.SRC.MON.DAXMON_MASK1.COMPL_MASK.value}),
        .cfg_axi_thresh_mask  ({8'h00,   hwif_out.SRC.MON.DAXMON_MASK2.THRESH_MASK.value}),
        .cfg_axi_perf_mask    ({8'h00,   hwif_out.SRC.MON.DAXMON_MASK2.PERF_MASK.value}),
        .cfg_axi_addr_mask    ({8'h00,   hwif_out.SRC.MON.DAXMON_MASK3.ADDR_MASK.value}),
        .cfg_axi_debug_mask   ({8'h00,   hwif_out.SRC.MON.DAXMON_MASK3.DEBUG_MASK.value}),

        // Protocol 1 - Read Engine Monitor (RDMON). AXIS ports reused.
        .cfg_axis_pkt_mask    (hwif_out.SRC.MON.RDMON_PKT_MASK.PKT_MASK.value),
        .cfg_axis_err_select  ({12'h000, hwif_out.SRC.MON.RDMON_ERR_CFG.ERR_SELECT.value}),
        .cfg_axis_error_mask  ({8'h00,   hwif_out.SRC.MON.RDMON_ERR_CFG.ERR_MASK.value}),
        .cfg_axis_timeout_mask({8'h00,   hwif_out.SRC.MON.RDMON_MASK1.TIMEOUT_MASK.value}),
        .cfg_axis_compl_mask  ({8'h00,   hwif_out.SRC.MON.RDMON_MASK1.COMPL_MASK.value}),
        .cfg_axis_credit_mask ({8'h00,   hwif_out.SRC.MON.RDMON_MASK2.THRESH_MASK.value}),
        .cfg_axis_channel_mask({8'h00,   hwif_out.SRC.MON.RDMON_MASK2.PERF_MASK.value}),
        .cfg_axis_stream_mask ({8'h00,   hwif_out.SRC.MON.RDMON_MASK3.ADDR_MASK.value}),

        // Protocol 2 - Write Engine Monitor (WRMON). CORE ports reused.
        .cfg_core_pkt_mask    (hwif_out.SRC.MON.WRMON_PKT_MASK.PKT_MASK.value),
        .cfg_core_err_select  ({12'h000, hwif_out.SRC.MON.WRMON_ERR_CFG.ERR_SELECT.value}),
        .cfg_core_error_mask  ({8'h00,   hwif_out.SRC.MON.WRMON_ERR_CFG.ERR_MASK.value}),
        .cfg_core_timeout_mask({8'h00,   hwif_out.SRC.MON.WRMON_MASK1.TIMEOUT_MASK.value}),
        .cfg_core_compl_mask  ({8'h00,   hwif_out.SRC.MON.WRMON_MASK1.COMPL_MASK.value}),
        .cfg_core_thresh_mask ({8'h00,   hwif_out.SRC.MON.WRMON_MASK2.THRESH_MASK.value}),
        .cfg_core_perf_mask   ({8'h00,   hwif_out.SRC.MON.WRMON_MASK2.PERF_MASK.value}),
        .cfg_core_debug_mask  ({8'h00,   hwif_out.SRC.MON.WRMON_MASK3.DEBUG_MASK.value}),

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

endmodule : rapids_beats_top
