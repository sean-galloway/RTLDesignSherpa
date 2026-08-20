// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: dma_slave_monitors
// Purpose: Monitored DMA-slave wrapper for the STREAM monitor-validation
//          harness. Mirrors how stream_top_ch8 exposes its in-core monitors:
//          the slave-side monitors feed a monbus_axil_axil_group, which drives
//          an AXIL master (bulk-trace writes -> a tally SRAM that lives on the
//          bridge as its OWN slave) plus an AXIL slave-read err/IRQ port.
//
//   s_axi ─▶ axi4_slave_rd_mon ─▶ fub ─▶ ┐
//   (STREAM) axi4_slave_wr_mon ─▶ fub ─▶ ├─▶ axi4_dma_slaves (LFSR rd / CRC wr)
//                  │ monbus              ┘
//                  └─▶ monbus_arbiter(2) ─▶ monbus_axil_axil_group ─▶ m_axil_* (to bridge)
//                                                                  └─▶ s_axil_* (err read)
//
// NO tally is instantiated here — the tally SRAM is a separate bridge slave,
// written by m_axil_* (exactly like STREAM's debug_sram capture). The read and
// write monitors have INDEPENDENT cfg controls (cfg_rd_* / cfg_wr_*).
//
// Subsystem: NexysA7/stream_characterization (monitor flow)
// Author: sean galloway

`timescale 1ns / 1ps
`include "reset_defs.svh"

module dma_slave_monitors
    import monitor_common_pkg::*;
#(
    parameter int NUM_CHANNELS   = 4,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 512,
    parameter int AXI_USER_WIDTH = 1,
    parameter int MAX_TRANSACTIONS = 16,
    // monbus group
    parameter int FIFO_DEPTH_ERR    = 64,
    parameter int FIFO_DEPTH_WRITE  = 96,
    parameter int S_AXIL_DATA_WIDTH = 32,
    parameter int USE_COMPRESSION   = 0,
    parameter int APB_ADDR_WIDTH    = 12,
    // Derived
    parameter int SW = AXI_DATA_WIDTH / 8
) (
    input  logic                          aclk,
    input  logic                          aresetn,
    input  logic                          cam_clear,

    // ---- DMA-slave observation (passthrough from axi4_dma_slaves) ----------
    input  logic                          read_lfsr_reset,
    input  logic                          write_crc_reset,
    output logic [NUM_CHANNELS-1:0][31:0] read_crc_value,
    output logic [NUM_CHANNELS-1:0]       read_crc_valid,
    output logic [NUM_CHANNELS-1:0][31:0] read_beat_count,
    output logic [31:0]                   read_beat_count_total,
    output logic [NUM_CHANNELS-1:0][31:0] write_crc_value,
    output logic [NUM_CHANNELS-1:0]       write_crc_valid,
    output logic [NUM_CHANNELS-1:0][31:0] write_beat_count,
    output logic [31:0]                   write_beat_count_total,
    output logic                          busy_rd,
    output logic                          busy_wr,

    // ---- AXI4 slave interface (STREAM is the master) -----------------------
    input  logic [AXI_ID_WIDTH-1:0]       s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_axi_araddr,
    input  logic [7:0]                    s_axi_arlen,
    input  logic [2:0]                    s_axi_arsize,
    input  logic [1:0]                    s_axi_arburst,
    input  logic                          s_axi_arlock,
    input  logic [3:0]                    s_axi_arcache,
    input  logic [2:0]                    s_axi_arprot,
    input  logic [3:0]                    s_axi_arqos,
    input  logic [3:0]                    s_axi_arregion,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_aruser,
    input  logic                          s_axi_arvalid,
    output logic                          s_axi_arready,
    output logic [AXI_ID_WIDTH-1:0]       s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0]     s_axi_rdata,
    output logic [1:0]                    s_axi_rresp,
    output logic                          s_axi_rlast,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_ruser,
    output logic                          s_axi_rvalid,
    input  logic                          s_axi_rready,

    input  logic [AXI_ID_WIDTH-1:0]       s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_axi_awaddr,
    input  logic [7:0]                    s_axi_awlen,
    input  logic [2:0]                    s_axi_awsize,
    input  logic [1:0]                    s_axi_awburst,
    input  logic                          s_axi_awlock,
    input  logic [3:0]                    s_axi_awcache,
    input  logic [2:0]                    s_axi_awprot,
    input  logic [3:0]                    s_axi_awqos,
    input  logic [3:0]                    s_axi_awregion,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_awuser,
    input  logic                          s_axi_awvalid,
    output logic                          s_axi_awready,
    input  logic [AXI_DATA_WIDTH-1:0]     s_axi_wdata,
    input  logic [SW-1:0]                 s_axi_wstrb,
    input  logic                          s_axi_wlast,
    input  logic [AXI_USER_WIDTH-1:0]     s_axi_wuser,
    input  logic                          s_axi_wvalid,
    output logic                          s_axi_wready,
    output logic [AXI_ID_WIDTH-1:0]       s_axi_bid,
    output logic [1:0]                    s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0]     s_axi_buser,
    output logic                          s_axi_bvalid,
    input  logic                          s_axi_bready,

    // ---- READ monitor config (independent) ---------------------------------

    // ---- WRITE monitor config (independent) --------------------------------

    // ---- monbus group: err/IRQ AXIL slave-read (to a bridge slave) ---------
    input  logic                          s_axil_arvalid,
    output logic                          s_axil_arready,
    input  logic [AXI_ADDR_WIDTH-1:0]     s_axil_araddr,
    input  logic [2:0]                    s_axil_arprot,
    output logic                          s_axil_rvalid,
    input  logic                          s_axil_rready,
    output logic [S_AXIL_DATA_WIDTH-1:0]  s_axil_rdata,
    output logic [1:0]                    s_axil_rresp,

    // ---- monbus group: bulk-trace AXIL master-write (to the tally slave) ---
    output logic                          m_axil_awvalid,
    input  logic                          m_axil_awready,
    output logic [AXI_ADDR_WIDTH-1:0]     m_axil_awaddr,
    output logic [2:0]                    m_axil_awprot,
    output logic                          m_axil_wvalid,
    input  logic                          m_axil_wready,
    output logic [63:0]                   m_axil_wdata,
    output logic [7:0]                    m_axil_wstrb,
    input  logic                          m_axil_bvalid,
    output logic                          m_axil_bready,
    input  logic [1:0]                    m_axil_bresp,

    output logic                          irq_out,
    // ---- APB configuration slave -------------------------------------
    // The slave monitors own their configuration rather than exporting ~28
    // ports for the harness to drive. Same chain stream_top_ch8 uses:
    //   flat APB -> apb4_slave -> peakrdl_to_cmdrsp -> slvmon_regs_top
    // (no cmdrsp_router: STREAM needs one because it has two targets behind
    // the APB; this block has one.)
    input  logic                          s_apb_psel,
    input  logic                          s_apb_penable,
    output logic                          s_apb_pready,
    input  logic [APB_ADDR_WIDTH-1:0]     s_apb_paddr,
    input  logic                          s_apb_pwrite,
    input  logic [31:0]                   s_apb_pwdata,
    input  logic [3:0]                    s_apb_pstrb,
    output logic [31:0]                   s_apb_prdata,
    output logic                          s_apb_pslverr,

    input  logic [AXI_ADDR_WIDTH-1:0]     cfg_base_addr,
    input  logic [AXI_ADDR_WIDTH-1:0]     cfg_limit_addr
);

    // Free-running monitor timestamp comes from the group; broadcast to both mons.
    monbus_timestamp_t w_mon_time;

    // Two monbus streams -> arbiter (client 0 = read, 1 = write).
    logic              mb_valid [2];
    logic              mb_ready [2];
    monitor_packet_t   mb_packet [2];
    monbus_timestamp_t mb_ts    [2];

    // Internal AXI wires: monitor fub side -> axi4_dma_slaves s_axi side.
    logic [AXI_ID_WIDTH-1:0]   i_arid;   logic [AXI_ADDR_WIDTH-1:0] i_araddr;
    logic [7:0]                i_arlen;  logic [2:0]                i_arsize;
    logic [1:0]                i_arburst; logic                     i_arlock;
    logic [3:0]                i_arcache; logic [2:0]               i_arprot;
    logic [3:0]                i_arqos;  logic [3:0]                i_arregion;
    logic [AXI_USER_WIDTH-1:0] i_aruser; logic                     i_arvalid, i_arready;
    logic [AXI_ID_WIDTH-1:0]   i_rid;    logic [AXI_DATA_WIDTH-1:0] i_rdata;
    logic [1:0]                i_rresp;  logic                      i_rlast;
    logic [AXI_USER_WIDTH-1:0] i_ruser;  logic                      i_rvalid, i_rready;
    logic [AXI_ID_WIDTH-1:0]   i_awid;   logic [AXI_ADDR_WIDTH-1:0] i_awaddr;
    logic [7:0]                i_awlen;  logic [2:0]                i_awsize;
    logic [1:0]                i_awburst; logic                     i_awlock;
    logic [3:0]                i_awcache; logic [2:0]               i_awprot;
    logic [3:0]                i_awqos;  logic [3:0]                i_awregion;
    logic [AXI_USER_WIDTH-1:0] i_awuser; logic                     i_awvalid, i_awready;
    logic [AXI_DATA_WIDTH-1:0] i_wdata;  logic [SW-1:0]            i_wstrb;
    logic                      i_wlast;  logic [AXI_USER_WIDTH-1:0] i_wuser;
    logic                      i_wvalid, i_wready;
    logic [AXI_ID_WIDTH-1:0]   i_bid;    logic [1:0]               i_bresp;
    logic [AXI_USER_WIDTH-1:0] i_buser;  logic                     i_bvalid, i_bready;

    // Agent-id reservation (keep in sync with stream_core's map): STREAM owns
    // agents 8 (desc-AXI), 9 (rd), 10 (wr), 16-23 (desc engines), 48-55
    // (schedulers). These test-slave monitors use 0x0001/0x0002 -- a reserved
    // band BELOW STREAM's range that must never overlap it, so a combined
    // stream+slave tally analysis keys unambiguously by agent id.

    // ---- Read-side slave monitor (independent cfg_rd_*) --------------------
    // =======================================================================
    // Configuration: APB -> cmd/rsp -> passthrough regblock
    // -----------------------------------------------------------------------
    // The same chain stream_top_ch8 uses. Everything below used to be tied off
    // here (latency threshold pinned at max, address checker held off, all nine
    // event masks zero), which is why these monitors could only ever emit
    // COMPLETION on silicon -- there was no way for a host to say otherwise.
    // =======================================================================
    logic                        w_cmd_valid, w_cmd_ready, w_cmd_pwrite;
    logic [APB_ADDR_WIDTH-1:0]   w_cmd_paddr;
    logic [31:0]                 w_cmd_pwdata;
    logic [3:0]                  w_cmd_pstrb;
    logic [2:0]                  w_cmd_pprot;
    logic                        w_rsp_valid, w_rsp_ready, w_rsp_pslverr;
    logic [31:0]                 w_rsp_prdata;

    apb4_slave #(
        .ADDR_WIDTH(APB_ADDR_WIDTH), .DATA_WIDTH(32)
    ) u_apb_slave (
        .pclk(aclk), .presetn(aresetn),
        .s_apb_PSEL(s_apb_psel),       .s_apb_PENABLE(s_apb_penable),
        .s_apb_PREADY(s_apb_pready),   .s_apb_PADDR(s_apb_paddr),
        .s_apb_PWRITE(s_apb_pwrite),   .s_apb_PWDATA(s_apb_pwdata),
        .s_apb_PSTRB(s_apb_pstrb),     .s_apb_PPROT(3'b000),
        .s_apb_PRDATA(s_apb_prdata),   .s_apb_PSLVERR(s_apb_pslverr),
        .cmd_valid(w_cmd_valid),   .cmd_ready(w_cmd_ready),
        .cmd_pwrite(w_cmd_pwrite), .cmd_paddr(w_cmd_paddr),
        .cmd_pwdata(w_cmd_pwdata), .cmd_pstrb(w_cmd_pstrb), .cmd_pprot(w_cmd_pprot),
        .rsp_valid(w_rsp_valid),   .rsp_ready(w_rsp_ready),
        .rsp_prdata(w_rsp_prdata), .rsp_pslverr(w_rsp_pslverr)
    );

    logic        w_rb_req, w_rb_req_is_wr, w_rb_stall_wr, w_rb_stall_rd;
    logic        w_rb_rd_ack, w_rb_rd_err, w_rb_wr_ack, w_rb_wr_err;
    logic [APB_ADDR_WIDTH-1:0] w_rb_addr;
    logic [31:0] w_rb_wr_data, w_rb_wr_biten, w_rb_rd_data;

    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH(APB_ADDR_WIDTH), .DATA_WIDTH(32)
    ) u_peakrdl_adapter (
        .aclk(aclk), .aresetn(aresetn),
        .cmd_valid(w_cmd_valid),   .cmd_ready(w_cmd_ready),
        .cmd_pwrite(w_cmd_pwrite), .cmd_paddr(w_cmd_paddr),
        .cmd_pwdata(w_cmd_pwdata), .cmd_pstrb(w_cmd_pstrb),
        .rsp_valid(w_rsp_valid),   .rsp_ready(w_rsp_ready),
        .rsp_prdata(w_rsp_prdata), .rsp_pslverr(w_rsp_pslverr),
        .regblk_req(w_rb_req),               .regblk_req_is_wr(w_rb_req_is_wr),
        .regblk_addr(w_rb_addr),             .regblk_wr_data(w_rb_wr_data),
        .regblk_wr_biten(w_rb_wr_biten),
        .regblk_req_stall_wr(w_rb_stall_wr), .regblk_req_stall_rd(w_rb_stall_rd),
        .regblk_rd_ack(w_rb_rd_ack),         .regblk_rd_err(w_rb_rd_err),
        .regblk_rd_data(w_rb_rd_data),
        .regblk_wr_ack(w_rb_wr_ack),         .regblk_wr_err(w_rb_wr_err)
    );

    slvmon_regs_top_pkg::slvmon_regs_top__out_t hwif;

    slvmon_regs_top u_slvmon_regs (
        .clk(aclk), .rst(~aresetn),          // PeakRDL wants active-high reset
        .s_cpuif_req(w_rb_req),              .s_cpuif_req_is_wr(w_rb_req_is_wr),
        .s_cpuif_addr(7'(w_rb_addr)),        .s_cpuif_wr_data(w_rb_wr_data),
        .s_cpuif_wr_biten(w_rb_wr_biten),
        .s_cpuif_req_stall_wr(w_rb_stall_wr),.s_cpuif_req_stall_rd(w_rb_stall_rd),
        .s_cpuif_rd_ack(w_rb_rd_ack),        .s_cpuif_rd_err(w_rb_rd_err),
        .s_cpuif_rd_data(w_rb_rd_data),
        .s_cpuif_wr_ack(w_rb_wr_ack),        .s_cpuif_wr_err(w_rb_wr_err),
        .hwif_out(hwif)
    );

    axi4_slave_rd_mon #(
        .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH), .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .MAX_TRANSACTIONS(MAX_TRANSACTIONS), .UNIT_ID(8'h10), .AGENT_ID(16'h0001)  // reserved slave band (< STREAM's 8)
    ) u_rd_mon (
        .aclk(aclk), .aresetn(aresetn), .cam_clear(cam_clear),
        .s_axi_arid(s_axi_arid), .s_axi_araddr(s_axi_araddr),
        .s_axi_arlen(s_axi_arlen), .s_axi_arsize(s_axi_arsize),
        .s_axi_arburst(s_axi_arburst), .s_axi_arlock(s_axi_arlock),
        .s_axi_arcache(s_axi_arcache), .s_axi_arprot(s_axi_arprot),
        .s_axi_arqos(s_axi_arqos), .s_axi_arregion(s_axi_arregion),
        .s_axi_aruser(s_axi_aruser), .s_axi_arvalid(s_axi_arvalid),
        .s_axi_arready(s_axi_arready),
        .s_axi_rid(s_axi_rid), .s_axi_rdata(s_axi_rdata),
        .s_axi_rresp(s_axi_rresp), .s_axi_rlast(s_axi_rlast),
        .s_axi_ruser(s_axi_ruser), .s_axi_rvalid(s_axi_rvalid),
        .s_axi_rready(s_axi_rready),
        .fub_axi_arid(i_arid), .fub_axi_araddr(i_araddr),
        .fub_axi_arlen(i_arlen), .fub_axi_arsize(i_arsize),
        .fub_axi_arburst(i_arburst), .fub_axi_arlock(i_arlock),
        .fub_axi_arcache(i_arcache), .fub_axi_arprot(i_arprot),
        .fub_axi_arqos(i_arqos), .fub_axi_arregion(i_arregion),
        .fub_axi_aruser(i_aruser), .fub_axi_arvalid(i_arvalid),
        .fub_axi_arready(i_arready),
        .fub_axi_rid(i_rid), .fub_axi_rdata(i_rdata),
        .fub_axi_rresp(i_rresp), .fub_axi_rlast(i_rlast),
        .fub_axi_ruser(i_ruser), .fub_axi_rvalid(i_rvalid),
        .fub_axi_rready(i_rready),
        .cfg_monitor_enable(hwif.SLVMON.RDSLV_ENABLE.MON_EN.value), .cfg_error_enable(hwif.SLVMON.RDSLV_ENABLE.ERR_EN.value),
        .cfg_timeout_enable(hwif.SLVMON.RDSLV_ENABLE.TIMEOUT_EN.value), .cfg_perf_enable(hwif.SLVMON.RDSLV_ENABLE.PERF_EN.value),
        .cfg_compl_enable(hwif.SLVMON.RDSLV_ENABLE.COMPL_EN.value), .cfg_threshold_enable(hwif.SLVMON.RDSLV_ENABLE.THRESH_EN.value),
        .cfg_debug_enable(hwif.SLVMON.RDSLV_ENABLE.DEBUG_EN.value), .cfg_timeout_cycles(hwif.SLVMON.RDSLV_TIMEOUT.TIMEOUT_CYCLES.value),
        // ACLK_MHZ is left at its default here, so the CFI LUT is degenerate
        // (every entry == ACLK_MHZ) and any index gives an exact 1 us tick.
        // Set ACLK_MHZ + a real CFI_MIN/MAX range and drive this from a CSR
        // if this block ever needs runtime frequency selection.
        .cfg_freq_sel(4'b0000),
        .cfg_latency_threshold(hwif.SLVMON.RDSLV_LATENCY_THRESH.VALUE.value),
        .cfg_axi_pkt_mask  (hwif.SLVMON.RDSLV_PKT_MASK.PKT_MASK.value),
        .cfg_axi_err_select(hwif.SLVMON.RDSLV_PKT_MASK.ERR_SELECT.value),
        .cfg_axi_error_mask  (hwif.SLVMON.RDSLV_MASK1.ERROR_MASK.value),
        .cfg_axi_timeout_mask(hwif.SLVMON.RDSLV_MASK1.TIMEOUT_MASK.value),
        .cfg_axi_compl_mask  (hwif.SLVMON.RDSLV_MASK2.COMPL_MASK.value),
        .cfg_axi_thresh_mask (hwif.SLVMON.RDSLV_MASK2.THRESH_MASK.value),
        .cfg_axi_perf_mask   (hwif.SLVMON.RDSLV_MASK3.PERF_MASK.value),
        .cfg_axi_addr_mask   (hwif.SLVMON.RDSLV_MASK3.ADDR_MASK.value),
        .cfg_axi_debug_mask  (hwif.SLVMON.RDSLV_MASK4.DEBUG_MASK.value),
        .cfg_addr_check_enable(hwif.SLVMON.RDSLV_ENABLE.ADDR_CHECK_EN.value),
        .cfg_addr_range_enable(hwif.SLVMON.RDSLV_ENABLE.ADDR_RANGE_EN.value),
        .cfg_addr_range_low (hwif.SLVMON.RDSLV_ADDR_RANGE_LOW.VALUE.value),
        .cfg_addr_range_high(hwif.SLVMON.RDSLV_ADDR_RANGE_HIGH.VALUE.value),
        .cfg_start_event_sel(3'h0), .cfg_end_event_sel(3'h0),
        .cfg_start_trigger(1'b0), .cfg_end_trigger(1'b0),
        .cfg_window_force_close(1'b0), .i_mon_time(w_mon_time),
        .monbus_valid(mb_valid[0]), .monbus_ready(mb_ready[0]),
        .monbus_packet(mb_packet[0]), .monbus_timestamp(mb_ts[0]),
        .busy(), .active_transactions(), .error_count(), .transaction_count(),
        .window_active(), .window_cycles(),
        .perf_prod_cycles(), .perf_bp_cycles(), .perf_starv_cycles(),
        .perf_idle_cycles(), .perf_beat_count(), .perf_byte_count(),
        .perf_burst_count(), .cfg_conflict_error()
    );

    // ---- Write-side slave monitor (independent cfg_wr_*) -------------------
    axi4_slave_wr_mon #(
        .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH), .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .MAX_TRANSACTIONS(MAX_TRANSACTIONS), .UNIT_ID(8'h11), .AGENT_ID(16'h0002)
    ) u_wr_mon (
        .aclk(aclk), .aresetn(aresetn), .cam_clear(cam_clear),
        .s_axi_awid(s_axi_awid), .s_axi_awaddr(s_axi_awaddr),
        .s_axi_awlen(s_axi_awlen), .s_axi_awsize(s_axi_awsize),
        .s_axi_awburst(s_axi_awburst), .s_axi_awlock(s_axi_awlock),
        .s_axi_awcache(s_axi_awcache), .s_axi_awprot(s_axi_awprot),
        .s_axi_awqos(s_axi_awqos), .s_axi_awregion(s_axi_awregion),
        .s_axi_awuser(s_axi_awuser), .s_axi_awvalid(s_axi_awvalid),
        .s_axi_awready(s_axi_awready),
        .s_axi_wdata(s_axi_wdata), .s_axi_wstrb(s_axi_wstrb),
        .s_axi_wlast(s_axi_wlast), .s_axi_wuser(s_axi_wuser),
        .s_axi_wvalid(s_axi_wvalid), .s_axi_wready(s_axi_wready),
        .s_axi_bid(s_axi_bid), .s_axi_bresp(s_axi_bresp),
        .s_axi_buser(s_axi_buser), .s_axi_bvalid(s_axi_bvalid),
        .s_axi_bready(s_axi_bready),
        .fub_axi_awid(i_awid), .fub_axi_awaddr(i_awaddr),
        .fub_axi_awlen(i_awlen), .fub_axi_awsize(i_awsize),
        .fub_axi_awburst(i_awburst), .fub_axi_awlock(i_awlock),
        .fub_axi_awcache(i_awcache), .fub_axi_awprot(i_awprot),
        .fub_axi_awqos(i_awqos), .fub_axi_awregion(i_awregion),
        .fub_axi_awuser(i_awuser), .fub_axi_awvalid(i_awvalid),
        .fub_axi_awready(i_awready),
        .fub_axi_wdata(i_wdata), .fub_axi_wstrb(i_wstrb),
        .fub_axi_wlast(i_wlast), .fub_axi_wuser(i_wuser),
        .fub_axi_wvalid(i_wvalid), .fub_axi_wready(i_wready),
        .fub_axi_bid(i_bid), .fub_axi_bresp(i_bresp),
        .fub_axi_buser(i_buser), .fub_axi_bvalid(i_bvalid),
        .fub_axi_bready(i_bready),
        .cfg_monitor_enable(hwif.SLVMON.WRSLV_ENABLE.MON_EN.value), .cfg_error_enable(hwif.SLVMON.WRSLV_ENABLE.ERR_EN.value),
        .cfg_timeout_enable(hwif.SLVMON.WRSLV_ENABLE.TIMEOUT_EN.value), .cfg_perf_enable(hwif.SLVMON.WRSLV_ENABLE.PERF_EN.value),
        .cfg_compl_enable(hwif.SLVMON.WRSLV_ENABLE.COMPL_EN.value), .cfg_threshold_enable(hwif.SLVMON.WRSLV_ENABLE.THRESH_EN.value),
        .cfg_debug_enable(hwif.SLVMON.WRSLV_ENABLE.DEBUG_EN.value), .cfg_timeout_cycles(hwif.SLVMON.WRSLV_TIMEOUT.TIMEOUT_CYCLES.value),
        .cfg_freq_sel(4'b0000),
        .cfg_latency_threshold(hwif.SLVMON.WRSLV_LATENCY_THRESH.VALUE.value),
        .cfg_axi_pkt_mask  (hwif.SLVMON.WRSLV_PKT_MASK.PKT_MASK.value),
        .cfg_axi_err_select(hwif.SLVMON.WRSLV_PKT_MASK.ERR_SELECT.value),
        .cfg_axi_error_mask  (hwif.SLVMON.WRSLV_MASK1.ERROR_MASK.value),
        .cfg_axi_timeout_mask(hwif.SLVMON.WRSLV_MASK1.TIMEOUT_MASK.value),
        .cfg_axi_compl_mask  (hwif.SLVMON.WRSLV_MASK2.COMPL_MASK.value),
        .cfg_axi_thresh_mask (hwif.SLVMON.WRSLV_MASK2.THRESH_MASK.value),
        .cfg_axi_perf_mask   (hwif.SLVMON.WRSLV_MASK3.PERF_MASK.value),
        .cfg_axi_addr_mask   (hwif.SLVMON.WRSLV_MASK3.ADDR_MASK.value),
        .cfg_axi_debug_mask  (hwif.SLVMON.WRSLV_MASK4.DEBUG_MASK.value),
        .cfg_addr_check_enable(hwif.SLVMON.WRSLV_ENABLE.ADDR_CHECK_EN.value),
        .cfg_addr_range_enable(hwif.SLVMON.WRSLV_ENABLE.ADDR_RANGE_EN.value),
        .cfg_addr_range_low (hwif.SLVMON.WRSLV_ADDR_RANGE_LOW.VALUE.value),
        .cfg_addr_range_high(hwif.SLVMON.WRSLV_ADDR_RANGE_HIGH.VALUE.value),
        .cfg_start_event_sel(3'h0), .cfg_end_event_sel(3'h0),
        .cfg_start_trigger(1'b0), .cfg_end_trigger(1'b0),
        .cfg_window_force_close(1'b0), .i_mon_time(w_mon_time),
        .monbus_valid(mb_valid[1]), .monbus_ready(mb_ready[1]),
        .monbus_packet(mb_packet[1]), .monbus_timestamp(mb_ts[1]),
        .busy(), .active_transactions(), .error_count(), .transaction_count(),
        .window_active(), .window_cycles(),
        .perf_prod_cycles(), .perf_bp_cycles(), .perf_starv_cycles(),
        .perf_idle_cycles(), .perf_beat_count(), .perf_byte_count(),
        .perf_burst_count(), .cfg_conflict_error()
    );

    // ---- The DMA slaves themselves (behind the monitors) -------------------
    axi4_dma_slaves #(
        .NUM_CHANNELS(NUM_CHANNELS), .AXI_ID_WIDTH(AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH), .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
        .AXI_USER_WIDTH(AXI_USER_WIDTH)
    ) u_dma_slaves (
        .aclk(aclk), .aresetn(aresetn),
        .read_lfsr_reset(read_lfsr_reset), .write_crc_reset(write_crc_reset),
        .read_crc_value(read_crc_value), .read_crc_valid(read_crc_valid),
        .read_beat_count(read_beat_count), .read_beat_count_total(read_beat_count_total),
        .write_crc_value(write_crc_value), .write_crc_valid(write_crc_valid),
        .write_beat_count(write_beat_count), .write_beat_count_total(write_beat_count_total),
        .s_axi_arid(i_arid), .s_axi_araddr(i_araddr), .s_axi_arlen(i_arlen),
        .s_axi_arsize(i_arsize), .s_axi_arburst(i_arburst), .s_axi_arlock(i_arlock),
        .s_axi_arcache(i_arcache), .s_axi_arprot(i_arprot), .s_axi_arqos(i_arqos),
        .s_axi_arregion(i_arregion), .s_axi_aruser(i_aruser),
        .s_axi_arvalid(i_arvalid), .s_axi_arready(i_arready),
        .s_axi_rid(i_rid), .s_axi_rdata(i_rdata), .s_axi_rresp(i_rresp),
        .s_axi_rlast(i_rlast), .s_axi_ruser(i_ruser), .s_axi_rvalid(i_rvalid),
        .s_axi_rready(i_rready),
        .s_axi_awid(i_awid), .s_axi_awaddr(i_awaddr), .s_axi_awlen(i_awlen),
        .s_axi_awsize(i_awsize), .s_axi_awburst(i_awburst), .s_axi_awlock(i_awlock),
        .s_axi_awcache(i_awcache), .s_axi_awprot(i_awprot), .s_axi_awqos(i_awqos),
        .s_axi_awregion(i_awregion), .s_axi_awuser(i_awuser),
        .s_axi_awvalid(i_awvalid), .s_axi_awready(i_awready),
        .s_axi_wdata(i_wdata), .s_axi_wstrb(i_wstrb), .s_axi_wlast(i_wlast),
        .s_axi_wuser(i_wuser), .s_axi_wvalid(i_wvalid), .s_axi_wready(i_wready),
        .s_axi_bid(i_bid), .s_axi_bresp(i_bresp), .s_axi_buser(i_buser),
        .s_axi_bvalid(i_bvalid), .s_axi_bready(i_bready),
        .busy_rd(busy_rd), .busy_wr(busy_wr)
    );

    // ---- Aggregate the two monbus streams -> one ---------------------------
    logic              arb_valid, arb_ready;
    monitor_packet_t   arb_packet;
    monbus_timestamp_t arb_ts;

    monbus_arbiter #(.CLIENTS(2)) u_arb (
        .axi_aclk(aclk), .axi_aresetn(aresetn), .block_arb(1'b0),
        .monbus_valid_in(mb_valid), .monbus_ready_in(mb_ready),
        .monbus_packet_in(mb_packet), .monbus_timestamp_in(mb_ts),
        .monbus_valid(arb_valid), .monbus_ready(arb_ready),
        .monbus_packet(arb_packet), .monbus_timestamp(arb_ts),
        .grant_valid(), .grant(), .grant_id(), .last_grant()
    );

    // ---- monbus group: AXIL master-write (to tally slave) + err read + IRQ -
    monbus_axil_axil_group #(
        .FIFO_DEPTH_ERR(FIFO_DEPTH_ERR), .FIFO_DEPTH_WRITE(FIFO_DEPTH_WRITE),
        .ADDR_WIDTH(AXI_ADDR_WIDTH), .S_AXIL_DATA_WIDTH(S_AXIL_DATA_WIDTH),
        .NUM_PROTOCOLS(3), .USE_COMPRESSION(USE_COMPRESSION)
    ) u_monbus_group (
        .axi_aclk(aclk), .axi_aresetn(aresetn), .cam_clear(cam_clear),
        .monbus_valid(arb_valid), .monbus_ready(arb_ready),
        .monbus_packet(arb_packet), .monbus_timestamp(arb_ts),
        .mon_time_out(w_mon_time),
        .s_axil_arvalid(s_axil_arvalid), .s_axil_arready(s_axil_arready),
        .s_axil_araddr(s_axil_araddr), .s_axil_arprot(s_axil_arprot),
        .s_axil_rvalid(s_axil_rvalid), .s_axil_rready(s_axil_rready),
        .s_axil_rdata(s_axil_rdata), .s_axil_rresp(s_axil_rresp),
        .m_axil_awvalid(m_axil_awvalid), .m_axil_awready(m_axil_awready),
        .m_axil_awaddr(m_axil_awaddr), .m_axil_awprot(m_axil_awprot),
        .m_axil_wvalid(m_axil_wvalid), .m_axil_wready(m_axil_wready),
        .m_axil_wdata(m_axil_wdata), .m_axil_wstrb(m_axil_wstrb),
        .m_axil_bvalid(m_axil_bvalid), .m_axil_bready(m_axil_bready),
        .m_axil_bresp(m_axil_bresp),
        .irq_out(irq_out),
        .cfg_base_addr(cfg_base_addr), .cfg_limit_addr(cfg_limit_addr),
        // Filter masks: pass everything (0 = no drop); no compression for initial tests.
        .cfg_flush_watermark(16'd16), .cfg_compress_en(USE_COMPRESSION[0]),
        .cfg_axi_pkt_mask(16'h0),  .cfg_axi_err_select(16'h0),
        .cfg_axi_error_mask(16'h0), .cfg_axi_timeout_mask(16'h0),
        .cfg_axi_compl_mask(16'h0), .cfg_axi_thresh_mask(16'h0),
        .cfg_axi_perf_mask(16'h0),  .cfg_axi_addr_mask(16'h0),
        .cfg_axi_debug_mask(16'h0),
        .cfg_axis_pkt_mask(16'h0),  .cfg_axis_err_select(16'h0),
        .cfg_axis_error_mask(16'h0), .cfg_axis_timeout_mask(16'h0),
        .cfg_axis_compl_mask(16'h0), .cfg_axis_credit_mask(16'h0),
        .cfg_axis_channel_mask(16'h0), .cfg_axis_stream_mask(16'h0),
        .cfg_core_pkt_mask(16'h0),  .cfg_core_err_select(16'h0),
        .cfg_core_error_mask(16'h0), .cfg_core_timeout_mask(16'h0),
        .cfg_core_compl_mask(16'h0), .cfg_core_thresh_mask(16'h0),
        .cfg_core_perf_mask(16'h0), .cfg_core_debug_mask(16'h0)
    );


endmodule : dma_slave_monitors
