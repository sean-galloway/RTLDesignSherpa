// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: dma_slave_monitors
// Purpose: Monitored DMA-slave wrapper for the STREAM monitor-validation
//          harness. Holds the DMA read/write slaves (axi4_dma_slaves) AND the
//          monitor group that observes them, so the whole slave-side monitor
//          subsystem is one drop-in block. Presents the SAME AXI slave
//          interface + LFSR/CRC observation outputs as axi4_dma_slaves, plus
//          the tally readback port.
//
//   s_axi ─▶ [axi4_slave_rd_mon] ─▶ ┐
//   (from     [axi4_slave_wr_mon] ─▶ ├─▶ axi4_dma_slaves (LFSR rd / CRC wr)
//    STREAM)         │ monbus         ┘
//                    └─▶ monbus_arbiter(2) ─▶ monbus_pkt_tally ─▶ rd port
//
// The monitors are passthrough snoopers (fub↔m_axi transparent), so the DMA
// slaves' pattern-gen/CRC behaviour is unchanged; they just also emit monbus,
// which the tally counts by {protocol, pkt_type, event_code}.
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
    // Tally (SRAM count matrix + 32-entry cache)
    parameter int TALLY_COUNT_WIDTH = 32,
    parameter int TALLY_CACHE_DEPTH = 32,
    parameter int TALLY_ADDR_BITS   = 16,
    parameter int TALLY_NUM_LATCH   = 4,
    // Derived
    parameter int SW      = AXI_DATA_WIDTH / 8,
    parameter int LSEL_W  = (TALLY_NUM_LATCH > 1) ? $clog2(TALLY_NUM_LATCH) : 1,
    parameter int LFILL_W = $clog2(TALLY_NUM_LATCH + 1)
) (
    input  logic                          aclk,
    input  logic                          aresetn,

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

    // ---- Monitor config (a few knobs; rest tied to safe defaults) ----------
    input  logic                          cfg_monitor_enable,
    input  logic                          cfg_error_enable,
    input  logic                          cfg_compl_enable,
    input  logic                          cfg_timeout_enable,
    input  logic [15:0]                   cfg_timeout_cycles,

    // ---- Tally control + readback (rd port for the fabric) -----------------
    input  logic                          tally_freeze,
    input  logic                          tally_flush,
    output logic                          tally_flush_busy,
    input  logic                          tally_clear,
    input  logic [TALLY_ADDR_BITS-1:0]    tally_rd_addr,
    output logic [TALLY_COUNT_WIDTH-1:0]  tally_rd_count,
    input  logic                          tally_watch_arm,
    input  logic [15:0]                   tally_watch_pkttype_mask,
    input  logic [LSEL_W-1:0]             tally_latch_sel,
    output logic                          tally_latch_valid,
    output logic [127:0]                  tally_latch_packet,
    output logic [63:0]                   tally_latch_ts,
    output logic [LFILL_W-1:0]            tally_latch_fill
);

    // Free-running monitor timestamp broadcast to both monitors.
    monbus_timestamp_t r_mon_time;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_mon_time <= '0;
        else                        r_mon_time <= r_mon_time + 1'b1;
    )

    // Two monbus streams into the arbiter (client 0 = read, 1 = write).
    logic              mb_valid [2];
    logic              mb_ready [2];
    monitor_packet_t   mb_packet [2];
    monbus_timestamp_t mb_ts    [2];

    // Internal AXI wires: monitor m_axi side -> axi4_dma_slaves s_axi side.
    // Read channel
    logic [AXI_ID_WIDTH-1:0]   i_arid;   logic [AXI_ADDR_WIDTH-1:0] i_araddr;
    logic [7:0]                i_arlen;  logic [2:0]                i_arsize;
    logic [1:0]                i_arburst; logic                     i_arlock;
    logic [3:0]                i_arcache; logic [2:0]               i_arprot;
    logic [3:0]                i_arqos;  logic [3:0]                i_arregion;
    logic [AXI_USER_WIDTH-1:0] i_aruser; logic                     i_arvalid, i_arready;
    logic [AXI_ID_WIDTH-1:0]   i_rid;    logic [AXI_DATA_WIDTH-1:0] i_rdata;
    logic [1:0]                i_rresp;  logic                      i_rlast;
    logic [AXI_USER_WIDTH-1:0] i_ruser;  logic                      i_rvalid, i_rready;
    // Write channel
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

    // ---- Read-side passthrough snoop monitor (s_axi -> internal) -----------
    axi4_slave_rd_mon #(
        .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH), .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .MAX_TRANSACTIONS(MAX_TRANSACTIONS), .UNIT_ID(8'h10), .AGENT_ID(16'h0001)
    ) u_rd_mon (
        .aclk(aclk), .aresetn(aresetn), .cam_clear(1'b0),
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
        .cfg_monitor_enable(cfg_monitor_enable), .cfg_error_enable(cfg_error_enable),
        .cfg_timeout_enable(cfg_timeout_enable), .cfg_perf_enable(1'b0),
        .cfg_compl_enable(cfg_compl_enable), .cfg_threshold_enable(1'b0),
        .cfg_debug_enable(1'b0), .cfg_timeout_cycles(cfg_timeout_cycles),
        .cfg_latency_threshold(32'hFFFFFFFF),
        .cfg_axi_pkt_mask(16'h0), .cfg_axi_err_select(16'h0),
        .cfg_axi_error_mask(16'h0), .cfg_axi_timeout_mask(16'h0),
        .cfg_axi_compl_mask(16'h0), .cfg_axi_thresh_mask(16'h0),
        .cfg_axi_perf_mask(16'h0), .cfg_axi_addr_mask(16'h0),
        .cfg_axi_debug_mask(16'h0),
        .cfg_addr_check_enable(1'b0), .cfg_addr_range_enable(1'b0),
        .cfg_addr_range_low('0), .cfg_addr_range_high('0),
        .cfg_start_event_sel(3'h0), .cfg_end_event_sel(3'h0),
        .cfg_start_trigger(1'b0), .cfg_end_trigger(1'b0),
        .cfg_window_force_close(1'b0), .i_mon_time(r_mon_time),
        .monbus_valid(mb_valid[0]), .monbus_ready(mb_ready[0]),
        .monbus_packet(mb_packet[0]), .monbus_timestamp(mb_ts[0]),
        .busy(), .active_transactions(), .error_count(), .transaction_count(),
        .window_active(), .window_cycles(),
        .perf_prod_cycles(), .perf_bp_cycles(), .perf_starv_cycles(),
        .perf_idle_cycles(), .perf_beat_count(), .perf_byte_count(),
        .perf_burst_count(), .cfg_conflict_error()
    );

    // ---- Write-side passthrough snoop monitor (s_axi -> internal) ----------
    axi4_slave_wr_mon #(
        .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH), .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .MAX_TRANSACTIONS(MAX_TRANSACTIONS), .UNIT_ID(8'h11), .AGENT_ID(16'h0002)
    ) u_wr_mon (
        .aclk(aclk), .aresetn(aresetn), .cam_clear(1'b0),
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
        .cfg_monitor_enable(cfg_monitor_enable), .cfg_error_enable(cfg_error_enable),
        .cfg_timeout_enable(cfg_timeout_enable), .cfg_perf_enable(1'b0),
        .cfg_compl_enable(cfg_compl_enable), .cfg_threshold_enable(1'b0),
        .cfg_debug_enable(1'b0), .cfg_timeout_cycles(cfg_timeout_cycles),
        .cfg_latency_threshold(32'hFFFFFFFF),
        .cfg_axi_pkt_mask(16'h0), .cfg_axi_err_select(16'h0),
        .cfg_axi_error_mask(16'h0), .cfg_axi_timeout_mask(16'h0),
        .cfg_axi_compl_mask(16'h0), .cfg_axi_thresh_mask(16'h0),
        .cfg_axi_perf_mask(16'h0), .cfg_axi_addr_mask(16'h0),
        .cfg_axi_debug_mask(16'h0),
        .cfg_addr_check_enable(1'b0), .cfg_addr_range_enable(1'b0),
        .cfg_addr_range_low('0), .cfg_addr_range_high('0),
        .cfg_start_event_sel(3'h0), .cfg_end_event_sel(3'h0),
        .cfg_start_trigger(1'b0), .cfg_end_trigger(1'b0),
        .cfg_window_force_close(1'b0), .i_mon_time(r_mon_time),
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
    logic              arb_valid;
    logic              arb_ready;
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

    // ---- Tabulate into the SRAM count matrix + cache -----------------------
    monbus_pkt_tally #(
        .PKT_WIDTH(128), .TS_WIDTH(64),
        .COUNT_WIDTH(TALLY_COUNT_WIDTH), .CACHE_DEPTH(TALLY_CACHE_DEPTH),
        .NUM_LATCH(TALLY_NUM_LATCH), .ADDR_BITS(TALLY_ADDR_BITS)
    ) u_tally (
        .clk(aclk), .rst_n(aresetn),
        .in_valid(arb_valid), .in_ready(arb_ready),
        .in_packet(arb_packet), .in_ts(arb_ts),
        .i_freeze(tally_freeze), .i_flush(tally_flush),
        .o_flush_busy(tally_flush_busy), .i_clear(tally_clear),
        .rd_addr(tally_rd_addr), .rd_count(tally_rd_count),
        .i_watch_arm(tally_watch_arm),
        .i_watch_pkttype_mask(tally_watch_pkttype_mask),
        .latch_sel(tally_latch_sel), .latch_valid(tally_latch_valid),
        .latch_packet(tally_latch_packet), .latch_ts(tally_latch_ts),
        .latch_fill(tally_latch_fill)
    );

endmodule : dma_slave_monitors
