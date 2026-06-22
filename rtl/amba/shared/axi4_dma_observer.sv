// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: axi4_dma_observer
// Purpose: Standalone, DMA-agnostic observability wrapper.
//
//   Drop in between an AXI4-master DMA (any number of read / write
//   master ports) and the fabric. Each (read, write) port pair gets
//   wrapped by axi4_master_rd_mon / axi4_master_wr_mon in pass-through
//   mode. All N monbus streams are merged by monbus_arbiter and fed
//   into monbus_axil_axi4_group, exposing:
//
//     - s_axil_*  : slave-read port for the host CPU's IRQ drain
//                   (3-beat-per-record slicing)
//     - m_axi_*   : AXI4-burst master-write port for bulk-trace
//                   capture to a memory ring
//     - irq_out   : asserted whenever the err FIFO has any entries
//
//   The DMA under test is not modified -- the observer sits inline
//   on its AXI external pins. Same clock domain on both sides.
//
//   Each tap (axi4_master_{rd,wr}_mon) is a pure observer: it watches
//   its AXI4 bus and emits a monbus packet on every event match. All
//   filtering of which packets ultimately reach the err FIFO or the
//   write FIFO is done by the central monbus_group filter (one set of
//   cfg_<proto>_*_mask + cfg_<proto>_err_select inputs at the observer
//   top, fed directly into u_group). The per-leaf cfg_axi_*_mask
//   inputs on each tap are tied to 0 ("don't pre-filter at the leaf")
//   so the central filter is the single point of control.
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi4_dma_observer
    import monitor_common_pkg::*;
#(
    // ---------- Tap counts ----------
    parameter int NUM_RD_PORTS       = 1,
    parameter int NUM_WR_PORTS       = 1,

    // ---------- DMA-side AXI widths (shared by all tap ports) ----------
    parameter int ADDR_WIDTH         = 32,
    parameter int DATA_WIDTH         = 128,
    parameter int AXI_ID_WIDTH       = 8,
    parameter int AXI_USER_WIDTH     = 1,

    // ---------- Observer dump-port (m_axi_*) sizing ----------
    parameter int OBS_AXI_ID_WIDTH   = 4,        // master-write id for dumps
    parameter int MAX_BURST_BEATS    = 64,       // 1..256 (256 is AXI4 max)

    // ---------- Group config ----------
    parameter int FIFO_DEPTH_ERR        = 64,
    parameter int FIFO_DEPTH_WRITE      = 96,    // beats
    parameter int FLUSH_TIMEOUT_CYCLES  = 1024,
    parameter int USE_COMPRESSION       = 0,

    // ---------- Per-leaf monitor config ----------
    parameter int MAX_TRANSACTIONS      = 16,
    parameter logic [7:0] UNIT_ID       = 8'h10, // distinguishes this observer's packets

    // ---------- axi_bus_meter integration ----------
    parameter bit ENABLE_BUS_METER      = 1'b1,  // 0 = omit meters, tie outputs to 0
    // 1 = derive write per-channel attribution from awid via an internal AW->W
    // order tracker (no dma_wr_active_ch_* sideband needed; valid when AW leads
    // W, the common case). 0 = use the explicit dma_wr_active_ch_* sideband.
    parameter bit WR_CH_FROM_AWID       = 1'b0,
    parameter int NUM_CHANNELS          = 1,     // 1 = aggregate only (no per-channel buckets)
    parameter int CW                    = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1,

    // ---------- axi_perf_latency_hist integration (RFC Stage E option 2 / E.3) ----------
    parameter bit ENABLE_LATENCY_HIST   = 1'b1,  // 0 = omit histograms, tie outputs to 0
    parameter int HIST_NUM_BINS         = 16,    // log2 latency bins: bin b = [2^b, 2^(b+1))
    parameter int HIST_MAX_OUTSTANDING  = 8,     // per-channel timestamp FIFO depth
    parameter int HIST_BINW             = (HIST_NUM_BINS > 1) ? $clog2(HIST_NUM_BINS) : 1
) (
    input  logic                                                aclk,
    input  logic                                                aresetn,
    // Synchronous clear for ALL CAMs in the observer: the compressor template
    // CAM (+ stats) in the monbus group and every tap's transaction CAM. Pulse
    // when idle to reset compression stats / unstick stale entries.
    input  logic                                                cam_clear,

    // ================================================================
    // Read tap pairs.
    // For each i in [0..NUM_RD_PORTS-1]:
    //   dma_rd_*  inputs come from the DMA's external read master port
    //   fab_rd_*  outputs go to the fabric's external read slave port
    // The observer passes signals through with one pipeline stage of
    // skid buffering (inherited from axi4_master_rd_mon).
    // ================================================================
    // AR channel (DMA -> observer)
    input  logic [NUM_RD_PORTS-1:0][AXI_ID_WIDTH-1:0]           dma_rd_arid,
    input  logic [NUM_RD_PORTS-1:0][ADDR_WIDTH-1:0]             dma_rd_araddr,
    input  logic [NUM_RD_PORTS-1:0][7:0]                        dma_rd_arlen,
    input  logic [NUM_RD_PORTS-1:0][2:0]                        dma_rd_arsize,
    input  logic [NUM_RD_PORTS-1:0][1:0]                        dma_rd_arburst,
    input  logic [NUM_RD_PORTS-1:0]                             dma_rd_arlock,
    input  logic [NUM_RD_PORTS-1:0][3:0]                        dma_rd_arcache,
    input  logic [NUM_RD_PORTS-1:0][2:0]                        dma_rd_arprot,
    input  logic [NUM_RD_PORTS-1:0][3:0]                        dma_rd_arqos,
    input  logic [NUM_RD_PORTS-1:0][3:0]                        dma_rd_arregion,
    input  logic [NUM_RD_PORTS-1:0][AXI_USER_WIDTH-1:0]         dma_rd_aruser,
    input  logic [NUM_RD_PORTS-1:0]                             dma_rd_arvalid,
    output logic [NUM_RD_PORTS-1:0]                             dma_rd_arready,
    // R channel (observer -> DMA)
    output logic [NUM_RD_PORTS-1:0][AXI_ID_WIDTH-1:0]           dma_rd_rid,
    output logic [NUM_RD_PORTS-1:0][DATA_WIDTH-1:0]             dma_rd_rdata,
    output logic [NUM_RD_PORTS-1:0][1:0]                        dma_rd_rresp,
    output logic [NUM_RD_PORTS-1:0]                             dma_rd_rlast,
    output logic [NUM_RD_PORTS-1:0][AXI_USER_WIDTH-1:0]         dma_rd_ruser,
    output logic [NUM_RD_PORTS-1:0]                             dma_rd_rvalid,
    input  logic [NUM_RD_PORTS-1:0]                             dma_rd_rready,
    // AR channel (observer -> fabric)
    output logic [NUM_RD_PORTS-1:0][AXI_ID_WIDTH-1:0]           fab_rd_arid,
    output logic [NUM_RD_PORTS-1:0][ADDR_WIDTH-1:0]             fab_rd_araddr,
    output logic [NUM_RD_PORTS-1:0][7:0]                        fab_rd_arlen,
    output logic [NUM_RD_PORTS-1:0][2:0]                        fab_rd_arsize,
    output logic [NUM_RD_PORTS-1:0][1:0]                        fab_rd_arburst,
    output logic [NUM_RD_PORTS-1:0]                             fab_rd_arlock,
    output logic [NUM_RD_PORTS-1:0][3:0]                        fab_rd_arcache,
    output logic [NUM_RD_PORTS-1:0][2:0]                        fab_rd_arprot,
    output logic [NUM_RD_PORTS-1:0][3:0]                        fab_rd_arqos,
    output logic [NUM_RD_PORTS-1:0][3:0]                        fab_rd_arregion,
    output logic [NUM_RD_PORTS-1:0][AXI_USER_WIDTH-1:0]         fab_rd_aruser,
    output logic [NUM_RD_PORTS-1:0]                             fab_rd_arvalid,
    input  logic [NUM_RD_PORTS-1:0]                             fab_rd_arready,
    // R channel (fabric -> observer)
    input  logic [NUM_RD_PORTS-1:0][AXI_ID_WIDTH-1:0]           fab_rd_rid,
    input  logic [NUM_RD_PORTS-1:0][DATA_WIDTH-1:0]             fab_rd_rdata,
    input  logic [NUM_RD_PORTS-1:0][1:0]                        fab_rd_rresp,
    input  logic [NUM_RD_PORTS-1:0]                             fab_rd_rlast,
    input  logic [NUM_RD_PORTS-1:0][AXI_USER_WIDTH-1:0]         fab_rd_ruser,
    input  logic [NUM_RD_PORTS-1:0]                             fab_rd_rvalid,
    output logic [NUM_RD_PORTS-1:0]                             fab_rd_rready,

    // ================================================================
    // Write tap pairs (same shape, write-channel direction).
    // ================================================================
    // AW channel (DMA -> observer)
    input  logic [NUM_WR_PORTS-1:0][AXI_ID_WIDTH-1:0]           dma_wr_awid,
    input  logic [NUM_WR_PORTS-1:0][ADDR_WIDTH-1:0]             dma_wr_awaddr,
    input  logic [NUM_WR_PORTS-1:0][7:0]                        dma_wr_awlen,
    input  logic [NUM_WR_PORTS-1:0][2:0]                        dma_wr_awsize,
    input  logic [NUM_WR_PORTS-1:0][1:0]                        dma_wr_awburst,
    input  logic [NUM_WR_PORTS-1:0]                             dma_wr_awlock,
    input  logic [NUM_WR_PORTS-1:0][3:0]                        dma_wr_awcache,
    input  logic [NUM_WR_PORTS-1:0][2:0]                        dma_wr_awprot,
    input  logic [NUM_WR_PORTS-1:0][3:0]                        dma_wr_awqos,
    input  logic [NUM_WR_PORTS-1:0][3:0]                        dma_wr_awregion,
    input  logic [NUM_WR_PORTS-1:0][AXI_USER_WIDTH-1:0]         dma_wr_awuser,
    input  logic [NUM_WR_PORTS-1:0]                             dma_wr_awvalid,
    output logic [NUM_WR_PORTS-1:0]                             dma_wr_awready,
    // W channel (DMA -> observer)
    input  logic [NUM_WR_PORTS-1:0][DATA_WIDTH-1:0]             dma_wr_wdata,
    input  logic [NUM_WR_PORTS-1:0][DATA_WIDTH/8-1:0]           dma_wr_wstrb,
    input  logic [NUM_WR_PORTS-1:0]                             dma_wr_wlast,
    input  logic [NUM_WR_PORTS-1:0][AXI_USER_WIDTH-1:0]         dma_wr_wuser,
    input  logic [NUM_WR_PORTS-1:0]                             dma_wr_wvalid,
    output logic [NUM_WR_PORTS-1:0]                             dma_wr_wready,
    // B channel (observer -> DMA)
    output logic [NUM_WR_PORTS-1:0][AXI_ID_WIDTH-1:0]           dma_wr_bid,
    output logic [NUM_WR_PORTS-1:0][1:0]                        dma_wr_bresp,
    output logic [NUM_WR_PORTS-1:0][AXI_USER_WIDTH-1:0]         dma_wr_buser,
    output logic [NUM_WR_PORTS-1:0]                             dma_wr_bvalid,
    input  logic [NUM_WR_PORTS-1:0]                             dma_wr_bready,
    // AW channel (observer -> fabric)
    output logic [NUM_WR_PORTS-1:0][AXI_ID_WIDTH-1:0]           fab_wr_awid,
    output logic [NUM_WR_PORTS-1:0][ADDR_WIDTH-1:0]             fab_wr_awaddr,
    output logic [NUM_WR_PORTS-1:0][7:0]                        fab_wr_awlen,
    output logic [NUM_WR_PORTS-1:0][2:0]                        fab_wr_awsize,
    output logic [NUM_WR_PORTS-1:0][1:0]                        fab_wr_awburst,
    output logic [NUM_WR_PORTS-1:0]                             fab_wr_awlock,
    output logic [NUM_WR_PORTS-1:0][3:0]                        fab_wr_awcache,
    output logic [NUM_WR_PORTS-1:0][2:0]                        fab_wr_awprot,
    output logic [NUM_WR_PORTS-1:0][3:0]                        fab_wr_awqos,
    output logic [NUM_WR_PORTS-1:0][3:0]                        fab_wr_awregion,
    output logic [NUM_WR_PORTS-1:0][AXI_USER_WIDTH-1:0]         fab_wr_awuser,
    output logic [NUM_WR_PORTS-1:0]                             fab_wr_awvalid,
    input  logic [NUM_WR_PORTS-1:0]                             fab_wr_awready,
    // W channel (observer -> fabric)
    output logic [NUM_WR_PORTS-1:0][DATA_WIDTH-1:0]             fab_wr_wdata,
    output logic [NUM_WR_PORTS-1:0][DATA_WIDTH/8-1:0]           fab_wr_wstrb,
    output logic [NUM_WR_PORTS-1:0]                             fab_wr_wlast,
    output logic [NUM_WR_PORTS-1:0][AXI_USER_WIDTH-1:0]         fab_wr_wuser,
    output logic [NUM_WR_PORTS-1:0]                             fab_wr_wvalid,
    input  logic [NUM_WR_PORTS-1:0]                             fab_wr_wready,
    // B channel (fabric -> observer)
    input  logic [NUM_WR_PORTS-1:0][AXI_ID_WIDTH-1:0]           fab_wr_bid,
    input  logic [NUM_WR_PORTS-1:0][1:0]                        fab_wr_bresp,
    input  logic [NUM_WR_PORTS-1:0][AXI_USER_WIDTH-1:0]         fab_wr_buser,
    input  logic [NUM_WR_PORTS-1:0]                             fab_wr_bvalid,
    output logic [NUM_WR_PORTS-1:0]                             fab_wr_bready,

    // ================================================================
    // Observability outputs
    // ================================================================

    // CPU-side err FIFO drain (AXIL slave-read)
    input  logic                                                s_axil_arvalid,
    output logic                                                s_axil_arready,
    input  logic [ADDR_WIDTH-1:0]                               s_axil_araddr,
    input  logic [2:0]                                          s_axil_arprot,
    output logic                                                s_axil_rvalid,
    input  logic                                                s_axil_rready,
    output logic [63:0]                                         s_axil_rdata,
    output logic [1:0]                                          s_axil_rresp,

    // Bulk-trace dump (AXI4 burst master-write)
    output logic [OBS_AXI_ID_WIDTH-1:0]                         m_axi_awid,
    output logic [ADDR_WIDTH-1:0]                               m_axi_awaddr,
    output logic [7:0]                                          m_axi_awlen,
    output logic [2:0]                                          m_axi_awsize,
    output logic [1:0]                                          m_axi_awburst,
    output logic                                                m_axi_awlock,
    output logic [3:0]                                          m_axi_awcache,
    output logic [2:0]                                          m_axi_awprot,
    output logic [3:0]                                          m_axi_awqos,
    output logic [3:0]                                          m_axi_awregion,
    output logic                                                m_axi_awuser,
    output logic                                                m_axi_awvalid,
    input  logic                                                m_axi_awready,
    output logic [63:0]                                         m_axi_wdata,
    output logic [7:0]                                          m_axi_wstrb,
    output logic                                                m_axi_wlast,
    output logic                                                m_axi_wuser,
    output logic                                                m_axi_wvalid,
    input  logic                                                m_axi_wready,
    input  logic [OBS_AXI_ID_WIDTH-1:0]                         m_axi_bid,
    input  logic [1:0]                                          m_axi_bresp,
    input  logic                                                m_axi_buser,
    input  logic                                                m_axi_bvalid,
    output logic                                                m_axi_bready,

    // IRQ
    output logic                                                irq_out,

    // ================================================================
    // Runtime config (drives the monbus_group's central filter)
    // ================================================================
    input  logic [ADDR_WIDTH-1:0]                               cfg_base_addr,
    input  logic [ADDR_WIDTH-1:0]                               cfg_limit_addr,
    input  logic [15:0]                                         cfg_flush_watermark,
    // Runtime compression enable (only effective when USE_COMPRESSION==1).
    // Brought to the top so it always traces back to a real config bit.
    input  logic                                                cfg_compress_en,

    // ----- Per-protocol filter masks (one set per protocol id) -----
    //
    // The taps (axi4_master_{rd,wr}_mon) observe their AXI4 buses and
    // emit a monbus packet on every match. Filtering of what reaches
    // the err FIFO / write FIFO happens **here**, inside monbus_group:
    //   cfg_<proto>_pkt_mask[i]        = 1 -> drop packets where pkt_type==i
    //   cfg_<proto>_err_select[i]      = 1 -> route those packets to err FIFO
    //                                          instead of write FIFO
    //   cfg_<proto>_<event>_mask[i]    = 1 -> drop on event_code==i within
    //                                          the named event class
    //
    // A monbus packet's protocol field selects which set the filter
    // applies. The taps in this observer always emit protocol=AXI, so
    // the AXIS / CORE sets only do work for an upstream caller that
    // arbitrates this observer's monbus together with an AXIS or CORE
    // monitor source -- but they're real filter inputs either way.

    // ----- AXI -----
    input  logic [15:0]                                         cfg_axi_pkt_mask,
    input  logic [15:0]                                         cfg_axi_err_select,
    input  logic [15:0]                                         cfg_axi_error_mask,
    input  logic [15:0]                                         cfg_axi_timeout_mask,
    input  logic [15:0]                                         cfg_axi_compl_mask,
    input  logic [15:0]                                         cfg_axi_thresh_mask,
    input  logic [15:0]                                         cfg_axi_perf_mask,
    input  logic [15:0]                                         cfg_axi_addr_mask,
    input  logic [15:0]                                         cfg_axi_debug_mask,

    // ----- AXIS -----
    input  logic [15:0]                                         cfg_axis_pkt_mask,
    input  logic [15:0]                                         cfg_axis_err_select,
    input  logic [15:0]                                         cfg_axis_error_mask,
    input  logic [15:0]                                         cfg_axis_timeout_mask,
    input  logic [15:0]                                         cfg_axis_compl_mask,
    input  logic [15:0]                                         cfg_axis_credit_mask,
    input  logic [15:0]                                         cfg_axis_channel_mask,
    input  logic [15:0]                                         cfg_axis_stream_mask,

    // ----- CORE -----
    input  logic [15:0]                                         cfg_core_pkt_mask,
    input  logic [15:0]                                         cfg_core_err_select,
    input  logic [15:0]                                         cfg_core_error_mask,
    input  logic [15:0]                                         cfg_core_timeout_mask,
    input  logic [15:0]                                         cfg_core_compl_mask,
    input  logic [15:0]                                         cfg_core_thresh_mask,
    input  logic [15:0]                                         cfg_core_perf_mask,
    input  logic [15:0]                                         cfg_core_debug_mask,

    // Status
    output logic                                                err_fifo_full,
    output logic                                                write_fifo_full,
    output logic [15:0]                                         err_fifo_count,
    output logic [15:0]                                         write_fifo_count,

    // ================================================================
    // axi_bus_meter inputs (optional; safe to tie off if ENABLE_BUS_METER=0)
    // ================================================================

    // One-cycle synchronous pulse clears all bucket counters and overflow
    // stickies. Held-high also works (the meter's accumulators stay
    // pinned at 0).
    input  logic                                                i_meter_clear,
    // Hold high to pause every bucket counter (the measurement window
    // closes). Held low for free-running measurement.
    input  logic                                                i_meter_freeze,

    // ---------- Read-side rid -> channel-id mapping ----------
    //
    // Runtime signal-list mapping. For each rd port and each logical
    // channel index `ch` in [0..NUM_CHANNELS-1]:
    //   cfg_rd_rid_per_channel[port][ch]        = rid value channel `ch` uses
    //   cfg_rd_rid_per_channel_valid[port][ch]  = 1 if that entry is in use
    // The bus-meter for that port matches the current rid against this
    // table; the first valid match's `ch` index becomes i_channel_id.
    // No match (or all-invalid) -> the cycle is not attributed (aggregate
    // counters still tick).
    input  logic [AXI_ID_WIDTH-1:0] cfg_rd_rid_per_channel       [NUM_RD_PORTS][NUM_CHANNELS],
    input  logic                    cfg_rd_rid_per_channel_valid [NUM_RD_PORTS][NUM_CHANNELS],

    // ---------- Write-side channel-active sideband (optional) ----------
    //
    // AXI4 W beats carry no AXI ID; per-channel attribution needs a
    // sideband from the DMA's W-phase FSM. STREAM's axi_write_engine
    // exposes o_active_channel_id / o_active_channel_valid that wires
    // directly here. DMAs without this output: tie both to 0 (aggregate
    // counters still tick; per-channel buckets stay at 0).
    input  logic [CW-1:0]           dma_wr_active_ch_id          [NUM_WR_PORTS],
    input  logic                    dma_wr_active_ch_valid       [NUM_WR_PORTS],

    // ================================================================
    // axi_bus_meter outputs (one set per monitored port)
    // ================================================================
    // Read-side meters
    output logic [31:0]             rd_meter_agg_productive      [NUM_RD_PORTS],
    output logic [31:0]             rd_meter_agg_backpressure    [NUM_RD_PORTS],
    output logic [31:0]             rd_meter_agg_starvation      [NUM_RD_PORTS],
    output logic [31:0]             rd_meter_agg_idle            [NUM_RD_PORTS],
    output logic [15:0]             rd_meter_ch_productive       [NUM_RD_PORTS][NUM_CHANNELS],
    output logic [15:0]             rd_meter_ch_backpressure     [NUM_RD_PORTS][NUM_CHANNELS],
    output logic [15:0]             rd_meter_ch_starvation       [NUM_RD_PORTS][NUM_CHANNELS],
    output logic [15:0]             rd_meter_ch_idle             [NUM_RD_PORTS][NUM_CHANNELS],
    output logic [NUM_CHANNELS*4-1:0] rd_meter_ch_overflow       [NUM_RD_PORTS],
    // Write-side meters
    output logic [31:0]             wr_meter_agg_productive      [NUM_WR_PORTS],
    output logic [31:0]             wr_meter_agg_backpressure    [NUM_WR_PORTS],
    output logic [31:0]             wr_meter_agg_starvation      [NUM_WR_PORTS],
    output logic [31:0]             wr_meter_agg_idle            [NUM_WR_PORTS],
    output logic [15:0]             wr_meter_ch_productive       [NUM_WR_PORTS][NUM_CHANNELS],
    output logic [15:0]             wr_meter_ch_backpressure     [NUM_WR_PORTS][NUM_CHANNELS],
    output logic [15:0]             wr_meter_ch_starvation       [NUM_WR_PORTS][NUM_CHANNELS],
    output logic [15:0]             wr_meter_ch_idle             [NUM_WR_PORTS][NUM_CHANNELS],
    output logic [NUM_CHANNELS*4-1:0] wr_meter_ch_overflow       [NUM_WR_PORTS],

    // ================================================================
    // axi_perf_latency_hist (RFC Stage E.3) — per-port latency histograms
    // ================================================================
    // Indexed readout: the selectors below are shared across all ports
    // (drive one {metric, bin}, read each port's count/total separately).
    // Reads expose two metrics (i_hist_metric: 0 = AR->first-R, 1 = AR->RLAST);
    // writes expose one metric (AW->B; i_hist_metric is ignored for writes).
    // o_*_hist_total is the per-metric transaction count (== burst count).
    // Frozen/cleared in lockstep with the meters (i_meter_clear/i_meter_freeze).
    input  logic                    i_hist_metric,
    input  logic [HIST_BINW-1:0]    i_hist_bin,
    output logic [31:0]             rd_hist_count   [NUM_RD_PORTS],
    output logic [31:0]             rd_hist_total   [NUM_RD_PORTS],
    output logic [31:0]             wr_hist_count   [NUM_WR_PORTS],
    output logic [31:0]             wr_hist_total   [NUM_WR_PORTS]
);

    // =================================================================
    // Local parameters / derived sizes
    // =================================================================
    localparam int NUM_MON_SOURCES = NUM_RD_PORTS + NUM_WR_PORTS;

    // Sanity: monbus_arbiter requires at least one client.
    initial begin
        if (NUM_MON_SOURCES < 1) begin
            $error("axi4_dma_observer: NUM_RD_PORTS + NUM_WR_PORTS must be >= 1");
        end
    end

    // =================================================================
    // Free-running timestamp (driven out by monbus_group, looped back
    // into every leaf monitor as i_mon_time)
    // =================================================================
    monbus_timestamp_t                              mon_time_w;

    // =================================================================
    // Per-source monbus streams + arbiter inputs (unpacked arrays as
    // monbus_arbiter expects)
    // =================================================================
    logic                                           mon_valid    [NUM_MON_SOURCES];
    logic                                           mon_ready    [NUM_MON_SOURCES];
    monitor_packet_t                                mon_packet   [NUM_MON_SOURCES];
    monbus_timestamp_t                              mon_ts       [NUM_MON_SOURCES];

    // =================================================================
    // Read-port monitors
    // =================================================================
    genvar gi;
    generate
        for (gi = 0; gi < NUM_RD_PORTS; gi = gi + 1) begin : gen_rd_mon
            axi4_master_rd_mon #(
                .AXI_ID_WIDTH    (AXI_ID_WIDTH),
                .AXI_ADDR_WIDTH  (ADDR_WIDTH),
                .AXI_DATA_WIDTH  (DATA_WIDTH),
                .AXI_USER_WIDTH  (AXI_USER_WIDTH),
                .USE_MONITOR     (1'b1),
                .UNIT_ID         (UNIT_ID),
                .AGENT_ID        ({8'h00, 4'h0, gi[3:0]}),  // RD ports: [3:0]=index, [7:4]=0
                .MAX_TRANSACTIONS(MAX_TRANSACTIONS)
            ) u_rd_mon (
                .aclk    (aclk),
                .aresetn (aresetn),
                .cam_clear (cam_clear),

                // fub side = DMA-facing (pass-through input from DMA)
                .fub_axi_arid    (dma_rd_arid[gi]),
                .fub_axi_araddr  (dma_rd_araddr[gi]),
                .fub_axi_arlen   (dma_rd_arlen[gi]),
                .fub_axi_arsize  (dma_rd_arsize[gi]),
                .fub_axi_arburst (dma_rd_arburst[gi]),
                .fub_axi_arlock  (dma_rd_arlock[gi]),
                .fub_axi_arcache (dma_rd_arcache[gi]),
                .fub_axi_arprot  (dma_rd_arprot[gi]),
                .fub_axi_arqos   (dma_rd_arqos[gi]),
                .fub_axi_arregion(dma_rd_arregion[gi]),
                .fub_axi_aruser  (dma_rd_aruser[gi]),
                .fub_axi_arvalid (dma_rd_arvalid[gi]),
                .fub_axi_arready (dma_rd_arready[gi]),
                .fub_axi_rid     (dma_rd_rid[gi]),
                .fub_axi_rdata   (dma_rd_rdata[gi]),
                .fub_axi_rresp   (dma_rd_rresp[gi]),
                .fub_axi_rlast   (dma_rd_rlast[gi]),
                .fub_axi_ruser   (dma_rd_ruser[gi]),
                .fub_axi_rvalid  (dma_rd_rvalid[gi]),
                .fub_axi_rready  (dma_rd_rready[gi]),

                // m_axi side = fabric-facing
                .m_axi_arid      (fab_rd_arid[gi]),
                .m_axi_araddr    (fab_rd_araddr[gi]),
                .m_axi_arlen     (fab_rd_arlen[gi]),
                .m_axi_arsize    (fab_rd_arsize[gi]),
                .m_axi_arburst   (fab_rd_arburst[gi]),
                .m_axi_arlock    (fab_rd_arlock[gi]),
                .m_axi_arcache   (fab_rd_arcache[gi]),
                .m_axi_arprot    (fab_rd_arprot[gi]),
                .m_axi_arqos     (fab_rd_arqos[gi]),
                .m_axi_arregion  (fab_rd_arregion[gi]),
                .m_axi_aruser    (fab_rd_aruser[gi]),
                .m_axi_arvalid   (fab_rd_arvalid[gi]),
                .m_axi_arready   (fab_rd_arready[gi]),
                .m_axi_rid       (fab_rd_rid[gi]),
                .m_axi_rdata     (fab_rd_rdata[gi]),
                .m_axi_rresp     (fab_rd_rresp[gi]),
                .m_axi_rlast     (fab_rd_rlast[gi]),
                .m_axi_ruser     (fab_rd_ruser[gi]),
                .m_axi_rvalid    (fab_rd_rvalid[gi]),
                .m_axi_rready    (fab_rd_rready[gi]),

                // Monitor enables (all-on default; expose later if needed)
                .cfg_monitor_enable   (1'b1),
                .cfg_error_enable     (1'b1),
                .cfg_timeout_enable   (1'b1),
                .cfg_perf_enable      (1'b0),     // perf packets off by default
                .cfg_compl_enable     (1'b1),
                .cfg_threshold_enable (1'b0),
                .cfg_debug_enable     (1'b0),
                .cfg_timeout_cycles   (16'd1024),
                .cfg_latency_threshold(32'h0000_FFFF),

                // Leaf filter masks tied to "let everything through";
                // the monbus_group's central filter does the real work.
                .cfg_axi_pkt_mask    (16'h0000),
                .cfg_axi_err_select  (16'h0000),
                .cfg_axi_error_mask  (16'h0000),
                .cfg_axi_timeout_mask(16'h0000),
                .cfg_axi_compl_mask  (16'h0000),
                .cfg_axi_thresh_mask (16'h0000),
                .cfg_axi_perf_mask   (16'h0000),
                .cfg_axi_addr_mask   (16'h0000),
                .cfg_axi_debug_mask  (16'h0000),

                // Address-range / perf-window: disabled in v1
                .cfg_addr_check_enable (1'b0),
                .cfg_addr_range_enable ('0),
                .cfg_addr_range_low    ('0),
                .cfg_addr_range_high   ('0),
                .cfg_start_event_sel   (3'd0),
                .cfg_end_event_sel     (3'd0),
                .cfg_start_trigger     (1'b0),
                .cfg_end_trigger       (1'b0),
                .cfg_window_force_close(1'b0),

                // Free-running timestamp loop-back
                .i_mon_time      (mon_time_w),

                // Monbus output -> arbiter slot
                .monbus_valid    (mon_valid[gi]),
                .monbus_ready    (mon_ready[gi]),
                .monbus_packet   (mon_packet[gi]),
                .monbus_timestamp(mon_ts[gi]),

                /* verilator lint_off PINCONNECTEMPTY */
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
                /* verilator lint_on PINCONNECTEMPTY */
            );
        end
    endgenerate

    // =================================================================
    // Write-port monitors
    // =================================================================
    generate
        for (gi = 0; gi < NUM_WR_PORTS; gi = gi + 1) begin : gen_wr_mon
            axi4_master_wr_mon #(
                .AXI_ID_WIDTH    (AXI_ID_WIDTH),
                .AXI_ADDR_WIDTH  (ADDR_WIDTH),
                .AXI_DATA_WIDTH  (DATA_WIDTH),
                .AXI_USER_WIDTH  (AXI_USER_WIDTH),
                .USE_MONITOR     (1'b1),
                .UNIT_ID         (UNIT_ID),
                .AGENT_ID        ({8'h00, 4'h1, gi[3:0]}),  // WR ports: [3:0]=idx, [7:4]=1
                .MAX_TRANSACTIONS(MAX_TRANSACTIONS)
            ) u_wr_mon (
                .aclk    (aclk),
                .aresetn (aresetn),
                .cam_clear (cam_clear),

                .fub_axi_awid    (dma_wr_awid[gi]),
                .fub_axi_awaddr  (dma_wr_awaddr[gi]),
                .fub_axi_awlen   (dma_wr_awlen[gi]),
                .fub_axi_awsize  (dma_wr_awsize[gi]),
                .fub_axi_awburst (dma_wr_awburst[gi]),
                .fub_axi_awlock  (dma_wr_awlock[gi]),
                .fub_axi_awcache (dma_wr_awcache[gi]),
                .fub_axi_awprot  (dma_wr_awprot[gi]),
                .fub_axi_awqos   (dma_wr_awqos[gi]),
                .fub_axi_awregion(dma_wr_awregion[gi]),
                .fub_axi_awuser  (dma_wr_awuser[gi]),
                .fub_axi_awvalid (dma_wr_awvalid[gi]),
                .fub_axi_awready (dma_wr_awready[gi]),
                .fub_axi_wdata   (dma_wr_wdata[gi]),
                .fub_axi_wstrb   (dma_wr_wstrb[gi]),
                .fub_axi_wlast   (dma_wr_wlast[gi]),
                .fub_axi_wuser   (dma_wr_wuser[gi]),
                .fub_axi_wvalid  (dma_wr_wvalid[gi]),
                .fub_axi_wready  (dma_wr_wready[gi]),
                .fub_axi_bid     (dma_wr_bid[gi]),
                .fub_axi_bresp   (dma_wr_bresp[gi]),
                .fub_axi_buser   (dma_wr_buser[gi]),
                .fub_axi_bvalid  (dma_wr_bvalid[gi]),
                .fub_axi_bready  (dma_wr_bready[gi]),

                .m_axi_awid      (fab_wr_awid[gi]),
                .m_axi_awaddr    (fab_wr_awaddr[gi]),
                .m_axi_awlen     (fab_wr_awlen[gi]),
                .m_axi_awsize    (fab_wr_awsize[gi]),
                .m_axi_awburst   (fab_wr_awburst[gi]),
                .m_axi_awlock    (fab_wr_awlock[gi]),
                .m_axi_awcache   (fab_wr_awcache[gi]),
                .m_axi_awprot    (fab_wr_awprot[gi]),
                .m_axi_awqos     (fab_wr_awqos[gi]),
                .m_axi_awregion  (fab_wr_awregion[gi]),
                .m_axi_awuser    (fab_wr_awuser[gi]),
                .m_axi_awvalid   (fab_wr_awvalid[gi]),
                .m_axi_awready   (fab_wr_awready[gi]),
                .m_axi_wdata     (fab_wr_wdata[gi]),
                .m_axi_wstrb     (fab_wr_wstrb[gi]),
                .m_axi_wlast     (fab_wr_wlast[gi]),
                .m_axi_wuser     (fab_wr_wuser[gi]),
                .m_axi_wvalid    (fab_wr_wvalid[gi]),
                .m_axi_wready    (fab_wr_wready[gi]),
                .m_axi_bid       (fab_wr_bid[gi]),
                .m_axi_bresp     (fab_wr_bresp[gi]),
                .m_axi_buser     (fab_wr_buser[gi]),
                .m_axi_bvalid    (fab_wr_bvalid[gi]),
                .m_axi_bready    (fab_wr_bready[gi]),

                .cfg_monitor_enable   (1'b1),
                .cfg_error_enable     (1'b1),
                .cfg_timeout_enable   (1'b1),
                .cfg_perf_enable      (1'b0),
                .cfg_compl_enable     (1'b1),
                .cfg_threshold_enable (1'b0),
                .cfg_debug_enable     (1'b0),
                .cfg_timeout_cycles   (16'd1024),
                .cfg_latency_threshold(32'h0000_FFFF),

                .cfg_axi_pkt_mask    (16'h0000),
                .cfg_axi_err_select  (16'h0000),
                .cfg_axi_error_mask  (16'h0000),
                .cfg_axi_timeout_mask(16'h0000),
                .cfg_axi_compl_mask  (16'h0000),
                .cfg_axi_thresh_mask (16'h0000),
                .cfg_axi_perf_mask   (16'h0000),
                .cfg_axi_addr_mask   (16'h0000),
                .cfg_axi_debug_mask  (16'h0000),

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

                .monbus_valid    (mon_valid[NUM_RD_PORTS + gi]),
                .monbus_ready    (mon_ready[NUM_RD_PORTS + gi]),
                .monbus_packet   (mon_packet[NUM_RD_PORTS + gi]),
                .monbus_timestamp(mon_ts[NUM_RD_PORTS + gi]),

                /* verilator lint_off PINCONNECTEMPTY */
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
                /* verilator lint_on PINCONNECTEMPTY */
            );
        end
    endgenerate

    // =================================================================
    // Aggregate all monbus sources via monbus_arbiter
    // =================================================================
    logic                arb_monbus_valid;
    logic                arb_monbus_ready;
    monitor_packet_t     arb_monbus_packet;
    monbus_timestamp_t   arb_monbus_timestamp;

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
        .monbus_valid_in     (mon_valid),
        .monbus_ready_in     (mon_ready),
        .monbus_packet_in    (mon_packet),
        .monbus_timestamp_in (mon_ts),
        .monbus_valid        (arb_monbus_valid),
        .monbus_ready        (arb_monbus_ready),
        .monbus_packet       (arb_monbus_packet),
        .monbus_timestamp    (arb_monbus_timestamp),
        /* verilator lint_off PINCONNECTEMPTY */
        .grant_valid         (),
        .grant               (),
        .grant_id            (),
        .last_grant          ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    // =================================================================
    // Output stage: monbus_axil_axi4_group
    //   - AXIL slave-read for CPU IRQ drain
    //   - AXI4 burst master-write for memory-ring dump
    // =================================================================
    monbus_axil_axi4_group #(
        .FIFO_DEPTH_ERR        (FIFO_DEPTH_ERR),
        .FIFO_DEPTH_WRITE      (FIFO_DEPTH_WRITE),
        .ADDR_WIDTH            (ADDR_WIDTH),
        .AXI_ID_WIDTH          (OBS_AXI_ID_WIDTH),
        .AXI_USER_WIDTH        (1),
        .MAX_BURST_BEATS       (MAX_BURST_BEATS),
        .FLUSH_TIMEOUT_CYCLES  (FLUSH_TIMEOUT_CYCLES),
        .USE_COMPRESSION       (USE_COMPRESSION)
    ) u_group (
        .axi_aclk         (aclk),
        .axi_aresetn      (aresetn),
        .cam_clear        (cam_clear),

        .monbus_valid     (arb_monbus_valid),
        .monbus_ready     (arb_monbus_ready),
        .monbus_packet    (arb_monbus_packet),
        .monbus_timestamp (arb_monbus_timestamp),

        .mon_time_out     (mon_time_w),

        // AXIL slave-read
        .s_axil_arvalid   (s_axil_arvalid),
        .s_axil_arready   (s_axil_arready),
        .s_axil_araddr    (s_axil_araddr),
        .s_axil_arprot    (s_axil_arprot),
        .s_axil_rvalid    (s_axil_rvalid),
        .s_axil_rready    (s_axil_rready),
        .s_axil_rdata     (s_axil_rdata),
        .s_axil_rresp     (s_axil_rresp),

        // AXI4 master-write
        .m_axi_awid       (m_axi_awid),
        .m_axi_awaddr     (m_axi_awaddr),
        .m_axi_awlen      (m_axi_awlen),
        .m_axi_awsize     (m_axi_awsize),
        .m_axi_awburst    (m_axi_awburst),
        .m_axi_awlock     (m_axi_awlock),
        .m_axi_awcache    (m_axi_awcache),
        .m_axi_awprot     (m_axi_awprot),
        .m_axi_awqos      (m_axi_awqos),
        .m_axi_awregion   (m_axi_awregion),
        .m_axi_awuser     (m_axi_awuser),
        .m_axi_awvalid    (m_axi_awvalid),
        .m_axi_awready    (m_axi_awready),
        .m_axi_wdata      (m_axi_wdata),
        .m_axi_wstrb      (m_axi_wstrb),
        .m_axi_wlast      (m_axi_wlast),
        .m_axi_wuser      (m_axi_wuser),
        .m_axi_wvalid     (m_axi_wvalid),
        .m_axi_wready     (m_axi_wready),
        .m_axi_bid        (m_axi_bid),
        .m_axi_bresp      (m_axi_bresp),
        .m_axi_buser      (m_axi_buser),
        .m_axi_bvalid     (m_axi_bvalid),
        .m_axi_bready     (m_axi_bready),

        .irq_out          (irq_out),

        // Address window + filter masks (caller-driven)
        .cfg_base_addr        (cfg_base_addr),
        .cfg_limit_addr       (cfg_limit_addr),
        .cfg_flush_watermark  (cfg_flush_watermark),
        .cfg_compress_en      (cfg_compress_en),

        .cfg_axi_pkt_mask     (cfg_axi_pkt_mask),
        .cfg_axi_err_select   (cfg_axi_err_select),
        .cfg_axi_error_mask   (cfg_axi_error_mask),
        .cfg_axi_timeout_mask (cfg_axi_timeout_mask),
        .cfg_axi_compl_mask   (cfg_axi_compl_mask),
        .cfg_axi_thresh_mask  (cfg_axi_thresh_mask),
        .cfg_axi_perf_mask    (cfg_axi_perf_mask),
        .cfg_axi_addr_mask    (cfg_axi_addr_mask),
        .cfg_axi_debug_mask   (cfg_axi_debug_mask),

        // AXIS / CORE protocol masks: this observer doesn't generate
        // AXIS or CORE packets, so tie all to 0 (no filtering).
        .cfg_axis_pkt_mask     (cfg_axis_pkt_mask),
        .cfg_axis_err_select   (cfg_axis_err_select),
        .cfg_axis_error_mask   (cfg_axis_error_mask),
        .cfg_axis_timeout_mask (cfg_axis_timeout_mask),
        .cfg_axis_compl_mask   (cfg_axis_compl_mask),
        .cfg_axis_credit_mask  (cfg_axis_credit_mask),
        .cfg_axis_channel_mask (cfg_axis_channel_mask),
        .cfg_axis_stream_mask  (cfg_axis_stream_mask),
        .cfg_core_pkt_mask     (cfg_core_pkt_mask),
        .cfg_core_err_select   (cfg_core_err_select),
        .cfg_core_error_mask   (cfg_core_error_mask),
        .cfg_core_timeout_mask (cfg_core_timeout_mask),
        .cfg_core_compl_mask   (cfg_core_compl_mask),
        .cfg_core_thresh_mask  (cfg_core_thresh_mask),
        .cfg_core_perf_mask    (cfg_core_perf_mask),
        .cfg_core_debug_mask   (cfg_core_debug_mask),

        .err_fifo_full      (err_fifo_full),
        .write_fifo_full    (write_fifo_full),
        .err_fifo_count     (err_fifo_count),
        .write_fifo_count   (write_fifo_count),

        /* verilator lint_off PINCONNECTEMPTY */
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

    // =================================================================
    // axi_bus_meter per-port instantiations
    //
    //   - One meter per rd port (snoops the fabric-side R handshake).
    //     i_channel_id comes from a priority-encoded rid lookup against
    //     cfg_rd_rid_per_channel[port][*]. i_channel_valid = rvalid AND
    //     (any entry matched).
    //
    //   - One meter per wr port (snoops the fabric-side W handshake).
    //     i_channel_id / i_channel_valid come straight from the optional
    //     DMA sideband inputs.
    //
    //   - ENABLE_BUS_METER=0 skips instantiation; all meter outputs tied
    //     to 0.
    // =================================================================
    genvar mi, ci;
    generate
        if (ENABLE_BUS_METER) begin : gen_meters

            // ---------- Read-side meters ----------
            for (mi = 0; mi < NUM_RD_PORTS; mi = mi + 1) begin : gen_rd_meter
                // rid -> channel-id priority-encoded lookup
                logic [CW-1:0]           rd_ch_id;
                logic                    rd_ch_match;
                logic [NUM_CHANNELS-1:0] rd_hit_mask;

                always_comb begin
                    for (int c = 0; c < NUM_CHANNELS; c = c + 1) begin
                        rd_hit_mask[c] = cfg_rd_rid_per_channel_valid[mi][c]
                                      && (fab_rd_rid[mi] == cfg_rd_rid_per_channel[mi][c]);
                    end
                    // Priority-encode: lowest-index matching channel wins
                    rd_ch_id    = '0;
                    rd_ch_match = 1'b0;
                    for (int c = 0; c < NUM_CHANNELS; c = c + 1) begin
                        if (!rd_ch_match && rd_hit_mask[c]) begin
                            rd_ch_id    = c[CW-1:0];
                            rd_ch_match = 1'b1;
                        end
                    end
                end

                axi_bus_meter #(
                    .NUM_CHANNELS (NUM_CHANNELS)
                ) u_rd_meter (
                    .aclk             (aclk),
                    .aresetn          (aresetn),
                    .i_clear          (i_meter_clear),
                    .i_freeze         (i_meter_freeze),
                    // Snoop the fabric-side R handshake. (Equivalent to
                    // dma-side post-skid since the wrappers don't drop
                    // beats.)
                    .i_valid          (fab_rd_rvalid[mi]),
                    .i_ready          (fab_rd_rready[mi]),
                    // rid is only meaningful when rvalid; gate the channel
                    // attribution accordingly. rd_ch_match additionally
                    // requires a matching entry in the rid->ch map.
                    .i_channel_id     (rd_ch_id),
                    .i_channel_valid  (fab_rd_rvalid[mi] && rd_ch_match),
                    .o_agg_productive   (rd_meter_agg_productive[mi]),
                    .o_agg_backpressure (rd_meter_agg_backpressure[mi]),
                    .o_agg_starvation   (rd_meter_agg_starvation[mi]),
                    .o_agg_idle         (rd_meter_agg_idle[mi]),
                    .o_ch_productive    (rd_meter_ch_productive[mi]),
                    .o_ch_backpressure  (rd_meter_ch_backpressure[mi]),
                    .o_ch_starvation    (rd_meter_ch_starvation[mi]),
                    .o_ch_idle          (rd_meter_ch_idle[mi]),
                    .o_ch_overflow      (rd_meter_ch_overflow[mi])
                );
            end

            // ---------- Write-side meters ----------
            for (mi = 0; mi < NUM_WR_PORTS; mi = mi + 1) begin : gen_wr_meter
                // Write per-channel attribution source.
                //   WR_CH_FROM_AWID=1: AXI4 W beats carry no WID, but W bursts
                //   follow AW-issue order -- so reconstruct the in-flight W
                //   burst's channel from awid with an AW->W order tracker
                //   (push awid's channel at AW-accept, head = current burst's
                //   channel, pop at WLAST). STREAM drives awid = channel, so no
                //   DMA sideband is needed. Correct when AW leads/accompanies W.
                //   WR_CH_FROM_AWID=0: use the explicit dma_wr_active_ch_* sideband.
                logic [CW-1:0]  wr_ch_id;
                logic           wr_ch_valid;

                if (WR_CH_FROM_AWID) begin : g_awid_track
                    localparam int AWQ_PTRW = (MAX_TRANSACTIONS > 1) ? $clog2(MAX_TRANSACTIONS) : 1;
                    logic [CW-1:0]     awq_mem [MAX_TRANSACTIONS];
                    logic [AWQ_PTRW:0] awq_wptr, awq_rptr;
                    logic              awq_empty, awq_full, awq_push, awq_pop;

                    assign awq_empty = (awq_wptr == awq_rptr);
                    assign awq_full  = (awq_wptr[AWQ_PTRW-1:0] == awq_rptr[AWQ_PTRW-1:0])
                                    && (awq_wptr[AWQ_PTRW]     != awq_rptr[AWQ_PTRW]);
                    assign awq_push  = fab_wr_awvalid[mi] && fab_wr_awready[mi] && !awq_full;
                    assign awq_pop   = fab_wr_wvalid[mi]  && fab_wr_wready[mi]
                                    && fab_wr_wlast[mi]   && !awq_empty;

                    `ALWAYS_FF_RST(aclk, aresetn,
                        if (`RST_ASSERTED(aresetn)) begin
                            awq_wptr <= '0;
                            awq_rptr <= '0;
                        end else begin
                            if (awq_push) begin
                                awq_mem[awq_wptr[AWQ_PTRW-1:0]] <= fab_wr_awid[mi][CW-1:0];
                                awq_wptr <= awq_wptr + 1'b1;
                            end
                            if (awq_pop) awq_rptr <= awq_rptr + 1'b1;
                        end
                    )
                    assign wr_ch_id    = awq_mem[awq_rptr[AWQ_PTRW-1:0]];
                    assign wr_ch_valid = !awq_empty;
                end else begin : g_sideband
                    assign wr_ch_id    = dma_wr_active_ch_id[mi];
                    assign wr_ch_valid = dma_wr_active_ch_valid[mi];
                end

                axi_bus_meter #(
                    .NUM_CHANNELS (NUM_CHANNELS)
                ) u_wr_meter (
                    .aclk             (aclk),
                    .aresetn          (aresetn),
                    .i_clear          (i_meter_clear),
                    .i_freeze         (i_meter_freeze),
                    .i_valid          (fab_wr_wvalid[mi]),
                    .i_ready          (fab_wr_wready[mi]),
                    .i_channel_id     (wr_ch_id),
                    .i_channel_valid  (wr_ch_valid),
                    .o_agg_productive   (wr_meter_agg_productive[mi]),
                    .o_agg_backpressure (wr_meter_agg_backpressure[mi]),
                    .o_agg_starvation   (wr_meter_agg_starvation[mi]),
                    .o_agg_idle         (wr_meter_agg_idle[mi]),
                    .o_ch_productive    (wr_meter_ch_productive[mi]),
                    .o_ch_backpressure  (wr_meter_ch_backpressure[mi]),
                    .o_ch_starvation    (wr_meter_ch_starvation[mi]),
                    .o_ch_idle          (wr_meter_ch_idle[mi]),
                    .o_ch_overflow      (wr_meter_ch_overflow[mi])
                );
            end

        end else begin : gen_no_meters
            // ENABLE_BUS_METER=0: tie every meter output to 0.
            for (mi = 0; mi < NUM_RD_PORTS; mi = mi + 1) begin : gen_rd_tieoff
                assign rd_meter_agg_productive[mi]   = '0;
                assign rd_meter_agg_backpressure[mi] = '0;
                assign rd_meter_agg_starvation[mi]   = '0;
                assign rd_meter_agg_idle[mi]         = '0;
                assign rd_meter_ch_overflow[mi]      = '0;
                for (ci = 0; ci < NUM_CHANNELS; ci = ci + 1) begin : gen_rd_ch_tie
                    assign rd_meter_ch_productive[mi][ci]   = '0;
                    assign rd_meter_ch_backpressure[mi][ci] = '0;
                    assign rd_meter_ch_starvation[mi][ci]   = '0;
                    assign rd_meter_ch_idle[mi][ci]         = '0;
                end
            end
            for (mi = 0; mi < NUM_WR_PORTS; mi = mi + 1) begin : gen_wr_tieoff
                assign wr_meter_agg_productive[mi]   = '0;
                assign wr_meter_agg_backpressure[mi] = '0;
                assign wr_meter_agg_starvation[mi]   = '0;
                assign wr_meter_agg_idle[mi]         = '0;
                assign wr_meter_ch_overflow[mi]      = '0;
                for (ci = 0; ci < NUM_CHANNELS; ci = ci + 1) begin : gen_wr_ch_tie
                    assign wr_meter_ch_productive[mi][ci]   = '0;
                    assign wr_meter_ch_backpressure[mi][ci] = '0;
                    assign wr_meter_ch_starvation[mi][ci]   = '0;
                    assign wr_meter_ch_idle[mi][ci]         = '0;
                end
            end
        end
    endgenerate

    // =================================================================
    // axi_perf_latency_hist per-port instantiations (RFC Stage E.3)
    //
    //   - One read histogram per rd port: AR->first-R + AR->RLAST, binned
    //     into HIST_NUM_BINS log2 bins (two metrics, select via i_hist_metric).
    //   - One write histogram per wr port: AW->B (one metric).
    //   Fed from the fabric-side handshakes (same side the meters snoop, no
    //   beats dropped through the pass-through wrappers); windowed in lockstep
    //   with the meters via i_meter_clear / i_meter_freeze. The in-core STREAM
    //   path drives those from its first-DMA-activity perf-window controller
    //   (the arm-gap fix); an observer-based harness drives them the same way.
    //   ENABLE_LATENCY_HIST=0 skips instantiation and ties outputs to 0.
    // =================================================================
    genvar hi;
    generate
        if (ENABLE_LATENCY_HIST) begin : gen_hist
            // ---------- Read-side histograms (AR->first-R, AR->RLAST) ----------
            for (hi = 0; hi < NUM_RD_PORTS; hi = hi + 1) begin : gen_rd_hist
                axi_perf_latency_hist #(
                    .ID_WIDTH        (AXI_ID_WIDTH),
                    .NUM_CHANNELS    (NUM_CHANNELS),
                    .MAX_OUTSTANDING (HIST_MAX_OUTSTANDING),
                    .NUM_BINS        (HIST_NUM_BINS),
                    .IS_READ         (1'b1)
                ) u_rd_lat_hist (
                    .aclk         (aclk),
                    .aresetn      (aresetn),
                    .i_clear      (i_meter_clear),
                    .i_freeze     (i_meter_freeze),
                    .cmd_valid    (fab_rd_arvalid[hi]),
                    .cmd_ready    (fab_rd_arready[hi]),
                    .cmd_id       (fab_rd_arid[hi]),
                    .data_valid   (fab_rd_rvalid[hi]),
                    .data_ready   (fab_rd_rready[hi]),
                    .data_last    (fab_rd_rlast[hi]),
                    .data_id      (fab_rd_rid[hi]),
                    .resp_valid   (1'b0),
                    .resp_ready   (1'b0),
                    .resp_id      ('0),
                    .i_hist_metric(i_hist_metric),
                    .i_hist_bin   (i_hist_bin),
                    .o_hist_count (rd_hist_count[hi]),
                    .o_hist_total (rd_hist_total[hi])
                );
            end
            // ---------- Write-side histograms (AW->B) ----------
            for (hi = 0; hi < NUM_WR_PORTS; hi = hi + 1) begin : gen_wr_hist
                axi_perf_latency_hist #(
                    .ID_WIDTH        (AXI_ID_WIDTH),
                    .NUM_CHANNELS    (NUM_CHANNELS),
                    .MAX_OUTSTANDING (HIST_MAX_OUTSTANDING),
                    .NUM_BINS        (HIST_NUM_BINS),
                    .IS_READ         (1'b0)
                ) u_wr_lat_hist (
                    .aclk         (aclk),
                    .aresetn      (aresetn),
                    .i_clear      (i_meter_clear),
                    .i_freeze     (i_meter_freeze),
                    .cmd_valid    (fab_wr_awvalid[hi]),
                    .cmd_ready    (fab_wr_awready[hi]),
                    .cmd_id       (fab_wr_awid[hi]),
                    .data_valid   (1'b0),
                    .data_ready   (1'b0),
                    .data_last    (1'b0),
                    .data_id      ('0),
                    .resp_valid   (fab_wr_bvalid[hi]),
                    .resp_ready   (fab_wr_bready[hi]),
                    .resp_id      (fab_wr_bid[hi]),
                    .i_hist_metric(i_hist_metric),
                    .i_hist_bin   (i_hist_bin),
                    .o_hist_count (wr_hist_count[hi]),
                    .o_hist_total (wr_hist_total[hi])
                );
            end
        end else begin : gen_no_hist
            for (hi = 0; hi < NUM_RD_PORTS; hi = hi + 1) begin : gen_rd_hist_tie
                assign rd_hist_count[hi] = '0;
                assign rd_hist_total[hi] = '0;
            end
            for (hi = 0; hi < NUM_WR_PORTS; hi = hi + 1) begin : gen_wr_hist_tie
                assign wr_hist_count[hi] = '0;
                assign wr_hist_total[hi] = '0;
            end
        end
    endgenerate

endmodule : axi4_dma_observer
