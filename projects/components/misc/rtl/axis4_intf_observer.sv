// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: axis4_intf_observer
// Purpose: Inline AXI4-Stream interface observer -- a passive tap for any
//          AXIS link (N ports), with its own APB configuration. The AXIS
//          sibling of axi4_intf_{master,slave}_observer: same APB window,
//          same obs_regs map, same monbus egress, same telemetry readback,
//          so one host decoder and one regmap serve all three.
//
//   Drop it beside any AXI4-Stream link -- a DMA's sink ingress (s_axis_*)
//   or source egress (m_axis_*), a switch port, a converter boundary. Every
//   obs_axis_* pin is an INPUT, both halves of the handshake included: this
//   block watches the wire and never drives it, so attaching it cannot
//   change the stream it measures (vault/handbook/design/observers-do-not-drive.md).
//
//   Per port it builds:
//     - an axis_bus_meter (cycle buckets + exact bytes/beats/packets, per
//       tid channel), read through OBS_STAT_SEL / OBS_STAT_DATA;
//     - an AXIS event TAP that emits PROTOCOL_AXIS monbus packets, merged by
//       monbus_arbiter into a monbus_axil4_{axi4,axil4}_group whose central
//       filter (AXIS_PKT_MASK / AXIS_MASK1..3) decides what reaches the err
//       FIFO (s_axil_* drain + irq_out) or the bulk dump (m_axi_* / m_axil_*).
//
//   No AXIS monitor exists in rtl/amba/monitor -- the AXI observers wrap
//   axi4_*_monlite, but there was never an axis4_* counterpart -- so the tap
//   is written here, in the lite's discipline: no CAM, no timer pool, stamps
//   not counters, and an event the monbus cannot take is DROPPED AND COUNTED
//   rather than stalling anything. The drop count feeds OBS_STICKY.TAP_BLOCKED.
//
//   The AXIS packet vocabulary is monitor_amba4_pkg's (PROTOCOL_AXIS is
//   valid for Error, Timeout, Completion, Credit, Channel and Stream; there
//   is NO Threshold class for AXIS, which is why MON_LATENCY drives a
//   Credit/BACKPRESSURE event here rather than a Threshold packet):
//
//     class       code                   fires when                              event_data
//     Error       VALID_TIMING           tvalid dropped before tready accepted   {stall cycles, packets done}
//     Error       STRB_INVALID           a beat handshook with tstrb == 0        {beats in pkt, packets done}
//     Timeout     HANDSHAKE              tvalid stalled >= MON_TIMEOUT us        {stall cycles, age us, limit us}
//     Timeout     PACKET                 in-packet gap >= MON_TIMEOUT us         {beats in pkt, age us, limit us}
//     Completion  STREAM_END             tlast handshook                         {tid, tdest, beats in pkt}
//     Credit      BACKPRESSURE           a stall reached MON_LATENCY cycles      {stall cycles, MON_LATENCY}
//     Channel     ID_CHANGE              tid differs from the previous beat      {prev tid, this tid, beats}
//                                        of the same packet (once per change)
//     Channel     DEST_CHANGE            tdest differs from the previous beat    {prev tdest, this tdest, beats}
//     Stream      START                  first beat of a packet handshook        {tid, tdest, packets done}
//     Stream      PAUSE / RESUME         tvalid dropped / returned mid-packet    {beats in pkt, packets done}
//
//   Runtime gating reuses MON_CTRL bit-for-bit with the AXI observers, and
//   OBS_CAPS0 reports the same bit for the cone each enable gates:
//     ERROR_EN[0] Error   TIMEOUT_EN[1] Timeout   COMPL_EN[2] Completion
//     THRESHOLD_EN[3] Credit   PERF_EN[4] Stream   DEBUG_EN[5] Channel
//   ADDR_CHECK_EN and the ADDR_RANGE* registers are inert (a stream has no
//   address); OBS_CAPS0.N_ADDR_RANGES reads 0 so software can tell.
//
//   Packet fields: channel_id = tid (low 9 bits), agent_id = {8'h00, 4'h2,
//   port[3:0]} (the AXI observers use 4'h0 for read taps and 4'h1 for
//   write taps), unit_id = UNIT_ID. A stalled beat's tdata is NOT checked
//   for stability: that costs DATA_WIDTH flops and a DATA_WIDTH compare per
//   port (512 each at the rapids width) for a violation no DMA in the tree
//   can commit, so the check is left out rather than parameter-gated off.
//
// Subsystem: amba
// Author: sean galloway

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axis4_intf_observer
    import monitor_common_pkg::*;
    import monitor_amba4_pkg::*;
#(
    // ---------- Tap count ----------
    parameter int NUM_PORTS          = 1,

    // ---------- Observed AXIS widths (shared by all ports) ----------
    parameter int DATA_WIDTH         = 512,
    parameter int AXIS_ID_WIDTH      = 8,
    parameter int AXIS_DEST_WIDTH    = 4,
    parameter int AXIS_USER_WIDTH    = 1,
    parameter int SW                 = DATA_WIDTH / 8,   // tstrb width

    // ---------- Egress (dump masters, AXIL drain) sizing ----------
    parameter int ADDR_WIDTH         = 32,
    parameter int OBS_AXI_ID_WIDTH   = 4,        // master-write id for dumps
    parameter int MAX_BURST_BEATS    = 64,       // 1..256 (256 is AXI4 max)

    // ---------- Group config ----------
    parameter int FIFO_DEPTH_ERR        = 64,
    parameter int FIFO_DEPTH_WRITE      = 96,    // beats
    parameter int FLUSH_TIMEOUT_CYCLES  = 1024,
    parameter int USE_COMPRESSION       = 0,

    // ---- Monbus egress: which dump master this instance exposes ----------
    // 0 = monbus_axil4_axi4_group -> AXI4 burst master (m_axi_*).
    // 1 = monbus_axil4_axil4_group -> AXIL write master (m_axil_*), which is
    //     what the harness tally paths consume.
    // BOTH port sets are always declared so the port list does not change
    // with the parameter; the unused set is driven to zero.
    parameter bit EGRESS_AXIL           = 1'b0,

    // Monitor timer LUT frequency, in MHz, and the CFI LUT bounds. Identical
    // contract to the AXI observers: the 1 us tick MON_TIMEOUT is expressed
    // in is exact only if ACLK_MHZ lands on the 60+5i grid, and elaboration
    // fails otherwise rather than skewing every timeout silently.
    parameter int ACLK_MHZ              = 100,
    parameter int CFI_MIN_FREQ_MHZ      = 60,
    parameter int CFI_MAX_FREQ_MHZ      = 135,

    // Build-time arm for the event taps. 0 compiles them out; the bus meters
    // live OUTSIDE this gate and keep counting either way. MON_CTRL.MONITOR_EN
    // is ANDed with this, so an unarmed tap cannot be armed from software.
    parameter bit ENABLE_MON_TAPS       = 1'b1,

    parameter logic [7:0] UNIT_ID       = 8'h11, // 8'h10 is the AXI observers

    // ---------- Per-tap cone enables ----------
    // Each one is a class of PROTOCOL_AXIS packet. Off = the compare logic
    // and its event data are constant-pruned; OBS_CAPS0 reports the truth.
    parameter bit TAP_ENABLE_ERROR_LOGIC     = 1'b0,
    parameter bit TAP_ENABLE_TIMEOUT_LOGIC   = 1'b0,
    parameter bit TAP_ENABLE_COMPL_LOGIC     = 1'b0,
    parameter bit TAP_ENABLE_CREDIT_LOGIC    = 1'b0,
    parameter bit TAP_ENABLE_STREAM_LOGIC    = 1'b0,
    parameter bit TAP_ENABLE_CHANNEL_LOGIC   = 1'b0,

    // APB config window width, VISIBLE at the top on purpose; the regblock's
    // own cpuif width is DERIVED from the generated package (see
    // CPUIF_ADDR_WIDTH) so it tracks the register map automatically.
    parameter int APB_ADDR_WIDTH             = 12,

    // ---------- axis_bus_meter integration ----------
    parameter bit ENABLE_BUS_METER      = 1'b1,  // 0 = omit meters, tie outputs to 0
    parameter int NUM_CHANNELS          = 1,     // per-tid buckets; 1 = aggregate only
    parameter int CW                    = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1
) (
    input  logic                                            aclk,
    input  logic                                            aresetn,

    // ---- APB configuration slave ------------------------------------------
    //   flat APB -> apb4_slave -> peakrdl_to_cmdrsp -> obs_regs_top
    input  logic                          s_apb_psel,
    input  logic                          s_apb_penable,
    output logic                          s_apb_pready,
    input  logic [APB_ADDR_WIDTH-1:0]     s_apb_paddr,
    input  logic                          s_apb_pwrite,
    input  logic [31:0]                   s_apb_pwdata,
    input  logic [3:0]                    s_apb_pstrb,
    output logic [31:0]                   s_apb_prdata,
    output logic                          s_apb_pslverr,
    // Synchronous clear: the monbus group's compressor CAM (+ stats) and
    // every tap's drop counter. Pulse when idle.
    input  logic                                            cam_clear,

    // ================================================================
    // OBSERVED AXI4-STREAM PORTS -- INPUTS ONLY, tready included.
    // ================================================================
    input  logic [NUM_PORTS-1:0][DATA_WIDTH-1:0]            obs_axis_tdata,
    input  logic [NUM_PORTS-1:0][SW-1:0]                    obs_axis_tstrb,
    input  logic [NUM_PORTS-1:0]                            obs_axis_tlast,
    input  logic [NUM_PORTS-1:0][AXIS_ID_WIDTH-1:0]         obs_axis_tid,
    input  logic [NUM_PORTS-1:0][AXIS_DEST_WIDTH-1:0]       obs_axis_tdest,
    input  logic [NUM_PORTS-1:0][AXIS_USER_WIDTH-1:0]       obs_axis_tuser,
    input  logic [NUM_PORTS-1:0]                            obs_axis_tvalid,
    input  logic [NUM_PORTS-1:0]                            obs_axis_tready,

    // ================================================================
    // Observability outputs (same shape as the AXI observers)
    // ================================================================

    // CPU-side err FIFO drain (AXIL slave-read)
    input  logic                                            s_axil_arvalid,
    output logic                                            s_axil_arready,
    input  logic [ADDR_WIDTH-1:0]                           s_axil_araddr,
    input  logic [2:0]                                      s_axil_arprot,
    output logic                                            s_axil_rvalid,
    input  logic                                            s_axil_rready,
    output logic [63:0]                                     s_axil_rdata,
    output logic [1:0]                                      s_axil_rresp,

    // Bulk-trace dump (AXI4 burst master-write). Zero when EGRESS_AXIL=1.
    output logic [OBS_AXI_ID_WIDTH-1:0]                     m_axi_awid,
    output logic [ADDR_WIDTH-1:0]                           m_axi_awaddr,
    output logic [7:0]                                      m_axi_awlen,
    output logic [2:0]                                      m_axi_awsize,
    output logic [1:0]                                      m_axi_awburst,
    output logic                                            m_axi_awlock,
    output logic [3:0]                                      m_axi_awcache,
    output logic [2:0]                                      m_axi_awprot,
    output logic [3:0]                                      m_axi_awqos,
    output logic [3:0]                                      m_axi_awregion,
    output logic                                            m_axi_awuser,
    output logic                                            m_axi_awvalid,
    input  logic                                            m_axi_awready,
    output logic [63:0]                                     m_axi_wdata,
    output logic [7:0]                                      m_axi_wstrb,
    output logic                                            m_axi_wlast,
    output logic                                            m_axi_wuser,
    output logic                                            m_axi_wvalid,
    input  logic                                            m_axi_wready,
    input  logic [OBS_AXI_ID_WIDTH-1:0]                     m_axi_bid,
    input  logic [1:0]                                      m_axi_bresp,
    input  logic                                            m_axi_buser,
    input  logic                                            m_axi_bvalid,
    output logic                                            m_axi_bready,

    // ---- AXIL dump master (EGRESS_AXIL=1). Zero when unused. ----------
    output logic                                            m_axil_awvalid,
    input  logic                                            m_axil_awready,
    output logic [ADDR_WIDTH-1:0]                           m_axil_awaddr,
    output logic [2:0]                                      m_axil_awprot,
    output logic                                            m_axil_wvalid,
    input  logic                                            m_axil_wready,
    output logic [63:0]                                     m_axil_wdata,
    output logic [7:0]                                      m_axil_wstrb,
    input  logic                                            m_axil_bvalid,
    output logic                                            m_axil_bready,
    input  logic [1:0]                                      m_axil_bresp,

    // IRQ: asserted whenever the err FIFO has any entries
    output logic                                            irq_out,

    // ================================================================
    // axis_bus_meter window control (safe to tie off if ENABLE_BUS_METER=0)
    // ================================================================
    // One-cycle synchronous pulse clears every bucket counter and overflow
    // sticky; held-high also works.
    input  logic                                            i_meter_clear,
    // Hold high to pause every bucket counter (the window closes).
    input  logic                                            i_meter_freeze
);

    // Telemetry lives behind this block's own regblock (OBS_STAT_SEL /
    // OBS_STAT_DATA, OBS_FIFO_STAT, OBS_STICKY, OBS_COMP_STAT*) rather than
    // on output pins, same as the AXI observers.
    logic                        err_fifo_full;
    logic                        write_fifo_full;
    logic [15:0]                 err_fifo_count;
    logic [15:0]                 write_fifo_count;
    logic [31:0]                 meter_agg_productive   [NUM_PORTS];
    logic [31:0]                 meter_agg_backpressure [NUM_PORTS];
    logic [31:0]                 meter_agg_starvation   [NUM_PORTS];
    logic [31:0]                 meter_agg_idle         [NUM_PORTS];
    logic [63:0]                 meter_agg_bytes        [NUM_PORTS];
    logic [31:0]                 meter_agg_beats        [NUM_PORTS];
    logic [31:0]                 meter_agg_packets      [NUM_PORTS];
    // PACKED [port][channel][16], not a 2-D unpacked array as in the AXI
    // observers: cocotb cannot read a 2-D unpacked handle under Verilator
    // (IndexError in .value), and the AXIS BFM walks every top-level handle
    // when it binds. The AXI observers never hit it because their TB binds
    // only an APB master, which does not walk.
    logic [NUM_PORTS-1:0][NUM_CHANNELS-1:0][15:0] meter_ch_productive;
    logic [NUM_PORTS-1:0][NUM_CHANNELS-1:0][15:0] meter_ch_backpressure;
    logic [NUM_PORTS-1:0][NUM_CHANNELS-1:0][15:0] meter_ch_starvation;
    logic [NUM_PORTS-1:0][NUM_CHANNELS-1:0][15:0] meter_ch_idle;
    logic [NUM_CHANNELS*4-1:0]   meter_ch_overflow      [NUM_PORTS];

    // Per-tap honesty counters: events the monbus could not take (holding
    // register occupied, or two classes fired in one cycle). Nothing here
    // reaches the observed stream; a non-zero count means the packet stream
    // UNDERCOUNTS, which is what OBS_STICKY.TAP_BLOCKED reports.
    logic [15:0]                 tap_dropped   [NUM_PORTS];
    logic [31:0]                 tap_packets   [NUM_PORTS];   // packets completed, per tap
    logic [NUM_PORTS-1:0]        tap_lost;

    // =======================================================================
    // Configuration: APB -> cmd/rsp -> passthrough regblock
    // Same chain as the AXI observers. No cmdrsp_router: one target.
    // =======================================================================
    logic                w_cmd_valid, w_cmd_ready, w_cmd_pwrite;
    logic [11:0]         w_cmd_paddr;
    logic [31:0]         w_cmd_pwdata;
    logic [3:0]          w_cmd_pstrb;
    logic [2:0]          w_cmd_pprot;
    logic                w_rsp_valid, w_rsp_ready, w_rsp_pslverr;
    logic [31:0]         w_rsp_prdata;

    // Regblock cpuif address width, DERIVED from the generated package so it
    // cannot drift from the register map (a hand-written cast here is what
    // made every register at or above 0x080 alias onto a low one in the AXI
    // observer's history).
    localparam int CPUIF_ADDR_WIDTH = obs_regs_top_pkg::OBS_REGS_TOP_MIN_ADDR_WIDTH;

    apb4_slave #(.ADDR_WIDTH(APB_ADDR_WIDTH), .DATA_WIDTH(32)) u_obs_apb (
        .pclk(aclk), .presetn(aresetn),
        .s_apb_PSEL(s_apb_psel),     .s_apb_PENABLE(s_apb_penable),
        .s_apb_PREADY(s_apb_pready), .s_apb_PADDR(s_apb_paddr),
        .s_apb_PWRITE(s_apb_pwrite), .s_apb_PWDATA(s_apb_pwdata),
        .s_apb_PSTRB(s_apb_pstrb),   .s_apb_PPROT(3'b000),
        .s_apb_PRDATA(s_apb_prdata), .s_apb_PSLVERR(s_apb_pslverr),
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

    peakrdl_to_cmdrsp #(.ADDR_WIDTH(APB_ADDR_WIDTH), .DATA_WIDTH(32)) u_obs_adapter (
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

    obs_regs_top_pkg::obs_regs_top__out_t hwif;
    // Hardware->software side of the regblock: the telemetry readback.
    // Every hw=w field is driven by exactly one continuous assign below.
    obs_regs_top_pkg::obs_regs_top__in_t hwif_i;

    obs_regs_top u_obs_regs (
        .clk(aclk), .rst(~aresetn),
        .s_cpuif_req(w_rb_req),               .s_cpuif_req_is_wr(w_rb_req_is_wr),
        .s_cpuif_addr(CPUIF_ADDR_WIDTH'(w_rb_addr)),         .s_cpuif_wr_data(w_rb_wr_data),
        .s_cpuif_wr_biten(w_rb_wr_biten),
        .s_cpuif_req_stall_wr(w_rb_stall_wr), .s_cpuif_req_stall_rd(w_rb_stall_rd),
        .s_cpuif_rd_ack(w_rb_rd_ack),         .s_cpuif_rd_err(w_rb_rd_err),
        .s_cpuif_rd_data(w_rb_rd_data),
        .s_cpuif_wr_ack(w_rb_wr_ack),         .s_cpuif_wr_err(w_rb_wr_err),
        .hwif_in(hwif_i),
        .hwif_out(hwif)
    );

    // The APB window must be able to address the whole regblock.
    initial begin
        if (APB_ADDR_WIDTH < CPUIF_ADDR_WIDTH)
            $error("APB_ADDR_WIDTH=%0d cannot address the %0d-bit regblock map",
                   APB_ADDR_WIDTH, CPUIF_ADDR_WIDTH);
    end

    // Local aliases: the group's central filter inputs, all three protocol
    // sets. This observer emits PROTOCOL_AXIS only; the AXI and CORE sets do
    // work only for an upstream caller that merges this monbus with others,
    // but they are real filter inputs either way.
    logic [15:0] cfg_axi_pkt_mask, cfg_axi_err_select, cfg_axi_error_mask;
    logic [15:0] cfg_axi_timeout_mask, cfg_axi_compl_mask, cfg_axi_thresh_mask;
    logic [15:0] cfg_axi_perf_mask, cfg_axi_addr_mask, cfg_axi_debug_mask;
    logic [15:0] cfg_axis_pkt_mask, cfg_axis_err_select, cfg_axis_error_mask;
    logic [15:0] cfg_axis_timeout_mask, cfg_axis_compl_mask, cfg_axis_channel_mask;
    logic [15:0] cfg_axis_credit_mask, cfg_axis_stream_mask;
    logic [15:0] cfg_core_pkt_mask, cfg_core_err_select, cfg_core_error_mask;
    logic [15:0] cfg_core_timeout_mask, cfg_core_compl_mask, cfg_core_thresh_mask;
    logic [15:0] cfg_core_perf_mask, cfg_core_debug_mask;
    logic [15:0] cfg_flush_watermark;
    logic        cfg_compress_en;
    logic [3:0]  cfg_freq_sel;
    logic [ADDR_WIDTH-1:0] cfg_base_addr, cfg_limit_addr;

    // Tap runtime config (MON_CTRL / MON_TIMEOUT / MON_LATENCY)
    logic        cfg_monitor_enable_w;
    logic        cfg_error_enable_w, cfg_timeout_enable_w, cfg_compl_enable_w;
    logic        cfg_credit_enable_w, cfg_stream_enable_w, cfg_channel_enable_w;
    logic [15:0] cfg_timeout_us_w;
    logic [31:0] cfg_latency_threshold_w;

    // Build-time LUT index for ACLK_MHZ, inverting the LINEAR mapping
    // freq[i] = MIN + (MAX-MIN)*i/(N-1) with N=16.
    localparam int CFI_ENTRIES    = 16;
    localparam int ACLK_FREQ_SEL  =
        ((ACLK_MHZ - CFI_MIN_FREQ_MHZ) * (CFI_ENTRIES - 1))
        / (CFI_MAX_FREQ_MHZ - CFI_MIN_FREQ_MHZ);

    initial begin
        if (ACLK_MHZ < CFI_MIN_FREQ_MHZ || ACLK_MHZ > CFI_MAX_FREQ_MHZ)
            $error("ACLK_MHZ=%0d outside the observer CFI LUT range %0d..%0d",
                   ACLK_MHZ, CFI_MIN_FREQ_MHZ, CFI_MAX_FREQ_MHZ);
        else if (CFI_MIN_FREQ_MHZ
                 + ((CFI_MAX_FREQ_MHZ - CFI_MIN_FREQ_MHZ) * ACLK_FREQ_SEL)
                   / (CFI_ENTRIES - 1) != ACLK_MHZ)
            $error("ACLK_MHZ=%0d is not on the CFI LUT grid (%0d..%0d/%0d entries); the 1 us tick would be inexact",
                   ACLK_MHZ, CFI_MIN_FREQ_MHZ, CFI_MAX_FREQ_MHZ, CFI_ENTRIES);
    end

    assign cfg_axi_pkt_mask      = hwif.OBS.AXI_PKT_MASK.PKT_MASK.value;
    assign cfg_axi_err_select    = hwif.OBS.AXI_PKT_MASK.ERR_SELECT.value;
    assign cfg_axi_error_mask    = hwif.OBS.AXI_MASK1.ERROR_MASK.value;
    assign cfg_axi_timeout_mask  = hwif.OBS.AXI_MASK1.TIMEOUT_MASK.value;
    assign cfg_axi_compl_mask    = hwif.OBS.AXI_MASK2.COMPL_MASK.value;
    assign cfg_axi_thresh_mask   = hwif.OBS.AXI_MASK2.THRESH_MASK.value;
    assign cfg_axi_perf_mask     = hwif.OBS.AXI_MASK3.PERF_MASK.value;
    assign cfg_axi_addr_mask     = hwif.OBS.AXI_MASK3.ADDR_MASK.value;
    assign cfg_axi_debug_mask    = hwif.OBS.AXI_MASK4.DEBUG_MASK.value;
    assign cfg_axis_pkt_mask     = hwif.OBS.AXIS_PKT_MASK.PKT_MASK.value;
    assign cfg_axis_err_select   = hwif.OBS.AXIS_PKT_MASK.ERR_SELECT.value;
    assign cfg_axis_error_mask   = hwif.OBS.AXIS_MASK1.ERROR_MASK.value;
    assign cfg_axis_timeout_mask = hwif.OBS.AXIS_MASK1.TIMEOUT_MASK.value;
    assign cfg_axis_compl_mask   = hwif.OBS.AXIS_MASK2.COMPL_MASK.value;
    assign cfg_axis_channel_mask = hwif.OBS.AXIS_MASK2.CHANNEL_MASK.value;
    assign cfg_axis_credit_mask  = hwif.OBS.AXIS_MASK3.CREDIT_MASK.value;
    assign cfg_axis_stream_mask  = hwif.OBS.AXIS_MASK3.STREAM_MASK.value;
    assign cfg_core_pkt_mask     = hwif.OBS.CORE_PKT_MASK.PKT_MASK.value;
    assign cfg_core_err_select   = hwif.OBS.CORE_PKT_MASK.ERR_SELECT.value;
    assign cfg_core_error_mask   = hwif.OBS.CORE_MASK1.ERROR_MASK.value;
    assign cfg_core_timeout_mask = hwif.OBS.CORE_MASK1.TIMEOUT_MASK.value;
    assign cfg_core_compl_mask   = hwif.OBS.CORE_MASK2.COMPL_MASK.value;
    assign cfg_core_thresh_mask  = hwif.OBS.CORE_MASK2.THRESH_MASK.value;
    assign cfg_core_perf_mask    = hwif.OBS.CORE_MASK3.PERF_MASK.value;
    assign cfg_core_debug_mask   = hwif.OBS.CORE_MASK3.DEBUG_MASK.value;
    assign cfg_flush_watermark   = hwif.OBS.OBS_CTRL.FLUSH_WATERMARK.value;
    assign cfg_compress_en       = hwif.OBS.OBS_CTRL.COMPRESS_EN.value;
    // At reset FREQ_SEL_OVR=0 selects the index DERIVED from ACLK_MHZ, so the
    // 1 us tick is right for whatever clock this was built at.
    assign cfg_freq_sel          = hwif.OBS.OBS_CTRL.FREQ_SEL_OVR.value
                                 ? hwif.OBS.OBS_CTRL.FREQ_SEL.value
                                 : ACLK_FREQ_SEL[3:0];
    assign cfg_base_addr         = ADDR_WIDTH'(hwif.OBS.OBS_BASE_ADDR.VALUE.value);
    assign cfg_limit_addr        = ADDR_WIDTH'(hwif.OBS.OBS_LIMIT_ADDR.VALUE.value);

    // MON_CTRL, bit-for-bit with the AXI observers; the AXIS class each bit
    // gates is in the header table. MONITOR_EN is ANDed with the build arm.
    assign cfg_monitor_enable_w  = ENABLE_MON_TAPS & hwif.OBS.MON_CTRL.MONITOR_EN.value;
    assign cfg_error_enable_w    = hwif.OBS.MON_CTRL.ERROR_EN.value;
    assign cfg_timeout_enable_w  = hwif.OBS.MON_CTRL.TIMEOUT_EN.value;
    assign cfg_compl_enable_w    = hwif.OBS.MON_CTRL.COMPL_EN.value;
    assign cfg_credit_enable_w   = hwif.OBS.MON_CTRL.THRESHOLD_EN.value;
    assign cfg_stream_enable_w   = hwif.OBS.MON_CTRL.PERF_EN.value;
    assign cfg_channel_enable_w  = hwif.OBS.MON_CTRL.DEBUG_EN.value;
    // MON_TIMEOUT is MICROSECONDS; 0 means 0xFFFF (register contract).
    assign cfg_timeout_us_w      = (hwif.OBS.MON_TIMEOUT.TIMEOUT_CYCLES.value == 16'd0)
                                 ? 16'hFFFF : hwif.OBS.MON_TIMEOUT.TIMEOUT_CYCLES.value;
    assign cfg_latency_threshold_w = hwif.OBS.MON_LATENCY.VALUE.value;

    // Capabilities: what this instance was BUILT with. Bits [5:0] pair with
    // MON_CTRL[5:0], AXIS class per the header table. N_ADDR_RANGES and
    // ID_SLICE read 0: neither exists for a stream. See the CAPS PACKING
    // note in obs_regs.rdl for why these are wide single fields.
    assign hwif_i.OBS.OBS_CAPS0.VALUE.next = {
        16'h0,                          // [31:16] reserved
        4'h0,                           // [15:12] N_ADDR_RANGES: none on a stream
        1'b0,                           // [11]    reserved
        1'b0,                           // [10]    ID_SLICE: not offered here
        EGRESS_AXIL,                    // [9]
        (USE_COMPRESSION != 0),         // [8]
        ENABLE_BUS_METER,               // [7]
        ENABLE_MON_TAPS,                // [6]
        TAP_ENABLE_CHANNEL_LOGIC,       // [5] Channel cone (MON_CTRL.DEBUG_EN)
        TAP_ENABLE_STREAM_LOGIC,        // [4] Stream cone  (MON_CTRL.PERF_EN)
        TAP_ENABLE_CREDIT_LOGIC,        // [3] Credit cone  (MON_CTRL.THRESHOLD_EN)
        TAP_ENABLE_COMPL_LOGIC,         // [2]
        TAP_ENABLE_TIMEOUT_LOGIC,       // [1]
        TAP_ENABLE_ERROR_LOGIC          // [0]
    };
    // Geometry: the port count sits in the NUM_RD_PORTS byte, NUM_WR_PORTS
    // reads 0 -- a stream has one direction.
    assign hwif_i.OBS.OBS_CAPS1.VALUE.next = {
        8'h00, 8'(NUM_CHANNELS), 8'h00, 8'(NUM_PORTS)
    };
    // Sizing: a stream has no transaction table. DATA_WIDTH and the tid
    // width are what software needs to interpret event_data and bytes.
    assign hwif_i.OBS.OBS_CAPS2.VALUE.next = {
        8'(ADDR_WIDTH), 8'(AXIS_ID_WIDTH), 16'(DATA_WIDTH)
    };

    // =================================================================
    // Local parameters / derived sizes
    // =================================================================
    localparam int TIDW = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1;

    initial begin
        if (NUM_PORTS < 1)
            $error("axis4_intf_observer: NUM_PORTS must be >= 1");
        if (NUM_CHANNELS > 1 && AXIS_ID_WIDTH < TIDW)
            $error("axis4_intf_observer: NUM_CHANNELS=%0d needs %0d tid bits, AXIS_ID_WIDTH=%0d",
                   NUM_CHANNELS, TIDW, AXIS_ID_WIDTH);
    end

    // =================================================================
    // Frequency-invariant microsecond stamp, shared by every tap. Same
    // knobs as the lite: counter_freq_invariant divides aclk by the LUT
    // entry cfg_freq_sel picks, so MON_TIMEOUT stays in microseconds at
    // any build frequency on the grid.
    // =================================================================
    logic        w_tick;
    logic [15:0] r_us;

    counter_freq_invariant #(
        .COUNTER_WIDTH    (1),
        .MIN_FREQ_MHZ     (CFI_MIN_FREQ_MHZ),
        .MAX_FREQ_MHZ     (CFI_MAX_FREQ_MHZ),
        .NUM_FREQ_ENTRIES (CFI_ENTRIES),
        .FREQ_STRATEGY    (0)
    ) u_tick (
        .clk          (aclk),
        .rst_n        (aresetn),
        .sync_reset_n (1'b1),
        .freq_sel     (cfg_freq_sel),
        .tick         (w_tick),
        /* verilator lint_off PINCONNECTEMPTY */
        .o_counter    ()
        /* verilator lint_on PINCONNECTEMPTY */
    );

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_us <= 16'd0;
        else if (w_tick)            r_us <= r_us + 16'd1;
    )

    // =================================================================
    // Free-running timestamp (driven out by monbus_group, stamped onto
    // every packet at emission)
    // =================================================================
    monbus_timestamp_t                              mon_time_w;

    // Per-source monbus streams + arbiter inputs (unpacked, as the arbiter
    // expects). monbus_arbiter sizes its grant id as $clog2(CLIENTS), which
    // is a [-1:0] vector at CLIENTS=1 -- Verilator refuses it (ASCRANGE) and
    // no other consumer has ever built the arbiter with one client. A
    // single-port observer therefore pads to two clients and ties the spare
    // input idle; the arbiter then has the shape every other instance has.
    localparam int ARB_CLIENTS = (NUM_PORTS < 2) ? 2 : NUM_PORTS;
    logic                                           mon_valid    [ARB_CLIENTS];
    logic                                           mon_ready    [ARB_CLIENTS];
    monitor_packet_t                                mon_packet   [ARB_CLIENTS];
    monbus_timestamp_t                              mon_ts       [ARB_CLIENTS];

    // =================================================================
    // Per-port AXIS event taps
    // =================================================================
    genvar gi;
    generate
        for (gi = 0; gi < NUM_PORTS; gi = gi + 1) begin : gen_tap
            // ---- the wire, this cycle ----
            logic                       w_tv, w_tr, w_tl, w_hs;
            assign w_tv = obs_axis_tvalid[gi];
            assign w_tr = obs_axis_tready[gi];
            assign w_tl = obs_axis_tlast[gi];
            assign w_hs = w_tv & w_tr;

            // ---- packet-level state ----
            logic                       r_in_pkt;        // a beat accepted, tlast not yet seen
            logic [31:0]                r_pkt_beats;     // beats accepted in the open packet
            logic [31:0]                r_pkt_count;     // packets completed
            logic [AXIS_ID_WIDTH-1:0]   r_pkt_tid;       // tid on the previous accepted beat
            logic [AXIS_DEST_WIDTH-1:0] r_pkt_tdest;     // tdest on the previous accepted beat
            logic                       r_paused;        // tvalid dropped inside a packet
            logic [31:0]                w_pkt_beats_now; // beats INCLUDING this cycle's handshake

            // ---- stall-level state ----
            logic                       r_valid_pend;    // tvalid high and not accepted last cycle
            logic [31:0]                r_stall_cycles;  // consecutive tvalid & ~tready cycles
            logic [15:0]                r_stall_stamp;   // r_us when the stall began
            logic [15:0]                r_beat_stamp;    // r_us at the last accepted beat
            logic                       r_tmo_hs_fired;  // one Timeout/HANDSHAKE per stall
            logic                       r_tmo_pkt_fired; // one Timeout/PACKET per gap
            logic                       r_credit_fired;  // one Credit/BACKPRESSURE per stall
            logic [15:0]                w_stall_age, w_beat_age;

            // ---- candidate events, cone-gated (constant-pruned when a cone
            //      is not built) ----
            logic w_en_err, w_en_tmo, w_en_compl, w_en_credit, w_en_stream, w_en_chan;
            logic w_err_valid_drop, w_err_strb0;
            logic w_tmo_hs, w_tmo_pkt;
            logic w_compl;
            logic w_credit;
            logic w_chan_id, w_chan_dest;
            logic w_strm_start, w_strm_pause, w_strm_resume;

            // ---- the one packet this cycle can emit ----
            logic                       w_ev_fire;
            logic [3:0]                 w_ev_type;
            logic [7:0]                 w_ev_code;
            logic [63:0]                w_ev_data;
            logic [3:0]                 w_ev_n;          // candidates this cycle
            monitor_packet_t            w_ev_pkt;

            // ---- holding register toward the arbiter ----
            logic                       r_hold_valid;
            monitor_packet_t            r_hold_pkt;
            monbus_timestamp_t          r_hold_ts;
            logic                       w_pop, w_can_take;
            logic [15:0]                r_dropped;

            assign w_pkt_beats_now = r_in_pkt ? (r_pkt_beats + 32'd1) : 32'd1;
            assign w_stall_age     = r_us - r_stall_stamp;
            assign w_beat_age      = r_us - r_beat_stamp;

            assign w_en_err    = TAP_ENABLE_ERROR_LOGIC   & cfg_monitor_enable_w & cfg_error_enable_w;
            assign w_en_tmo    = TAP_ENABLE_TIMEOUT_LOGIC & cfg_monitor_enable_w & cfg_timeout_enable_w;
            assign w_en_compl  = TAP_ENABLE_COMPL_LOGIC   & cfg_monitor_enable_w & cfg_compl_enable_w;
            assign w_en_credit = TAP_ENABLE_CREDIT_LOGIC  & cfg_monitor_enable_w & cfg_credit_enable_w;
            assign w_en_stream = TAP_ENABLE_STREAM_LOGIC  & cfg_monitor_enable_w & cfg_stream_enable_w;
            assign w_en_chan   = TAP_ENABLE_CHANNEL_LOGIC & cfg_monitor_enable_w & cfg_channel_enable_w;

            // AXIS rule: once TVALID is asserted it must stay asserted until
            // the handshake. r_valid_pend remembers an unaccepted TVALID; a
            // low TVALID the cycle after is the violation.
            assign w_err_valid_drop = w_en_err & r_valid_pend & ~w_tv;
            // A beat that carries no payload byte. Legal AXIS (position
            // bytes) but on a DMA stream it is a bug; AXIS_MASK1.ERROR_MASK
            // drops it for a link where it is expected.
            assign w_err_strb0      = w_en_err & w_hs & (obs_axis_tstrb[gi] == '0);

            assign w_tmo_hs   = w_en_tmo & w_tv & ~w_tr & r_valid_pend
                              & (w_stall_age >= cfg_timeout_us_w) & ~r_tmo_hs_fired;
            assign w_tmo_pkt  = w_en_tmo & r_in_pkt & ~w_hs
                              & (w_beat_age >= cfg_timeout_us_w) & ~r_tmo_pkt_fired;

            assign w_compl    = w_en_compl & w_hs & w_tl;

            // MON_LATENCY re-purposed as the stall length, in CYCLES, above
            // which backpressure is reported. Once per stall.
            assign w_credit   = w_en_credit & w_tv & ~w_tr
                              & (r_stall_cycles >= cfg_latency_threshold_w) & ~r_credit_fired;

            // Against the PREVIOUS beat, not the packet's first: a change then
            // reports once, instead of on every remaining beat of the packet.
            assign w_chan_id   = w_en_chan & w_hs & r_in_pkt & (obs_axis_tid[gi]   != r_pkt_tid);
            assign w_chan_dest = w_en_chan & w_hs & r_in_pkt & (obs_axis_tdest[gi] != r_pkt_tdest);

            assign w_strm_start  = w_en_stream & w_hs & ~r_in_pkt;
            assign w_strm_pause  = w_en_stream & r_in_pkt & ~w_tv & ~r_paused;
            assign w_strm_resume = w_en_stream & r_paused & w_tv;

            // Priority when several fire in one cycle: Error > Timeout >
            // Completion > Credit > Channel > Stream. The losers are counted
            // in r_dropped, never silently discarded.
            always_comb begin
                w_ev_fire = 1'b0;
                w_ev_type = PktTypeError;
                w_ev_code = 8'h00;
                w_ev_data = 64'h0;
                w_ev_n    = 4'(  $countones({w_err_valid_drop, w_err_strb0, w_tmo_hs, w_tmo_pkt,
                                             w_compl, w_credit, w_chan_id, w_chan_dest,
                                             w_strm_start, w_strm_pause, w_strm_resume}));
                if (w_err_valid_drop) begin
                    w_ev_fire = 1'b1; w_ev_type = PktTypeError;
                    w_ev_code = 8'(AXIS_ERR_VALID_TIMING);
                    w_ev_data = {r_stall_cycles, r_pkt_count};
                end else if (w_err_strb0) begin
                    w_ev_fire = 1'b1; w_ev_type = PktTypeError;
                    w_ev_code = 8'(AXIS_ERR_STRB_INVALID);
                    w_ev_data = {w_pkt_beats_now, r_pkt_count};
                end else if (w_tmo_hs) begin
                    w_ev_fire = 1'b1; w_ev_type = PktTypeTimeout;
                    w_ev_code = 8'(AXIS_TIMEOUT_HANDSHAKE);
                    w_ev_data = {r_stall_cycles, w_stall_age, cfg_timeout_us_w};
                end else if (w_tmo_pkt) begin
                    w_ev_fire = 1'b1; w_ev_type = PktTypeTimeout;
                    w_ev_code = 8'(AXIS_TIMEOUT_PACKET);
                    w_ev_data = {r_pkt_beats, w_beat_age, cfg_timeout_us_w};
                end else if (w_compl) begin
                    w_ev_fire = 1'b1; w_ev_type = PktTypeCompletion;
                    w_ev_code = 8'(AXIS_COMPL_STREAM_END);
                    w_ev_data = {16'(obs_axis_tid[gi]), 16'(obs_axis_tdest[gi]), w_pkt_beats_now};
                end else if (w_credit) begin
                    w_ev_fire = 1'b1; w_ev_type = PktTypeCredit;
                    w_ev_code = 8'(AXIS_CREDIT_BACKPRESSURE);
                    w_ev_data = {r_stall_cycles, cfg_latency_threshold_w};
                end else if (w_chan_id) begin
                    w_ev_fire = 1'b1; w_ev_type = PktTypeChannel;
                    w_ev_code = 8'(AXIS_CHAN_ID_CHANGE);
                    w_ev_data = {16'(r_pkt_tid), 16'(obs_axis_tid[gi]), w_pkt_beats_now};
                end else if (w_chan_dest) begin
                    w_ev_fire = 1'b1; w_ev_type = PktTypeChannel;
                    w_ev_code = 8'(AXIS_CHAN_DEST_CHANGE);
                    w_ev_data = {16'(r_pkt_tdest), 16'(obs_axis_tdest[gi]), w_pkt_beats_now};
                end else if (w_strm_start) begin
                    w_ev_fire = 1'b1; w_ev_type = PktTypeStream;
                    w_ev_code = 8'(AXIS_STREAM_START);
                    w_ev_data = {16'(obs_axis_tid[gi]), 16'(obs_axis_tdest[gi]), r_pkt_count};
                end else if (w_strm_pause) begin
                    w_ev_fire = 1'b1; w_ev_type = PktTypeStream;
                    w_ev_code = 8'(AXIS_STREAM_PAUSE);
                    w_ev_data = {r_pkt_beats, r_pkt_count};
                end else if (w_strm_resume) begin
                    w_ev_fire = 1'b1; w_ev_type = PktTypeStream;
                    w_ev_code = 8'(AXIS_STREAM_RESUME);
                    w_ev_data = {r_pkt_beats, r_pkt_count};
                end
            end

            assign w_ev_pkt = create_monitor_packet(
                w_ev_type, PROTOCOL_AXIS, w_ev_code,
                9'(obs_axis_tid[gi]),                 // channel_id = tid
                UNIT_ID,
                {8'h00, 4'h2, 4'(gi)},                // agent: AXIS tap gi
                w_ev_data);

            // ---- state ----
            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    r_in_pkt        <= 1'b0;
                    r_pkt_beats     <= 32'd0;
                    r_pkt_count     <= 32'd0;
                    r_pkt_tid       <= '0;
                    r_pkt_tdest     <= '0;
                    r_paused        <= 1'b0;
                    r_valid_pend    <= 1'b0;
                    r_stall_cycles  <= 32'd0;
                    r_stall_stamp   <= 16'd0;
                    r_beat_stamp    <= 16'd0;
                    r_tmo_hs_fired  <= 1'b0;
                    r_tmo_pkt_fired <= 1'b0;
                    r_credit_fired  <= 1'b0;
                end else begin
                    // packet tracking
                    if (w_hs) begin
                        r_beat_stamp    <= r_us;
                        r_tmo_pkt_fired <= 1'b0;
                        r_pkt_tid       <= obs_axis_tid[gi];
                        r_pkt_tdest     <= obs_axis_tdest[gi];
                        if (w_tl) begin
                            r_in_pkt    <= 1'b0;
                            r_pkt_beats <= 32'd0;
                            r_pkt_count <= r_pkt_count + 32'd1;
                        end else begin
                            r_in_pkt    <= 1'b1;
                            r_pkt_beats <= w_pkt_beats_now;
                        end
                    end else if (w_tmo_pkt) begin
                        r_tmo_pkt_fired <= 1'b1;
                    end
                    // source bubble inside a packet
                    if (w_strm_pause)       r_paused <= 1'b1;
                    else if (w_tv || !r_in_pkt) r_paused <= 1'b0;
                    // stall tracking
                    if (w_tv && !w_tr) begin
                        r_valid_pend   <= 1'b1;
                        r_stall_cycles <= r_stall_cycles + 32'd1;
                        if (!r_valid_pend) r_stall_stamp <= r_us;
                        if (w_tmo_hs)      r_tmo_hs_fired <= 1'b1;
                        if (w_credit)      r_credit_fired <= 1'b1;
                    end else begin
                        r_valid_pend   <= 1'b0;
                        r_stall_cycles <= 32'd0;
                        r_tmo_hs_fired <= 1'b0;
                        r_credit_fired <= 1'b0;
                    end
                end
            )

            // ---- holding register: one packet in flight per tap ----
            // The arbiter's input skid absorbs a cycle or two of merge
            // backpressure; anything beyond that is a DROP, counted here.
            assign w_pop      = r_hold_valid & mon_ready[gi];
            assign w_can_take = ~r_hold_valid | w_pop;

            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn)) begin
                    r_hold_valid <= 1'b0;
                    r_hold_pkt   <= '0;
                    r_hold_ts    <= '0;
                    r_dropped    <= 16'd0;
                end else begin
                    if (w_ev_fire && w_can_take) begin
                        r_hold_valid <= 1'b1;
                        r_hold_pkt   <= w_ev_pkt;
                        r_hold_ts    <= mon_time_w;
                    end else if (w_pop) begin
                        r_hold_valid <= 1'b0;
                    end
                    if (cam_clear) begin
                        r_dropped <= 16'd0;
                    end else if (w_ev_fire) begin
                        // the winner is lost if the register is busy; every
                        // simultaneous loser is lost regardless
                        r_dropped <= r_dropped + 16'(w_ev_n) - (w_can_take ? 16'd1 : 16'd0);
                    end
                end
            )

            assign mon_valid[gi]  = r_hold_valid;
            assign mon_packet[gi] = r_hold_pkt;
            assign mon_ts[gi]     = r_hold_ts;
            assign tap_dropped[gi] = r_dropped;
            assign tap_packets[gi] = r_pkt_count;
            assign tap_lost[gi]    = (r_dropped != 16'd0);
        end
    endgenerate

    // =================================================================
    // Aggregate all monbus sources via monbus_arbiter
    // =================================================================
    logic                arb_monbus_valid;
    logic                arb_monbus_ready;
    monitor_packet_t     arb_monbus_packet;
    monbus_timestamp_t   arb_monbus_timestamp;

    generate
        for (gi = NUM_PORTS; gi < ARB_CLIENTS; gi = gi + 1) begin : gen_arb_pad
            assign mon_valid[gi]  = 1'b0;
            assign mon_packet[gi] = '0;
            assign mon_ts[gi]     = '0;
        end
    endgenerate

    monbus_arbiter #(
        .CLIENTS            (ARB_CLIENTS),
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
    // Output stage: the monbus group (one of two egress flavours)
    // =================================================================
    logic [15:0] w_comp_stat_tier1_a;
    logic [15:0] w_comp_stat_tier1_b;
    logic [15:0] w_comp_stat_tier1_c;
    logic [15:0] w_comp_stat_tier0;
    logic [15:0] w_comp_stat_cam_miss;
    logic [15:0] w_comp_stat_delta_ts_ovf;
    logic [15:0] w_comp_stat_event_data_ovf;
    logic [15:0] w_comp_stat_ed_delta_ovf;

    generate
    if (EGRESS_AXIL) begin : g_egress_axil
        assign m_axi_awid = '0; assign m_axi_awaddr = '0;
        assign m_axi_awlen = '0; assign m_axi_awsize = '0;
        assign m_axi_awburst = '0; assign m_axi_awlock = 1'b0;
        assign m_axi_awcache = '0; assign m_axi_awprot = '0;
        assign m_axi_awqos = '0; assign m_axi_awregion = '0;
        assign m_axi_awuser = '0; assign m_axi_awvalid = 1'b0;
        assign m_axi_wdata = '0; assign m_axi_wstrb = '0;
        assign m_axi_wlast = 1'b0; assign m_axi_wuser = '0;
        assign m_axi_wvalid = 1'b0; assign m_axi_bready = 1'b0;
        monbus_axil4_axil4_group #(
            .FIFO_DEPTH_ERR        (FIFO_DEPTH_ERR),
            .FIFO_DEPTH_WRITE      (FIFO_DEPTH_WRITE),
            .ADDR_WIDTH            (ADDR_WIDTH),
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

            .s_axil_arvalid   (s_axil_arvalid),
            .s_axil_arready   (s_axil_arready),
            .s_axil_araddr    (s_axil_araddr),
            .s_axil_arprot    (s_axil_arprot),
            .s_axil_rvalid    (s_axil_rvalid),
            .s_axil_rready    (s_axil_rready),
            .s_axil_rdata     (s_axil_rdata),
            .s_axil_rresp     (s_axil_rresp),

            .m_axil_awvalid   (m_axil_awvalid),
            .m_axil_awready   (m_axil_awready),
            .m_axil_awaddr    (m_axil_awaddr),
            .m_axil_awprot    (m_axil_awprot),
            .m_axil_wvalid    (m_axil_wvalid),
            .m_axil_wready    (m_axil_wready),
            .m_axil_wdata     (m_axil_wdata),
            .m_axil_wstrb     (m_axil_wstrb),
            .m_axil_bvalid    (m_axil_bvalid),
            .m_axil_bready    (m_axil_bready),
            .m_axil_bresp     (m_axil_bresp),

            .irq_out          (irq_out),

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

            // The set that does the work here: every packet is PROTOCOL_AXIS.
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

            .mon_compressor_stat_tier1_a        (w_comp_stat_tier1_a),
            .mon_compressor_stat_tier1_b        (w_comp_stat_tier1_b),
            .mon_compressor_stat_tier1_c        (w_comp_stat_tier1_c),
            .mon_compressor_stat_tier0          (w_comp_stat_tier0),
            .mon_compressor_stat_cam_miss       (w_comp_stat_cam_miss),
            .mon_compressor_stat_delta_ts_ovf   (w_comp_stat_delta_ts_ovf),
            .mon_compressor_stat_event_data_ovf (w_comp_stat_event_data_ovf),
            .mon_compressor_stat_ed_delta_ovf   (w_comp_stat_ed_delta_ovf)
        );
    end else begin : g_egress_axi4
        assign m_axil_awvalid = 1'b0; assign m_axil_awaddr = '0;
        assign m_axil_awprot = '0; assign m_axil_wvalid = 1'b0;
        assign m_axil_wdata = '0; assign m_axil_wstrb = '0;
        assign m_axil_bready = 1'b0;
        monbus_axil4_axi4_group #(
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

            .s_axil_arvalid   (s_axil_arvalid),
            .s_axil_arready   (s_axil_arready),
            .s_axil_araddr    (s_axil_araddr),
            .s_axil_arprot    (s_axil_arprot),
            .s_axil_rvalid    (s_axil_rvalid),
            .s_axil_rready    (s_axil_rready),
            .s_axil_rdata     (s_axil_rdata),
            .s_axil_rresp     (s_axil_rresp),

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

            .mon_compressor_stat_tier1_a        (w_comp_stat_tier1_a),
            .mon_compressor_stat_tier1_b        (w_comp_stat_tier1_b),
            .mon_compressor_stat_tier1_c        (w_comp_stat_tier1_c),
            .mon_compressor_stat_tier0          (w_comp_stat_tier0),
            .mon_compressor_stat_cam_miss       (w_comp_stat_cam_miss),
            .mon_compressor_stat_delta_ts_ovf   (w_comp_stat_delta_ts_ovf),
            .mon_compressor_stat_event_data_ovf (w_comp_stat_event_data_ovf),
            .mon_compressor_stat_ed_delta_ovf   (w_comp_stat_ed_delta_ovf)
        );
    end
    endgenerate

    // =================================================================
    // axis_bus_meter per port. Lives OUTSIDE the tap gate: it counts in
    // every build, ENABLE_MON_TAPS or not. tid's low bits pick the channel
    // bucket; tstrb gives exact payload bytes.
    // =================================================================
    genvar mi, ci;
    generate
        if (ENABLE_BUS_METER) begin : gen_meters
            for (mi = 0; mi < NUM_PORTS; mi = mi + 1) begin : gen_meter
                // the meter's per-channel outputs are 1-D unpacked; repack
                // them into the port-indexed packed arrays above
                logic [15:0] w_ch_prod  [NUM_CHANNELS];
                logic [15:0] w_ch_bp    [NUM_CHANNELS];
                logic [15:0] w_ch_starv [NUM_CHANNELS];
                logic [15:0] w_ch_idle  [NUM_CHANNELS];
                for (ci = 0; ci < NUM_CHANNELS; ci = ci + 1) begin : gen_ch_pack
                    assign meter_ch_productive[mi][ci]   = w_ch_prod[ci];
                    assign meter_ch_backpressure[mi][ci] = w_ch_bp[ci];
                    assign meter_ch_starvation[mi][ci]   = w_ch_starv[ci];
                    assign meter_ch_idle[mi][ci]         = w_ch_idle[ci];
                end
                axis_bus_meter #(
                    .DATA_WIDTH   (DATA_WIDTH),
                    .NUM_CHANNELS (NUM_CHANNELS),
                    .TID_WIDTH    (TIDW)
                ) u_meter (
                    .aclk               (aclk),
                    .aresetn            (aresetn),
                    .i_clear            (i_meter_clear),
                    .i_freeze           (i_meter_freeze),
                    .i_tvalid           (obs_axis_tvalid[mi]),
                    .i_tready           (obs_axis_tready[mi]),
                    .i_tlast            (obs_axis_tlast[mi]),
                    .i_tstrb            (obs_axis_tstrb[mi]),
                    .i_tid              (obs_axis_tid[mi][TIDW-1:0]),
                    .o_agg_productive   (meter_agg_productive[mi]),
                    .o_agg_backpressure (meter_agg_backpressure[mi]),
                    .o_agg_starvation   (meter_agg_starvation[mi]),
                    .o_agg_idle         (meter_agg_idle[mi]),
                    .o_agg_bytes        (meter_agg_bytes[mi]),
                    .o_agg_beats        (meter_agg_beats[mi]),
                    .o_agg_packets      (meter_agg_packets[mi]),
                    .o_ch_productive    (w_ch_prod),
                    .o_ch_backpressure  (w_ch_bp),
                    .o_ch_starvation    (w_ch_starv),
                    .o_ch_idle          (w_ch_idle),
                    .o_ch_overflow      (meter_ch_overflow[mi])
                );
            end
        end else begin : gen_no_meters
            for (mi = 0; mi < NUM_PORTS; mi = mi + 1) begin : gen_tieoff
                assign meter_agg_productive[mi]   = '0;
                assign meter_agg_backpressure[mi] = '0;
                assign meter_agg_starvation[mi]   = '0;
                assign meter_agg_idle[mi]         = '0;
                assign meter_agg_bytes[mi]        = '0;
                assign meter_agg_beats[mi]        = '0;
                assign meter_agg_packets[mi]      = '0;
                assign meter_ch_overflow[mi]      = '0;
                assign meter_ch_productive[mi]    = '0;
                assign meter_ch_backpressure[mi]  = '0;
                assign meter_ch_starvation[mi]    = '0;
                assign meter_ch_idle[mi]          = '0;
            end
        end
    endgenerate

    // =========================================================================
    // Telemetry readback mux (OBS_STAT_SEL -> OBS_STAT_DATA)
    //
    // METRIC 0..8 mean exactly what they mean on the AXI observers (cycle
    // buckets, aggregate then per channel). 9/10 (latency histogram) read 0:
    // a stream has no command-to-response latency to bin. 11..16 are the
    // AXIS-native counters this block adds. IS_WRITE must be 0 -- a stream
    // has one direction, and IS_WRITE=1 reads 0 so a host that copied the
    // AXI observer's write-side loop sees nothing rather than a duplicate.
    // =========================================================================
    logic [31:0] w_stat_data;
    always_comb begin
        automatic int unsigned ti = hwif.OBS.OBS_STAT_SEL.TAP.value;
        automatic int unsigned ci_sel = hwif.OBS.OBS_STAT_SEL.CHANNEL.value;
        automatic logic        iw = hwif.OBS.OBS_STAT_SEL.IS_WRITE.value;
        w_stat_data = 32'h0;
        if (!iw && ti < NUM_PORTS) begin
            case (hwif.OBS.OBS_STAT_SEL.METRIC.value)
                8'd0:  w_stat_data = meter_agg_productive[ti];
                8'd1:  w_stat_data = meter_agg_backpressure[ti];
                8'd2:  w_stat_data = meter_agg_starvation[ti];
                8'd3:  w_stat_data = meter_agg_idle[ti];
                8'd4:  if (ci_sel < NUM_CHANNELS) w_stat_data = 32'(meter_ch_productive[ti][ci_sel]);
                8'd5:  if (ci_sel < NUM_CHANNELS) w_stat_data = 32'(meter_ch_backpressure[ti][ci_sel]);
                8'd6:  if (ci_sel < NUM_CHANNELS) w_stat_data = 32'(meter_ch_starvation[ti][ci_sel]);
                8'd7:  if (ci_sel < NUM_CHANNELS) w_stat_data = 32'(meter_ch_idle[ti][ci_sel]);
                // {prod, bp, starv, idle} overflow stickies for the channel
                8'd8:  if (ci_sel < NUM_CHANNELS) w_stat_data = 32'(meter_ch_overflow[ti][ci_sel*4 +: 4]);
                // AXIS-native throughput (productive beats only)
                8'd11: w_stat_data = meter_agg_bytes[ti][31:0];
                8'd12: w_stat_data = meter_agg_bytes[ti][63:32];
                8'd13: w_stat_data = meter_agg_beats[ti];
                8'd14: w_stat_data = meter_agg_packets[ti];
                // tap honesty: events the monbus did not take, and packets
                // the tap itself closed (compare with 14 to prove the tap
                // and the meter saw the same stream)
                8'd15: w_stat_data = 32'(tap_dropped[ti]);
                8'd16: w_stat_data = tap_packets[ti];
                default: w_stat_data = 32'h0;
            endcase
        end
    end

    // Continuous per-field drive rather than a struct-wide assignment: the
    // generated hwif struct has no operator= in the simulator's C++ backend.
    // Every hw=w field in obs_regs is driven here, so nothing floats.
    assign hwif_i.OBS.OBS_STAT_DATA.VALUE.next        = w_stat_data;
    assign hwif_i.OBS.OBS_FIFO_STAT.ERR_COUNT.next    = 16'(err_fifo_count);
    assign hwif_i.OBS.OBS_FIFO_STAT.WRITE_COUNT.next  = 15'(write_fifo_count);
    assign hwif_i.OBS.OBS_FIFO_STAT.ANY_FULL.next     = err_fifo_full | write_fifo_full;
    // No latency histogram here, so nothing can lose a sample.
    assign hwif_i.OBS.OBS_STICKY.HIST_SAMPLE_LOST.next = 1'b0;
    assign hwif_i.OBS.OBS_STICKY.TAP_BLOCKED.next      = |tap_lost;
    assign hwif_i.OBS.OBS_COMP_STAT0.TIER1.next    = 16'(w_comp_stat_tier1_a);
    assign hwif_i.OBS.OBS_COMP_STAT0.TIER0.next    = 16'(w_comp_stat_tier0);
    assign hwif_i.OBS.OBS_COMP_STAT1.CAM_MISS.next = 16'(w_comp_stat_cam_miss);
    assign hwif_i.OBS.OBS_COMP_STAT1.OVERFLOW.next = 16'(w_comp_stat_event_data_ovf);

endmodule : axis4_intf_observer
