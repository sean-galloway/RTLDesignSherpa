// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: cxs_intf_observer
// Purpose: Inline CXS (Arm IHI 0079) link observer -- a passive tap for any
//          credited CXS link (N ports), with its own APB configuration. The
//          CXS sibling of axis4_intf_observer: same APB window, same obs_regs
//          map, same monbus egress, same telemetry readback, so one host
//          decoder and one regmap serve all four observers.
//
//   Drop it beside any CXS link -- a DMA's write-path (sink) or read-path
//   (source) link, a switch port. Every obs_cxs_* pin is an INPUT, the
//   receiver's CXSCRDGNT and CXSACTIVEACK included: this block watches the
//   wire and never drives it (vault/handbook/design/observers-do-not-drive.md).
//
//   Per port it builds:
//     - a cxs_link_snoop (rtl/amba/cxs): credits in flight, link state, and
//       the credit / link / per-stream framing checks, from the wires alone;
//     - a cxs_monitor_lite event TAP fed by the snoop, emitting PROTOCOL_CXS
//       monbus packets (Error / Timeout / Completion / Credit / Channel /
//       Stream; codes in rtl/amba/includes/ocelus_cxs_pkg.sv), merged by
//       monbus_arbiter into a monbus_axil4_{axi4,axil4}_group. The group
//       filters PROTOCOL_CXS through its AXIS slot, so AXIS_PKT_MASK /
//       AXIS_MASK1..3 govern these packets too;
//     - an axis_bus_meter with the cycle buckets mapped to CXS:
//         productive    a flit crossed the link
//         backpressure  RUN, no credit held: the receiver is throttling
//         starvation    RUN, a credit held, no flit: the transmitter has none
//         idle          the link is not in RUN
//       The channel bucket is the low CXSSRCID bits. Bytes are FLIT
//       granular (DATA_WIDTH/8 per flit): a passive tap cannot know how much
//       of a CXS flit is payload.
//
//   A passive tap cannot see whether the transmitter WANTS to send, so the
//   lite's credit-starved input is the snoop's run_no_credit (the receiver
//   throttling), not the endpoint's own starvation flag.
//
//   Runtime gating reuses MON_CTRL bit-for-bit with the other observers:
//     ERROR_EN[0] Error   TIMEOUT_EN[1] Timeout   COMPL_EN[2] Completion
//     THRESHOLD_EN[3] Credit   PERF_EN[4] Stream   DEBUG_EN[5] Channel
//   ADDR_CHECK_EN and the ADDR_RANGE* registers are inert.
//
//   Packet fields: agent_id = {8'h00, 4'h3, port[3:0]} (the AXIS observer
//   uses 4'h2), unit_id = UNIT_ID.
//
// Subsystem: amba
// Author: sean galloway
// Created: 2026-10-16

`timescale 1ns / 1ps

`include "reset_defs.svh"

module cxs_intf_observer
    import monitor_common_pkg::*;
    import cxs_pkg::*;
#(
    // ---------- Tap count ----------
    parameter int NUM_PORTS          = 1,

    // ---------- Observed CXS link (shared by all ports) ----------
    parameter int DATA_WIDTH            = 512,   // CXSDATAFLITWIDTH (data itself is not observed)
    parameter int CXS_MAX_PKT_PER_FLIT  = 2,
    parameter int CXS_START_ALIGN       = 16,
    parameter int CXS_SRCID_WIDTH       = 8,
    parameter int CXS_TGTID_WIDTH       = 4,
    parameter int CXS_MAX_CREDIT        = 15,    // the link's credit limit (beyond 63 is fine here)
    parameter int CXS_STREAM_PRCL_BITS  = 0,     // per-stream framing key (cxs_stream_key)
    parameter int CXS_STREAM_SRCID_BITS = 0,
    parameter int CXS_STREAM_TGTID_BITS = 0,
    parameter int CNTL_PW = port_w(cntl_width(CXS_MAX_PKT_PER_FLIT, DATA_WIDTH, CXS_START_ALIGN)),
    parameter int SRCID_PW = port_w(CXS_SRCID_WIDTH),
    parameter int TGTID_PW = port_w(CXS_TGTID_WIDTH),

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

    parameter logic [7:0] UNIT_ID       = 8'h12, // 8'h10 AXI, 8'h11 AXIS observers

    // ---------- Per-tap cone enables ----------
    // Each one is a class of PROTOCOL_CXS packet. Off = the compare logic
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
    parameter int NUM_CHANNELS          = 1,     // per-CXSSRCID buckets; 1 = aggregate only
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
    // OBSERVED CXS LINKS -- INPUTS ONLY, the receiver's wires included.
    // ================================================================
    input  logic [NUM_PORTS-1:0]                            obs_cxs_valid,
    input  logic [NUM_PORTS-1:0][CNTL_PW-1:0]               obs_cxs_cntl,
    input  logic [NUM_PORTS-1:0][2:0]                       obs_cxs_prcltype,
    input  logic [NUM_PORTS-1:0][SRCID_PW-1:0]              obs_cxs_srcid,
    input  logic [NUM_PORTS-1:0][TGTID_PW-1:0]              obs_cxs_tgtid,
    input  logic [NUM_PORTS-1:0]                            obs_cxs_crdgnt,
    input  logic [NUM_PORTS-1:0]                            obs_cxs_crdrtn,
    input  logic [NUM_PORTS-1:0]                            obs_cxs_activereq,
    input  logic [NUM_PORTS-1:0]                            obs_cxs_activeack,
    // Observed for completeness and so a link BFM binds unchanged; the tap
    // does not use them (as axis4_intf_observer ignores tdata/tuser): a
    // passive observer has no use for the payload, and the deactivation hint
    // shows up as the link state it causes.
    input  logic [NUM_PORTS-1:0][DATA_WIDTH-1:0]            obs_cxs_data,
    input  logic [NUM_PORTS-1:0]                            obs_cxs_deacthint,

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
    // axis_bus_meter window control, PER PORT (tie off if ENABLE_BUS_METER=0)
    // ================================================================
    // Per port, unlike the AXI observers' single pair: the ports of one CXS
    // observer routinely belong to different transfers -- a DMA's sink ingress
    // starts streaming at the kick, before its write side is busy, while the
    // source egress runs inside the write-side window -- so one window cannot
    // bracket both. The rapids harness keeps two windows for exactly this
    // reason; sharing one gave the ingress port prod=0 on the board.
    // Bit i is port i. One-cycle pulse clears port i's buckets and stickies
    // (held-high also works); freeze held high pauses them.
    input  logic [NUM_PORTS-1:0]                            i_meter_clear,
    input  logic [NUM_PORTS-1:0]                            i_meter_freeze
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
    // (IndexError in .value), and a stream BFM walks every top-level handle
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
    // sets. This observer emits PROTOCOL_CXS only, which the group filters
    // through its AXIS set; the AXI and CORE sets do
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

    // MON_CTRL, bit-for-bit with the AXI observers; the CXS class each bit
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
    // MON_CTRL[5:0], CXS class per the header table. N_ADDR_RANGES and
    // ID_SLICE read 0: neither exists for a stream. See the CAPS PACKING
    // note in obs_regs.rdl for why these are wide single fields.
    assign hwif_i.OBS.OBS_CAPS0.VALUE.next = {
        16'h0,                          // [31:16] reserved
        4'h0,                           // [15:12] N_ADDR_RANGES: none on a CXS link
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
        8'(ADDR_WIDTH), 8'(CXS_SRCID_WIDTH), 16'(DATA_WIDTH)
    };

    // =================================================================
    // Local parameters / derived sizes
    // =================================================================
    localparam int TIDW = (NUM_CHANNELS > 1) ? $clog2(NUM_CHANNELS) : 1;

    initial begin
        if (NUM_PORTS < 1)
            $error("cxs_intf_observer: NUM_PORTS must be >= 1");
        if (NUM_CHANNELS > 1 && CXS_SRCID_WIDTH < TIDW)
            $error("cxs_intf_observer: NUM_CHANNELS=%0d needs %0d CXSSRCID bits, CXS_SRCID_WIDTH=%0d",
                   NUM_CHANNELS, TIDW, CXS_SRCID_WIDTH);
    end

    // =================================================================
    // Free-running timestamp (driven out by monbus_group, stamped onto
    // every packet at emission)
    // =================================================================
    monbus_timestamp_t                              mon_time_w;

    // Per-source monbus streams + arbiter inputs (unpacked, as the arbiter
    // expects). CLIENTS=1 was once padded to two because the arbiter's grant
    // id sized as [-1:0] and Verilator refused it (ASCRANGE); the arbiter
    // widths are guarded now (utility-ip/misc TASK-005), so a single-port
    // observer builds the arbiter with exactly one client.
    logic                                           mon_valid    [NUM_PORTS];
    logic                                           mon_ready    [NUM_PORTS];
    monitor_packet_t                                mon_packet   [NUM_PORTS];
    monbus_timestamp_t                              mon_ts       [NUM_PORTS];

    // =================================================================
    // Per-port CXS link snoop + event tap
    // =================================================================
    localparam int SNOOP_CRW = $clog2(CXS_MAX_CREDIT + 2);
    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_obs_payload;
    assign unused_obs_payload = ^{obs_cxs_data, obs_cxs_deacthint};
    /* verilator lint_on UNUSEDSIGNAL */
    localparam int LITE_CRW  = $clog2(CXS_MAX_CREDIT + 1);
    logic [NUM_PORTS-1:0] snoop_run_no_credit;
    logic [NUM_PORTS-1:0] snoop_protocol_error;
    logic [SNOOP_CRW-1:0] snoop_credits [NUM_PORTS];

    genvar gi;
    generate
        for (gi = 0; gi < NUM_PORTS; gi = gi + 1) begin : gen_tap
            logic        w_tap_busy;
            logic [15:0] w_tap_error_count;
            logic [31:0] w_tap_flits;
            logic [1:0]  w_link_state;
            logic        w_in_packet;

            cxs_link_snoop #(
                .CXS_DATA_WIDTH        (DATA_WIDTH),
                .CXS_MAX_PKT_PER_FLIT  (CXS_MAX_PKT_PER_FLIT),
                .CXS_START_ALIGN       (CXS_START_ALIGN),
                .CXS_SRCID_WIDTH       (CXS_SRCID_WIDTH),
                .CXS_TGTID_WIDTH       (CXS_TGTID_WIDTH),
                .CXS_MAX_CREDIT        (CXS_MAX_CREDIT),
                .CXS_STREAM_PRCL_BITS  (CXS_STREAM_PRCL_BITS),
                .CXS_STREAM_SRCID_BITS (CXS_STREAM_SRCID_BITS),
                .CXS_STREAM_TGTID_BITS (CXS_STREAM_TGTID_BITS)
            ) u_snoop (
                .aclk           (aclk),
                .aresetn        (aresetn),
                .clear          (cam_clear),
                .cxs_valid      (obs_cxs_valid[gi]),
                .cxs_cntl       (obs_cxs_cntl[gi]),
                .cxs_prcltype   (obs_cxs_prcltype[gi]),
                .cxs_srcid      (obs_cxs_srcid[gi]),
                .cxs_tgtid      (obs_cxs_tgtid[gi]),
                .cxs_crdgnt     (obs_cxs_crdgnt[gi]),
                .cxs_crdrtn     (obs_cxs_crdrtn[gi]),
                .cxs_activereq  (obs_cxs_activereq[gi]),
                .cxs_activeack  (obs_cxs_activeack[gi]),
                .credits        (snoop_credits[gi]),
                .link_state     (w_link_state),
                .run_no_credit  (snoop_run_no_credit[gi]),
                .in_packet      (w_in_packet),
                .protocol_error (snoop_protocol_error[gi])
            );

            cxs_monitor_lite #(
                .UNIT_ID               (UNIT_ID),
                .AGENT_ID              ({8'h00, 4'h3, 4'(gi)}),   // agent: CXS tap gi
                .CXS_DATA_WIDTH        (DATA_WIDTH),
                .CXS_MAX_PKT_PER_FLIT  (CXS_MAX_PKT_PER_FLIT),
                .CXS_START_ALIGN       (CXS_START_ALIGN),
                .CXS_SRCID_WIDTH       (CXS_SRCID_WIDTH),
                .CXS_TGTID_WIDTH       (CXS_TGTID_WIDTH),
                .CXS_MAX_CREDIT        (CXS_MAX_CREDIT),
                .CXS_STREAM_PRCL_BITS  (CXS_STREAM_PRCL_BITS),
                .CXS_STREAM_SRCID_BITS (CXS_STREAM_SRCID_BITS),
                .CXS_STREAM_TGTID_BITS (CXS_STREAM_TGTID_BITS),
                .AGE_WIDTH             (16),
                .CFI_MIN_FREQ_MHZ      (CFI_MIN_FREQ_MHZ),
                .CFI_MAX_FREQ_MHZ      (CFI_MAX_FREQ_MHZ),
                .CFI_NUM_FREQ_ENTRIES  (CFI_ENTRIES),
                .CFI_FREQ_STRATEGY     (0),
                // 16 deep, as the AXIS observer (the egress err FIFO drains in
                // bursts; see axis4_intf_observer for the measured case)
                .OUT_DEPTH             (16)
            ) u_cxs_tap (
                .aclk                  (aclk),
                .aresetn               (aresetn),
                .clear                 (cam_clear),
                .i_mon_time            (mon_time_w),
                // a flit on the wire is accepted by definition: no READY
                .fub_valid             (obs_cxs_valid[gi]),
                .fub_ready             (1'b1),
                .fub_cntl              (obs_cxs_cntl[gi]),
                .fub_prcltype          (obs_cxs_prcltype[gi]),
                .fub_srcid             (obs_cxs_srcid[gi]),
                .fub_tgtid             (obs_cxs_tgtid[gi]),
                .link_state            (w_link_state),
                .credits               (LITE_CRW'(snoop_credits[gi])),
                .credit_starved        (snoop_run_no_credit[gi]),
                .protocol_error        (snoop_protocol_error[gi]),
                .parity_error          (1'b0),     // check signals are not observed
                .cfg_freq_sel          (cfg_freq_sel),
                .cfg_timeout_cnt       (cfg_timeout_us_w),
                .cfg_error_enable      (TAP_ENABLE_ERROR_LOGIC   & cfg_monitor_enable_w & cfg_error_enable_w),
                .cfg_timeout_enable    (TAP_ENABLE_TIMEOUT_LOGIC & cfg_monitor_enable_w & cfg_timeout_enable_w),
                .cfg_compl_enable      (TAP_ENABLE_COMPL_LOGIC   & cfg_monitor_enable_w & cfg_compl_enable_w),
                .cfg_credit_enable     (TAP_ENABLE_CREDIT_LOGIC  & cfg_monitor_enable_w & cfg_credit_enable_w),
                .cfg_channel_enable    (TAP_ENABLE_CHANNEL_LOGIC & cfg_monitor_enable_w & cfg_channel_enable_w),
                .cfg_stream_enable     (TAP_ENABLE_STREAM_LOGIC  & cfg_monitor_enable_w & cfg_stream_enable_w),
                .cfg_stall_threshold   (cfg_latency_threshold_w),
                .cfg_cxs_pkt_mask      (16'h0000),
                .monbus_valid          (mon_valid[gi]),
                .monbus_ready          (mon_ready[gi]),
                .monbus_packet         (mon_packet[gi]),
                .monbus_timestamp      (mon_ts[gi]),
                /* verilator lint_off UNUSEDSIGNAL */
                .busy                  (w_tap_busy),
                .error_count           (w_tap_error_count),
                .flit_count            (w_tap_flits),
                /* verilator lint_on UNUSEDSIGNAL */
                .packet_count          (tap_packets[gi]),
                .dropped_count         (tap_dropped[gi])
            );
            /* verilator lint_off UNUSEDSIGNAL */
            logic unused_in_packet;
            assign unused_in_packet = w_in_packet;
            /* verilator lint_on UNUSEDSIGNAL */

            // TAP_BLOCKED is sticky until cam_clear (the core's counter
            // clears itself when its drop report leaves).
            logic r_tap_lost;
            `ALWAYS_FF_RST(aclk, aresetn,
                if (`RST_ASSERTED(aresetn))        r_tap_lost <= 1'b0;
                else if (cam_clear)                r_tap_lost <= 1'b0;
                else if (tap_dropped[gi] != 16'd0) r_tap_lost <= 1'b1;
            )
            assign tap_lost[gi] = r_tap_lost;
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
        .CLIENTS            (NUM_PORTS),
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

            // The set that does the work here: PROTOCOL_CXS rides the AXIS slot.
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
    // axis_bus_meter per port, the buckets mapped to CXS (header). Lives
    // OUTSIDE the tap gate: it counts in every build. CXSSRCID's low bits pick
    // the channel bucket; bytes are flit granular.
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
                // productive = flit; backpressure = RUN with no credit (tvalid
                // up, tready down); starvation = RUN, credit, no flit (tready
                // up only); idle = not in RUN (both down)
                wire w_run     = obs_cxs_activereq[mi] && obs_cxs_activeack[mi];
                wire w_m_valid = obs_cxs_valid[mi] || (w_run && snoop_run_no_credit[mi]);
                wire w_m_ready = obs_cxs_valid[mi] || (w_run && !snoop_run_no_credit[mi]);
                wire w_m_last  = obs_cxs_valid[mi] &&
                                 (|obs_cxs_cntl[mi][end_lsb(CXS_MAX_PKT_PER_FLIT, DATA_WIDTH, CXS_START_ALIGN) +: CXS_MAX_PKT_PER_FLIT]);
                logic [TIDW-1:0] w_m_tid;
                assign w_m_tid = TIDW'(obs_cxs_srcid[mi]);
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
                    .i_clear            (i_meter_clear[mi]),
                    .i_freeze           (i_meter_freeze[mi]),
                    .i_tvalid           (w_m_valid),
                    .i_tready           (w_m_ready),
                    .i_tlast            (w_m_last),
                    .i_tstrb            ({(DATA_WIDTH/8){1'b1}}),
                    .i_tid              (w_m_tid),
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
    // buckets, aggregate then per channel; CXS mapping in the header). 9/10
    // (latency histogram) read 0. 11..16 are the stream counters the AXIS
    // observer adds (bytes are flit granular here); 17 is the snoop's
    // credits in flight and 18 its sticky protocol_error. IS_WRITE must be 0 -- a stream
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
                // CXS throughput: flits, flit-granular bytes, packets ended
                8'd11: w_stat_data = meter_agg_bytes[ti][31:0];
                8'd12: w_stat_data = meter_agg_bytes[ti][63:32];
                8'd13: w_stat_data = meter_agg_beats[ti];
                8'd14: w_stat_data = meter_agg_packets[ti];
                // tap honesty: events the monbus did not take, and packets
                // the tap itself closed (compare with 14 to prove the tap
                // and the meter saw the same stream)
                8'd15: w_stat_data = 32'(tap_dropped[ti]);
                8'd16: w_stat_data = tap_packets[ti];
                8'd17: w_stat_data = 32'(snoop_credits[ti]);
                8'd18: w_stat_data = 32'(snoop_protocol_error[ti]);
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

endmodule : cxs_intf_observer
