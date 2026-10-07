// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2025 sean galloway
//
// Module: harness_csr
// Purpose: Control/status registers for the STREAM characterization harness.
//
// Host-visible AXI4-Lite slave with a small set of registers for driving
// and observing the test flow. Separate from the STREAM config registers
// (which live in the STREAM APB space).
//
// Every external AXI4-Lite channel is isolated with a gaxi_skid_buffer
// for timing closure.
//
// Register map (byte offsets from S1 base = 0x0001_0000):
//
//   0x00  CTRL            RW  Control bits
//                              [0]   start           (self-clearing pulse)
//                              [1]   clear_stats     (self-clearing pulse)
//                              [2]   freeze_trace    (latch; stops debug_sram writes)
//                              [3]   soft_reset      (self-clearing pulse)
//                              [4]   cam_clear       (self-clearing pulse; sync-clears
//                                                    all stream CAMs: monbus compressor
//                                                    template CAM + stats, and the
//                                                    monitor transaction CAMs)
//
//   0x04  STATUS          R   Status bits
//                              [0]   stream_irq      (latched)
//                              [1]   any_error       (sticky; cleared by clear_stats)
//                              [2]   trace_overflow  (sticky)
//                              [3]   clear_busy      (1 while debug_sram wipe runs)
//                                                    Software polls this after
//                                                    writing CTRL.clear_stats and
//                                                    must wait for 0 before
//                                                    starting the next capture.
//
//   0x08  DBG_WR_PTR      R   Number of 32-bit words written to debug_sram
//   0x0C  DBG_OVERFLOW    R   Sticky overflow flag as a full word
//   0x10  CRC_RD_EXPECTED R   Pseudo-random source CRC (from pattern gen)
//   0x14  CRC_WR_EXPECTED R   Expected CRC at write sink
//   0x18  CRC_WR_COMPUTED R   Actual CRC computed by write sink
//   0x1C  CRC_MATCH       R   [0] = CRC match, [1] = CRC valid
//   0x20  SCRATCH         RW  Free scratchpad for host bring-up / ping test
//   0x24  BUILD_ID        R   Parameter-driven build ID (for host handshake)
//
//   BUILD_ID says only WHICH HARNESS this is, not which build of it. The
//   monitor flow ships TWO bitstreams (all-except-error / error-only) and a
//   host that guesses wrong reports a missing cone as a missed fault.
//   0x1D0  BUILD_VERSION  R  functional build number
//   0x1D4  BUILD_CONFIG   R  [4:0] num_channels
//                            [5]   error_flavor (1 = error-cone-only build)
//                            [6]   use_axi_monitors
//                            [7]   gen_mon (per-channel CORE emitters built)
//                            [15:8] data_width_bytes (DATA_WIDTH/8)
//   The host derives beats and throughput from the datapath width. It used to
//   hard-code 16 B in two files with nothing tying that to the build, so a
//   width change would silently scale every beat count and MB/s figure by the
//   ratio -- and a wrong throughput number looks exactly like a real one.
//   Reported here so the host reads the width instead of assuming it.
//   0x1D8  BUILD_N_PROFILE R  tally legal-set size
//
//   0x28  TIMER_CTRL      W   [0] = clear pulse (resets done/cycles/pass)
//                              Reads as 0.
//   0x2C  TIMER_STATUS    R   [0] = done   (latched: stop trigger fired)
//                              [1] = running (between start and stop)
//                              [2] = pass   (CRC matched at stop edge)
//   0x30  TIMER_CYCLES_LO R   Low 32 b of 64 b cycle counter (10 ns / cycle)
//   0x34  TIMER_CYCLES_HI R   High 32 b
//   0x38  TIMER_EXPECTED_BEATS RW  Expected sink-side beat count (host programs
//                              this before the kick; timer stops when the
//                              sink slave's write_beat_count >= this value).
//                              Write 0 to disable beat-based stop.
//
//   0x3C  RESP_DELAY      RW  Per-beat hold time injected into the response
//                              channels by the axi_response_delay blocks in
//                              the harness. Used for bandwidth-vs-latency
//                              characterization studies (host can sweep this
//                              between runs without rebuilding the bitstream).
//                              [15:0]  rd_delay_cycles  (0 = bypass on R)
//                              [31:16] wr_delay_cycles  (0 = bypass on B)
//
//   Per-engine cycle stamps captured during the timed window. All four are
//   sampled from the same 64-bit timer_cycles base, so subtraction across
//   first/last gives a steady-state engine throughput uncontaminated by
//   descriptor-fetch or last-burst-tail overhead. Cleared by TIMER_CTRL.
//
//   0x40  TIMER_R_FIRST_LO  R  Cycle of first R beat (low 32 bits)
//   0x44  TIMER_R_FIRST_HI  R  Cycle of first R beat (high 32 bits)
//   0x48  TIMER_R_LAST_LO   R  Cycle of last  R beat (low 32 bits)
//   0x4C  TIMER_R_LAST_HI   R  Cycle of last  R beat (high 32 bits)
//   0x50  TIMER_W_FIRST_LO  R  Cycle of first W beat (low 32 bits)
//   0x54  TIMER_W_FIRST_HI  R  Cycle of first W beat (high 32 bits)
//   0x58  TIMER_W_LAST_LO   R  Cycle of last  W beat (low 32 bits)
//   0x5C  TIMER_W_LAST_HI   R  Cycle of last  W beat (high 32 bits)
//
//   Per-channel CRC verification (multi-channel pass/fail visibility).
//   The slave-side LFSR/CRC keeps independent state per channel, demuxed
//   off s_axi_arid / s_axi_wuser low bits. A run is "pass" only if every
//   channel that produced beats also matched.
//
//   0x60 + 4*ch:  CRC_RD_PER_CH[ch]   R  Per-channel read CRC value
//                                        (NUM_CHANNELS slots, ch 0..NC-1)
//   0x80 + 4*ch:  CRC_WR_PER_CH[ch]   R  Per-channel write CRC value
//   0xA0          CRC_VALID_MASK      R  [NC-1:0] = per-channel valid bits
//                                        (a channel is "valid" once both
//                                         its read and write CRCs have
//                                         seen at least one beat each)
//   0xA4          CRC_MATCH_MASK      R  [NC-1:0] = per-channel match bits
//                                        (read CRC == write CRC AND valid)
//
//   (Kick-burst fast path REMOVED: the launch now lives inside STREAM as
//    CHx_CTRL_{LOW,HIGH} + KICK_ENABLE, so the harness no longer needs a
//    CSR shortcut around the per-channel APB kick.)
//
//   0xD4  DESC_SRAM_AR_HS  R  AXIL AR handshake at the desc_ram SRAM port
//                              (s2_arvalid && s2_arready). Localizes the
//                              wedge to bridge-vs-SRAM: if SRAM_AR_HS counts
//                              up but R_HS doesn't, the SRAM is stuck on
//                              read; if DESC_AR_HS (STREAM 256b) increments
//                              but SRAM_AR_HS doesn't, the bridge converter
//                              (256→64 or AXI4→AXIL) is stalled internally.
//   0xD8  DESC_SRAM_R_HS   R  AXIL R handshake at the SRAM port
//                              (s2_rvalid && s2_rready).
//   0xDC                   --  Reserved (read as 0)
//
//   desc_ram observation counters. Track AXI4 (STREAM ↔ desc_ram) and
//   AXIL (host ↔ desc_ram) valid/ready activity. All 32-bit, saturate at
//   2^32-1, clear on CTRL.clear_stats. Lets the host answer "is the SRAM
//   responding or is STREAM not accepting?" without touching the trace SRAM.
//
//   0xE0  DESC_AR_HS       R  AXI4 AR accepted at STREAM 256b master
//                              (desc_arvalid && desc_arready)
//   0xE4  DESC_AR_STALL    R  AXI4 AR stalled at STREAM 256b master
//                              (desc_arvalid && !desc_arready)
//                              -- if nonzero, the bridge front-end stalled
//                                 on the STREAM-side AR.
//   0xE8  DESC_R_HS        R  AXI4 R delivered at STREAM 256b master
//                              (desc_rvalid && desc_rready)
//   0xEC  DESC_R_STALL     R  AXI4 R stalled (desc_rvalid && !desc_rready)
//                              -- if nonzero, STREAM failed to accept R
//   0xF0  DESC_AW_HS       R  AXIL AW handshake at SRAM port (s2_aw*)
//   0xF4  DESC_W_HS        R  AXIL W handshake at SRAM port (s2_w*)
//   0xF8  DESC_B_HS        R  AXIL B handshake at SRAM port (s2_b*)
//   0xFC  DESC_VR_LIVE     R  Live single-cycle snapshot of all live
//                              valid/ready pairs (see harness for layout).
//
//   AXI bus meter readback. Two meters live in this CSR space:
//     R-meter at 0x100  -- watches the read engine's R bus
//     W-meter at 0x180  -- watches the write engine's W bus
//   Both share the same layout, base + offset:
//
//   +0x00  AGG_PRODUCTIVE     R  Cycles with (valid && ready)
//   +0x04  AGG_BACKPRESSURE   R  Cycles with (valid && !ready)
//   +0x08  AGG_STARVATION     R  Cycles with (!valid && ready)
//   +0x0C  AGG_IDLE           R  Cycles with (!valid && !ready)
//   +0x10  CH_OVERFLOW        R  Per-(channel, bucket) sticky overflow mask.
//                                Bit layout (NUM_CHANNELS=8):
//                                [3:0]    = ch0 {prod, bp, starv, idle}
//                                [7:4]    = ch1 ...
//                                [31:28]  = ch7 ...
//                                If any bit is set, the corresponding 16-bit
//                                per-channel counter wrapped past 65535
//                                cycles (~655 us at 100 MHz). Discard that
//                                channel's per-bucket value for the run.
//   +0x20+4*ch  CH[ch]_PROD_BP    R  {bp[15:0], productive[15:0]}
//   +0x40+4*ch  CH[ch]_STARV_IDLE R  {idle[15:0], starvation[15:0]}
//
//   All bus-meter counters clear synchronously on CTRL.clear_stats, in lock
//   step with debug_sram and the CRC state. No separate clear-bit needed.
//
//   MonBus compressor statistics (R, from stream_top_ch8; 0 unless the
//   build sets USE_MON_COMPRESSION=1):
//     0x1E0 COMP_TIER1_A      0x1E4 COMP_TIER1_B    0x1E8 COMP_TIER1_C
//     0x1EC COMP_TIER0        0x1F0 COMP_CAM_MISS   0x1F4 COMP_DELTA_TS_OVF
//     0x1F8 COMP_EVENT_DATA_OVF                     0x1FC COMP_ED_DELTA_OVF
//   Compression ratio ~= records_in / (tier1_a+tier1_b+tier1_c+tier0).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module harness_csr #(
    parameter int AW = 32,
    parameter int DW = 32,
    parameter int NUM_CHANNELS = 1,
    parameter logic [31:0] BUILD_ID = 32'h5354_5243,  // "STRC"
    // BUILD_ID names the harness FAMILY and nothing more. Which BUILD of it
    // is on the board had to be supplied out of band -- by remembering which
    // .bit was programmed last. A wrong assumption did not announce itself:
    // it came out as "the monitor did not catch the fault", when the truth
    // was that the cone is not in this bitstream. These are driven from the
    // harness's OWN parameters, so what the host reads is what the bitstream
    // was compiled with and cannot drift from it.
    parameter int BUILD_VERSION      = 1,      // bump per functional build
    parameter int BUILD_ERROR_FLAVOR = 0,      // 1 = error cone compiled in
    // 1 = timeout/compl/threshold/perf/debug cones compiled in. Separate
    // from ERROR_FLAVOR because a union build has BOTH set, which a single
    // flavour bit cannot express -- and the host decides what to exercise
    // from these, so an under-reported build silently skips coverage.
    parameter int BUILD_MAIN_CONES   = 1,
    parameter int BUILD_NUM_CHANNELS = 4,
    parameter int BUILD_N_PROFILE    = 64,
    // Harness clock in Hz. The host converts cycle counts to bandwidth with
    // this; when it was not published the host had to ASSUME a frequency,
    // and the 100 MHz assumption silently inflated every GB/s figure by 11%
    // once the harness moved to 90 MHz. Publishing it makes the conversion
    // a fact the board states rather than a constant the host guesses.
    parameter int BUILD_CLK_HZ       = 100_000_000,
    parameter int BUILD_USE_MONITORS = 1,
    parameter int BUILD_GEN_MON      = 0,      // per-channel CORE emitters built?
    // Datapath width in BYTES. 8 bits holds up to 255 B (2040 b), covering
    // 128 b (16 B, current) through the IP's native 512 b (64 B).
    parameter int BUILD_DATA_WIDTH_B = 16,

    parameter int SKID_DEPTH_AW = 2,
    parameter int SKID_DEPTH_W  = 2,
    parameter int SKID_DEPTH_B  = 2,
    parameter int SKID_DEPTH_AR = 2,
    parameter int SKID_DEPTH_R  = 2
) (
    input  logic            aclk,
    input  logic            aresetn,

    // =====================================================================
    // AXI4-Lite slave
    // =====================================================================
    input  logic [AW-1:0]   s_awaddr,
    input  logic [2:0]      s_awprot,
    input  logic            s_awvalid,
    output logic            s_awready,

    input  logic [DW-1:0]   s_wdata,
    input  logic [DW/8-1:0] s_wstrb,
    input  logic            s_wvalid,
    output logic            s_wready,

    output logic [1:0]      s_bresp,
    output logic            s_bvalid,
    input  logic            s_bready,

    input  logic [AW-1:0]   s_araddr,
    input  logic [2:0]      s_arprot,
    input  logic            s_arvalid,
    output logic            s_arready,

    output logic [DW-1:0]   s_rdata,
    output logic [1:0]      s_rresp,
    output logic            s_rvalid,
    input  logic            s_rready,

    // =====================================================================
    // Control outputs (to harness)
    // =====================================================================
    output logic            o_start_pulse,
    output logic            o_clear_stats_pulse,
    output logic            o_freeze_trace,
    output logic            o_soft_reset_pulse,
    output logic            o_cam_clear_pulse,   // CTRL[4]: sync-clear all stream CAMs

    // =====================================================================
    // Status/statistics inputs (from harness)
    // =====================================================================
    input  logic            i_stream_irq,
    input  logic            i_any_error,
    input  logic [31:0]     i_dbg_wr_ptr,
    input  logic            i_dbg_overflow,
    input  logic            i_dbg_clear_busy,

    // MonBus compressor statistics (from stream_top_ch8). Live only when
    // USE_MON_COMPRESSION=1; read-only at 0x100..0x11C.
    input  logic [31:0]     i_mon_comp_tier1_a,
    input  logic [31:0]     i_mon_comp_tier1_b,
    input  logic [31:0]     i_mon_comp_tier1_c,
    input  logic [31:0]     i_mon_comp_tier0,
    input  logic [31:0]     i_mon_comp_cam_miss,
    input  logic [31:0]     i_mon_comp_delta_ts_ovf,
    input  logic [31:0]     i_mon_comp_event_data_ovf,
    input  logic [31:0]     i_mon_comp_ed_delta_ovf,

    // RFC Stage E: external axi4_intf_master_observer perf readback (revives the
    // 0x100-0x128 range the retired harness axi_bus_meter used). Aggregate
    // R/W bus-meter buckets + an indexed latency-histogram readout, sourced
    // from the standalone observer dropped inline on STREAM's rd/wr AXI. Used
    // for observer-vs-in-core equivalence and the eventual USE_AXI_MONITORS=0
    // path where the observer is the sole perf source.
    // Indexed histogram readout. o_obs_hist_sel = {bin[5:2], metric[1], bus[0]}
    // (bus 0=read/1=write; metric 0=AR->firstR or AW->B, 1=AR->RLAST). The
    // harness drives the observer's i_hist_metric/i_hist_bin from this and
    // muxes the selected count/total back into i_obs_hist_data/total.
    // o_obs_hist_sel RETIRED -- drove nothing; see 0x120 note below.

    input  logic [31:0]     i_crc_rd_expected,
    input  logic [31:0]     i_crc_wr_expected,
    input  logic [31:0]     i_crc_wr_computed,
    input  logic            i_crc_valid,
    input  logic            i_crc_match,

    // Per-channel CRC arrays + bitmasks (multi-channel verification).
    input  logic [NUM_CHANNELS-1:0][31:0] i_crc_rd_per_ch,
    input  logic [NUM_CHANNELS-1:0][31:0] i_crc_wr_per_ch,
    input  logic [NUM_CHANNELS-1:0]       i_crc_valid_mask,
    input  logic [NUM_CHANNELS-1:0]       i_crc_match_mask,

    // =====================================================================
    // Characterization timer interface
    // =====================================================================
    output logic            o_timer_clear_pulse,
    output logic [31:0]     o_timer_expected_beats,
    input  logic            i_timer_done,
    input  logic            i_timer_running,
    input  logic            i_timer_pass,
    input  logic [63:0]     i_timer_cycles,

    // Per-engine first/last beat cycle stamps (sampled from i_timer_cycles).
    // Subtract first from last to get pure engine throughput windows.
    input  logic [63:0]     i_timer_r_first,
    input  logic [63:0]     i_timer_r_last,
    input  logic [63:0]     i_timer_w_first,
    input  logic [63:0]     i_timer_w_last,

    // =====================================================================
    // Response-delay knobs (driven from RESP_DELAY register @ 0x3C)
    // =====================================================================
    output logic [15:0]     o_rd_resp_delay_cyc,
    output logic [15:0]     o_wr_resp_delay_cyc,

    // =====================================================================

    // =====================================================================
    // desc_ram observation counters (read at 0xD4/0xD8 + 0xE0-0xFC,
    // cleared by CTRL.clear_stats inside the harness). All free-running
    // 32-bit saturating counters; per-bit live snapshot also exposed.
    // =====================================================================
    input  logic [31:0]                   i_desc_sram_ar_hs,
    input  logic [31:0]                   i_desc_sram_r_hs,
    input  logic [31:0]                   i_desc_ar_hs,
    input  logic [31:0]                   i_desc_ar_stall,
    input  logic [31:0]                   i_desc_r_hs,
    input  logic [31:0]                   i_desc_r_stall,
    input  logic [31:0]                   i_desc_aw_hs,
    input  logic [31:0]                   i_desc_w_hs,
    input  logic [31:0]                   i_desc_b_hs,
    input  logic [15:0]                   i_desc_vr_live
);

    localparam int AW_PKT_W = AW + 3;
    localparam int W_PKT_W  = DW + (DW/8);
    localparam int B_PKT_W  = 2;
    localparam int AR_PKT_W = AW + 3;
    localparam int R_PKT_W  = DW + 2;

    // =========================================================================
    // AW / W / B skid buffers
    // =========================================================================
    logic                 int_awvalid, int_awready;
    logic [AW_PKT_W-1:0]  int_aw_pkt;
    logic [AW-1:0]        int_awaddr;
    logic [2:0]           int_awprot;
    assign {int_awaddr, int_awprot} = int_aw_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_AW),
        .DATA_WIDTH(AW_PKT_W)
    ) u_skid_aw (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(s_awvalid), .wr_ready(s_awready),
        .wr_data ({s_awaddr, s_awprot}),
        .count   (),
        .rd_valid(int_awvalid), .rd_ready(int_awready),
        .rd_count(), .rd_data(int_aw_pkt)
    );

    logic                int_wvalid, int_wready;
    logic [W_PKT_W-1:0]  int_w_pkt;
    logic [DW-1:0]       int_wdata;
    logic [DW/8-1:0]     int_wstrb;
    assign {int_wdata, int_wstrb} = int_w_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_W),
        .DATA_WIDTH(W_PKT_W)
    ) u_skid_w (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(s_wvalid), .wr_ready(s_wready),
        .wr_data ({s_wdata, s_wstrb}),
        .count   (),
        .rd_valid(int_wvalid), .rd_ready(int_wready),
        .rd_count(), .rd_data(int_w_pkt)
    );

    logic                int_bvalid, int_bready;
    logic [B_PKT_W-1:0]  int_b_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_B),
        .DATA_WIDTH(B_PKT_W)
    ) u_skid_b (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(int_bvalid), .wr_ready(int_bready),
        .wr_data (int_b_pkt),
        .count   (),
        .rd_valid(s_bvalid), .rd_ready(s_bready),
        .rd_count(), .rd_data(s_bresp)
    );

    // =========================================================================
    // AR / R skid buffers
    // =========================================================================
    logic                 int_arvalid, int_arready;
    logic [AR_PKT_W-1:0]  int_ar_pkt;
    logic [AW-1:0]        int_araddr;
    logic [2:0]           int_arprot;
    assign {int_araddr, int_arprot} = int_ar_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_AR),
        .DATA_WIDTH(AR_PKT_W)
    ) u_skid_ar (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(s_arvalid), .wr_ready(s_arready),
        .wr_data ({s_araddr, s_arprot}),
        .count   (),
        .rd_valid(int_arvalid), .rd_ready(int_arready),
        .rd_count(), .rd_data(int_ar_pkt)
    );

    logic                int_rvalid, int_rready;
    logic [R_PKT_W-1:0]  int_r_pkt;

    gaxi_skid_buffer #(
        .DEPTH     (SKID_DEPTH_R),
        .DATA_WIDTH(R_PKT_W)
    ) u_skid_r (
        .axi_aclk(aclk), .axi_aresetn(aresetn),
        .wr_valid(int_rvalid), .wr_ready(int_rready),
        .wr_data (int_r_pkt),
        .count   (),
        .rd_valid(s_rvalid), .rd_ready(s_rready),
        .rd_count(), .rd_data({s_rdata, s_rresp})
    );

    // =========================================================================
    // Register storage
    // =========================================================================
    // Register storage is the GENERATED block below; only the two sticky bits
    // are kept here, because they are set by hardware events and cleared by a
    // CTRL pulse rather than written by software.
    logic r_irq_latched;
    logic r_any_error_sticky;

    // Everything software writes now comes out of harness_csr_regs' hwif_out.
    // The RDL's singlepulse fields land exactly on the old *_pulse signals --
    // which is the check that the RDL was already an accurate model of this
    // hardware, not a parallel description of it.
    logic        r_freeze_trace;
    logic [31:0] r_scratch;
    logic        r_start_pulse;
    logic        r_clear_stats_pulse;
    logic        r_soft_reset_pulse;
    logic        r_cam_clear_pulse;
    logic        r_timer_clear_pulse;
    logic [31:0] r_timer_expected_beats;
    logic [15:0] r_rd_resp_delay_cyc;
    logic [15:0] r_wr_resp_delay_cyc;

    harness_csr_regs_top_pkg::harness_csr_regs_top__in_t  w_hwif_in;
    harness_csr_regs_top_pkg::harness_csr_regs_top__out_t w_hwif_out;

    assign r_freeze_trace         = w_hwif_out.CTRL.FREEZE_TRACE.value;
    assign r_start_pulse          = w_hwif_out.CTRL.START.value;
    assign r_clear_stats_pulse    = w_hwif_out.CTRL.CLEAR_STATS.value;
    assign r_soft_reset_pulse     = w_hwif_out.CTRL.SOFT_RESET.value;
    assign r_cam_clear_pulse      = w_hwif_out.CTRL.CAM_CLEAR.value;
    assign r_scratch              = w_hwif_out.SCRATCH.VALUE.value;
    assign r_timer_clear_pulse    = w_hwif_out.TIMER_CTRL.CLEAR.value;
    assign r_timer_expected_beats = w_hwif_out.TIMER_EXPECTED_BEATS.VALUE.value;
    assign r_rd_resp_delay_cyc    = w_hwif_out.RESP_DELAY.RD_DELAY.value;
    assign r_wr_resp_delay_cyc    = w_hwif_out.RESP_DELAY.WR_DELAY.value;

    // Single cpuif port, two independent AXI channels: writes win and a read
    // simply waits, which costs nothing because the host never pipelines the
    // two against each other.
    logic        w_cpuif_req;
    logic        w_cpuif_req_is_wr;
    logic [8:0]  w_cpuif_addr;
    logic [31:0] w_cpuif_wr_data;
    logic        w_cpuif_rd_ack;
    logic [31:0] w_cpuif_rd_data;
    logic        w_wr_req;
    logic        w_rd_req;

    assign w_cpuif_req       = w_wr_req | w_rd_req;
    assign w_cpuif_req_is_wr = w_wr_req;
    assign w_cpuif_addr      = w_wr_req ? int_awaddr[8:0] : int_araddr[8:0];
    assign w_cpuif_wr_data   = int_wdata;

    harness_csr_regs_top u_regs (
        .clk                  (aclk),
        .rst                  (~aresetn),
        .s_cpuif_req          (w_cpuif_req),
        .s_cpuif_req_is_wr    (w_cpuif_req_is_wr),
        .s_cpuif_addr         (w_cpuif_addr),
        .s_cpuif_wr_data      (w_cpuif_wr_data),
        .s_cpuif_wr_biten     ({32{1'b1}}),
        .s_cpuif_req_stall_wr (),
        .s_cpuif_req_stall_rd (),
        .s_cpuif_rd_ack       (w_cpuif_rd_ack),
        .s_cpuif_rd_err       (),
        .s_cpuif_rd_data      (w_cpuif_rd_data),
        .s_cpuif_wr_ack       (),
        .s_cpuif_wr_err       (),
        .hwif_in              (w_hwif_in),
        .hwif_out             (w_hwif_out)
    );


    // Kick-burst storage: per-channel address shadow + pulse-per-cycle

    // Fixed-shape views over per-channel CRC arrays so the read-decode
    // case below can index them with literals regardless of NUM_CHANNELS.
    // Channels >= NUM_CHANNELS read as 0.
    localparam int CRC_VIEW_NC = 8;
    logic [31:0] crc_rd_view [CRC_VIEW_NC];
    logic [31:0] crc_wr_view [CRC_VIEW_NC];
    genvar gi;
    generate
        for (gi = 0; gi < CRC_VIEW_NC; gi++) begin : g_crc_view
            if (gi < NUM_CHANNELS) begin : g_real
                assign crc_rd_view[gi] = i_crc_rd_per_ch[gi];
                assign crc_wr_view[gi] = i_crc_wr_per_ch[gi];
            end else begin : g_pad
                assign crc_rd_view[gi] = 32'h0;
                assign crc_wr_view[gi] = 32'h0;
            end
        end
    endgenerate

    // Likewise for the per-channel valid/match bitmasks, padded to 32 bits.
    logic [31:0] w_crc_valid_word;
    logic [31:0] w_crc_match_word;
    always_comb begin
        w_crc_valid_word = '0;
        w_crc_match_word = '0;
        for (int ci = 0; ci < NUM_CHANNELS; ci++) begin
            w_crc_valid_word[ci] = i_crc_valid_mask[ci];
            w_crc_match_word[ci] = i_crc_match_mask[ci];
        end
    end

    // ---- hwif_in: hardware -> register block -------------------------------
    // GENERATED PAIRING, not hand-typed. The RDL and the retired hand-written
    // read decode agreed on all 64 offsets exactly, so every read-only
    // register's source is taken from the decode it replaces.
    assign w_hwif_in.STATUS.STREAM_IRQ.next = r_irq_latched;
    assign w_hwif_in.STATUS.ANY_ERROR.next = r_any_error_sticky;
    assign w_hwif_in.STATUS.TRACE_OVERFLOW.next = i_dbg_overflow;
    assign w_hwif_in.STATUS.CLEAR_BUSY.next = i_dbg_clear_busy;
    assign w_hwif_in.DBG_WR_PTR.VALUE.next = i_dbg_wr_ptr;
    assign w_hwif_in.DBG_OVERFLOW.VALUE.next = {31'd0, i_dbg_overflow};
    assign w_hwif_in.CRC_RD_EXPECTED.VALUE.next = i_crc_rd_expected;
    assign w_hwif_in.CRC_WR_EXPECTED.VALUE.next = i_crc_wr_expected;
    assign w_hwif_in.CRC_WR_COMPUTED.VALUE.next = i_crc_wr_computed;
    assign w_hwif_in.CRC_MATCH.MATCH.next = i_crc_match;
    assign w_hwif_in.CRC_MATCH.VALID.next = i_crc_valid;
    assign w_hwif_in.BUILD_ID.VALUE.next = BUILD_ID;
    assign w_hwif_in.TIMER_STATUS.DONE.next = i_timer_done;
    assign w_hwif_in.TIMER_STATUS.RUNNING.next = i_timer_running;
    assign w_hwif_in.TIMER_STATUS.PASS.next = i_timer_pass;
    assign w_hwif_in.TIMER_CYCLES_LO.VALUE.next = i_timer_cycles[31:0];
    assign w_hwif_in.TIMER_CYCLES_HI.VALUE.next = i_timer_cycles[63:32];
    assign w_hwif_in.TIMER_R_FIRST_LO.VALUE.next = i_timer_r_first[31:0];
    assign w_hwif_in.TIMER_R_FIRST_HI.VALUE.next = i_timer_r_first[63:32];
    assign w_hwif_in.TIMER_R_LAST_LO.VALUE.next = i_timer_r_last [31:0];
    assign w_hwif_in.TIMER_R_LAST_HI.VALUE.next = i_timer_r_last [63:32];
    assign w_hwif_in.TIMER_W_FIRST_LO.VALUE.next = i_timer_w_first[31:0];
    assign w_hwif_in.TIMER_W_FIRST_HI.VALUE.next = i_timer_w_first[63:32];
    assign w_hwif_in.TIMER_W_LAST_LO.VALUE.next = i_timer_w_last [31:0];
    assign w_hwif_in.TIMER_W_LAST_HI.VALUE.next = i_timer_w_last [63:32];
    assign w_hwif_in.CRC_RD_PER_CH0.VALUE.next = crc_rd_view[0];
    assign w_hwif_in.CRC_RD_PER_CH1.VALUE.next = crc_rd_view[1];
    assign w_hwif_in.CRC_RD_PER_CH2.VALUE.next = crc_rd_view[2];
    assign w_hwif_in.CRC_RD_PER_CH3.VALUE.next = crc_rd_view[3];
    assign w_hwif_in.CRC_RD_PER_CH4.VALUE.next = crc_rd_view[4];
    assign w_hwif_in.CRC_RD_PER_CH5.VALUE.next = crc_rd_view[5];
    assign w_hwif_in.CRC_RD_PER_CH6.VALUE.next = crc_rd_view[6];
    assign w_hwif_in.CRC_RD_PER_CH7.VALUE.next = crc_rd_view[7];
    assign w_hwif_in.CRC_WR_PER_CH0.VALUE.next = crc_wr_view[0];
    assign w_hwif_in.CRC_WR_PER_CH1.VALUE.next = crc_wr_view[1];
    assign w_hwif_in.CRC_WR_PER_CH2.VALUE.next = crc_wr_view[2];
    assign w_hwif_in.CRC_WR_PER_CH3.VALUE.next = crc_wr_view[3];
    assign w_hwif_in.CRC_WR_PER_CH4.VALUE.next = crc_wr_view[4];
    assign w_hwif_in.CRC_WR_PER_CH5.VALUE.next = crc_wr_view[5];
    assign w_hwif_in.CRC_WR_PER_CH6.VALUE.next = crc_wr_view[6];
    assign w_hwif_in.CRC_WR_PER_CH7.VALUE.next = crc_wr_view[7];
    assign w_hwif_in.CRC_VALID_MASK.VALUE.next = w_crc_valid_word;
    assign w_hwif_in.CRC_MATCH_MASK.VALUE.next = w_crc_match_word;
    assign w_hwif_in.DESC_SRAM_AR_HS.VALUE.next = i_desc_sram_ar_hs;
    assign w_hwif_in.DESC_SRAM_R_HS.VALUE.next = i_desc_sram_r_hs;
    assign w_hwif_in.DESC_AR_HS.VALUE.next = i_desc_ar_hs;
    assign w_hwif_in.DESC_AR_STALL.VALUE.next = i_desc_ar_stall;
    assign w_hwif_in.DESC_R_HS.VALUE.next = i_desc_r_hs;
    assign w_hwif_in.DESC_R_STALL.VALUE.next = i_desc_r_stall;
    assign w_hwif_in.DESC_AW_HS.VALUE.next = i_desc_aw_hs;
    assign w_hwif_in.DESC_W_HS.VALUE.next = i_desc_w_hs;
    assign w_hwif_in.DESC_B_HS.VALUE.next = i_desc_b_hs;
    assign w_hwif_in.DESC_VR_LIVE.VALUE.next = {16'h0, i_desc_vr_live};
    assign w_hwif_in.BUILD_VERSION.VALUE.next = 32'(BUILD_VERSION);
    // ALL SIX fields, matching the retired decode's concatenation exactly:
    //   {15'h0, MAIN_CONES, DATA_WIDTH_B[7:0], GEN_MON, USE_MONITORS,
    //    ERROR_FLAVOR, NUM_CHANNELS[4:0]}
    // I first mapped only two of them by hand and left four undriven, which
    // synthesis caught as "does not have driver". USE_MONITORS is the one that
    // would have hurt: the host reads bit 6 to choose the monbus capture
    // window, so an undriven bit sends records at the wrong slave.
    assign w_hwif_in.BUILD_CONFIG.NUM_CHANNELS.next = 5'(BUILD_NUM_CHANNELS);
    assign w_hwif_in.BUILD_CONFIG.ERROR_FLAVOR.next = 1'(BUILD_ERROR_FLAVOR);
    assign w_hwif_in.BUILD_CONFIG.USE_MONITORS.next = 1'(BUILD_USE_MONITORS);
    assign w_hwif_in.BUILD_CONFIG.GEN_MON.next      = 1'(BUILD_GEN_MON);
    assign w_hwif_in.BUILD_CONFIG.DATA_WIDTH_B.next = 8'(BUILD_DATA_WIDTH_B);
    assign w_hwif_in.BUILD_CONFIG.MAIN_CONES.next   = 1'(BUILD_MAIN_CONES);
    assign w_hwif_in.BUILD_N_PROFILE.VALUE.next = 32'(BUILD_N_PROFILE);
    assign w_hwif_in.BUILD_CLK_HZ.VALUE.next = 32'(BUILD_CLK_HZ);
    assign w_hwif_in.COMP_TIER1_A.VALUE.next = i_mon_comp_tier1_a;
    assign w_hwif_in.COMP_TIER1_B.VALUE.next = i_mon_comp_tier1_b;
    assign w_hwif_in.COMP_TIER1_C.VALUE.next = i_mon_comp_tier1_c;
    assign w_hwif_in.COMP_TIER0.VALUE.next = i_mon_comp_tier0;
    assign w_hwif_in.COMP_CAM_MISS.VALUE.next = i_mon_comp_cam_miss;
    assign w_hwif_in.COMP_DELTA_TS_OVF.VALUE.next = i_mon_comp_delta_ts_ovf;
    assign w_hwif_in.COMP_EVENT_DATA_OVF.VALUE.next = i_mon_comp_event_data_ovf;
    assign w_hwif_in.COMP_ED_DELTA_OVF.VALUE.next = i_mon_comp_ed_delta_ovf;

    // =========================================================================
    // Write channel FSM (operates on skid-buffer outputs)
    // =========================================================================
    typedef enum logic [1:0] {
        W_IDLE  = 2'd0,
        W_BRESP = 2'd1
    } w_state_t;

    w_state_t r_wstate;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            // Reset values and the one-cycle auto-clear of the CTRL /
            // TIMER_CTRL pulses now live in the register block: every pulse is
            // a `singlepulse` field in harness_csr.rdl, which is exactly what
            // this hand-written block was open-coding.
            r_wstate            <= W_IDLE;
        end else begin

            case (r_wstate)
                W_IDLE: begin
                    if (int_awvalid && int_wvalid) begin
                        // The decode is the register block's job now.
                        // Use the same 9-bit slice as the read path so the
                        // meter region 0x100-0x1FF stays read-only (no write
                        // case-match means write goes to default = ignore),
                        // with the sole exception of the RFC Stage E observer
                        // histogram selector at 0x120 (RW).
                        r_wstate <= W_BRESP;
                    end
                end
                W_BRESP: begin
                    if (int_bready) r_wstate <= W_IDLE;
                end
                default: r_wstate <= W_IDLE;
            endcase
        end
    )

    // The write moment: exactly when the old decode's case fired.
    assign w_wr_req = (r_wstate == W_IDLE) && int_awvalid && int_wvalid;

    assign int_awready = (r_wstate == W_IDLE) && int_wvalid;
    assign int_wready  = (r_wstate == W_IDLE) && int_awvalid;
    assign int_bvalid  = (r_wstate == W_BRESP);
    assign int_b_pkt   = 2'b00;

    // =========================================================================
    // Sticky status bits
    // =========================================================================
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_irq_latched      <= 1'b0;
            r_any_error_sticky <= 1'b0;
        end else begin
            if (r_clear_stats_pulse) begin
                r_irq_latched      <= 1'b0;
                r_any_error_sticky <= 1'b0;
            end else begin
                if (i_stream_irq) r_irq_latched      <= 1'b1;
                if (i_any_error)  r_any_error_sticky <= 1'b1;
            end
        end
    )

    // =========================================================================
    // Read channel FSM
    // =========================================================================
    typedef enum logic [0:0] {
        R_IDLE  = 1'b0,
        R_RRESP = 1'b1
    } r_state_t;

    r_state_t r_rstate;
    logic [31:0] r_rdata;

    // 9-bit decode to span 0x000-0x1FF (meter readback lives at 0x100+).
    logic [8:0] w_raddr;
    assign w_raddr = int_araddr[8:0];

    // The read moment. A write in the same cycle wins the single cpuif port,
    // so the read simply re-asserts until it is granted and acked.
    assign w_rd_req = (r_rstate == R_IDLE) && int_arvalid && !w_wr_req;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rstate <= R_IDLE;
            r_rdata  <= '0;
        end else begin
            case (r_rstate)
                R_IDLE: begin
                    if (int_arvalid) begin
                        r_rdata <= w_cpuif_rd_data;
                        r_rstate <= R_RRESP;
                    end
                end
                R_RRESP: if (int_rready) r_rstate <= R_IDLE;
                default: r_rstate <= R_IDLE;
            endcase
        end
    )

    assign int_arready = (r_rstate == R_IDLE);
    assign int_rvalid  = (r_rstate == R_RRESP);
    assign int_r_pkt   = {r_rdata, 2'b00};  // rdata + OKAY

    // =========================================================================
    // Outputs
    // =========================================================================
    assign o_start_pulse       = r_start_pulse;
    assign o_clear_stats_pulse = r_clear_stats_pulse;
    assign o_freeze_trace      = r_freeze_trace;
    assign o_soft_reset_pulse  = r_soft_reset_pulse;
    assign o_cam_clear_pulse   = r_cam_clear_pulse;
    assign o_timer_clear_pulse    = r_timer_clear_pulse;
    assign o_timer_expected_beats = r_timer_expected_beats;
    assign o_rd_resp_delay_cyc    = r_rd_resp_delay_cyc;
    assign o_wr_resp_delay_cyc    = r_wr_resp_delay_cyc;


    // Prevent unused signal warnings
    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0, int_awprot, int_wstrb, int_arprot, 1'b0};
    /* verilator lint_on UNUSED */

endmodule : harness_csr
