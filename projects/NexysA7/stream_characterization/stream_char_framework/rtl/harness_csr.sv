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
//   0x28  TIMER_CTRL      W   [0] = clear pulse (resets done/cycles/pass)
//                              Reads as 0.
//   0x2C  TIMER_STATUS    R   [0] = done   (latched: stop trigger fired)
//                              [1] = running (between start and stop)
//                              [2] = pass   (CRC matched at stop edge)
//   0x30  TIMER_CYCLES_LO R   Low 32 b of 64 b cycle counter (10 ns / cycle)
//   0x34  TIMER_CYCLES_HI R   High 32 b
//   0x38  TIMER_EXP_BEATS RW  Expected sink-side beat count (host programs
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
//   Kick-burst fast path. Bypasses the slow APB-via-UART kick sequence
//   (which would otherwise stretch out by ~2 ms per UART write at 115200
//   baud, pushing the harness timer's "first AR -> last W" window way
//   past the actual hardware compute). Programming sequence:
//     1. Write CHx_KICK_ADDR for every channel that should be kicked.
//     2. Write KICK_GO with a bitmask of channels — that single APB write
//        pulses the in-hardware kick lines for every selected channel
//        within one aclk cycle, so multi-channel runs actually pipeline
//        rather than serializing on UART.
//
//   CH_KICK_ADDR[ch]  RW  Per-channel descriptor address latch (8 slots).
//                          Layout SKIPS 0xC0 (that slot is KICK_GO):
//                          ch 0..3 -> 0xB0/0xB4/0xB8/0xBC
//                          ch 4..7 -> 0xC4/0xC8/0xCC/0xD0
//                          Host code must NOT use a bare "BASE + 4*ch"
//                          stride -- that lands ch=4 on 0xC0 and writes
//                          into KICK_GO, firing a spurious one-cycle
//                          kick whose mask is the LSBs of the address.
//   0xC0          KICK_GO  W  Bitmask: writing N pulses the hardware
//                              kick line for each set bit for one cycle.
//                              Reads as 0.
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

    // RFC Stage E: external axi4_dma_observer perf readback (revives the
    // 0x100-0x128 range the retired harness axi_bus_meter used). Aggregate
    // R/W bus-meter buckets + an indexed latency-histogram readout, sourced
    // from the standalone observer dropped inline on STREAM's rd/wr AXI. Used
    // for observer-vs-in-core equivalence and the eventual USE_AXI_MONITORS=0
    // path where the observer is the sole perf source.
    input  logic [31:0]     i_obs_rd_prod,
    input  logic [31:0]     i_obs_rd_bp,
    input  logic [31:0]     i_obs_rd_starv,
    input  logic [31:0]     i_obs_rd_idle,
    input  logic [31:0]     i_obs_wr_prod,
    input  logic [31:0]     i_obs_wr_bp,
    input  logic [31:0]     i_obs_wr_starv,
    input  logic [31:0]     i_obs_wr_idle,
    // Indexed histogram readout. o_obs_hist_sel = {bin[5:2], metric[1], bus[0]}
    // (bus 0=read/1=write; metric 0=AR->firstR or AW->B, 1=AR->RLAST). The
    // harness drives the observer's i_hist_metric/i_hist_bin from this and
    // muxes the selected count/total back into i_obs_hist_data/total.
    output logic [5:0]      o_obs_hist_sel,
    input  logic [31:0]     i_obs_hist_data,
    input  logic [31:0]     i_obs_hist_total,

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
    // Kick-burst fast path (CH_KICK_ADDR slots split around KICK_GO @ 0xC0;
    // see address-map block at top of file for the layout)
    // =====================================================================
    output logic [NUM_CHANNELS-1:0]       o_kick_burst_mask,  // 1-cycle pulse
    output logic [NUM_CHANNELS-1:0][31:0] o_kick_burst_addr,  // shadow values

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
    logic r_freeze_trace;
    logic r_irq_latched;
    logic r_any_error_sticky;
    logic [31:0] r_scratch;
    logic [5:0]  r_obs_hist_sel;   // RFC Stage E observer hist selector @ 0x120

    logic r_start_pulse;
    logic r_clear_stats_pulse;
    logic r_soft_reset_pulse;
    logic r_cam_clear_pulse;
    logic r_timer_clear_pulse;
    logic [31:0] r_timer_expected_beats;
    logic [15:0] r_rd_resp_delay_cyc;
    logic [15:0] r_wr_resp_delay_cyc;

    // Kick-burst storage: per-channel address shadow + pulse-per-cycle
    // trigger output. Writing CH_KICK_ADDR[ch] latches an address; the
    // address-map block at top of file shows the per-channel offsets
    // (split around the 0xC0 KICK_GO slot). Writing KICK_GO (0xC0) with
    // a bitmask asserts o_kick_burst_mask for that bitmask for exactly
    // one cycle.
    logic [31:0] r_kick_addr [8];   // 8 fixed slots; only NUM_CHANNELS used
    logic [7:0]  r_kick_go_pulse;   // one-cycle pulse driven by 0xC0 write

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
            r_wstate            <= W_IDLE;
            r_freeze_trace      <= 1'b0;
            r_scratch           <= '0;
            r_start_pulse          <= 1'b0;
            r_clear_stats_pulse    <= 1'b0;
            r_soft_reset_pulse     <= 1'b0;
            r_cam_clear_pulse      <= 1'b0;
            r_timer_clear_pulse    <= 1'b0;
            r_timer_expected_beats <= '0;
            r_rd_resp_delay_cyc    <= '0;
            r_wr_resp_delay_cyc    <= '0;
            r_obs_hist_sel         <= '0;
            for (int i = 0; i < 8; i++) r_kick_addr[i] <= '0;
            r_kick_go_pulse        <= '0;
        end else begin
            r_start_pulse          <= 1'b0;
            r_clear_stats_pulse    <= 1'b0;
            r_soft_reset_pulse     <= 1'b0;
            r_cam_clear_pulse      <= 1'b0;
            r_timer_clear_pulse    <= 1'b0;
            r_kick_go_pulse        <= '0;  // single-cycle trigger

            case (r_wstate)
                W_IDLE: begin
                    if (int_awvalid && int_wvalid) begin
                        // Use the same 9-bit slice as the read path so the
                        // meter region 0x100-0x1FF stays read-only (no write
                        // case-match means write goes to default = ignore),
                        // with the sole exception of the RFC Stage E observer
                        // histogram selector at 0x120 (RW).
                        case (int_awaddr[8:0])
                            8'h00: begin
                                r_start_pulse       <= int_wdata[0];
                                r_clear_stats_pulse <= int_wdata[1];
                                r_freeze_trace      <= int_wdata[2];
                                r_soft_reset_pulse  <= int_wdata[3];
                                r_cam_clear_pulse   <= int_wdata[4];
                            end
                            8'h20: r_scratch <= int_wdata;
                            8'h28: r_timer_clear_pulse <= int_wdata[0];
                            8'h38: r_timer_expected_beats <= int_wdata;
                            8'h3C: begin
                                r_rd_resp_delay_cyc <= int_wdata[15:0];
                                r_wr_resp_delay_cyc <= int_wdata[31:16];
                            end
                            // Kick-burst shadow address per channel
                            // (0xB0..0xCC: 8 slots = enough for NC up to 8)
                            8'hB0: r_kick_addr[0] <= int_wdata;
                            8'hB4: r_kick_addr[1] <= int_wdata;
                            8'hB8: r_kick_addr[2] <= int_wdata;
                            8'hBC: r_kick_addr[3] <= int_wdata;
                            8'hC4: r_kick_addr[4] <= int_wdata;
                            8'hC8: r_kick_addr[5] <= int_wdata;
                            8'hCC: r_kick_addr[6] <= int_wdata;
                            8'hD0: r_kick_addr[7] <= int_wdata;
                            // Kick-burst trigger: bitmask of channels to
                            // pulse for exactly one cycle. Auto-clears.
                            8'hC0: r_kick_go_pulse <= int_wdata[7:0];
                            // RFC Stage E observer histogram selector (RW):
                            // {bin[5:2], metric[1], bus[0]}. Drives the
                            // observer's hist read port; data/total stream
                            // back through 0x124/0x128 (read-only).
                            9'h120: r_obs_hist_sel <= int_wdata[5:0];
                            default: ; // ignore
                        endcase
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

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rstate <= R_IDLE;
            r_rdata  <= '0;
        end else begin
            case (r_rstate)
                R_IDLE: begin
                    if (int_arvalid) begin
                        case (w_raddr)
                            8'h00: r_rdata <= {28'd0, 1'b0, r_freeze_trace, 2'b00};
                            8'h04: r_rdata <= {28'd0, i_dbg_clear_busy, i_dbg_overflow, r_any_error_sticky, r_irq_latched};
                            8'h08: r_rdata <= i_dbg_wr_ptr;
                            8'h0C: r_rdata <= {31'd0, i_dbg_overflow};
                            8'h10: r_rdata <= i_crc_rd_expected;
                            8'h14: r_rdata <= i_crc_wr_expected;
                            8'h18: r_rdata <= i_crc_wr_computed;
                            8'h1C: r_rdata <= {30'd0, i_crc_valid, i_crc_match};
                            8'h20: r_rdata <= r_scratch;
                            8'h24: r_rdata <= BUILD_ID;
                            8'h28: r_rdata <= 32'h0000_0000;  // TIMER_CTRL is W-only
                            8'h2C: r_rdata <= {29'd0, i_timer_pass,
                                                       i_timer_running,
                                                       i_timer_done};
                            8'h30: r_rdata <= i_timer_cycles[31:0];
                            8'h34: r_rdata <= i_timer_cycles[63:32];
                            8'h38: r_rdata <= r_timer_expected_beats;
                            8'h3C: r_rdata <= {r_wr_resp_delay_cyc, r_rd_resp_delay_cyc};
                            8'h40: r_rdata <= i_timer_r_first[31:0];
                            8'h44: r_rdata <= i_timer_r_first[63:32];
                            8'h48: r_rdata <= i_timer_r_last [31:0];
                            8'h4C: r_rdata <= i_timer_r_last [63:32];
                            8'h50: r_rdata <= i_timer_w_first[31:0];
                            8'h54: r_rdata <= i_timer_w_first[63:32];
                            8'h58: r_rdata <= i_timer_w_last [31:0];
                            8'h5C: r_rdata <= i_timer_w_last [63:32];
                            // Per-channel CRC values (NC up to CRC_VIEW_NC=8).
                            // 0x60..0x7C: read CRCs, 0x80..0x9C: write CRCs.
                            8'h60: r_rdata <= crc_rd_view[0];
                            8'h64: r_rdata <= crc_rd_view[1];
                            8'h68: r_rdata <= crc_rd_view[2];
                            8'h6C: r_rdata <= crc_rd_view[3];
                            8'h70: r_rdata <= crc_rd_view[4];
                            8'h74: r_rdata <= crc_rd_view[5];
                            8'h78: r_rdata <= crc_rd_view[6];
                            8'h7C: r_rdata <= crc_rd_view[7];
                            8'h80: r_rdata <= crc_wr_view[0];
                            8'h84: r_rdata <= crc_wr_view[1];
                            8'h88: r_rdata <= crc_wr_view[2];
                            8'h8C: r_rdata <= crc_wr_view[3];
                            8'h90: r_rdata <= crc_wr_view[4];
                            8'h94: r_rdata <= crc_wr_view[5];
                            8'h98: r_rdata <= crc_wr_view[6];
                            8'h9C: r_rdata <= crc_wr_view[7];
                            8'hA0: r_rdata <= w_crc_valid_word;
                            8'hA4: r_rdata <= w_crc_match_word;
                            // SRAM-side desc_ram handshake counters
                            // (see 0xD4/0xD8 in the address-map docstring).
                            8'hD4: r_rdata <= i_desc_sram_ar_hs;
                            8'hD8: r_rdata <= i_desc_sram_r_hs;
                            // desc_ram observation counters / live valid-ready
                            // snapshot (see address-map docstring 0xE0..0xFC).
                            8'hE0: r_rdata <= i_desc_ar_hs;
                            8'hE4: r_rdata <= i_desc_ar_stall;
                            8'hE8: r_rdata <= i_desc_r_hs;
                            8'hEC: r_rdata <= i_desc_r_stall;
                            8'hF0: r_rdata <= i_desc_aw_hs;
                            8'hF4: r_rdata <= i_desc_w_hs;
                            8'hF8: r_rdata <= i_desc_b_hs;
                            8'hFC: r_rdata <= {16'h0, i_desc_vr_live};
                            // Kick-burst shadow registers (read-back)
                            8'hB0: r_rdata <= r_kick_addr[0];
                            8'hB4: r_rdata <= r_kick_addr[1];
                            8'hB8: r_rdata <= r_kick_addr[2];
                            8'hBC: r_rdata <= r_kick_addr[3];
                            8'hC0: r_rdata <= 32'h0;  // KICK_GO is W-only
                            8'hC4: r_rdata <= r_kick_addr[4];
                            8'hC8: r_rdata <= r_kick_addr[5];
                            8'hCC: r_rdata <= r_kick_addr[6];
                            8'hD0: r_rdata <= r_kick_addr[7];

                            // RFC Stage E: external axi4_dma_observer perf
                            // readback (revives 0x100-0x128). Aggregate R/W
                            // buckets + indexed latency-histogram readout.
                            9'h100: r_rdata <= i_obs_rd_prod;
                            9'h104: r_rdata <= i_obs_rd_bp;
                            9'h108: r_rdata <= i_obs_rd_starv;
                            9'h10C: r_rdata <= i_obs_rd_idle;
                            9'h110: r_rdata <= i_obs_wr_prod;
                            9'h114: r_rdata <= i_obs_wr_bp;
                            9'h118: r_rdata <= i_obs_wr_starv;
                            9'h11C: r_rdata <= i_obs_wr_idle;
                            9'h120: r_rdata <= {26'd0, r_obs_hist_sel};
                            9'h124: r_rdata <= i_obs_hist_data;
                            9'h128: r_rdata <= i_obs_hist_total;

                            // MonBus compressor statistics (0 unless the
                            // build has USE_MON_COMPRESSION=1).
                            9'h1E0: r_rdata <= i_mon_comp_tier1_a;
                            9'h1E4: r_rdata <= i_mon_comp_tier1_b;
                            9'h1E8: r_rdata <= i_mon_comp_tier1_c;
                            9'h1EC: r_rdata <= i_mon_comp_tier0;
                            9'h1F0: r_rdata <= i_mon_comp_cam_miss;
                            9'h1F4: r_rdata <= i_mon_comp_delta_ts_ovf;
                            9'h1F8: r_rdata <= i_mon_comp_event_data_ovf;
                            9'h1FC: r_rdata <= i_mon_comp_ed_delta_ovf;

                            default: r_rdata <= 32'h0000_0000;
                        endcase
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
    assign o_obs_hist_sel         = r_obs_hist_sel;

    // Kick-burst outputs: pulse the mask exactly when KICK_GO was just
    // written (one aclk cycle), and broadcast the per-channel shadow
    // addresses so stream_top_ch8 latches the right one for each ch.
    always_comb begin
        for (int ch = 0; ch < NUM_CHANNELS; ch++) begin
            o_kick_burst_mask[ch] = r_kick_go_pulse[ch];
            o_kick_burst_addr[ch] = r_kick_addr[ch];
        end
    end

    // Prevent unused signal warnings
    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0, int_awprot, int_wstrb, int_arprot, 1'b0};
    /* verilator lint_on UNUSED */

endmodule : harness_csr
