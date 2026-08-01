// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: harness_csr
// Purpose: Control / status / engine-cfg registers for the DDR2/LPDDR2
//          characterization harness. AXI4-Lite slave; host visibility
//          via the 1->5 UART-fed AXIL bridge.
//
// This is the DDR2 sibling of stream_char_framework/rtl/harness_csr.sv.
// Same shape (skid-buffered AXIL slave, one write FSM + one read decode),
// different register map. Because the char macro has two indepedent
// master-side engines (axi4_master_wr_pattern_gen + axi4_master_rd_crc_check)
// each with ~15 cfg inputs, this CSR block ALSO holds every engine cfg
// register — the host writes them here, this block fans them out as
// steady-state signals to the char macro.
//
// Register map (byte offsets from harness_csr base = 0x0001_0000):
//
// -- Harness control / status --------------------------------------------
//   0x00  CTRL              RW  [0]  start_wr     (self-clearing pulse)
//                                [1]  start_rd     (self-clearing pulse)
//                                [2]  clear_stats  (self-clearing pulse)
//                                [3]  freeze_trace (latch; stops debug_sram)
//                                [4]  soft_reset   (self-clearing pulse)
//   0x04  STATUS            R   [0]  wr_done       (from engine)
//                                [1]  rd_done       (from engine)
//                                [2]  wr_error      (bresp / sticky)
//                                [3]  rd_error      (rresp / data / sticky)
//                                [4]  any_error     (any of the above)
//                                [5]  dbg_clear_busy
//                                [6]  init_done     (controller init sequence)
//                                [7]  init_fail
//   0x08  DBG_WR_PTR        R   words written to debug_sram
//   0x0C  DBG_OVERFLOW      R   sticky trace-overflow flag
//   0x10  CRC_EXPECTED      R   from WR engine (o_expected_crc)
//   0x14  CRC_ACTUAL        R   from RD engine (o_actual_crc)
//   0x18  CRC_MATCH         R   [0]match [1]exp_valid [2]act_valid
//                                [3] beats_mismatched != 0
//   0x1C  SCRATCH           RW  host bring-up ping
//   0x20  BUILD_ID          R   parameter-driven build ID (default "DDR2")
//   0x24  BEATS_MISM        R   o_beats_mismatched (RD engine)
//
// -- Characterization timer ----------------------------------------------
//   0x28  TIMER_CTRL        W   [0] clear-pulse (resets done/cycles/pass)
//   0x2C  TIMER_STATUS      R   [0]done [1]running [2]pass
//   0x30  TIMER_CYCLES_LO   R   64b cycle counter, low
//   0x34  TIMER_CYCLES_HI   R
//   0x38  TIMER_EXP_BEATS   RW  stop trigger; 0 = disable
//   0x3C  RESP_DELAY        RW  [15:0]rd_delay [31:16]wr_delay (axi_response_delay)
//
//   0x40  TIMER_R_FIRST_LO  R
//   0x44  TIMER_R_FIRST_HI  R
//   0x48  TIMER_R_LAST_LO   R
//   0x4C  TIMER_R_LAST_HI   R
//   0x50  TIMER_W_FIRST_LO  R
//   0x54  TIMER_W_FIRST_HI  R
//   0x58  TIMER_W_LAST_LO   R
//   0x5C  TIMER_W_LAST_HI   R
//
// -- Runtime controller cfg (drives ddr2_char_macro cfg inputs) ----------
//   0x60  CTRLR_CFG         RW  [0]     memtype (0=DDR2, 1=LPDDR2)
//                                [15:8]  t_phy_wrlat
//                                [23:16] t_rddata_en
//                                [24]    rd_in_order
//   0x64  CTRLR_CAP         RW  [3:0]   cap_lookahead_max
//                                [7:4]   cap_synth_mask
//   0x68  DFI_TUNING        RW  [3:0]   cmd_delay (DFI cmd->data align, dflt 1; pre-pull + pipe trim)
//                                       [7:4]   rddata_delay (realign PHY rddata to late rddata_valid; dflt 0=passthru, set ~read_latency)
//
// -- WR engine cfg (0x100..0x12F) ----------------------------------------
//   0x100  WR_START_ADDR    RW
//   0x104  WR_STRIDE_0      RW  (signed, STRIDE_WIDTH-bit sign-extended in RTL)
//   0x108  WR_STRIDE_1      RW
//   0x10C  WR_WRAP_MASK_0   RW
//   0x110  WR_WRAP_MASK_1   RW
//   0x114  WR_BLEN_TXN      RW  [7:0]burst_len  [23:8]txn_count  [31:24]gap[3:0]
//   0x118  WR_AXI_ATTR      RW  [7:0]axi_id  [9:8]id_mode  [12:10]axi_size
//                                 [14:13]axi_burst  [15]data_mode
//   0x11C  WR_LFSR_SEED     RW
//   0x120  WR_HASH_SEED0    RW
//   0x124  WR_HASH_SEED1    RW
//   0x128  WR_HASH_SEED2    RW
//
// -- RD engine cfg (0x180..0x1AF) — mirror of WR ------------------------
//   0x180  RD_START_ADDR    RW
//   0x184  RD_STRIDE_0      RW
//   0x188  RD_STRIDE_1      RW
//   0x18C  RD_WRAP_MASK_0   RW
//   0x190  RD_WRAP_MASK_1   RW
//   0x194  RD_BLEN_TXN      RW
//   0x198  RD_AXI_ATTR      RW
//   0x19C  RD_LFSR_SEED     RW
//   0x1A0  RD_HASH_SEED0    RW
//   0x1A4  RD_HASH_SEED1    RW
//   0x1A8  RD_HASH_SEED2    RW
//
// -- Perf readback (from axi_bus_meter + axi_perf_latency_hist tapped ---
//   inside ddr2_char_macro). All 32b, clear on CTRL.clear_stats via the
//   perf_clear pulse; freeze via CTRL.freeze_trace via perf_freeze.
//   Sits at 0x1C0..0x1E8 (after RD engine cfg) so it doesn't collide
//   with the 0x100/0x180 engine-cfg blocks.
//
//   0x1C0  OBS_RD_PROD       R  RD data-channel meter: productive cycles
//   0x1C4  OBS_RD_BP         R                          backpressure
//   0x1C8  OBS_RD_STARV      R                          starvation
//   0x1CC  OBS_RD_IDLE       R                          idle
//   0x1D0  OBS_WR_PROD       R  WR data-channel meter: productive
//   0x1D4  OBS_WR_BP         R                          backpressure
//   0x1D8  OBS_WR_STARV      R                          starvation
//   0x1DC  OBS_WR_IDLE       R                          idle
//   0x1E0  OBS_HIST_SEL      RW indexed histogram selector:
//                              [0]    bus       (0=read, 1=write)
//                              [1]    metric    (RD only: 0=AR->firstR,
//                                                          1=AR->RLAST)
//                              [5:2]  bin index (log2 latency bin 0..15)
//   0x1E4  OBS_HIST_COUNT    R   count of the selected bin
//   0x1E8  OBS_HIST_TOTAL    R   total transactions on the selected metric
//
// -- Build identity (read-only, elaboration-time constants) --------------
//   BUILD_ID above names the harness FAMILY and nothing more. Which build is
//   loaded, and the geometry it was compiled for, had to be supplied out of
//   band: by env var in sim (TEST_DFI_RATE / TEST_DRAM_BL), by assumption on
//   silicon. A wrong assumption showed up as a read path returning garbage,
//   not as a mismatch anyone could see. These make it a comparison.
//
//   0x1EC  BUILD_VERSION     R   functional build number, bumped per build
//   0x1F0  BUILD_CONFIG      R   [3:0]   dfi_rate
//                                [7:4]   gear_ratio = $clog2(dfi_rate)
//                                [15:8]  dram_bl (JEDEC MR0 burst length)
//                                [21:16] row_width
//                                [25:22] bank_width (DFI bank bus width)
//   0x1F4  BUILD_DATA_CFG    R   [15:0]  axi_data_width, bits
//                                [23:16] dram_beat_width, bits
//                                [31:24] dram_device_width, bits
//
// Any address not listed reads as 0 and ignores writes.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module harness_csr
    import pumice_pkg::*;
#(
    parameter int AW = 32,
    parameter int DW = 32,
    parameter int AXI_ID_WIDTH     = 8,
    parameter int STRIDE_WIDTH     = 24,
    parameter int TXN_COUNT_WIDTH  = 16,
    parameter int BURST_LEN_WIDTH  = 8,
    parameter logic [31:0] BUILD_ID = 32'h4444_5232,  // "DDR2"

    // ---- Build identity / configuration, readable by the host -------------
    // BUILD_ID says only WHICH HARNESS this is. It cannot say which build of
    // it is loaded, so a host had to be TOLD the geometry out of band -- the
    // sim passes TEST_DFI_RATE / TEST_DRAM_BL by environment variable, and on
    // silicon it was simply assumed. When the assumption was wrong the symptom
    // was a read path that returned garbage, not a mismatch anyone could see.
    //
    // These two registers close that: the values are the ones the bitstream
    // was COMPILED with, so the host can ask the board what it is talking to
    // instead of guessing. Wrong-bitstream becomes a comparison, not a debug
    // session.
    parameter int BUILD_VERSION      = 1,   // bump per functional build
    parameter int CFG_DFI_RATE       = 2,   // DFI phases per controller cycle
    parameter int CFG_DRAM_BL        = 4,   // JEDEC burst length (MR0)
    parameter int CFG_ROW_WIDTH      = 13,
    parameter int CFG_BANK_WIDTH     = 3,
    parameter int CFG_AXI_DATA_W     = 64,
    parameter int CFG_DRAM_BEAT_W    = 64,  // pumice DRAM beat, bits
    parameter int CFG_DRAM_DEVICE_W  = 64,  // physical device width, bits

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
    // Harness control outputs
    // =====================================================================
    output logic            o_start_wr_pulse,
    output logic            o_start_rd_pulse,
    output logic            o_clear_stats_pulse,
    output logic            o_freeze_trace,
    output logic            o_soft_reset_pulse,

    // =====================================================================
    // Harness status inputs
    // =====================================================================
    input  logic            i_wr_done,
    input  logic            i_rd_done,
    input  logic            i_wr_error,
    input  logic            i_rd_error,
    input  logic            i_init_done,
    input  logic            i_init_fail,
    input  logic [31:0]     i_dbg_wr_ptr,
    input  logic            i_dbg_overflow,
    input  logic            i_dbg_clear_busy,

    input  logic [31:0]     i_crc_expected,
    input  logic [31:0]     i_crc_actual,
    input  logic            i_crc_exp_valid,
    input  logic            i_crc_act_valid,
    input  logic [TXN_COUNT_WIDTH-1:0] i_beats_mismatched,

    // =====================================================================
    // Timer interface
    // =====================================================================
    output logic            o_timer_clear_pulse,
    output logic [31:0]     o_timer_expected_beats,
    input  logic            i_timer_done,
    input  logic            i_timer_running,
    input  logic            i_timer_pass,
    input  logic [63:0]     i_timer_cycles,
    input  logic [63:0]     i_timer_r_first,
    input  logic [63:0]     i_timer_r_last,
    input  logic [63:0]     i_timer_w_first,
    input  logic [63:0]     i_timer_w_last,

    // =====================================================================
    // Response-delay knobs
    // =====================================================================
    output logic [15:0]     o_rd_resp_delay_cyc,
    output logic [15:0]     o_wr_resp_delay_cyc,

    // =====================================================================
    // Perf observability (from ddr2_char_macro's tapped bus meters +
    // latency histograms). See register map 0x100-0x128.
    // =====================================================================
    output logic            o_perf_clear,       // = CTRL.clear_stats pulse
    output logic            o_perf_freeze,      // = CTRL.freeze_trace latch
    input  logic [31:0]     i_obs_rd_prod,
    input  logic [31:0]     i_obs_rd_bp,
    input  logic [31:0]     i_obs_rd_starv,
    input  logic [31:0]     i_obs_rd_idle,
    input  logic [31:0]     i_obs_wr_prod,
    input  logic [31:0]     i_obs_wr_bp,
    input  logic [31:0]     i_obs_wr_starv,
    input  logic [31:0]     i_obs_wr_idle,
    output logic            o_obs_hist_metric,  // = OBS_HIST_SEL[1]
    output logic [3:0]      o_obs_hist_bin,     // = OBS_HIST_SEL[5:2]
    output logic            o_obs_hist_bus_sel, // = OBS_HIST_SEL[0] (0=rd 1=wr)
    input  logic [31:0]     i_obs_rd_hist_count,
    input  logic [31:0]     i_obs_rd_hist_total,
    input  logic [31:0]     i_obs_wr_hist_count,
    input  logic [31:0]     i_obs_wr_hist_total,

    // =====================================================================
    // Runtime controller cfg outputs (into ddr2_char_macro)
    // =====================================================================
    output memtype_e        o_memtype,
    output logic [7:0]      o_t_phy_wrlat,
    output logic [7:0]      o_t_rddata_en,
    output logic            o_rd_in_order,
    output logic [3:0]      o_cap_lookahead_max,
    output logic [3:0]      o_cap_synth_mask,
    output logic [3:0]      o_cmd_delay,        // DFI_TUNING.cmd_delay (runtime)
    output logic [3:0]      o_rddata_delay,     // DFI_TUNING.rddata_delay (runtime)

    // ---- a7ddrphy calibration CSR passthrough (firmware leveling) ----
    // Indirect access at harness_csr offsets 0x080-0x08C: write ADDR (0x080)
    // + WDATA (0x084), pulse CTRL (0x088)[0] to drive one CSR-bus write; read
    // RDATA (0x08C) returns the PHY's dat_r for the current ADDR. The 13 knobs
    // are documented in rtl-vivado/a7ddrphy/a7ddrphy_csr_map.txt.
    output logic [9:0]      o_phy_csr_adr,
    output logic            o_phy_csr_we,
    output logic [31:0]     o_phy_csr_dat_w,
    input  logic [31:0]     i_phy_csr_dat_r,

    // =====================================================================
    // WR-engine cfg outputs (drive ddr2_char_macro cfg_wr_* inputs)
    // =====================================================================
    output logic [AW-1:0]                       o_cfg_wr_start_addr,
    output logic signed [STRIDE_WIDTH-1:0]      o_cfg_wr_stride_0,
    output logic signed [STRIDE_WIDTH-1:0]      o_cfg_wr_stride_1,
    output logic [AW-1:0]                       o_cfg_wr_wrap_mask_0,
    output logic [AW-1:0]                       o_cfg_wr_wrap_mask_1,
    output logic [BURST_LEN_WIDTH-1:0]          o_cfg_wr_burst_len,
    output logic [TXN_COUNT_WIDTH-1:0]          o_cfg_wr_txn_count,
    output logic [AXI_ID_WIDTH-1:0]             o_cfg_wr_axi_id,
    output logic [1:0]                          o_cfg_wr_id_mode,
    output logic [2:0]                          o_cfg_wr_axi_size,
    output logic [1:0]                          o_cfg_wr_axi_burst,
    output logic [3:0]                          o_cfg_wr_gap,
    output logic                                o_cfg_wr_data_mode,
    output logic [31:0]                         o_cfg_wr_lfsr_seed,
    output logic [31:0]                         o_cfg_wr_hash_seed0,
    output logic [31:0]                         o_cfg_wr_hash_seed1,
    output logic [31:0]                         o_cfg_wr_hash_seed2,

    // =====================================================================
    // RD-engine cfg outputs (drive ddr2_char_macro cfg_rd_* inputs)
    // =====================================================================
    output logic [AW-1:0]                       o_cfg_rd_start_addr,
    output logic signed [STRIDE_WIDTH-1:0]      o_cfg_rd_stride_0,
    output logic signed [STRIDE_WIDTH-1:0]      o_cfg_rd_stride_1,
    output logic [AW-1:0]                       o_cfg_rd_wrap_mask_0,
    output logic [AW-1:0]                       o_cfg_rd_wrap_mask_1,
    output logic [BURST_LEN_WIDTH-1:0]          o_cfg_rd_burst_len,
    output logic [TXN_COUNT_WIDTH-1:0]          o_cfg_rd_txn_count,
    output logic [AXI_ID_WIDTH-1:0]             o_cfg_rd_axi_id,
    output logic [1:0]                          o_cfg_rd_id_mode,
    output logic [2:0]                          o_cfg_rd_axi_size,
    output logic [1:0]                          o_cfg_rd_axi_burst,
    output logic [3:0]                          o_cfg_rd_gap,
    output logic                                o_cfg_rd_data_mode,
    output logic [31:0]                         o_cfg_rd_lfsr_seed,
    output logic [31:0]                         o_cfg_rd_hash_seed0,
    output logic [31:0]                         o_cfg_rd_hash_seed1,
    output logic [31:0]                         o_cfg_rd_hash_seed2
);

    // Packed widths for the skid buffers
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
    // Harness control latches / pulses
    logic        r_freeze_trace;
    logic        r_start_wr_pulse;
    logic        r_start_rd_pulse;
    logic        r_clear_stats_pulse;
    logic        r_soft_reset_pulse;

    // Sticky status
    logic        r_wr_err_sticky;
    logic        r_rd_err_sticky;

    logic [31:0] r_scratch;
    // a7ddrphy CSR passthrough state
    logic [9:0]  r_phy_csr_addr;
    logic [31:0] r_phy_csr_wdata;
    logic        r_phy_csr_we_pulse;

    // Timer
    logic        r_timer_clear_pulse;
    logic [31:0] r_timer_expected_beats;

    // Response delay
    logic [15:0] r_rd_resp_delay_cyc;
    logic [15:0] r_wr_resp_delay_cyc;

    // Controller runtime cfg
    logic [31:0] r_ctrlr_cfg;   // {7'd0, rd_in_order, t_rddata_en, t_phy_wrlat, 7'd0, memtype}
    logic [31:0] r_ctrlr_cap;   // {24'd0, cap_synth_mask, cap_lookahead_max}
    logic [31:0] r_dfi_tuning;  // [3:0]cmd_delay [7:4]rddata_delay — DFI cmd/read alignment

    // WR engine cfg
    logic [31:0] r_wr_start_addr;
    logic [31:0] r_wr_stride_0;
    logic [31:0] r_wr_stride_1;
    logic [31:0] r_wr_wrap_mask_0;
    logic [31:0] r_wr_wrap_mask_1;
    logic [31:0] r_wr_blen_txn;   // [7:0]burst_len [23:8]txn_count [27:24]gap
    logic [31:0] r_wr_axi_attr;   // [7:0]axi_id [9:8]id_mode [12:10]axi_size [14:13]axi_burst [15]data_mode
    logic [31:0] r_wr_lfsr_seed;
    logic [31:0] r_wr_hash_seed0;
    logic [31:0] r_wr_hash_seed1;
    logic [31:0] r_wr_hash_seed2;

    // RD engine cfg (mirror)
    logic [31:0] r_rd_start_addr;
    logic [31:0] r_rd_stride_0;
    logic [31:0] r_rd_stride_1;
    logic [31:0] r_rd_wrap_mask_0;
    logic [31:0] r_rd_wrap_mask_1;
    logic [31:0] r_rd_blen_txn;
    logic [31:0] r_rd_axi_attr;
    logic [31:0] r_rd_lfsr_seed;
    logic [31:0] r_rd_hash_seed0;
    logic [31:0] r_rd_hash_seed1;
    logic [31:0] r_rd_hash_seed2;

    // Perf hist selector: {bin[5:2], metric[1], bus[0]}.
    logic [5:0]  r_obs_hist_sel;

    // =========================================================================
    // Write channel FSM
    // =========================================================================
    typedef enum logic [1:0] {
        W_IDLE  = 2'd0,
        W_BRESP = 2'd1
    } w_state_t;

    w_state_t r_wstate;

    // 9-bit slice covers 0x000..0x1FF (harness ctrl + engine cfg regions).
    logic [8:0] w_waddr;
    assign w_waddr = int_awaddr[8:0];

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wstate               <= W_IDLE;
            r_freeze_trace         <= 1'b0;
            r_start_wr_pulse       <= 1'b0;
            r_start_rd_pulse       <= 1'b0;
            r_clear_stats_pulse    <= 1'b0;
            r_soft_reset_pulse     <= 1'b0;
            r_scratch              <= '0;
            r_timer_clear_pulse    <= 1'b0;
            r_timer_expected_beats <= '0;
            r_rd_resp_delay_cyc    <= '0;
            r_wr_resp_delay_cyc    <= '0;
            r_ctrlr_cfg            <= '0;
            r_ctrlr_cap            <= '0;
            r_dfi_tuning           <= 32'd1;   // cmd_delay=1: pre-pull + 1-cyc pipeline trim
                                               // makes wrdata concurrent natively

            r_wr_start_addr        <= '0;
            r_wr_stride_0          <= '0;
            r_wr_stride_1          <= '0;
            r_wr_wrap_mask_0       <= '0;
            r_wr_wrap_mask_1       <= '0;
            r_wr_blen_txn          <= '0;
            r_wr_axi_attr          <= '0;
            r_wr_lfsr_seed         <= '0;
            r_wr_hash_seed0        <= '0;
            r_wr_hash_seed1        <= '0;
            r_wr_hash_seed2        <= '0;

            r_rd_start_addr        <= '0;
            r_rd_stride_0          <= '0;
            r_rd_stride_1          <= '0;
            r_rd_wrap_mask_0       <= '0;
            r_rd_wrap_mask_1       <= '0;
            r_rd_blen_txn          <= '0;
            r_rd_axi_attr          <= '0;
            r_rd_lfsr_seed         <= '0;
            r_rd_hash_seed0        <= '0;
            r_rd_hash_seed1        <= '0;
            r_rd_hash_seed2        <= '0;
            r_obs_hist_sel         <= '0;
            r_phy_csr_addr         <= '0;
            r_phy_csr_wdata        <= '0;
            r_phy_csr_we_pulse     <= 1'b0;
        end else begin
            // Default: pulses auto-clear each cycle
            r_start_wr_pulse       <= 1'b0;
            r_start_rd_pulse       <= 1'b0;
            r_clear_stats_pulse    <= 1'b0;
            r_soft_reset_pulse     <= 1'b0;
            r_timer_clear_pulse    <= 1'b0;
            r_phy_csr_we_pulse     <= 1'b0;

            case (r_wstate)
                W_IDLE: begin
                    if (int_awvalid && int_wvalid) begin
                        case (w_waddr)
                            9'h000: begin
                                r_start_wr_pulse    <= int_wdata[0];
                                r_start_rd_pulse    <= int_wdata[1];
                                r_clear_stats_pulse <= int_wdata[2];
                                r_freeze_trace      <= int_wdata[3];
                                r_soft_reset_pulse  <= int_wdata[4];
                            end
                            9'h01C: r_scratch <= int_wdata;
                            9'h028: r_timer_clear_pulse <= int_wdata[0];
                            9'h038: r_timer_expected_beats <= int_wdata;
                            9'h03C: begin
                                r_rd_resp_delay_cyc <= int_wdata[15:0];
                                r_wr_resp_delay_cyc <= int_wdata[31:16];
                            end
                            9'h060: r_ctrlr_cfg  <= int_wdata;
                            9'h064: r_ctrlr_cap  <= int_wdata;
                            9'h068: r_dfi_tuning <= int_wdata;

                            // a7ddrphy calibration CSR passthrough
                            9'h080: r_phy_csr_addr     <= int_wdata[9:0];
                            9'h084: r_phy_csr_wdata    <= int_wdata;
                            9'h088: r_phy_csr_we_pulse <= int_wdata[0];

                            // WR engine cfg
                            9'h100: r_wr_start_addr  <= int_wdata;
                            9'h104: r_wr_stride_0    <= int_wdata;
                            9'h108: r_wr_stride_1    <= int_wdata;
                            9'h10C: r_wr_wrap_mask_0 <= int_wdata;
                            9'h110: r_wr_wrap_mask_1 <= int_wdata;
                            9'h114: r_wr_blen_txn    <= int_wdata;
                            9'h118: r_wr_axi_attr    <= int_wdata;
                            9'h11C: r_wr_lfsr_seed   <= int_wdata;
                            9'h120: r_wr_hash_seed0  <= int_wdata;
                            9'h124: r_wr_hash_seed1  <= int_wdata;
                            9'h128: r_wr_hash_seed2  <= int_wdata;

                            // RD engine cfg
                            9'h180: r_rd_start_addr  <= int_wdata;
                            9'h184: r_rd_stride_0    <= int_wdata;
                            9'h188: r_rd_stride_1    <= int_wdata;
                            9'h18C: r_rd_wrap_mask_0 <= int_wdata;
                            9'h190: r_rd_wrap_mask_1 <= int_wdata;
                            9'h194: r_rd_blen_txn    <= int_wdata;
                            9'h198: r_rd_axi_attr    <= int_wdata;
                            9'h19C: r_rd_lfsr_seed   <= int_wdata;
                            9'h1A0: r_rd_hash_seed0  <= int_wdata;
                            9'h1A4: r_rd_hash_seed1  <= int_wdata;
                            9'h1A8: r_rd_hash_seed2  <= int_wdata;

                            // Perf hist selector (only RW perf reg)
                            9'h1E0: r_obs_hist_sel <= int_wdata[5:0];

                            default: ;  // ignore
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
    // Sticky error latches (cleared by CTRL.clear_stats)
    // =========================================================================
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_wr_err_sticky <= 1'b0;
            r_rd_err_sticky <= 1'b0;
        end else begin
            if (r_clear_stats_pulse) begin
                r_wr_err_sticky <= 1'b0;
                r_rd_err_sticky <= 1'b0;
            end else begin
                if (i_wr_error) r_wr_err_sticky <= 1'b1;
                if (i_rd_error) r_rd_err_sticky <= 1'b1;
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

    logic [8:0] w_raddr;
    assign w_raddr = int_araddr[8:0];

    // Assembled words
    logic [31:0] w_status;
    always_comb begin
        w_status = '0;
        w_status[0] = i_wr_done;
        w_status[1] = i_rd_done;
        w_status[2] = r_wr_err_sticky;
        w_status[3] = r_rd_err_sticky;
        w_status[4] = r_wr_err_sticky | r_rd_err_sticky;
        w_status[5] = i_dbg_clear_busy;
        w_status[6] = i_init_done;
        w_status[7] = i_init_fail;
    end

    logic [31:0] w_crc_match;
    always_comb begin
        w_crc_match = '0;
        w_crc_match[0] = (i_crc_expected == i_crc_actual)
                         && i_crc_exp_valid && i_crc_act_valid;
        w_crc_match[1] = i_crc_exp_valid;
        w_crc_match[2] = i_crc_act_valid;
        w_crc_match[3] = |i_beats_mismatched;
    end

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rstate <= R_IDLE;
            r_rdata  <= '0;
        end else begin
            case (r_rstate)
                R_IDLE: begin
                    if (int_arvalid) begin
                        case (w_raddr)
                            9'h000: r_rdata <= {27'd0, 1'b0, r_freeze_trace, 3'b000};
                            9'h004: r_rdata <= w_status;
                            9'h008: r_rdata <= i_dbg_wr_ptr;
                            9'h00C: r_rdata <= {31'd0, i_dbg_overflow};
                            9'h010: r_rdata <= i_crc_expected;
                            9'h014: r_rdata <= i_crc_actual;
                            9'h018: r_rdata <= w_crc_match;
                            9'h01C: r_rdata <= r_scratch;
                            9'h020: r_rdata <= BUILD_ID;
                            9'h024: r_rdata <= {{(32-TXN_COUNT_WIDTH){1'b0}}, i_beats_mismatched};

                            9'h028: r_rdata <= 32'h0;  // TIMER_CTRL is W-only
                            9'h02C: r_rdata <= {29'd0, i_timer_pass,
                                                       i_timer_running,
                                                       i_timer_done};
                            9'h030: r_rdata <= i_timer_cycles[31:0];
                            9'h034: r_rdata <= i_timer_cycles[63:32];
                            9'h038: r_rdata <= r_timer_expected_beats;
                            9'h03C: r_rdata <= {r_wr_resp_delay_cyc, r_rd_resp_delay_cyc};
                            9'h040: r_rdata <= i_timer_r_first[31:0];
                            9'h044: r_rdata <= i_timer_r_first[63:32];
                            9'h048: r_rdata <= i_timer_r_last[31:0];
                            9'h04C: r_rdata <= i_timer_r_last[63:32];
                            9'h050: r_rdata <= i_timer_w_first[31:0];
                            9'h054: r_rdata <= i_timer_w_first[63:32];
                            9'h058: r_rdata <= i_timer_w_last[31:0];
                            9'h05C: r_rdata <= i_timer_w_last[63:32];

                            9'h060: r_rdata <= r_ctrlr_cfg;
                            9'h064: r_rdata <= r_ctrlr_cap;
                            9'h068: r_rdata <= r_dfi_tuning;

                            // a7ddrphy calibration CSR passthrough
                            9'h080: r_rdata <= {22'd0, r_phy_csr_addr};
                            9'h084: r_rdata <= r_phy_csr_wdata;
                            9'h08C: r_rdata <= i_phy_csr_dat_r;

                            9'h100: r_rdata <= r_wr_start_addr;
                            9'h104: r_rdata <= r_wr_stride_0;
                            9'h108: r_rdata <= r_wr_stride_1;
                            9'h10C: r_rdata <= r_wr_wrap_mask_0;
                            9'h110: r_rdata <= r_wr_wrap_mask_1;
                            9'h114: r_rdata <= r_wr_blen_txn;
                            9'h118: r_rdata <= r_wr_axi_attr;
                            9'h11C: r_rdata <= r_wr_lfsr_seed;
                            9'h120: r_rdata <= r_wr_hash_seed0;
                            9'h124: r_rdata <= r_wr_hash_seed1;
                            9'h128: r_rdata <= r_wr_hash_seed2;

                            9'h180: r_rdata <= r_rd_start_addr;
                            9'h184: r_rdata <= r_rd_stride_0;
                            9'h188: r_rdata <= r_rd_stride_1;
                            9'h18C: r_rdata <= r_rd_wrap_mask_0;
                            9'h190: r_rdata <= r_rd_wrap_mask_1;
                            9'h194: r_rdata <= r_rd_blen_txn;
                            9'h198: r_rdata <= r_rd_axi_attr;
                            9'h19C: r_rdata <= r_rd_lfsr_seed;
                            9'h1A0: r_rdata <= r_rd_hash_seed0;
                            9'h1A4: r_rdata <= r_rd_hash_seed1;
                            9'h1A8: r_rdata <= r_rd_hash_seed2;

                            // Perf: bus-meter readback (RD then WR)
                            9'h1C0: r_rdata <= i_obs_rd_prod;
                            9'h1C4: r_rdata <= i_obs_rd_bp;
                            9'h1C8: r_rdata <= i_obs_rd_starv;
                            9'h1CC: r_rdata <= i_obs_rd_idle;
                            9'h1D0: r_rdata <= i_obs_wr_prod;
                            9'h1D4: r_rdata <= i_obs_wr_bp;
                            9'h1D8: r_rdata <= i_obs_wr_starv;
                            9'h1DC: r_rdata <= i_obs_wr_idle;

                            // Perf: histogram selector + selected bin
                            // (mux count/total across RD and WR sides
                            // based on selector bit 0).
                            9'h1E0: r_rdata <= {26'd0, r_obs_hist_sel};
                            9'h1E4: r_rdata <= r_obs_hist_sel[0]
                                                ? i_obs_wr_hist_count
                                                : i_obs_rd_hist_count;
                            9'h1E8: r_rdata <= r_obs_hist_sel[0]
                                                ? i_obs_wr_hist_total
                                                : i_obs_rd_hist_total;

                            // Build identity. Constant, elaboration-time: what
                            // the host reads is what this bitstream was built
                            // with, so it cannot drift from the hardware.
                            9'h1EC: r_rdata <= 32'(BUILD_VERSION);
                            9'h1F0: r_rdata <= {
                                                  6'd0,                     // [31:26]
                                                  4'(CFG_BANK_WIDTH),       // [25:22]
                                                  6'(CFG_ROW_WIDTH),        // [21:16]
                                                  8'(CFG_DRAM_BL),          // [15:8]
                                                  4'($clog2(CFG_DFI_RATE)), // [7:4] gear
                                                  4'(CFG_DFI_RATE)          // [3:0]
                                               };
                            9'h1F4: r_rdata <= {
                                                  8'(CFG_DRAM_DEVICE_W),    // [31:24]
                                                  8'(CFG_DRAM_BEAT_W),      // [23:16]
                                                  16'(CFG_AXI_DATA_W)       // [15:0]
                                               };

                            default: r_rdata <= 32'h0;
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
    assign int_r_pkt   = {r_rdata, 2'b00};

    // =========================================================================
    // Output assignment
    // =========================================================================
    assign o_start_wr_pulse    = r_start_wr_pulse;
    assign o_start_rd_pulse    = r_start_rd_pulse;
    assign o_clear_stats_pulse = r_clear_stats_pulse;
    assign o_freeze_trace      = r_freeze_trace;
    assign o_soft_reset_pulse  = r_soft_reset_pulse;

    assign o_timer_clear_pulse    = r_timer_clear_pulse;

    // a7ddrphy calibration CSR bus. adr/dat_w held from the passthrough
    // registers; we pulses one cycle on a CTRL write (firmware leveling).
    assign o_phy_csr_adr   = r_phy_csr_addr;
    assign o_phy_csr_dat_w = r_phy_csr_wdata;
    assign o_phy_csr_we    = r_phy_csr_we_pulse;
    assign o_timer_expected_beats = r_timer_expected_beats;
    assign o_rd_resp_delay_cyc    = r_rd_resp_delay_cyc;
    assign o_wr_resp_delay_cyc    = r_wr_resp_delay_cyc;

    // Perf outputs: clear ganged to CTRL.clear_stats pulse; freeze ganged
    // to CTRL.freeze_trace. Hist selector splits into per-side signals.
    assign o_perf_clear       = r_clear_stats_pulse;
    assign o_perf_freeze      = r_freeze_trace;
    assign o_obs_hist_bus_sel = r_obs_hist_sel[0];
    assign o_obs_hist_metric  = r_obs_hist_sel[1];
    assign o_obs_hist_bin     = r_obs_hist_sel[5:2];

    // Controller runtime cfg unpack
    // r_ctrlr_cfg: [0]memtype [15:8]t_phy_wrlat [23:16]t_rddata_en [24]rd_in_order
    assign o_memtype           = memtype_e'(r_ctrlr_cfg[0]);
    assign o_t_phy_wrlat       = r_ctrlr_cfg[15:8];
    assign o_t_rddata_en       = r_ctrlr_cfg[23:16];
    assign o_rd_in_order       = r_ctrlr_cfg[24];
    // r_ctrlr_cap: [3:0]cap_lookahead_max [7:4]cap_synth_mask
    assign o_cap_lookahead_max = r_ctrlr_cap[3:0];
    assign o_cap_synth_mask    = r_ctrlr_cap[7:4];
    assign o_cmd_delay         = r_dfi_tuning[3:0];
    assign o_rddata_delay      = r_dfi_tuning[7:4];

    // WR-engine cfg unpack
    assign o_cfg_wr_start_addr  = r_wr_start_addr[AW-1:0];
    assign o_cfg_wr_stride_0    = r_wr_stride_0[STRIDE_WIDTH-1:0];
    assign o_cfg_wr_stride_1    = r_wr_stride_1[STRIDE_WIDTH-1:0];
    assign o_cfg_wr_wrap_mask_0 = r_wr_wrap_mask_0[AW-1:0];
    assign o_cfg_wr_wrap_mask_1 = r_wr_wrap_mask_1[AW-1:0];
    assign o_cfg_wr_burst_len   = r_wr_blen_txn[BURST_LEN_WIDTH-1:0];
    assign o_cfg_wr_txn_count   = r_wr_blen_txn[TXN_COUNT_WIDTH+7:8];
    assign o_cfg_wr_gap         = r_wr_blen_txn[27:24];
    assign o_cfg_wr_axi_id      = r_wr_axi_attr[AXI_ID_WIDTH-1:0];
    assign o_cfg_wr_id_mode     = r_wr_axi_attr[9:8];
    assign o_cfg_wr_axi_size    = r_wr_axi_attr[12:10];
    assign o_cfg_wr_axi_burst   = r_wr_axi_attr[14:13];
    assign o_cfg_wr_data_mode   = r_wr_axi_attr[15];
    assign o_cfg_wr_lfsr_seed   = r_wr_lfsr_seed;
    assign o_cfg_wr_hash_seed0  = r_wr_hash_seed0;
    assign o_cfg_wr_hash_seed1  = r_wr_hash_seed1;
    assign o_cfg_wr_hash_seed2  = r_wr_hash_seed2;

    // RD-engine cfg unpack
    assign o_cfg_rd_start_addr  = r_rd_start_addr[AW-1:0];
    assign o_cfg_rd_stride_0    = r_rd_stride_0[STRIDE_WIDTH-1:0];
    assign o_cfg_rd_stride_1    = r_rd_stride_1[STRIDE_WIDTH-1:0];
    assign o_cfg_rd_wrap_mask_0 = r_rd_wrap_mask_0[AW-1:0];
    assign o_cfg_rd_wrap_mask_1 = r_rd_wrap_mask_1[AW-1:0];
    assign o_cfg_rd_burst_len   = r_rd_blen_txn[BURST_LEN_WIDTH-1:0];
    assign o_cfg_rd_txn_count   = r_rd_blen_txn[TXN_COUNT_WIDTH+7:8];
    assign o_cfg_rd_gap         = r_rd_blen_txn[27:24];
    assign o_cfg_rd_axi_id      = r_rd_axi_attr[AXI_ID_WIDTH-1:0];
    assign o_cfg_rd_id_mode     = r_rd_axi_attr[9:8];
    assign o_cfg_rd_axi_size    = r_rd_axi_attr[12:10];
    assign o_cfg_rd_axi_burst   = r_rd_axi_attr[14:13];
    assign o_cfg_rd_data_mode   = r_rd_axi_attr[15];
    assign o_cfg_rd_lfsr_seed   = r_rd_lfsr_seed;
    assign o_cfg_rd_hash_seed0  = r_rd_hash_seed0;
    assign o_cfg_rd_hash_seed1  = r_rd_hash_seed1;
    assign o_cfg_rd_hash_seed2  = r_rd_hash_seed2;

    // Prevent unused signal warnings
    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0, int_awprot, int_wstrb, int_arprot, 1'b0};
    /* verilator lint_on UNUSED */

endmodule : harness_csr
