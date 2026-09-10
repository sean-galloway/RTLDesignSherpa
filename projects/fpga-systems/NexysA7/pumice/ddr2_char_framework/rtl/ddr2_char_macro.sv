// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ddr2_char_macro
// Purpose: Single instantiation point binding the master-side AXI4
//          characterization engines to the pumice memory controller.
//          The macro hides all the AXI plumbing between the engines and
//          the controller's s_axi port so the bench just programs cfg
//          ports + drives DFI + APB to exercise the full path.
//
// Documentation: projects/fpga-systems/NexysA7/shared/README.md
// Subsystem: fpga-systems/NexysA7/shared
//
// Author: sean galloway
// Created: 2026-06-25

`timescale 1ns / 1ps

`include "reset_defs.svh"

//==============================================================================
// Module: ddr2_char_macro
//==============================================================================
// Description:
//   Wraps the three blocks that form the bring-up + characterization loop:
//
//     axi4_master_wr_pattern_gen  →┐
//                                  ├→  pumice_top  →  DFI (external)
//     axi4_master_rd_crc_check    →┘
//
//   The writer drives s_axi AW/W and receives B from the controller; the
//   reader drives s_axi AR and receives R. Both engines share the same
//   mc_clk / mc_rst_n domain as the controller. APB CSR, DFI, and the
//   runtime control inputs (memtype, t_phy_wrlat, ...) are passed
//   straight through so the bench can drive them with existing BFMs:
//
//     - APB: programmed via the standard APBMaster BFM
//     - DFI: terminated by dfi_slave_phy (DV repo BFM)
//
//   Both engines' cfg ports are exposed individually (no shared bundle)
//   so the bench can sweep writer and reader workloads independently.
//==============================================================================
module ddr2_char_macro
    import pumice_pkg::*;
#(
    // ---- AXI4 ----
    parameter int AXI_ADDR_WIDTH   = 32,
    parameter int AXI_DATA_WIDTH   = 64,
    // AXI_ID_WIDTH=8 to match the pattern-gen engines' internal 8-bit LFSR
    // for the ID-picker (axi4_master_wr_pattern_gen slices cfg_axi_id[7:0]
    // for the LFSR seed; narrower ID widths cause a synth part-select
    // error). Same width stream_top_ch8 uses for its native AXI_ID_WIDTH.
    parameter int AXI_ID_WIDTH     = 8,
    parameter int AXI_USER_WIDTH   = 8,
    parameter int AXI_STRB_WIDTH   = AXI_DATA_WIDTH / 8,
    parameter int BURST_LEN_WIDTH  = 8,

    // ---- APB CSR ----
    parameter int APB_ADDR_WIDTH   = 12,
    parameter int APB_DATA_WIDTH   = 32,
    parameter int APB_STRB_WIDTH   = APB_DATA_WIDTH / 8,
    parameter int APB_PROT_WIDTH   = 3,

    // ---- DRAM topology ----
    parameter int NUM_RANKS        = 1,
    parameter int NUM_BANKS        = 8,
    // ROW_WIDTH = chip row-address bits. Nexys A7 DDR2 (MT47H64M16, 1Gb x16)
    // has 13 row bits (A0-A12). Default 13 so the controller never issues a
    // row address the chip can't decode (14 would alias/wrap into rows 0..8191).
    // Propagates to pumice_top and sizes DFI_ADDR_BUS_W = ROW_WIDTH*DFI_RATE.
    parameter int ROW_WIDTH        = 13,
    parameter int COL_WIDTH        = 10,

    // ---- Controller depths ----
    parameter int WR_CAM_DEPTH     = 16,
    parameter int RD_CAM_DEPTH     = 16,
    // Reads in flight (pumice_rd_return_ring ticket space). The sustained read
    // rate cannot exceed RD_RET_DEPTH / (alloc-to-R-drain latency), so on a
    // board with a long PHY read latency this is a direct bandwidth knob. It
    // was NOT threaded through here until 2026-09-10, so every board build ran
    // the controller default whatever this file said.
    parameter int RD_RET_DEPTH     = 32,
    parameter int W_BUF_DEPTH      = 128,

    // ---- DFI ----
    parameter int DFI_RATE         = 2,
    parameter int DRAM_BEAT_WIDTH  = AXI_DATA_WIDTH,
    // Physical DRAM device x-width (Nexys A7 MT47H64M16 => 16). Scales the
    // JEDEC burst length to pumice-beat units in pumice_core_macro so a x16
    // BL4 = 2 pumice beats = 1 DFI cycle. Default = DRAM_BEAT_WIDTH (ratio 1).
    parameter int DRAM_DEVICE_WIDTH = DRAM_BEAT_WIDTH,
    // TASK-GEAR: DRAM strobe tracks the DRAM beat (not AXI). With beat < AXI
    // (GEAR>1) these differ; defaulting to AXI_STRB_WIDTH left the DFI mask
    // width stuck at the AXI value when DRAM_BEAT_WIDTH was overridden.
    parameter int DRAM_STRB_WIDTH  = DRAM_BEAT_WIDTH / 8,
    parameter int DFI_DATA_WIDTH   = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DFI_STRB_WIDTH   = DRAM_STRB_WIDTH * DFI_RATE,
    parameter int DFI_EN_WIDTH     = DFI_RATE,
    parameter int DFI_VALID_WIDTH  = DFI_RATE,
    parameter int DFI_ADDR_BUS_W   = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W   = $clog2(NUM_BANKS) * DFI_RATE,
    parameter int DFI_CTRL_BUS_W   = 1 * DFI_RATE,
    parameter int DFI_CS_BUS_W     = NUM_RANKS * DFI_RATE,

    // ---- Controller policy ----
    parameter int PAGE_POLICY      = 32'(PAGE_POLICY_CLOSE),
    // DRAM burst length (JEDEC MR0), in DRAM beats. The controller divides this
    // by DFI_RATE internally to get AXI beats per burst. BL8 at nphases=4/x16:
    // a BL8 read = 8 device-words = one FULL 128b DFI word in one 8-slot PHY
    // event, so the read aligner's grab-all captures the whole word cleanly.
    // BL4 filled only 4 of 8 slots (half stale) -> the on-silicon read-fail
    // root cause. N_SUBCMD collapses to 1 at BL8 (no sub-word packing).
    parameter int DRAM_BL          = 8,

    // Legal-AxLEN quantum for the pattern generators: cfg_wr/rd_burst_len must be
    // a nonzero integer multiple of this (one AXI burst -> integer DRAM bursts).
    // = AXI beats per DRAM burst = DRAM_BL*DRAM_DEVICE_WIDTH/AXI_DATA_WIDTH. 1 =
    // unconstrained (DEFAULT — the DV engine sweeps burst_len 1/2/4/8 for
    // coverage). Real projects (e.g. the board top) set the computed value so a
    // SW BLEN_TXN misconfig fails loud instead of silently SLVERR/partial-write.
    parameter int BURST_LEN_MULTIPLE = 1,

    // ---- Generator array ----
    // Concurrent traffic generators per direction. TWO -- the first rung of a
    // ladder that climbs to four and, on a larger part, to eight. Two 2x1 AXI4
    // crossbars (one per direction) merge the two generators onto pumice's
    // single s_axi so the controller sees genuine multi-master contention,
    // which a single directly-wired stream never could. This is the stress
    // step that proves the microarchitecture; growing it is an array bound, a
    // parameter and a bridge-config regen, not an address-map migration.
    //
    // Not one per bank: eight of each was the intent and does not fit the
    // XC7A100T (66470 LUTs against 63400; placement short by 1469 slices).
    // Four fit at 77% LUTs / 47% DSPs. Two sit further below the fit ceiling
    // and prove multi-master behaviour with the most routing and timing
    // headroom before the ladder climbs.
    //
    // NUM_GEN <= NUM_BANKS is the invariant, not equality. Each generator is
    // expected to SPAN NUM_BANKS/NUM_GEN banks -- four, here -- so two
    // generators keep all eight banks busy. One generator per bank would have
    // left half the device idle, which is the corner the array exists to
    // provoke in the first place.
    //
    // The span is an ADDRESS PATTERN, not hardware: the host gives each
    // generator a wrap window covering that many banks. Nothing here can
    // enforce it, because the bank field's position is pumice's runtime
    // ADDR_MAP.bank_lsb, so the host asserts the mapping and reads the
    // compiled count back from GEN_CONFIG.
    parameter int NUM_GEN          = 2,
    // per-generator bursts in flight (AW/AR issued minus B/RLAST received)
    parameter int GEN_MAX_OUTSTANDING = 8,

    // ---- Engine workload ranges ----
    parameter int TXN_COUNT_WIDTH  = 16,
    parameter int INDEX_WIDTH      = 16,
    parameter int STRIDE_WIDTH     = 24,

    // ---- Reader-engine debug FIFO depth (0 = elide; >0 = capture
    //      every R beat's (actual, expected, mismatch) into a gaxi
    //      fifo the bench can drain) ----
    parameter int RD_DBG_FIFO_DEPTH = 0,

    // ---- Aliases ----
    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH,
    parameter int SW = AXI_STRB_WIDTH
) (
    //=========================================================================
    // Clocks + resets
    //=========================================================================
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,
    input  logic                       pclk,
    input  logic                       presetn,

    //=========================================================================
    // APB CSR -> the generator config block (chargen_regs)
    //
    // The engines' cfg_* ports are GONE. There are sixteen of them now -- eight
    // writers and eight readers, one per DRAM bank -- and a per-engine port
    // surface would have been about six hundred wires for whoever instantiates
    // this to drive. Config lives in chargen_regs behind this window instead
    // (rtl/chargen_regs.rdl, bridge slave chargen_apb at 0x000A0000), so the
    // harness is reduced to routing one APB slave.
    //
    // Status comes back the same way -- per-generator STATUS/CRC registers plus
    // the DONE and ERRORS roll-ups -- rather than as output pins.
    //=========================================================================
    input  logic                       s_chargen_apb_PSEL,
    input  logic                       s_chargen_apb_PENABLE,
    output logic                       s_chargen_apb_PREADY,
    input  logic [APB_ADDR_WIDTH-1:0]  s_chargen_apb_PADDR,
    input  logic                       s_chargen_apb_PWRITE,
    input  logic [APB_DATA_WIDTH-1:0]  s_chargen_apb_PWDATA,
    input  logic [APB_STRB_WIDTH-1:0]  s_chargen_apb_PSTRB,
    input  logic [APB_PROT_WIDTH-1:0]  s_chargen_apb_PPROT,
    output logic [APB_DATA_WIDTH-1:0]  s_chargen_apb_PRDATA,
    output logic                       s_chargen_apb_PSLVERR,

    //=========================================================================
    // Run-level aggregate status (for the harness timer + harness_csr)
    //=========================================================================
    // Per-generator detail lives in chargen_regs and the host reads it there.
    // What the HARNESS needs is different and much smaller: when did the run
    // start, when is it over, and did anything go wrong -- because that is what
    // the measurement window is bracketed by and what the pass/fail LED shows.
    //
    // "Done" is over the generators that were actually LAUNCHED, not all of
    // them. A sweep that starts four writers must not wait forever on four it
    // deliberately left idle, and an AND over all sixteen would do exactly that.
    output logic                       gen_wr_started,
    output logic                       gen_rd_started,
    output logic                       gen_wr_done,
    output logic                       gen_rd_done,
    output logic                       gen_any_error,
    // Data integrity across the whole run, in one bit, so the board's pass
    // indicator still means something. See the aggregation below for the
    // pairing convention it assumes.
    output logic                       gen_crc_match,

    //=========================================================================
    // APB CSR → controller
    //=========================================================================
    input  logic                       s_apb_PSEL,
    input  logic                       s_apb_PENABLE,
    output logic                       s_apb_PREADY,
    input  logic [APB_ADDR_WIDTH-1:0]  s_apb_PADDR,
    input  logic                       s_apb_PWRITE,
    input  logic [APB_DATA_WIDTH-1:0]  s_apb_PWDATA,
    input  logic [APB_STRB_WIDTH-1:0]  s_apb_PSTRB,
    input  logic [APB_PROT_WIDTH-1:0]  s_apb_PPROT,
    output logic [APB_DATA_WIDTH-1:0]  s_apb_PRDATA,
    output logic                       s_apb_PSLVERR,

    //=========================================================================
    // DFI passthrough (terminated by dfi_slave_phy in the bench)
    //=========================================================================
    output logic [DFI_ADDR_BUS_W-1:0]  dfi_address_o,
    output logic [DFI_BANK_BUS_W-1:0]  dfi_bank_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_cas_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_ras_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_we_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_cs_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_cke_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_odt_o,
    output logic [DFI_DATA_WIDTH-1:0]  dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]  dfi_wrdata_mask_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]  dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0] dfi_rddata_valid_i,
    output logic [DFI_CS_BUS_W-1:0]    dfi_dram_clk_disable_o,
    output logic                       dfi_init_start_o,
    input  logic                       dfi_init_complete_i,
    output logic                       dfi_ctrlupd_req_o,
    input  logic                       dfi_ctrlupd_ack_i,
    input  logic                       dfi_phyupd_req_i,
    output logic                       dfi_phyupd_ack_o,
    input  logic [1:0]                 dfi_phyupd_type_i,

    //=========================================================================
    // Runtime controls (carry parameters not yet in CSR map)
    //=========================================================================
    input  memtype_e                   memtype_i,
    input  logic [7:0]                 t_phy_wrlat_i,
    input  logic [7:0]                 t_rddata_en_i,
    input  logic                       rd_in_order_i,
    input  logic [3:0]                 cap_lookahead_max_i,
    input  logic [3:0]                 cap_synth_mask_i,

    //=========================================================================
    // Reader-engine debug FIFO drain port. Only meaningful when
    // RD_DBG_FIFO_DEPTH > 0. Tied off internally otherwise.
    //=========================================================================
    output logic                       rd_dbg_valid,
    input  logic                       rd_dbg_ready,
    output logic [DW-1:0]              rd_dbg_actual,
    output logic [DW-1:0]              rd_dbg_expected,
    output logic                       rd_dbg_mismatch,

    //-------------------------------------------------------------------------
    // Perf observability (bus meters + latency histograms tapped on the
    // internal AXI wires between the WR/RD engines and the controller's
    // s_axi port). Both meters watch the data-channel handshake
    // (W for WR, R for RD) since that's the throughput surface.
    //-------------------------------------------------------------------------
    input  logic                       perf_clear,
    input  logic                       perf_freeze,
    output logic [31:0]                perf_wr_prod,
    output logic [31:0]                perf_wr_bp,
    output logic [31:0]                perf_wr_starv,
    output logic [31:0]                perf_wr_idle,
    output logic [31:0]                perf_rd_prod,
    output logic [31:0]                perf_rd_bp,
    output logic [31:0]                perf_rd_starv,
    output logic [31:0]                perf_rd_idle,
    // Indexed histogram readback. i_hist_metric bit 0 (RD) picks
    // 0=AR->firstR, 1=AR->RLAST. WR side is single-metric (AW->B).
    input  logic                       i_hist_metric,
    input  logic [3:0]                 i_hist_bin,
    output logic [31:0]                perf_wr_hist_count,
    output logic [31:0]                perf_wr_hist_total,
    output logic [31:0]                perf_rd_hist_count,
    output logic [31:0]                perf_rd_hist_total
);

    //=========================================================================
    // Engines, generator config and perf -- the DUT-agnostic half.
    //=========================================================================
    // Extracted to char_engine_block on 2026-09-10 so the LiteDRAM comparison
    // flow drives its controller from the SAME engines, config registers and
    // perf taps. Two copies of this spine is exactly how the LiteDRAM harness
    // drifted onto a harness_csr port list that no longer existed.
    logic [IW-1:0] wr_awid;    logic [AW-1:0] wr_awaddr;
    logic [7:0]    wr_awlen;   logic [2:0]    wr_awsize;
    logic [1:0]    wr_awburst; logic          wr_awlock;
    logic [3:0]    wr_awcache, wr_awqos, wr_awregion;
    logic [2:0]    wr_awprot;  logic [UW-1:0] wr_awuser, wr_wuser;
    logic          wr_awvalid, wr_awready;
    logic [DW-1:0] wr_wdata;   logic [SW-1:0] wr_wstrb;
    logic          wr_wlast, wr_wvalid, wr_wready;
    logic [IW-1:0] wr_bid;     logic [1:0]    wr_bresp;
    logic [UW-1:0] wr_buser;   logic          wr_bvalid, wr_bready;

    logic [IW-1:0] rd_arid;    logic [AW-1:0] rd_araddr;
    logic [7:0]    rd_arlen;   logic [2:0]    rd_arsize;
    logic [1:0]    rd_arburst; logic          rd_arlock;
    logic [3:0]    rd_arcache, rd_arqos, rd_arregion;
    logic [2:0]    rd_arprot;  logic [UW-1:0] rd_aruser, rd_ruser;
    logic          rd_arvalid, rd_arready;
    logic [IW-1:0] rd_rid;     logic [DW-1:0] rd_rdata;
    logic [1:0]    rd_rresp;   logic          rd_rlast, rd_rvalid, rd_rready;

    char_engine_block #(
        .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH       (AXI_ID_WIDTH),
        .AXI_USER_WIDTH     (AXI_USER_WIDTH),
        .AXI_STRB_WIDTH     (AXI_STRB_WIDTH),
        .BURST_LEN_WIDTH    (BURST_LEN_WIDTH),
        .BURST_LEN_MULTIPLE (BURST_LEN_MULTIPLE),
        .APB_ADDR_WIDTH     (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH     (APB_DATA_WIDTH),
        .APB_STRB_WIDTH     (APB_STRB_WIDTH),
        .APB_PROT_WIDTH     (APB_PROT_WIDTH),
        .NUM_BANKS          (NUM_BANKS),
        .NUM_GEN            (NUM_GEN),
        .GEN_MAX_OUTSTANDING(GEN_MAX_OUTSTANDING),
        .TXN_COUNT_WIDTH    (TXN_COUNT_WIDTH),
        .INDEX_WIDTH        (INDEX_WIDTH),
        .STRIDE_WIDTH       (STRIDE_WIDTH),
        .RD_DBG_FIFO_DEPTH  (RD_DBG_FIFO_DEPTH)
    ) u_engines (
        .mc_clk (mc_clk), .mc_rst_n (mc_rst_n),
        .pclk   (pclk),   .presetn  (presetn),

        .s_chargen_apb_PSEL   (s_chargen_apb_PSEL),
        .s_chargen_apb_PENABLE(s_chargen_apb_PENABLE),
        .s_chargen_apb_PREADY (s_chargen_apb_PREADY),
        .s_chargen_apb_PADDR  (s_chargen_apb_PADDR),
        .s_chargen_apb_PWRITE (s_chargen_apb_PWRITE),
        .s_chargen_apb_PWDATA (s_chargen_apb_PWDATA),
        .s_chargen_apb_PSTRB  (s_chargen_apb_PSTRB),
        .s_chargen_apb_PPROT  (s_chargen_apb_PPROT),
        .s_chargen_apb_PRDATA (s_chargen_apb_PRDATA),
        .s_chargen_apb_PSLVERR(s_chargen_apb_PSLVERR),

        .gen_wr_started (gen_wr_started),
        .gen_rd_started (gen_rd_started),
        .gen_wr_done    (gen_wr_done),
        .gen_rd_done    (gen_rd_done),
        .gen_any_error  (gen_any_error),
        .gen_crc_match  (gen_crc_match),

        .rd_dbg_valid   (rd_dbg_valid),
        .rd_dbg_ready   (rd_dbg_ready),
        .rd_dbg_actual  (rd_dbg_actual),
        .rd_dbg_expected(rd_dbg_expected),
        .rd_dbg_mismatch(rd_dbg_mismatch),

        .perf_clear     (perf_clear),
        .perf_freeze    (perf_freeze),
        .perf_wr_prod   (perf_wr_prod),
        .perf_wr_bp     (perf_wr_bp),
        .perf_wr_starv  (perf_wr_starv),
        .perf_wr_idle   (perf_wr_idle),
        .perf_rd_prod   (perf_rd_prod),
        .perf_rd_bp     (perf_rd_bp),
        .perf_rd_starv  (perf_rd_starv),
        .perf_rd_idle   (perf_rd_idle),
        .i_hist_metric  (i_hist_metric),
        .i_hist_bin     (i_hist_bin),
        .perf_wr_hist_count(perf_wr_hist_count),
        .perf_wr_hist_total(perf_wr_hist_total),
        .perf_rd_hist_count(perf_rd_hist_count),
        .perf_rd_hist_total(perf_rd_hist_total),

        .m_axi_awid   (wr_awid),   .m_axi_awaddr (wr_awaddr),
        .m_axi_awlen  (wr_awlen),  .m_axi_awsize (wr_awsize),
        .m_axi_awburst(wr_awburst),.m_axi_awlock (wr_awlock),
        .m_axi_awcache(wr_awcache),.m_axi_awprot (wr_awprot),
        .m_axi_awqos  (wr_awqos),  .m_axi_awregion(wr_awregion),
        .m_axi_awuser (wr_awuser), .m_axi_awvalid(wr_awvalid),
        .m_axi_awready(wr_awready),
        .m_axi_wdata  (wr_wdata),  .m_axi_wstrb  (wr_wstrb),
        .m_axi_wlast  (wr_wlast),  .m_axi_wuser  (wr_wuser),
        .m_axi_wvalid (wr_wvalid), .m_axi_wready (wr_wready),
        .m_axi_bid    (wr_bid),    .m_axi_bresp  (wr_bresp),
        .m_axi_buser  (wr_buser),  .m_axi_bvalid (wr_bvalid),
        .m_axi_bready (wr_bready),

        .m_axi_arid   (rd_arid),   .m_axi_araddr (rd_araddr),
        .m_axi_arlen  (rd_arlen),  .m_axi_arsize (rd_arsize),
        .m_axi_arburst(rd_arburst),.m_axi_arlock (rd_arlock),
        .m_axi_arcache(rd_arcache),.m_axi_arprot (rd_arprot),
        .m_axi_arqos  (rd_arqos),  .m_axi_arregion(rd_arregion),
        .m_axi_aruser (rd_aruser), .m_axi_arvalid(rd_arvalid),
        .m_axi_arready(rd_arready),
        .m_axi_rid    (rd_rid),    .m_axi_rdata  (rd_rdata),
        .m_axi_rresp  (rd_rresp),  .m_axi_rlast  (rd_rlast),
        .m_axi_ruser  (rd_ruser),  .m_axi_rvalid (rd_rvalid),
        .m_axi_rready (rd_rready)
    );

    //=========================================================================
    // pumice controller
    //=========================================================================
    // -------------------------------------------------------------------------
    // Config path: the macro's APB CSR port is adapted to the rearchitected
    // controller's PeakRDL passthrough ("cpuif") register interface. Software
    // programs memtype / timings / DFI phase / ADDR_MAP by name through this
    // window (the retired extern cfg inputs below are no longer wired into the
    // controller — config is CSR-driven). Mirrors the STREAM stream_apb path.
    // -------------------------------------------------------------------------
    logic                        ctrl_cpuif_req, ctrl_cpuif_req_is_wr;
    logic [APB_ADDR_WIDTH-1:0]   ctrl_cpuif_addr;
    logic [APB_DATA_WIDTH-1:0]   ctrl_cpuif_wr_data, ctrl_cpuif_wr_biten;
    logic                        ctrl_cpuif_req_stall_wr, ctrl_cpuif_req_stall_rd;
    logic                        ctrl_cpuif_rd_ack, ctrl_cpuif_rd_err;
    logic [APB_DATA_WIDTH-1:0]   ctrl_cpuif_rd_data;
    logic                        ctrl_cpuif_wr_ack, ctrl_cpuif_wr_err;

    apb4_to_peakrdl #(
        .ADDR_WIDTH (APB_ADDR_WIDTH),
        .DATA_WIDTH (APB_DATA_WIDTH),
        .PROT_WIDTH (APB_PROT_WIDTH)
    ) u_csr_shim (
        .aclk        (mc_clk),   .aresetn (mc_rst_n),
        .pclk        (pclk),     .presetn (presetn),
        .s_apb_PSEL  (s_apb_PSEL),   .s_apb_PENABLE(s_apb_PENABLE),
        .s_apb_PREADY(s_apb_PREADY), .s_apb_PADDR  (s_apb_PADDR),
        .s_apb_PWRITE(s_apb_PWRITE), .s_apb_PWDATA (s_apb_PWDATA),
        .s_apb_PSTRB (s_apb_PSTRB),  .s_apb_PPROT  (s_apb_PPROT),
        .s_apb_PRDATA(s_apb_PRDATA), .s_apb_PSLVERR(s_apb_PSLVERR),
        .cpuif_req         (ctrl_cpuif_req),
        .cpuif_req_is_wr   (ctrl_cpuif_req_is_wr),
        .cpuif_addr        (ctrl_cpuif_addr),
        .cpuif_wr_data     (ctrl_cpuif_wr_data),
        .cpuif_wr_biten    (ctrl_cpuif_wr_biten),
        .cpuif_req_stall_wr(ctrl_cpuif_req_stall_wr),
        .cpuif_req_stall_rd(ctrl_cpuif_req_stall_rd),
        .cpuif_rd_ack      (ctrl_cpuif_rd_ack),
        .cpuif_rd_err      (ctrl_cpuif_rd_err),
        .cpuif_rd_data     (ctrl_cpuif_rd_data),
        .cpuif_wr_ack      (ctrl_cpuif_wr_ack),
        .cpuif_wr_err      (ctrl_cpuif_wr_err)
    );

    // Retired DFI sideband pins — the rearchitected controller does not drive
    // these. Present sane constants so the harness / DFI BFM interface is
    // unchanged: CKE held active, clock enabled, no ctrlupd / phyupd.
    assign dfi_cke_o              = '1;
    assign dfi_dram_clk_disable_o = '0;
    assign dfi_ctrlupd_req_o      = 1'b0;
    assign dfi_phyupd_ack_o       = 1'b0;

    // Host AXI is AXI_DATA_WIDTH (64); the controller core + DFI run at
    // DRAM_BEAT_WIDTH*DFI_RATE. pumice_top_geared bridges the two host<->core
    // widths with the formal AXI dwidth converters.
    pumice_top_geared #(
        .HOST_AXI_DATA_WIDTH (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
        .NUM_RANKS       (NUM_RANKS),
        .NUM_BANKS       (NUM_BANKS),
        .ROW_WIDTH       (ROW_WIDTH),
        .COL_WIDTH       (COL_WIDTH),
        .DFI_RATE        (DFI_RATE),
        .DRAM_BEAT_WIDTH (DRAM_BEAT_WIDTH),
        .DRAM_DEVICE_WIDTH (DRAM_DEVICE_WIDTH),
        .DRAM_BL         (DRAM_BL),
        .NUM_ENTRIES     (WR_CAM_DEPTH),
        .N_SRAM_SLOTS    (WR_CAM_DEPTH),
        .RD_RET_DEPTH    (RD_RET_DEPTH),
        .CSR_ADDR_W      (APB_ADDR_WIDTH)
    ) u_ctrl (
        .aclk                  (mc_clk),
        .aresetn               (mc_rst_n),
        .dfi_clk               (mc_clk),
        .dfi_rstn              (mc_rst_n),
        // Register cpuif (from the APB->cpuif shim)
        .s_cpuif_req           (ctrl_cpuif_req),
        .s_cpuif_req_is_wr     (ctrl_cpuif_req_is_wr),
        .s_cpuif_addr          (ctrl_cpuif_addr),
        .s_cpuif_wr_data       (ctrl_cpuif_wr_data),
        .s_cpuif_wr_biten      (ctrl_cpuif_wr_biten),
        .s_cpuif_req_stall_wr  (ctrl_cpuif_req_stall_wr),
        .s_cpuif_req_stall_rd  (ctrl_cpuif_req_stall_rd),
        .s_cpuif_rd_ack        (ctrl_cpuif_rd_ack),
        .s_cpuif_rd_err        (ctrl_cpuif_rd_err),
        .s_cpuif_rd_data       (ctrl_cpuif_rd_data),
        .s_cpuif_wr_ack        (ctrl_cpuif_wr_ack),
        .s_cpuif_wr_err        (ctrl_cpuif_wr_err),
        .init_done_o           (),
        // AXI — writer drives the W half, reader drives the R half
        .s_axi_awid            (wr_awid),
        .s_axi_awaddr          (wr_awaddr),
        .s_axi_awlen           (wr_awlen),
        .s_axi_awsize          (wr_awsize),
        .s_axi_awburst         (wr_awburst),
        .s_axi_awlock          (wr_awlock),
        .s_axi_awcache         (wr_awcache),
        .s_axi_awprot          (wr_awprot),
        .s_axi_awqos           (wr_awqos),
        .s_axi_awregion        (wr_awregion),
        .s_axi_awuser          (wr_awuser),
        .s_axi_awvalid         (wr_awvalid),
        .s_axi_awready         (wr_awready),
        .s_axi_wdata           (wr_wdata),
        .s_axi_wstrb           (wr_wstrb),
        .s_axi_wlast           (wr_wlast),
        .s_axi_wuser           (wr_wuser),
        .s_axi_wvalid          (wr_wvalid),
        .s_axi_wready          (wr_wready),
        .s_axi_bid             (wr_bid),
        .s_axi_bresp           (wr_bresp),
        .s_axi_buser           (wr_buser),
        .s_axi_bvalid          (wr_bvalid),
        .s_axi_bready          (wr_bready),
        .s_axi_arid            (rd_arid),
        .s_axi_araddr          (rd_araddr),
        .s_axi_arlen           (rd_arlen),
        .s_axi_arsize          (rd_arsize),
        .s_axi_arburst         (rd_arburst),
        .s_axi_arlock          (rd_arlock),
        .s_axi_arcache         (rd_arcache),
        .s_axi_arprot          (rd_arprot),
        .s_axi_arqos           (rd_arqos),
        .s_axi_arregion        (rd_arregion),
        .s_axi_aruser          (rd_aruser),
        .s_axi_arvalid         (rd_arvalid),
        .s_axi_arready         (rd_arready),
        .s_axi_rid             (rd_rid),
        .s_axi_rdata           (rd_rdata),
        .s_axi_rresp           (rd_rresp),
        .s_axi_rlast           (rd_rlast),
        .s_axi_ruser           (rd_ruser),
        .s_axi_rvalid          (rd_rvalid),
        .s_axi_rready          (rd_rready),
        // DFI 2.1 pin bus (the retired cke / dram_clk_disable / ctrlupd /
        // phyupd sidebands are tied off above; the geared top has no such pins)
        .dfi_address_o         (dfi_address_o),
        .dfi_bank_o            (dfi_bank_o),
        .dfi_cas_n_o           (dfi_cas_n_o),
        .dfi_ras_n_o           (dfi_ras_n_o),
        .dfi_we_n_o            (dfi_we_n_o),
        .dfi_cs_n_o            (dfi_cs_n_o),
        .dfi_odt_o             (dfi_odt_o),
        .dfi_wrdata_o          (dfi_wrdata_o),
        .dfi_wrdata_en_o       (dfi_wrdata_en_o),
        .dfi_wrdata_mask_o     (dfi_wrdata_mask_o),
        .dfi_rddata_en_o       (dfi_rddata_en_o),
        .dfi_rddata_i          (dfi_rddata_i),
        .dfi_rddata_valid_i    (dfi_rddata_valid_i),
        .dfi_init_start_o      (dfi_init_start_o),
        .dfi_init_complete_i   (dfi_init_complete_i)
    );
endmodule : ddr2_char_macro
