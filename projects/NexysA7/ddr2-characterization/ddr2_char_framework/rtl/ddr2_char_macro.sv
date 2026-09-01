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
// Documentation: projects/NexysA7/ddr2-characterization/README.md
// Subsystem: NexysA7/ddr2-characterization
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
    // Concurrent traffic generators per direction. ONE. The array went 8 -> 4
    // -> 2 -> 1 chasing timing, and the 2+2 build settled the question: it did
    // NOT close (-7.339 ns vs -7.732 at 4+4), so generator count was never the
    // limiter. The binding constraint is SLICE OCCUPANCY, not LUTs -- 2+2 sat
    // at 66% LUTs but 91.5% slices, leaving the placer nowhere to put anything
    // close together, and 81% of every failing path was wire delay.
    //
    // With one of each the two 8x1 crossbars are gone entirely and the writer
    // and reader drive pumice's AXI slave port directly. Not one per bank:
    // eight of each was the intent and does not fit the XC7A100T (66470 LUTs
    // against 63400; placement short by 1469 slices). Four fits with routing
    // and timing margin and still provokes bank concurrency, which one stream
    // never could.
    //
    // NUM_GEN <= NUM_BANKS is the invariant, not equality. Each generator is
    // expected to SPAN NUM_BANKS/NUM_GEN banks -- two, here -- so four
    // generators keep all eight banks busy. One generator per bank would have
    // left half the device idle, which is the corner the array exists to
    // provoke in the first place.
    //
    // The span is an ADDRESS PATTERN, not hardware: the host gives each
    // generator a wrap window covering that many banks. Nothing here can
    // enforce it, because the bank field's position is pumice's runtime
    // ADDR_MAP.bank_lsb, so the host asserts the mapping and reads the
    // compiled count back from GEN_CONFIG.
    parameter int NUM_GEN          = 1,

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
    // Internal AXI nets — writer drives AW/W, reader drives AR, both
    // share s_axi at the controller's slave port.
    //=========================================================================
    logic [IW-1:0] wr_awid;
    logic [AW-1:0] wr_awaddr;
    logic [7:0]    wr_awlen;
    logic [2:0]    wr_awsize;
    logic [1:0]    wr_awburst;
    logic          wr_awlock;
    logic [3:0]    wr_awcache, wr_awqos, wr_awregion;
    logic [2:0]    wr_awprot;
    logic [UW-1:0] wr_awuser, wr_wuser;
    logic          wr_awvalid, wr_awready;
    logic [DW-1:0] wr_wdata;
    logic [SW-1:0] wr_wstrb;
    logic          wr_wlast, wr_wvalid, wr_wready;
    logic [IW-1:0] wr_bid;
    logic [1:0]    wr_bresp;
    logic [UW-1:0] wr_buser;
    logic          wr_bvalid, wr_bready;

    logic [IW-1:0] rd_arid;
    logic [AW-1:0] rd_araddr;
    logic [7:0]    rd_arlen;
    logic [2:0]    rd_arsize;
    logic [1:0]    rd_arburst;
    logic          rd_arlock;
    logic [3:0]    rd_arcache, rd_arqos, rd_arregion;
    logic [2:0]    rd_arprot;
    logic [UW-1:0] rd_aruser, rd_ruser;
    logic          rd_arvalid, rd_arready;
    logic [IW-1:0] rd_rid;
    logic [DW-1:0] rd_rdata;
    logic [1:0]    rd_rresp;
    logic          rd_rlast, rd_rvalid, rd_rready;

    //=========================================================================
    // Elaboration check: the array shape must match the device
    //=========================================================================
    // More generators than banks would put two streams on one bank and
    // manufacture conflicts the device would not otherwise see, so the number
    // coming out would not be the number the sweep thinks it is. Fewer is a
    // deliberate area trade (see the parameter comment) and is allowed -- the
    // host spreads them.
    initial begin
        if (NUM_GEN > NUM_BANKS) begin
            $error("ddr2_char_macro: NUM_GEN (%0d) exceeds NUM_BANKS (%0d) -- two streams would share a bank",
                   NUM_GEN, NUM_BANKS);
            $finish;
        end
    end

    //=========================================================================
    // Generator config block: APB -> cpuif shim -> chargen_regs
    //=========================================================================
    // Same shim the controller CSR path uses (apb4_to_peakrdl), for the same
    // reason: PeakRDL's own apb4 cpuif emits an `apb4_intf.slave` port and this
    // repo has no such interface. The shim also carries the pclk -> mc_clk
    // crossing, so the host bus and the generators stay in their own domains.
    logic                        cg_cpuif_req, cg_cpuif_req_is_wr;
    logic [APB_ADDR_WIDTH-1:0]   cg_cpuif_addr;
    logic [APB_DATA_WIDTH-1:0]   cg_cpuif_wr_data, cg_cpuif_wr_biten;
    logic                        cg_cpuif_req_stall_wr, cg_cpuif_req_stall_rd;
    logic                        cg_cpuif_rd_ack, cg_cpuif_rd_err;
    logic [APB_DATA_WIDTH-1:0]   cg_cpuif_rd_data;
    logic                        cg_cpuif_wr_ack, cg_cpuif_wr_err;

    apb4_to_peakrdl #(
        .ADDR_WIDTH (APB_ADDR_WIDTH),
        .DATA_WIDTH (APB_DATA_WIDTH),
        .PROT_WIDTH (APB_PROT_WIDTH)
    ) u_chargen_shim (
        .aclk        (mc_clk),   .aresetn (mc_rst_n),
        .pclk        (pclk),     .presetn (presetn),
        .s_apb_PSEL  (s_chargen_apb_PSEL),   .s_apb_PENABLE(s_chargen_apb_PENABLE),
        .s_apb_PREADY(s_chargen_apb_PREADY), .s_apb_PADDR  (s_chargen_apb_PADDR),
        .s_apb_PWRITE(s_chargen_apb_PWRITE), .s_apb_PWDATA (s_chargen_apb_PWDATA),
        .s_apb_PSTRB (s_chargen_apb_PSTRB),  .s_apb_PPROT  (s_chargen_apb_PPROT),
        .s_apb_PRDATA(s_chargen_apb_PRDATA), .s_apb_PSLVERR(s_chargen_apb_PSLVERR),
        .cpuif_req         (cg_cpuif_req),
        .cpuif_req_is_wr   (cg_cpuif_req_is_wr),
        .cpuif_addr        (cg_cpuif_addr),
        .cpuif_wr_data     (cg_cpuif_wr_data),
        .cpuif_wr_biten    (cg_cpuif_wr_biten),
        .cpuif_req_stall_wr(cg_cpuif_req_stall_wr),
        .cpuif_req_stall_rd(cg_cpuif_req_stall_rd),
        .cpuif_rd_ack      (cg_cpuif_rd_ack),
        .cpuif_rd_err      (cg_cpuif_rd_err),
        .cpuif_rd_data     (cg_cpuif_rd_data),
        .cpuif_wr_ack      (cg_cpuif_wr_ack),
        .cpuif_wr_err      (cg_cpuif_wr_err)
    );

    chargen_regs_pkg::chargen_regs__out_t cg_out;
    chargen_regs_pkg::chargen_regs__in_t  cg_in;

    chargen_regs u_chargen_regs (
        .clk                   (mc_clk),
        .rst                   (~mc_rst_n),
        .s_cpuif_req           (cg_cpuif_req),
        .s_cpuif_req_is_wr     (cg_cpuif_req_is_wr),
        .s_cpuif_addr          (cg_cpuif_addr[10:0]),
        .s_cpuif_wr_data       (cg_cpuif_wr_data),
        .s_cpuif_wr_biten      (cg_cpuif_wr_biten),
        .s_cpuif_req_stall_wr  (cg_cpuif_req_stall_wr),
        .s_cpuif_req_stall_rd  (cg_cpuif_req_stall_rd),
        .s_cpuif_rd_ack        (cg_cpuif_rd_ack),
        .s_cpuif_rd_err        (cg_cpuif_rd_err),
        .s_cpuif_rd_data       (cg_cpuif_rd_data),
        .s_cpuif_wr_ack        (cg_cpuif_wr_ack),
        .s_cpuif_wr_err        (cg_cpuif_wr_err),
        .hwif_in               (cg_in),
        .hwif_out              (cg_out)
    );

    //=========================================================================
    // Launch: gather the sixteen singlepulse GO bits into two vectors
    //=========================================================================
    // singlepulse is a per-field property and a field must be one bit, so the
    // register is written out bit by bit and re-assembled here. It is still one
    // host write and one start edge -- which is the entire point. A per-
    // generator start register would mean generator 0 had been running for
    // however long it took the host to program generator 15, and that skew is
    // what produced meaningless zero-utilization windows on rapids.
    logic [NUM_GEN-1:0] w_wr_go, w_rd_go;
    assign w_wr_go = cg_out.GO.wr_go0.value;
    assign w_rd_go = cg_out.GO.rd_go0.value;

    //=========================================================================
    // Per-generator AXI nets
    //=========================================================================
    // Unpacked arrays here, flat named ports at the bridge below: the bridge is
    // generated with one port group per master (wrgen0_axi_*, wrgen1_axi_*, ...)
    // so its connections cannot be written as a loop. If NUM_GEN ever changes,
    // the bridge TOMLs change with it and the connection blocks below are
    // regenerated to match -- they are the one place in this file that is
    // mechanically tied to the master count.
    logic [IW-1:0] gw_awid    [NUM_GEN];
    logic [AW-1:0] gw_awaddr  [NUM_GEN];
    logic [7:0]    gw_awlen   [NUM_GEN];
    logic [2:0]    gw_awsize  [NUM_GEN];
    logic [1:0]    gw_awburst [NUM_GEN];
    logic          gw_awlock  [NUM_GEN];
    logic [3:0]    gw_awcache [NUM_GEN], gw_awqos [NUM_GEN], gw_awregion [NUM_GEN];
    logic [2:0]    gw_awprot  [NUM_GEN];
    logic [UW-1:0] gw_awuser  [NUM_GEN], gw_wuser [NUM_GEN];
    logic          gw_awvalid [NUM_GEN], gw_awready [NUM_GEN];
    logic [DW-1:0] gw_wdata   [NUM_GEN];
    logic [SW-1:0] gw_wstrb   [NUM_GEN];
    logic          gw_wlast   [NUM_GEN], gw_wvalid [NUM_GEN], gw_wready [NUM_GEN];
    logic [IW-1:0] gw_bid     [NUM_GEN];
    logic [1:0]    gw_bresp   [NUM_GEN];
    logic          gw_buser   [NUM_GEN], gw_bvalid [NUM_GEN], gw_bready [NUM_GEN];

    logic [IW-1:0] gr_arid    [NUM_GEN];
    logic [AW-1:0] gr_araddr  [NUM_GEN];
    logic [7:0]    gr_arlen   [NUM_GEN];
    logic [2:0]    gr_arsize  [NUM_GEN];
    logic [1:0]    gr_arburst [NUM_GEN];
    logic          gr_arlock  [NUM_GEN];
    logic [3:0]    gr_arcache [NUM_GEN], gr_arqos [NUM_GEN], gr_arregion [NUM_GEN];
    logic [2:0]    gr_arprot  [NUM_GEN];
    logic [UW-1:0] gr_aruser  [NUM_GEN], gr_ruser [NUM_GEN];
    logic          gr_arvalid [NUM_GEN], gr_arready [NUM_GEN];
    logic [IW-1:0] gr_rid     [NUM_GEN];
    logic [DW-1:0] gr_rdata   [NUM_GEN];
    logic [1:0]    gr_rresp   [NUM_GEN];
    logic          gr_rlast   [NUM_GEN], gr_rvalid [NUM_GEN], gr_rready [NUM_GEN];

    // Per-generator status, gathered for the roll-up registers.
    logic [NUM_GEN-1:0] w_wr_done, w_wr_crc_valid, w_wr_bresp_err;
    logic [NUM_GEN-1:0] w_rd_done, w_rd_crc_valid, w_rd_data_err;
    logic [NUM_GEN-1:0] w_rd_rresp_err, w_rd_stray_err;

    // The reader debug FIFO drains generator 0 only. It is a bench aid for
    // eyeballing a mismatching beat, not a checker -- every reader's mismatch
    // is already counted in its own BEATS_MISM register, which is what the host
    // reads. Eight drain ports would be eight more things to wire for a facility
    // that is used interactively, on one stream, when something has already
    // gone wrong.
    logic               w_dbg_valid    [NUM_GEN];
    logic               w_dbg_ready    [NUM_GEN];
    logic [DW-1:0]      w_dbg_actual   [NUM_GEN];
    logic [DW-1:0]      w_dbg_expected [NUM_GEN];
    logic               w_dbg_mismatch [NUM_GEN];

    logic [TXN_COUNT_WIDTH-1:0] w_rd_beats_mism [NUM_GEN];
    logic [TXN_COUNT_WIDTH-1:0] w_rd_stray_cnt  [NUM_GEN];
    logic [31:0]                w_wr_crc        [NUM_GEN];
    logic [31:0]                w_rd_crc        [NUM_GEN];

    //=========================================================================
    // Write generators -- one per bank
    //=========================================================================
    generate
    for (genvar g = 0; g < NUM_GEN; g++) begin : g_wr_engine
        axi4_master_wr_pattern_gen #(
            .AXI_ID_WIDTH       (AXI_ID_WIDTH),
            .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
            .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
            .AXI_USER_WIDTH     (AXI_USER_WIDTH),
            .AXI_WSTRB_WIDTH    (AXI_STRB_WIDTH),
            .TXN_COUNT_WIDTH    (TXN_COUNT_WIDTH),
            .INDEX_WIDTH        (INDEX_WIDTH),
            .STRIDE_WIDTH       (STRIDE_WIDTH),
            .BURST_LEN_MULTIPLE (BURST_LEN_MULTIPLE)
        ) u_wr_engine (
            .aclk                 (mc_clk),
            .aresetn              (mc_rst_n),
            .cfg_start_addr       (AW'(cg_out.WR_GEN[g].START_ADDR.addr.value)),
            .cfg_addr_stride_0    (signed'(cg_out.WR_GEN[g].STRIDE_0.stride.value)),
            .cfg_addr_stride_1    (signed'(cg_out.WR_GEN[g].STRIDE_1.stride.value)),
            .cfg_addr_wrap_mask_0 (AW'(cg_out.WR_GEN[g].WRAP_MASK_0.mask.value)),
            .cfg_addr_wrap_mask_1 (AW'(cg_out.WR_GEN[g].WRAP_MASK_1.mask.value)),
            .cfg_burst_len        (cg_out.WR_GEN[g].BLEN_TXN.burst_len.value),
            .cfg_txn_count        (cg_out.WR_GEN[g].BLEN_TXN.txn_count.value),
            .cfg_axi_id           (cg_out.WR_GEN[g].AXI_ATTR.axi_id.value),
            .cfg_id_mode          (cg_out.WR_GEN[g].AXI_ATTR.id_mode.value),
            .cfg_axi_size         (cg_out.WR_GEN[g].AXI_ATTR.axi_size.value),
            .cfg_axi_burst        (cg_out.WR_GEN[g].AXI_ATTR.axi_burst.value),
            .cfg_lfsr_seed        (cg_out.WR_GEN[g].LFSR_SEED.seed.value),
            .cfg_data_mode        (cg_out.WR_GEN[g].AXI_ATTR.data_mode.value),
            .cfg_hash_seed0       (cg_out.WR_GEN[g].HASH_SEED0.seed.value),
            .cfg_hash_seed1       (cg_out.WR_GEN[g].HASH_SEED1.seed.value),
            .cfg_hash_seed2       (cg_out.WR_GEN[g].HASH_SEED2.seed.value),
            .cfg_wr_gap           (cg_out.WR_GEN[g].BLEN_TXN.gap.value),
            .cfg_start            (w_wr_go[g]),
            .cfg_done             (w_wr_done[g]),
            .o_expected_crc       (w_wr_crc[g]),
            .o_expected_crc_valid (w_wr_crc_valid[g]),
            .o_bresp_error        (w_wr_bresp_err[g]),
            .m_axi_awid           (gw_awid[g]),
            .m_axi_awaddr         (gw_awaddr[g]),
            .m_axi_awlen          (gw_awlen[g]),
            .m_axi_awsize         (gw_awsize[g]),
            .m_axi_awburst        (gw_awburst[g]),
            .m_axi_awlock         (gw_awlock[g]),
            .m_axi_awcache        (gw_awcache[g]),
            .m_axi_awprot         (gw_awprot[g]),
            .m_axi_awqos          (gw_awqos[g]),
            .m_axi_awregion       (gw_awregion[g]),
            .m_axi_awuser         (gw_awuser[g]),
            .m_axi_awvalid        (gw_awvalid[g]),
            .m_axi_awready        (gw_awready[g]),
            .m_axi_wdata          (gw_wdata[g]),
            .m_axi_wstrb          (gw_wstrb[g]),
            .m_axi_wlast          (gw_wlast[g]),
            .m_axi_wuser          (gw_wuser[g]),
            .m_axi_wvalid         (gw_wvalid[g]),
            .m_axi_wready         (gw_wready[g]),
            .m_axi_bid            (gw_bid[g]),
            .m_axi_bresp          (gw_bresp[g]),
            .m_axi_buser          (gw_buser[g]),
            .m_axi_bvalid         (gw_bvalid[g]),
            .m_axi_bready         (gw_bready[g])
        );
    end
    endgenerate

    //=========================================================================
    // Read generators -- one per bank
    //=========================================================================
    generate
    for (genvar g = 0; g < NUM_GEN; g++) begin : g_rd_engine
        axi4_master_rd_crc_check #(
            .AXI_ID_WIDTH       (AXI_ID_WIDTH),
            .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
            .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
            .AXI_USER_WIDTH     (AXI_USER_WIDTH),
            .TXN_COUNT_WIDTH    (TXN_COUNT_WIDTH),
            .INDEX_WIDTH        (INDEX_WIDTH),
            .STRIDE_WIDTH       (STRIDE_WIDTH),
            .BURST_LEN_MULTIPLE (BURST_LEN_MULTIPLE),
            // Only generator 0 carries the debug FIFO; see the note above.
            .DBG_FIFO_DEPTH     ((g == 0) ? RD_DBG_FIFO_DEPTH : 0)
        ) u_rd_engine (
            .aclk                 (mc_clk),
            .aresetn              (mc_rst_n),
            .cfg_start_addr       (AW'(cg_out.RD_GEN[g].START_ADDR.addr.value)),
            .cfg_addr_stride_0    (signed'(cg_out.RD_GEN[g].STRIDE_0.stride.value)),
            .cfg_addr_stride_1    (signed'(cg_out.RD_GEN[g].STRIDE_1.stride.value)),
            .cfg_addr_wrap_mask_0 (AW'(cg_out.RD_GEN[g].WRAP_MASK_0.mask.value)),
            .cfg_addr_wrap_mask_1 (AW'(cg_out.RD_GEN[g].WRAP_MASK_1.mask.value)),
            .cfg_burst_len        (cg_out.RD_GEN[g].BLEN_TXN.burst_len.value),
            .cfg_txn_count        (cg_out.RD_GEN[g].BLEN_TXN.txn_count.value),
            .cfg_axi_id           (cg_out.RD_GEN[g].AXI_ATTR.axi_id.value),
            .cfg_id_mode          (cg_out.RD_GEN[g].AXI_ATTR.id_mode.value),
            .cfg_axi_size         (cg_out.RD_GEN[g].AXI_ATTR.axi_size.value),
            .cfg_axi_burst        (cg_out.RD_GEN[g].AXI_ATTR.axi_burst.value),
            .cfg_lfsr_seed        (cg_out.RD_GEN[g].LFSR_SEED.seed.value),
            .cfg_data_mode        (cg_out.RD_GEN[g].AXI_ATTR.data_mode.value),
            .cfg_hash_seed0       (cg_out.RD_GEN[g].HASH_SEED0.seed.value),
            .cfg_hash_seed1       (cg_out.RD_GEN[g].HASH_SEED1.seed.value),
            .cfg_hash_seed2       (cg_out.RD_GEN[g].HASH_SEED2.seed.value),
            .cfg_rd_gap           (cg_out.RD_GEN[g].BLEN_TXN.gap.value),
            .cfg_start            (w_rd_go[g]),
            .cfg_done             (w_rd_done[g]),
            .o_actual_crc         (w_rd_crc[g]),
            .o_actual_crc_valid   (w_rd_crc_valid[g]),
            .o_data_error         (w_rd_data_err[g]),
            .o_rresp_error        (w_rd_rresp_err[g]),
            .o_stray_beat_error   (w_rd_stray_err[g]),
            .o_stray_beats        (w_rd_stray_cnt[g]),
            .o_beats_mismatched   (w_rd_beats_mism[g]),
            .m_axi_arid           (gr_arid[g]),
            .m_axi_araddr         (gr_araddr[g]),
            .m_axi_arlen          (gr_arlen[g]),
            .m_axi_arsize         (gr_arsize[g]),
            .m_axi_arburst        (gr_arburst[g]),
            .m_axi_arlock         (gr_arlock[g]),
            .m_axi_arcache        (gr_arcache[g]),
            .m_axi_arprot         (gr_arprot[g]),
            .m_axi_arqos          (gr_arqos[g]),
            .m_axi_arregion       (gr_arregion[g]),
            .m_axi_aruser         (gr_aruser[g]),
            .m_axi_arvalid        (gr_arvalid[g]),
            .m_axi_arready        (gr_arready[g]),
            .m_axi_rid            (gr_rid[g]),
            .m_axi_rdata          (gr_rdata[g]),
            .m_axi_rresp          (gr_rresp[g]),
            .m_axi_rlast          (gr_rlast[g]),
            .m_axi_ruser          (gr_ruser[g]),
            .m_axi_rvalid         (gr_rvalid[g]),
            .m_axi_rready         (gr_rready[g]),
            .dbg_valid            (w_dbg_valid[g]),
            .dbg_ready            (w_dbg_ready[g]),
            .dbg_actual           (w_dbg_actual[g]),
            .dbg_expected         (w_dbg_expected[g]),
            .dbg_mismatch         (w_dbg_mismatch[g])
        );
    end
    endgenerate

    //=========================================================================
    // Launched mask + run-level aggregation
    //=========================================================================
    // A generator counts as in-flight from its GO pulse until its done. The
    // mask latches at launch and holds until reset, so "all done" means all of
    // the ones we started -- see the port comment for why an AND over all
    // sixteen would be wrong.
    //
    // The mask only ever ACCUMULATES, and that is safe rather than sloppy,
    // because an engine's done is a held level rather than a pulse. A second
    // run that launches a different subset leaves the previous run's
    // generators marked launched, but they are also still reporting done, so
    // they contribute a constant 1 and the aggregate tracks only the ones
    // actually running. Clearing the mask per run would need a clear pulse the
    // host has to remember to send, and forgetting it would report done
    // early -- a worse failure than carrying a stale bit that reads as
    // finished because it IS finished.
    logic [NUM_GEN-1:0] r_wr_launched, r_rd_launched;

    always_ff @(posedge mc_clk or negedge mc_rst_n) begin
        if (!mc_rst_n) begin
            r_wr_launched <= '0;
            r_rd_launched <= '0;
        end else begin
            r_wr_launched <= r_wr_launched | w_wr_go;
            r_rd_launched <= r_rd_launched | w_rd_go;
        end
    end

    assign gen_wr_started = |w_wr_go;
    assign gen_rd_started = |w_rd_go;

    // Nothing launched is not "done" -- it is "not started". Reporting done
    // before a run begins would let the harness close its measurement window
    // on an empty interval and call the result zero.
    assign gen_wr_done = (r_wr_launched != '0) &&
                         ((w_wr_done & r_wr_launched) == r_wr_launched);
    assign gen_rd_done = (r_rd_launched != '0) &&
                         ((w_rd_done & r_rd_launched) == r_rd_launched);

    assign gen_any_error = |w_wr_bresp_err | |w_rd_data_err |
                           |w_rd_rresp_err | |w_rd_stray_err;

    //=========================================================================
    // CRC aggregate -- every launched pair matched
    //=========================================================================
    // THE CONVENTION THIS ASSUMES, stated because it is an assumption in
    // hardware and not something the RTL can check: writer i and reader i are
    // programmed as a MATCHED PAIR over the same address pattern on bank i.
    // That is what the register layout is designed for -- identical config
    // blocks for WR_GEN[i] and RD_GEN[i] -- and the host asserts it when it
    // programs them. A host that pairs them differently will see this bit go
    // low while the per-generator CRCs in chargen_regs are individually fine,
    // which is the right failure: loud, and localisable by reading the pairs.
    //
    // Only pairs where BOTH ends were launched participate. A write-only sweep
    // has no reader to compare against, and demanding a match there would
    // report corruption on a run that never read anything.
    logic [NUM_GEN-1:0] w_pair_launched, w_pair_ok;

    assign w_pair_launched = r_wr_launched & r_rd_launched;

    generate
    for (genvar g = 0; g < NUM_GEN; g++) begin : g_crc_pair
        assign w_pair_ok[g] = w_wr_crc_valid[g] & w_rd_crc_valid[g] &
                              (w_wr_crc[g] == w_rd_crc[g]);
    end
    endgenerate

    // No matched pair ran => nothing was verified, so this is NOT a pass.
    assign gen_crc_match = (w_pair_launched != '0) &&
                           ((w_pair_ok & w_pair_launched) == w_pair_launched);

    //=========================================================================
    // Status back into the register block
    //=========================================================================
    always_comb begin
        for (int g = 0; g < NUM_GEN; g++) begin
            cg_in.WR_GEN[g].STATUS.done.next        = w_wr_done[g];
            cg_in.WR_GEN[g].STATUS.crc_valid.next   = w_wr_crc_valid[g];
            cg_in.WR_GEN[g].STATUS.bresp_error.next = w_wr_bresp_err[g];
            cg_in.WR_GEN[g].EXPECTED_CRC.crc.next = w_wr_crc[g];

            cg_in.RD_GEN[g].STATUS.done.next             = w_rd_done[g];
            cg_in.RD_GEN[g].STATUS.crc_valid.next        = w_rd_crc_valid[g];
            cg_in.RD_GEN[g].STATUS.data_error.next       = w_rd_data_err[g];
            cg_in.RD_GEN[g].STATUS.rresp_error.next      = w_rd_rresp_err[g];
            cg_in.RD_GEN[g].STATUS.stray_beat_error.next = w_rd_stray_err[g];
            cg_in.RD_GEN[g].ACTUAL_CRC.crc.next        = w_rd_crc[g];
            cg_in.RD_GEN[g].BEATS_MISM.beats.next        = 32'(w_rd_beats_mism[g]);
            cg_in.RD_GEN[g].STRAY_BEATS.beats.next       = 32'(w_rd_stray_cnt[g]);
        end

        // Roll-ups: a poll costs one read instead of sixteen.
        cg_in.DONE.wr_done.next = 8'(w_wr_done);
        cg_in.DONE.rd_done.next = 8'(w_rd_done);

        cg_in.ERRORS.wr_bresp_error.next = 8'(w_wr_bresp_err);
        // Any read-side error at all -- the per-generator STATUS says which.
        cg_in.ERRORS.rd_any_error.next   = 8'(w_rd_data_err | w_rd_rresp_err | w_rd_stray_err);

        // Identity, from this instance's own parameters, so the count the host
        // programs cannot drift from the count that was compiled.
        cg_in.GEN_CONFIG.num_wr_gen.next = 8'(NUM_GEN);
        cg_in.GEN_CONFIG.num_rd_gen.next = 8'(NUM_GEN);
        cg_in.GEN_CONFIG.num_banks.next  = 8'(NUM_BANKS);
        cg_in.BLOCK_ID.id.next        = 32'h4347454E;   // "CGEN"
    end


    //=========================================================================
    // Direct connection: the single generator pair drives pumice's s_axi
    //=========================================================================
    // No crossbar. With NUM_GEN=1 there is nothing to arbitrate, and the two
    // generated 8x1 AXI4 bridges that used to sit here were deleted rather
    // than shrunk: ~9000 lines of crossbar whose slice cost bought no timing
    // (see the NUM_GEN comment above). Restoring them is a bridge-config regen
    // if the array ever grows back.
    //
    // The `user` bits narrow to one here for the same reason they did through
    // the bridge: pumice's s_axi_awuser / wuser / aruser are single bits, so
    // anything wider dies at the controller regardless. Taking bit 0
    // explicitly keeps that visible at the boundary.
    assign wr_awid    = gw_awid[0];
    assign wr_awaddr  = gw_awaddr[0];
    assign wr_awlen   = gw_awlen[0];
    assign wr_awsize  = gw_awsize[0];
    assign wr_awburst = gw_awburst[0];
    assign wr_awlock  = gw_awlock[0];
    assign wr_awcache = gw_awcache[0];
    assign wr_awprot  = gw_awprot[0];
    assign wr_awqos   = gw_awqos[0];
    assign wr_awregion= gw_awregion[0];
    assign wr_awuser  = UW'(gw_awuser[0][0]);
    assign wr_awvalid = gw_awvalid[0];
    assign gw_awready[0] = wr_awready;

    assign wr_wdata   = gw_wdata[0];
    assign wr_wstrb   = gw_wstrb[0];
    assign wr_wlast   = gw_wlast[0];
    assign wr_wuser   = UW'(gw_wuser[0][0]);
    assign wr_wvalid  = gw_wvalid[0];
    assign gw_wready[0] = wr_wready;

    assign gw_bid[0]    = wr_bid;
    assign gw_bresp[0]  = wr_bresp;
    assign gw_buser[0]  = wr_buser[0];
    assign gw_bvalid[0] = wr_bvalid;
    assign wr_bready    = gw_bready[0];

    assign rd_arid    = gr_arid[0];
    assign rd_araddr  = gr_araddr[0];
    assign rd_arlen   = gr_arlen[0];
    assign rd_arsize  = gr_arsize[0];
    assign rd_arburst = gr_arburst[0];
    assign rd_arlock  = gr_arlock[0];
    assign rd_arcache = gr_arcache[0];
    assign rd_arprot  = gr_arprot[0];
    assign rd_arqos   = gr_arqos[0];
    assign rd_arregion= gr_arregion[0];
    assign rd_aruser  = UW'(gr_aruser[0][0]);
    assign rd_arvalid = gr_arvalid[0];
    assign gr_arready[0] = rd_arready;

    assign gr_rid[0]    = rd_rid;
    assign gr_rdata[0]  = rd_rdata;
    assign gr_rresp[0]  = rd_rresp;
    assign gr_rlast[0]  = rd_rlast;
    assign gr_ruser[0]  = UW'(rd_ruser[0]);
    assign gr_rvalid[0] = rd_rvalid;
    assign rd_rready    = gr_rready[0];

    //=========================================================================
    // Reader debug FIFO drain -- generator 0 only
    //=========================================================================
    // A port connection cannot be a ternary, so every reader gets its own drain
    // nets and the module port selects generator 0 here. The other seven are
    // held permanently drained (ready = 1): an undrained FIFO would fill and
    // then backpressure nothing -- the engine does not stall on it -- but a
    // never-emptied buffer is a confusing thing to meet in a waveform, and
    // draining it costs one constant.
    assign rd_dbg_valid    = w_dbg_valid[0];
    assign rd_dbg_actual   = w_dbg_actual[0];
    assign rd_dbg_expected = w_dbg_expected[0];
    assign rd_dbg_mismatch = w_dbg_mismatch[0];
    assign w_dbg_ready[0]  = rd_dbg_ready;

    generate
    for (genvar g = 1; g < NUM_GEN; g++) begin : g_dbg_drain
        assign w_dbg_ready[g] = 1'b1;
    end
    endgenerate

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

    //=========================================================================
    // Perf blocks: bus meters + latency histograms, tapped on the internal
    // AXI wires between the engines and the controller's s_axi port.
    //=========================================================================
    // Ignore per-channel arrays -- we run aggregate-only with NUM_CHANNELS=1.
    logic [15:0] w_wr_meter_ch_prod   [1];
    logic [15:0] w_wr_meter_ch_bp     [1];
    logic [15:0] w_wr_meter_ch_starv  [1];
    logic [15:0] w_wr_meter_ch_idle   [1];
    logic [3:0]  w_wr_meter_ch_overflow;
    logic [15:0] w_rd_meter_ch_prod   [1];
    logic [15:0] w_rd_meter_ch_bp     [1];
    logic [15:0] w_rd_meter_ch_starv  [1];
    logic [15:0] w_rd_meter_ch_idle   [1];
    logic [3:0]  w_rd_meter_ch_overflow;

    // WR-side data-channel meter (W handshake).
    axi_bus_meter #(
        .NUM_CHANNELS (1)
    ) u_meter_wr (
        .aclk           (mc_clk),
        .aresetn        (mc_rst_n),
        .i_clear        (perf_clear),
        .i_freeze       (perf_freeze),
        .i_valid        (wr_wvalid),
        .i_ready        (wr_wready),
        .i_channel_id   ('0),
        .i_channel_valid(1'b1),
        .o_agg_productive   (perf_wr_prod),
        .o_agg_backpressure (perf_wr_bp),
        .o_agg_starvation   (perf_wr_starv),
        .o_agg_idle         (perf_wr_idle),
        .o_ch_productive    (w_wr_meter_ch_prod),
        .o_ch_backpressure  (w_wr_meter_ch_bp),
        .o_ch_starvation    (w_wr_meter_ch_starv),
        .o_ch_idle          (w_wr_meter_ch_idle),
        .o_ch_overflow      (w_wr_meter_ch_overflow)
    );

    // RD-side data-channel meter (R handshake).
    axi_bus_meter #(
        .NUM_CHANNELS (1)
    ) u_meter_rd (
        .aclk           (mc_clk),
        .aresetn        (mc_rst_n),
        .i_clear        (perf_clear),
        .i_freeze       (perf_freeze),
        .i_valid        (rd_rvalid),
        .i_ready        (rd_rready),
        .i_channel_id   ('0),
        .i_channel_valid(1'b1),
        .o_agg_productive   (perf_rd_prod),
        .o_agg_backpressure (perf_rd_bp),
        .o_agg_starvation   (perf_rd_starv),
        .o_agg_idle         (perf_rd_idle),
        .o_ch_productive    (w_rd_meter_ch_prod),
        .o_ch_backpressure  (w_rd_meter_ch_bp),
        .o_ch_starvation    (w_rd_meter_ch_starv),
        .o_ch_idle          (w_rd_meter_ch_idle),
        .o_ch_overflow      (w_rd_meter_ch_overflow)
    );

    // Latency hist: WR side tracks AW -> B (single metric).
    // MAX_OUTSTANDING sizes the timestamp FIFO. A command arriving at a
    // full FIFO degrades SILENTLY (never timestamped, missing from
    // o_hist_total -- see the o_cmd_block comment in the hist RTL), and
    // with o_cmd_block unconsumed here the FIFO must cover the WHOLE
    // engine-side admission domain: pumice CAM (8) + front skid stages +
    // generator lookahead. Depth 8 lost up to 31/64 samples in the sim
    // multiid_min profile (PUMICE-011 MISSING side); 32 covers it.
    axi_perf_latency_hist #(
        .ID_WIDTH        (IW),
        .NUM_CHANNELS    (1),
        .MAX_OUTSTANDING (32),
        .NUM_BINS        (16),
        .IS_READ         (1'b0)
    ) u_hist_wr (
        .aclk       (mc_clk),
        .aresetn    (mc_rst_n),
        // Backpressure request; not consumed here.
        .o_cmd_block  (),
        .i_clear    (perf_clear),
        .i_freeze   (perf_freeze),
        .cmd_valid  (wr_awvalid),
        .cmd_ready  (wr_awready),
        .cmd_id     (wr_awid),
        .data_valid (wr_wvalid),
        .data_ready (wr_wready),
        .data_last  (wr_wlast),
        .data_id    (wr_awid),   // AW id -- WR data has no id
        .resp_valid (wr_bvalid),
        .resp_ready (wr_bready),
        .resp_id    (wr_bid),
        .i_hist_metric (1'b0),   // WR ignores metric bit
        .i_hist_bin    (i_hist_bin),
        .o_hist_count  (perf_wr_hist_count),
        .o_hist_total  (perf_wr_hist_total)
    );

    // Latency hist: RD side tracks AR -> firstR / RLAST (metric selects).
    // MAX_OUTSTANDING: same sizing contract as the WR hist above.
    axi_perf_latency_hist #(
        .ID_WIDTH        (IW),
        .NUM_CHANNELS    (1),
        .MAX_OUTSTANDING (32),
        .NUM_BINS        (16),
        .IS_READ         (1'b1)
    ) u_hist_rd (
        .aclk       (mc_clk),
        .aresetn    (mc_rst_n),
        // Backpressure request; not consumed here.
        .o_cmd_block  (),
        .i_clear    (perf_clear),
        .i_freeze   (perf_freeze),
        .cmd_valid  (rd_arvalid),
        .cmd_ready  (rd_arready),
        .cmd_id     (rd_arid),
        .data_valid (rd_rvalid),
        .data_ready (rd_rready),
        .data_last  (rd_rlast),
        .data_id    (rd_rid),
        .resp_valid (1'b0),
        .resp_ready (1'b0),
        .resp_id    ('0),
        .i_hist_metric (i_hist_metric),
        .i_hist_bin    (i_hist_bin),
        .o_hist_count  (perf_rd_hist_count),
        .o_hist_total  (perf_rd_hist_total)
    );

    // Per-channel arrays are unused when NUM_CHANNELS=1 -- silence lint.
    /* verilator lint_off UNUSED */
    wire _unused_perf = &{1'b0,
        w_wr_meter_ch_prod[0], w_wr_meter_ch_bp[0],
        w_wr_meter_ch_starv[0], w_wr_meter_ch_idle[0],
        w_wr_meter_ch_overflow,
        w_rd_meter_ch_prod[0], w_rd_meter_ch_bp[0],
        w_rd_meter_ch_starv[0], w_rd_meter_ch_idle[0],
        w_rd_meter_ch_overflow,
        1'b0};
    /* verilator lint_on UNUSED */

endmodule : ddr2_char_macro
