// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: char_engine_block
// Purpose: The DUT-agnostic half of the DDR2 characterization harness
//
// Documentation: ddr2-characterization/flows-litedram-uart/HARNESS_PLAN.md
//==============================================================================
// Description:
//   Everything in the characterization loop that is NOT the memory controller:
//
//     chargen_regs (per-generator config, PeakRDL behind an APB window)
//       -> axi4_master_wr_pattern_gen [NUM_GEN] -> bridge_ddr2_char_wr -|
//       -> axi4_master_rd_crc_check   [NUM_GEN] -> bridge_ddr2_char_rd -|
//                                                                       v
//                                              ONE AXI4 master port (m_axi_*)
//       + axi_bus_meter x2 and axi_perf_latency_hist x2 tapped on that port
//
//   Extracted from ddr2_char_macro on 2026-09-10 so the pumice flow and the
//   LiteDRAM comparison flow drive their controllers with the SAME engines,
//   the same config registers and the same perf taps -- the only thing that
//   differs between the two measurements is the controller itself.
//
//   That was not true before: the LiteDRAM harness carried its own copy with a
//   single wr + single rd engine wired to a harness_csr port list that had
//   since been replaced (41 dead ports). A comparison run through two
//   different measurement paths is not an A/B, and a second copy of this spine
//   is how it drifted in the first place.
//
//   Consumers:
//     ddr2_char_macro   -> this block + pumice_top_geared (DFI out)
//     char_engine_harness (flows-litedram-uart) -> this block + litedram_core
//==============================================================================
`timescale 1ns / 1ps
`include "reset_defs.svh"

module char_engine_block
    import pumice_pkg::*;
#(
    // ---- AXI4 ----
    parameter int AXI_ADDR_WIDTH   = 32,
    parameter int AXI_DATA_WIDTH   = 64,
    // AXI_ID_WIDTH=8 to match the pattern-gen engines' internal 8-bit LFSR
    // for the ID-picker (axi4_master_wr_pattern_gen slices cfg_axi_id[7:0]).
    parameter int AXI_ID_WIDTH     = 8,
    parameter int AXI_USER_WIDTH   = 8,
    parameter int AXI_STRB_WIDTH   = AXI_DATA_WIDTH / 8,
    parameter int BURST_LEN_WIDTH  = 8,
    // AXI beats per DRAM burst = DRAM_BL*DRAM_DEVICE_WIDTH/AXI_DATA_WIDTH.
    // 1 = unconstrained (the DV engine sweeps burst_len for coverage); a real
    // top sets the computed value so a software BLEN_TXN misconfig fails loud
    // instead of silently SLVERR-ing or half-writing. Passed in rather than
    // derived here: it is a property of the DRAM the block is driving, and
    // this block is deliberately DUT-agnostic.
    parameter int BURST_LEN_MULTIPLE = 1,

    // ---- APB (chargen config window) ----
    parameter int APB_ADDR_WIDTH   = 12,
    parameter int APB_DATA_WIDTH   = 32,
    parameter int APB_STRB_WIDTH   = APB_DATA_WIDTH / 8,
    parameter int APB_PROT_WIDTH   = 3,

    // ---- Generator array ----
    // NUM_GEN <= NUM_BANKS is the invariant, not equality: each generator is
    // expected to SPAN NUM_BANKS/NUM_GEN banks, so two keep all eight busy.
    // NUM_BANKS is carried purely for that elaboration check.
    parameter int NUM_BANKS        = 8,
    parameter int NUM_GEN          = 2,
    parameter int GEN_MAX_OUTSTANDING = 8,

    // ---- Engine workload ranges ----
    parameter int TXN_COUNT_WIDTH  = 16,
    parameter int INDEX_WIDTH      = 16,
    parameter int STRIDE_WIDTH     = 24,

    // ---- Reader-engine debug FIFO depth (0 = elide) ----
    parameter int RD_DBG_FIFO_DEPTH = 0,

    // ---- Pumice-side (bridge slave-side) ID width ----
    // The two generators reach pumice through the generated 2-master bridges,
    // whose slave-side IDs are {master index, master id} (BRIDGE-016): one
    // bit wider than the generators' own 8. Sized from the bridge package so
    // this block cannot silently truncate the master index if the bridge
    // config ever changes; the rd bridge has the same shape and width.
    parameter int M_AXI_ID_WIDTH   = bridge_ddr2_char_wr_pkg::XBAR_ID_WIDTH,

    // ---- Aliases ----
    parameter int IW = AXI_ID_WIDTH,
    parameter int PIW = M_AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH,
    parameter int SW = AXI_STRB_WIDTH
) (
    input  logic mc_clk,
    input  logic mc_rst_n,
    input  logic pclk,
    input  logic presetn,

    //---- Generator config window (APB -> chargen_regs) --------------------
    input  logic                        s_chargen_apb_PSEL,
    input  logic                        s_chargen_apb_PENABLE,
    output logic                        s_chargen_apb_PREADY,
    input  logic [APB_ADDR_WIDTH-1:0]   s_chargen_apb_PADDR,
    input  logic                        s_chargen_apb_PWRITE,
    input  logic [APB_DATA_WIDTH-1:0]   s_chargen_apb_PWDATA,
    input  logic [APB_STRB_WIDTH-1:0]   s_chargen_apb_PSTRB,
    input  logic [APB_PROT_WIDTH-1:0]   s_chargen_apb_PPROT,
    output logic [APB_DATA_WIDTH-1:0]   s_chargen_apb_PRDATA,
    output logic                        s_chargen_apb_PSLVERR,

    //---- Run-level aggregate status --------------------------------------
    output logic gen_wr_started,
    output logic gen_rd_started,
    output logic gen_wr_done,
    output logic gen_rd_done,
    output logic gen_any_error,
    output logic gen_crc_match,

    //---- Reader debug stream (RD_DBG_FIFO_DEPTH > 0) ----------------------
    output logic          rd_dbg_valid,
    input  logic          rd_dbg_ready,
    output logic [DW-1:0] rd_dbg_actual,
    output logic [DW-1:0] rd_dbg_expected,
    output logic          rd_dbg_mismatch,

    //---- Perf ------------------------------------------------------------
    input  logic        perf_clear,
    input  logic        perf_freeze,
    output logic [31:0] perf_wr_prod,
    output logic [31:0] perf_wr_bp,
    output logic [31:0] perf_wr_starv,
    output logic [31:0] perf_wr_idle,
    output logic [31:0] perf_rd_prod,
    output logic [31:0] perf_rd_bp,
    output logic [31:0] perf_rd_starv,
    output logic [31:0] perf_rd_idle,
    input  logic        i_hist_metric,
    input  logic [3:0]  i_hist_bin,
    output logic [31:0] perf_wr_hist_count,
    output logic [31:0] perf_wr_hist_total,
    output logic [31:0] perf_rd_hist_count,
    output logic [31:0] perf_rd_hist_total,

    //=========================================================================
    // The merged AXI4 master -- this is the controller boundary. The write
    // engines own AW/W/B and the read engines own AR/R; the two crossbars
    // above merge NUM_GEN masters per direction onto this one port.
    //=========================================================================
    output logic [PIW-1:0] m_axi_awid,
    output logic [AW-1:0] m_axi_awaddr,
    output logic [7:0]    m_axi_awlen,
    output logic [2:0]    m_axi_awsize,
    output logic [1:0]    m_axi_awburst,
    output logic          m_axi_awlock,
    output logic [3:0]    m_axi_awcache,
    output logic [2:0]    m_axi_awprot,
    output logic [3:0]    m_axi_awqos,
    output logic [3:0]    m_axi_awregion,
    output logic [UW-1:0] m_axi_awuser,
    output logic          m_axi_awvalid,
    input  logic          m_axi_awready,
    output logic [DW-1:0] m_axi_wdata,
    output logic [SW-1:0] m_axi_wstrb,
    output logic          m_axi_wlast,
    output logic [UW-1:0] m_axi_wuser,
    output logic          m_axi_wvalid,
    input  logic          m_axi_wready,
    input  logic [PIW-1:0] m_axi_bid,
    input  logic [1:0]    m_axi_bresp,
    input  logic [UW-1:0] m_axi_buser,
    input  logic          m_axi_bvalid,
    output logic          m_axi_bready,
    output logic [PIW-1:0] m_axi_arid,
    output logic [AW-1:0] m_axi_araddr,
    output logic [7:0]    m_axi_arlen,
    output logic [2:0]    m_axi_arsize,
    output logic [1:0]    m_axi_arburst,
    output logic          m_axi_arlock,
    output logic [3:0]    m_axi_arcache,
    output logic [2:0]    m_axi_arprot,
    output logic [3:0]    m_axi_arqos,
    output logic [3:0]    m_axi_arregion,
    output logic [UW-1:0] m_axi_aruser,
    output logic          m_axi_arvalid,
    input  logic          m_axi_arready,
    input  logic [PIW-1:0] m_axi_rid,
    input  logic [DW-1:0] m_axi_rdata,
    input  logic [1:0]    m_axi_rresp,
    input  logic          m_axi_rlast,
    input  logic [UW-1:0] m_axi_ruser,
    input  logic          m_axi_rvalid,
    output logic          m_axi_rready
);

    //=========================================================================
    // Internal AXI nets — writer drives AW/W, reader drives AR, both
    // share s_axi at the controller's slave port.
    //=========================================================================
    logic [PIW-1:0] wr_awid;   // bridge slave side: {master index, id}
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
    logic [PIW-1:0] wr_bid;
    logic [1:0]    wr_bresp;
    logic [UW-1:0] wr_buser;
    logic          wr_bvalid, wr_bready;

    logic [PIW-1:0] rd_arid;
    logic [AW-1:0] rd_araddr;
    logic [7:0]    rd_arlen;
    logic [2:0]    rd_arsize;
    logic [1:0]    rd_arburst;
    logic          rd_arlock;
    logic [3:0]    rd_arcache, rd_arqos, rd_arregion;
    logic [2:0]    rd_arprot;
    logic [UW-1:0] rd_aruser, rd_ruser;
    logic          rd_arvalid, rd_arready;
    logic [PIW-1:0] rd_rid;
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
            $error("char_engine_block: NUM_GEN (%0d) exceeds NUM_BANKS (%0d) -- two streams would share a bank",
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
    assign w_wr_go = {cg_out.GO.wr_go1.value, cg_out.GO.wr_go0.value};
    assign w_rd_go = {cg_out.GO.rd_go1.value, cg_out.GO.rd_go0.value};

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
            .BURST_LEN_MULTIPLE (BURST_LEN_MULTIPLE),
            .MAX_OUTSTANDING    (GEN_MAX_OUTSTANDING)
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
            .MAX_OUTSTANDING    (GEN_MAX_OUTSTANDING),
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

    `ALWAYS_FF_RST(mc_clk, mc_rst_n,
        if (`RST_ASSERTED(mc_rst_n)) begin
            r_wr_launched <= '0;
            r_rd_launched <= '0;
        end else begin
            r_wr_launched <= r_wr_launched | w_wr_go;
            r_rd_launched <= r_rd_launched | w_rd_go;
        end
    )

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
    // Write bridge: two generators -> pumice's AW/W/B channel group
    //=========================================================================
    // The `user` bits narrow to one here on purpose. pumice's s_axi_awuser and
    // s_axi_wuser are single bits, so anything wider dies at the controller
    // regardless; taking bit 0 explicitly makes that visible at the boundary
    // instead of leaving a silent width truncation for lint to swallow.
    bridge_ddr2_char_wr u_wr_bridge (
        .aclk    (mc_clk),
        .aresetn (mc_rst_n),

        // Generator 0 -> low bank half
        .wrgen0_axi_awid     (gw_awid[0]),
        .wrgen0_axi_awaddr   (gw_awaddr[0]),
        .wrgen0_axi_awlen    (gw_awlen[0]),
        .wrgen0_axi_awsize   (gw_awsize[0]),
        .wrgen0_axi_awburst  (gw_awburst[0]),
        .wrgen0_axi_awlock   (gw_awlock[0]),
        .wrgen0_axi_awcache  (gw_awcache[0]),
        .wrgen0_axi_awprot   (gw_awprot[0]),
        .wrgen0_axi_awqos    (gw_awqos[0]),
        .wrgen0_axi_awregion (gw_awregion[0]),
        .wrgen0_axi_awuser   (gw_awuser[0][0]),
        .wrgen0_axi_awvalid  (gw_awvalid[0]),
        .wrgen0_axi_awready  (gw_awready[0]),
        .wrgen0_axi_wdata    (gw_wdata[0]),
        .wrgen0_axi_wstrb    (gw_wstrb[0]),
        .wrgen0_axi_wlast    (gw_wlast[0]),
        .wrgen0_axi_wuser    (gw_wuser[0][0]),
        .wrgen0_axi_wvalid   (gw_wvalid[0]),
        .wrgen0_axi_wready   (gw_wready[0]),
        .wrgen0_axi_bid      (gw_bid[0]),
        .wrgen0_axi_bresp    (gw_bresp[0]),
        .wrgen0_axi_buser    (gw_buser[0]),
        .wrgen0_axi_bvalid   (gw_bvalid[0]),
        .wrgen0_axi_bready   (gw_bready[0]),

        // Generator 1 -> high bank half
        .wrgen1_axi_awid     (gw_awid[1]),
        .wrgen1_axi_awaddr   (gw_awaddr[1]),
        .wrgen1_axi_awlen    (gw_awlen[1]),
        .wrgen1_axi_awsize   (gw_awsize[1]),
        .wrgen1_axi_awburst  (gw_awburst[1]),
        .wrgen1_axi_awlock   (gw_awlock[1]),
        .wrgen1_axi_awcache  (gw_awcache[1]),
        .wrgen1_axi_awprot   (gw_awprot[1]),
        .wrgen1_axi_awqos    (gw_awqos[1]),
        .wrgen1_axi_awregion (gw_awregion[1]),
        .wrgen1_axi_awuser   (gw_awuser[1][0]),
        .wrgen1_axi_awvalid  (gw_awvalid[1]),
        .wrgen1_axi_awready  (gw_awready[1]),
        .wrgen1_axi_wdata    (gw_wdata[1]),
        .wrgen1_axi_wstrb    (gw_wstrb[1]),
        .wrgen1_axi_wlast    (gw_wlast[1]),
        .wrgen1_axi_wuser    (gw_wuser[1][0]),
        .wrgen1_axi_wvalid   (gw_wvalid[1]),
        .wrgen1_axi_wready   (gw_wready[1]),
        .wrgen1_axi_bid      (gw_bid[1]),
        .wrgen1_axi_bresp    (gw_bresp[1]),
        .wrgen1_axi_buser    (gw_buser[1]),
        .wrgen1_axi_bvalid   (gw_bvalid[1]),
        .wrgen1_axi_bready   (gw_bready[1]),

        // Slave: pumice's write half
        .pumice_wr_axi_awid    (wr_awid),
        .pumice_wr_axi_awaddr  (wr_awaddr),
        .pumice_wr_axi_awlen   (wr_awlen),
        .pumice_wr_axi_awsize  (wr_awsize),
        .pumice_wr_axi_awburst (wr_awburst),
        .pumice_wr_axi_awlock  (wr_awlock),
        .pumice_wr_axi_awcache (wr_awcache),
        .pumice_wr_axi_awprot  (wr_awprot),
        .pumice_wr_axi_awqos   (wr_awqos),
        .pumice_wr_axi_awregion(wr_awregion),
        .pumice_wr_axi_awuser  (wr_awuser[0]),
        .pumice_wr_axi_awvalid (wr_awvalid),
        .pumice_wr_axi_awready (wr_awready),
        .pumice_wr_axi_wdata   (wr_wdata),
        .pumice_wr_axi_wstrb   (wr_wstrb),
        .pumice_wr_axi_wlast   (wr_wlast),
        .pumice_wr_axi_wuser   (wr_wuser[0]),
        .pumice_wr_axi_wvalid  (wr_wvalid),
        .pumice_wr_axi_wready  (wr_wready),
        .pumice_wr_axi_bid     (wr_bid),
        .pumice_wr_axi_bresp   (wr_bresp),
        .pumice_wr_axi_buser   (wr_buser[0]),
        .pumice_wr_axi_bvalid  (wr_bvalid),
        .pumice_wr_axi_bready  (wr_bready)
    );

    // The upper user bits are unused by construction (see above).
    assign wr_awuser[UW-1:1] = '0;
    assign wr_wuser [UW-1:1] = '0;

    //=========================================================================
    // Read bridge: two generators -> pumice's AR/R channel group
    //=========================================================================
    bridge_ddr2_char_rd u_rd_bridge (
        .aclk    (mc_clk),
        .aresetn (mc_rst_n),

        // Generator 0 -> low bank half
        .rdgen0_axi_arid     (gr_arid[0]),
        .rdgen0_axi_araddr   (gr_araddr[0]),
        .rdgen0_axi_arlen    (gr_arlen[0]),
        .rdgen0_axi_arsize   (gr_arsize[0]),
        .rdgen0_axi_arburst  (gr_arburst[0]),
        .rdgen0_axi_arlock   (gr_arlock[0]),
        .rdgen0_axi_arcache  (gr_arcache[0]),
        .rdgen0_axi_arprot   (gr_arprot[0]),
        .rdgen0_axi_arqos    (gr_arqos[0]),
        .rdgen0_axi_arregion (gr_arregion[0]),
        .rdgen0_axi_aruser   (gr_aruser[0][0]),
        .rdgen0_axi_arvalid  (gr_arvalid[0]),
        .rdgen0_axi_arready  (gr_arready[0]),
        .rdgen0_axi_rid      (gr_rid[0]),
        .rdgen0_axi_rdata    (gr_rdata[0]),
        .rdgen0_axi_rresp    (gr_rresp[0]),
        .rdgen0_axi_rlast    (gr_rlast[0]),
        .rdgen0_axi_ruser    (gr_ruser[0]),
        .rdgen0_axi_rvalid   (gr_rvalid[0]),
        .rdgen0_axi_rready   (gr_rready[0]),

        // Generator 1 -> high bank half
        .rdgen1_axi_arid     (gr_arid[1]),
        .rdgen1_axi_araddr   (gr_araddr[1]),
        .rdgen1_axi_arlen    (gr_arlen[1]),
        .rdgen1_axi_arsize   (gr_arsize[1]),
        .rdgen1_axi_arburst  (gr_arburst[1]),
        .rdgen1_axi_arlock   (gr_arlock[1]),
        .rdgen1_axi_arcache  (gr_arcache[1]),
        .rdgen1_axi_arprot   (gr_arprot[1]),
        .rdgen1_axi_arqos    (gr_arqos[1]),
        .rdgen1_axi_arregion (gr_arregion[1]),
        .rdgen1_axi_aruser   (gr_aruser[1][0]),
        .rdgen1_axi_arvalid  (gr_arvalid[1]),
        .rdgen1_axi_arready  (gr_arready[1]),
        .rdgen1_axi_rid      (gr_rid[1]),
        .rdgen1_axi_rdata    (gr_rdata[1]),
        .rdgen1_axi_rresp    (gr_rresp[1]),
        .rdgen1_axi_rlast    (gr_rlast[1]),
        .rdgen1_axi_ruser    (gr_ruser[1]),
        .rdgen1_axi_rvalid   (gr_rvalid[1]),
        .rdgen1_axi_rready   (gr_rready[1]),

        // Slave: pumice's read half
        .pumice_rd_axi_arid    (rd_arid),
        .pumice_rd_axi_araddr  (rd_araddr),
        .pumice_rd_axi_arlen   (rd_arlen),
        .pumice_rd_axi_arsize  (rd_arsize),
        .pumice_rd_axi_arburst (rd_arburst),
        .pumice_rd_axi_arlock  (rd_arlock),
        .pumice_rd_axi_arcache (rd_arcache),
        .pumice_rd_axi_arprot  (rd_arprot),
        .pumice_rd_axi_arqos   (rd_arqos),
        .pumice_rd_axi_arregion(rd_arregion),
        .pumice_rd_axi_aruser  (rd_aruser[0]),
        .pumice_rd_axi_arvalid (rd_arvalid),
        .pumice_rd_axi_arready (rd_arready),
        .pumice_rd_axi_rid     (rd_rid),
        .pumice_rd_axi_rdata   (rd_rdata),
        .pumice_rd_axi_rresp   (rd_rresp),
        .pumice_rd_axi_rlast   (rd_rlast),
        .pumice_rd_axi_ruser   (rd_ruser[0]),
        .pumice_rd_axi_rvalid  (rd_rvalid),
        .pumice_rd_axi_rready  (rd_rready)
    );

    assign rd_aruser[UW-1:1] = '0;

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
    // multiid_min profile (PUMICE-020 MISSING side); 32 covers it.
    axi_perf_latency_hist #(
        .ID_WIDTH        (PIW),   // pumice side, {master index, id}
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
        .ID_WIDTH        (PIW),   // pumice side, {master index, id}
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


    //=========================================================================
    // Merged AXI -> the module's master port. The internal wr_*/rd_* nets are
    // what the crossbars drive and what the perf meters tap, so the mapping
    // stays a rename rather than another layer of muxing.
    //=========================================================================
    assign m_axi_awid     = wr_awid;
    assign m_axi_awaddr   = wr_awaddr;
    assign m_axi_awlen    = wr_awlen;
    assign m_axi_awsize   = wr_awsize;
    assign m_axi_awburst  = wr_awburst;
    assign m_axi_awlock   = wr_awlock;
    assign m_axi_awcache  = wr_awcache;
    assign m_axi_awprot   = wr_awprot;
    assign m_axi_awqos    = wr_awqos;
    assign m_axi_awregion = wr_awregion;
    assign m_axi_awuser   = wr_awuser;
    assign m_axi_awvalid  = wr_awvalid;
    assign wr_awready     = m_axi_awready;
    assign m_axi_wdata    = wr_wdata;
    assign m_axi_wstrb    = wr_wstrb;
    assign m_axi_wlast    = wr_wlast;
    assign m_axi_wuser    = wr_wuser;
    assign m_axi_wvalid   = wr_wvalid;
    assign wr_wready      = m_axi_wready;
    assign wr_bid         = m_axi_bid;
    assign wr_bresp       = m_axi_bresp;
    assign wr_buser       = m_axi_buser;
    assign wr_bvalid      = m_axi_bvalid;
    assign m_axi_bready   = wr_bready;

    assign m_axi_arid     = rd_arid;
    assign m_axi_araddr   = rd_araddr;
    assign m_axi_arlen    = rd_arlen;
    assign m_axi_arsize   = rd_arsize;
    assign m_axi_arburst  = rd_arburst;
    assign m_axi_arlock   = rd_arlock;
    assign m_axi_arcache  = rd_arcache;
    assign m_axi_arprot   = rd_arprot;
    assign m_axi_arqos    = rd_arqos;
    assign m_axi_arregion = rd_arregion;
    assign m_axi_aruser   = rd_aruser;
    assign m_axi_arvalid  = rd_arvalid;
    assign rd_arready     = m_axi_arready;
    assign rd_rid         = m_axi_rid;
    assign rd_rdata       = m_axi_rdata;
    assign rd_rresp       = m_axi_rresp;
    assign rd_rlast       = m_axi_rlast;
    assign rd_ruser       = m_axi_ruser;
    assign rd_rvalid      = m_axi_rvalid;
    assign m_axi_rready   = rd_rready;

endmodule : char_engine_block
