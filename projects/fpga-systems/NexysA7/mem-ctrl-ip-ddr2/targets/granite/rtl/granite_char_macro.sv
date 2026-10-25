// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: granite_char_macro
// Purpose: Single instantiation point binding the master-side AXI4
//          characterization engines to the granite memory controller.
//          Mirrors ddr2_char_macro.sv (pumice) with the controller swapped
//          for granite_top_geared. Command-history scoreboard parameters
//          are absent because Granite's lite SKU core does not export them.
//
// Documentation: projects/fpga-systems/NexysA7/shared/README.md

`timescale 1ns / 1ps

`include "reset_defs.svh"

module granite_char_macro
    import granite_pkg::*;
    import mc_common_pkg::*;
#(
    // ---- AXI4 ----
    parameter int AXI_ADDR_WIDTH   = 32,
    parameter int AXI_DATA_WIDTH   = 64,
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
    parameter int ROW_WIDTH        = 13,
    parameter int COL_WIDTH        = 10,

    // ---- Controller depths ----
    parameter int WR_CAM_DEPTH     = 16,
    parameter bit HAS_LPDDR2     = 1'b1, // LPDDR2 training plane built (0 = DDR2-only build)
    parameter bit DFI_CDC_EN     = 1'b0, // this macro ties dfi_clk to mc_clk (below): no DFI crossing by default
    // AXI-plane lean knobs (pumice TASK-054), granite defaults = the measured lean form:
    parameter bit HAS_SNARF        = 1'b0, // 1 = snarf probe / staged admit / source arbiter in the read intake (pumice's CAM store); granite's FIFO store has no snarf
    parameter int INTAKE_FIFO_DEPTH = 0,   // rd-data and wr-data FIFOs in the intakes; 0 = none (the skids feed the ring / store directly; cycle-identical, measured)
    parameter int AXI_SKID_DEPTH   = 2,    // R and W skid depth in the AXI slave shells (2..8); 2 measured cycle-identical to 4
    parameter bit SHARED_ADDR_MAP  = 1'b0, // 1 = one address mapper for both intakes with an alternating grant: -23 percent on the mixed family, so OFF
    // Scheduler / DFI knobs (pumice TASK-055), granite defaults = the measured form:
    parameter bit HAS_PAGE_POLICY   = 1'b1, // 0 = no runtime page-policy engine (close-on-drain alone): measured -8 percent on 8-thread streams, so ON
    parameter int BANK_CAP_MIXED    = 6,    // FIFO store per-bank cap while the other direction holds entries (0 = off)
    parameter bit HAS_AGE           = 1'b0, // store age promotion (CSR age_thresh -> aged-first pick); 0 compiles the ages out (pumice TASK-059)
    parameter bit PP_TIMEOUT_CLOSE  = 1'b1, // page-policy idle-timeout close; 0 compiles the timers out (inert at tr_init 0, the default)
    parameter int BANK_TW           = 5,    // per-bank timer width (pumice TASK-056): 5 covers DDR2 at <= 100 MHz (tRC 6), measured cycle-identical; 8 = the CSR field width; a CSR value above the range saturates
    parameter int DFI_CMD_FIFO_DEPTH = 4,   // DFI plane command FIFO (8 before; 4 measured cycle-identical on every cell)
    parameter int DFI_WD_FIFO_DEPTH  = 16,  // DFI plane write-data FIFO (32 before; 16 measured cycle-identical)
    parameter int DFI_RD_FIFO_DEPTH  = 4,   // DFI plane read-return FIFO (0 = RD_RET_DEPTH x BURST_WORDS, the whole window, before); 4 holds the
                                            // return in the same-clock form where the ring is always ready; 2 loses beats where dfi_clk runs at 2x aclk
    parameter int STORE_BACKEND   = 1,    // granite_core storage backend (1 = per-bank FIFO store, 0 = entry store)
    parameter int BANK_FIFO_DEPTH = 0,    // 0 = NUM_ENTRIES (pool-only admission)
    parameter bit HEAD2_EN        = 1'b1, // 0 = one head record per bank (FIFO store)
    parameter bit FIXED_TIMINGS   = 1'b0, // 1 = granite_core T_* constants replace the TIMINGS CSRs
    parameter int RD_CAM_DEPTH     = 16,
    parameter int RD_RET_DEPTH     = 32,
    parameter int W_BUF_DEPTH      = 128,

    // ---- DFI ----
    parameter int DFI_RATE         = 2,
    parameter int DRAM_BEAT_WIDTH  = AXI_DATA_WIDTH,
    parameter int DRAM_DEVICE_WIDTH = DRAM_BEAT_WIDTH,
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
    parameter int DRAM_BL          = 8,
    parameter int BURST_LEN_MULTIPLE = 1,

    // ---- Generator array ----
    parameter int NUM_GEN          = 4,
    parameter int GEN_MAX_OUTSTANDING = 32,

    // ---- Engine workload ranges ----
    parameter int TXN_COUNT_WIDTH  = 16,
    parameter int INDEX_WIDTH      = 16,
    parameter int STRIDE_WIDTH     = 24,

    // ---- Reader-engine debug FIFO depth (0 = elide) ----
    parameter int RD_DBG_FIFO_DEPTH = 0,

    // ---- Aliases ----
    parameter int IW = AXI_ID_WIDTH,
    parameter int PIW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH,
    parameter int SW = AXI_STRB_WIDTH
) (
    input  logic                       mc_clk,
    input  logic                       mc_rst_n,
    input  logic                       pclk,
    input  logic                       presetn,

    // APB CSR -> generator config block (chargen_regs)
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

    // Run-level aggregate status
    output logic                       gen_wr_started,
    output logic                       gen_rd_started,
    output logic                       gen_wr_done,
    output logic                       gen_rd_done,
    output logic                       gen_any_error,
    output logic                       gen_crc_match,

    // APB CSR -> controller
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

    // DFI passthrough
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

    // Runtime controls
    input  memtype_e                   memtype_i,
    input  logic [7:0]                 t_phy_wrlat_i,
    input  logic [7:0]                 t_rddata_en_i,
    input  logic                       rd_in_order_i,
    input  logic [3:0]                 cap_lookahead_max_i,
    input  logic [3:0]                 cap_synth_mask_i,

    // Reader-engine debug FIFO drain port
    output logic                       rd_dbg_valid,
    input  logic                       rd_dbg_ready,
    output logic [DW-1:0]              rd_dbg_actual,
    output logic [DW-1:0]              rd_dbg_expected,
    output logic                       rd_dbg_mismatch,

    // Perf observability
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
    input  logic                       i_hist_metric,
    input  logic [3:0]                 i_hist_bin,
    output logic [31:0]                perf_wr_hist_count,
    output logic [31:0]                perf_wr_hist_total,
    output logic [31:0]                perf_rd_hist_count,
    output logic [31:0]                perf_rd_hist_total
);

    // Engines, generator config and perf -- the DUT-agnostic half.
    logic [PIW-1:0] wr_awid;   logic [AW-1:0] wr_awaddr;
    logic [7:0]    wr_awlen;   logic [2:0]    wr_awsize;
    logic [1:0]    wr_awburst; logic          wr_awlock;
    logic [3:0]    wr_awcache, wr_awqos, wr_awregion;
    logic [2:0]    wr_awprot;  logic [UW-1:0] wr_awuser, wr_wuser;
    logic          wr_awvalid, wr_awready;
    logic [DW-1:0] wr_wdata;   logic [SW-1:0] wr_wstrb;
    logic          wr_wlast, wr_wvalid, wr_wready;
    logic [PIW-1:0] wr_bid;     logic [1:0]    wr_bresp;
    logic [UW-1:0] wr_buser;   logic          wr_bvalid, wr_bready;

    logic [PIW-1:0] rd_arid;   logic [AW-1:0] rd_araddr;
    logic [7:0]    rd_arlen;   logic [2:0]    rd_arsize;
    logic [1:0]    rd_arburst; logic          rd_arlock;
    logic [3:0]    rd_arcache, rd_arqos, rd_arregion;
    logic [2:0]    rd_arprot;  logic [UW-1:0] rd_aruser, rd_ruser;
    logic          rd_arvalid, rd_arready;
    logic [PIW-1:0] rd_rid;     logic [DW-1:0] rd_rdata;
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

    // Config path: APB CSR -> PeakRDL cpuif shim.
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

    // Retired DFI sideband pins — Granite core does not drive these.
    assign dfi_cke_o              = '1;
    assign dfi_dram_clk_disable_o = '0;
    assign dfi_ctrlupd_req_o      = 1'b0;
    assign dfi_phyupd_ack_o       = 1'b0;

    // Host AXI is AXI_DATA_WIDTH; controller core + DFI run at DRAM_BEAT_WIDTH*DFI_RATE.
    // granite_top_geared bridges host<->core widths with the formal converters.
    granite_top_geared #(
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
        .RD_RET_DEPTH    (RD_RET_DEPTH),
        .CSR_ADDR_W      (APB_ADDR_WIDTH),
        .HAS_LPDDR2      (HAS_LPDDR2),
        .DFI_CDC_EN      (DFI_CDC_EN),
        .HAS_SNARF        (HAS_SNARF),
        .INTAKE_FIFO_DEPTH(INTAKE_FIFO_DEPTH),
        .AXI_SKID_DEPTH   (AXI_SKID_DEPTH),
        .SHARED_ADDR_MAP  (SHARED_ADDR_MAP),
        .HAS_PAGE_POLICY   (HAS_PAGE_POLICY),
        .BANK_TW           (BANK_TW),
        .BANK_CAP_MIXED    (BANK_CAP_MIXED),
        .HAS_AGE           (HAS_AGE),
        .PP_TIMEOUT_CLOSE  (PP_TIMEOUT_CLOSE),
        .DFI_CMD_FIFO_DEPTH(DFI_CMD_FIFO_DEPTH),
        .DFI_WD_FIFO_DEPTH (DFI_WD_FIFO_DEPTH),
        .DFI_RD_FIFO_DEPTH (DFI_RD_FIFO_DEPTH),
        .STORE_BACKEND   (STORE_BACKEND),
        .BANK_FIFO_DEPTH (BANK_FIFO_DEPTH),
        .HEAD2_EN        (HEAD2_EN),
        .FIXED_TIMINGS   (FIXED_TIMINGS)
    ) u_ctrl (
        .aclk                  (mc_clk),
        .aresetn               (mc_rst_n),
        .dfi_clk               (mc_clk),
        .dfi_rstn              (mc_rst_n),
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
endmodule : granite_char_macro
