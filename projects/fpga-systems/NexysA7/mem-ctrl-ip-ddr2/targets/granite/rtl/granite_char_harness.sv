// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: granite_char_harness
// Purpose: Internal integration for the Granite DDR2/LPDDR2 characterization
//          harness. Sibling of build-perf/rtl/ddr2_char_harness.sv; swaps the
//          macro instance to granite_char_macro.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module granite_char_harness
    import granite_pkg::*;
    import mc_common_pkg::*;
    import mem_char_pkg::*;
#(
    parameter int FPGA_CLK_HZ        = 100_000_000,
    parameter int UART_BAUD          = 115_200,
    parameter int LED_UPDATE_HZ      = 200,
    parameter int SEVEN_SEG_REFRESH  = 1_000,

    parameter int DEBUG_SRAM_WORDS   = 512,
    parameter int DFI_MON_RAM_WORDS  = 512,

    parameter int AXI_ADDR_WIDTH     = 32,
    parameter int AXI_DATA_WIDTH     = 64,
    parameter int AXI_ID_WIDTH       = 8,
    parameter int AXI_USER_WIDTH     = 8,
    parameter int AXI_STRB_WIDTH     = AXI_DATA_WIDTH / 8,

    parameter int ROW_WIDTH          = 13,
    parameter int APB_ADDR_WIDTH     = 12,
    parameter int APB_DATA_WIDTH     = 32,
    parameter int APB_STRB_WIDTH     = APB_DATA_WIDTH / 8,
    parameter int APB_PROT_WIDTH     = 3,

    parameter int STRIDE_WIDTH       = 24,
    parameter int TXN_COUNT_WIDTH    = 16,
    parameter int BURST_LEN_WIDTH    = 8,

    parameter int DRAM_BEAT_WIDTH    = AXI_DATA_WIDTH,
    parameter int DRAM_DEVICE_WIDTH  = DRAM_BEAT_WIDTH,
    parameter int DFI_RATE           = 2,
    parameter int DRAM_BL            = 4,
    parameter int BUILD_VERSION      = 1,
    parameter int BURST_LEN_MULTIPLE = 1,
    parameter int DFI_ADDR_BUS_W     = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W     = 3 * DFI_RATE,
    parameter int DFI_CTRL_BUS_W     = DFI_RATE,
    parameter int DFI_CS_BUS_W       = DFI_RATE,
    parameter int DFI_DATA_WIDTH     = DFI_RATE * DRAM_BEAT_WIDTH,
    parameter int DFI_STRB_WIDTH     = DFI_DATA_WIDTH / 8,
    parameter int CMD_MAX_DELAY      = 8,
    parameter int RD_RET_DEPTH       = 32,
    parameter int RD_DBG_FIFO_DEPTH  = 0,
    // injectors per direction in char_gen_unit (<= NUM_BANKS); eight per
    // direction is the owner's load point (2026-10-22)
    parameter int NUM_GEN            = 4,
    parameter bit HAS_LPDDR2         = 1'b1, // LPDDR2 training plane built (0 = DDR2-only build)
    parameter bit DFI_CDC_EN         = 1'b0, // the macro ties dfi_clk to mc_clk: no DFI crossing by default
    // AXI-plane lean knobs (pumice TASK-054), granite defaults = the measured lean form:
    parameter bit HAS_SNARF        = 1'b0, // 1 = snarf probe / staged admit / source arbiter in the read intake (pumice's CAM store); granite's FIFO store has no snarf
    parameter int INTAKE_FIFO_DEPTH = 0,   // rd-data and wr-data FIFOs in the intakes; 0 = none (the skids feed the ring / store directly; cycle-identical, measured)
    parameter int AXI_SKID_DEPTH   = 2,    // R and W skid depth in the AXI slave shells (2..8); 2 measured cycle-identical to 4
    parameter bit SHARED_ADDR_MAP  = 1'b0, // 1 = one address mapper for both intakes with an alternating grant: -23 percent on the mixed family, so OFF
    // granite_core storage and timing knobs (report 5.10): the board ships
    // NUM_ENTRIES 8 on the FIFO store, bank queues pool-deep (BANK_FIFO_DEPTH 0)
    parameter int NUM_ENTRIES        = 8,
    parameter int STORE_BACKEND      = 1,
    parameter int BANK_FIFO_DEPTH    = 0,  // 0 = NUM_ENTRIES
    parameter bit HEAD2_EN           = 1'b1,  // 0 = one head record per bank (FIFO store)
    parameter bit FIXED_TIMINGS      = 1'b0  // 1 = T_* constants replace the TIMINGS CSRs
) (
    input  logic                        aclk,
    input  logic                        aresetn,

    input  logic                        i_uart_rx,
    output logic                        o_uart_tx,

    output logic [15:0]                 o_led,
    output logic [7:0]                  o_seven_seg_an,
    output logic [6:0]                  o_seven_seg_seg,
    output logic                        o_seven_seg_dp,

    output logic [DFI_ADDR_BUS_W-1:0]   o_dfi_address,
    output logic [DFI_BANK_BUS_W-1:0]   o_dfi_bank,
    output logic [DFI_CTRL_BUS_W-1:0]   o_dfi_cas_n,
    output logic [DFI_CTRL_BUS_W-1:0]   o_dfi_ras_n,
    output logic [DFI_CTRL_BUS_W-1:0]   o_dfi_we_n,
    output logic [DFI_CS_BUS_W-1:0]     o_dfi_cs_n,
    output logic [DFI_CS_BUS_W-1:0]     o_dfi_cke,
    output logic [DFI_CS_BUS_W-1:0]     o_dfi_odt,
    output logic [DFI_DATA_WIDTH-1:0]   o_dfi_wrdata,
    output logic [DFI_STRB_WIDTH-1:0]   o_dfi_wrdata_mask,
    output logic [DFI_RATE-1:0]         o_dfi_wrdata_en,
    output logic [DFI_RATE-1:0]         o_dfi_rddata_en,
    input  logic [DFI_DATA_WIDTH-1:0]   i_dfi_rddata,
    input  logic [DFI_RATE-1:0]         i_dfi_rddata_valid,
    output logic [DFI_CS_BUS_W-1:0]     o_dfi_dram_clk_disable,
    output logic                        o_dfi_init_start,
    input  logic                        i_dfi_init_complete,
    output logic                        o_dfi_ctrlupd_req,
    input  logic                        i_dfi_ctrlupd_ack,
    input  logic                        i_dfi_phyupd_req,
    output logic                        o_dfi_phyupd_ack,
    input  logic [1:0]                  i_dfi_phyupd_type,

    output logic [9:0]                  o_phy_csr_adr,
    output logic                        o_phy_csr_we,
    output logic [31:0]                 o_phy_csr_dat_w,
    input  logic [31:0]                 i_phy_csr_dat_r
);

    localparam int CLKS_PER_BIT = FPGA_CLK_HZ / UART_BAUD;

    // Reset synchroniser
    (* ASYNC_REG = "TRUE" *) logic r_rst_meta, r_rst_sync;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_rst_meta <= 1'b0;
            r_rst_sync <= 1'b0;
        end else begin
            r_rst_meta <= 1'b1;
            r_rst_sync <= r_rst_meta;
        end
    )

    logic unit_aresetn;
    assign unit_aresetn = r_rst_sync;

    // UART <-> AXIL bridge
    logic [31:0] uart_awaddr, uart_wdata, uart_araddr, uart_rdata;
    logic [3:0]  uart_wstrb;
    logic [2:0]  uart_awprot, uart_arprot;
    logic [1:0]  uart_bresp, uart_rresp;
    logic        uart_awvalid, uart_awready, uart_wvalid, uart_wready;
    logic        uart_bvalid,  uart_bready;
    logic        uart_arvalid, uart_arready, uart_rvalid, uart_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH (32),
        .AXIL_DATA_WIDTH (32),
        .CLKS_PER_BIT    (CLKS_PER_BIT)
    ) u_uart (
        .aclk     (aclk),
        .aresetn  (unit_aresetn),
        .i_uart_rx(i_uart_rx),
        .o_uart_tx(o_uart_tx),

        .m_axil_awaddr (uart_awaddr),
        .m_axil_awprot (uart_awprot),
        .m_axil_awvalid(uart_awvalid),
        .m_axil_awready(uart_awready),
        .m_axil_wdata  (uart_wdata),
        .m_axil_wstrb  (uart_wstrb),
        .m_axil_wvalid (uart_wvalid),
        .m_axil_wready (uart_wready),
        .m_axil_bresp  (uart_bresp),
        .m_axil_bvalid (uart_bvalid),
        .m_axil_bready (uart_bready),
        .m_axil_araddr (uart_araddr),
        .m_axil_arprot (uart_arprot),
        .m_axil_arvalid(uart_arvalid),
        .m_axil_arready(uart_arready),
        .m_axil_rdata  (uart_rdata),
        .m_axil_rresp  (uart_rresp),
        .m_axil_rvalid (uart_rvalid),
        .m_axil_rready (uart_rready)
    );

    // Slave-side signal declarations for each bridge output
    logic         apb_psel, apb_penable, apb_pwrite;
    logic [31:0]  apb_paddr_full;
    logic [31:0]  apb_pwdata, apb_prdata;
    logic [3:0]   apb_pstrb;
    logic [2:0]   apb_pprot;
    logic         apb_pready, apb_pslverr;

    logic [31:0] s1_awaddr, s1_wdata, s1_araddr, s1_rdata;
    logic [3:0]  s1_wstrb;
    logic [2:0]  s1_awprot, s1_arprot;
    logic [1:0]  s1_bresp, s1_rresp;
    logic s1_awvalid, s1_awready, s1_wvalid, s1_wready, s1_bvalid, s1_bready;
    logic s1_arvalid, s1_arready, s1_rvalid, s1_rready;

    logic [31:0] s2_awaddr, s2_araddr;
    logic [63:0] s2_wdata, s2_rdata;
    logic [7:0]  s2_wstrb;
    logic [2:0]  s2_awprot, s2_arprot;
    logic [1:0]  s2_bresp, s2_rresp;
    logic s2_awvalid, s2_awready, s2_wvalid, s2_wready, s2_bvalid, s2_bready;
    logic s2_arvalid, s2_arready, s2_rvalid, s2_rready;

    logic [31:0] s3_awaddr, s3_wdata, s3_araddr, s3_rdata;
    logic [3:0]  s3_wstrb;
    logic [2:0]  s3_awprot, s3_arprot;
    logic [1:0]  s3_bresp, s3_rresp;
    logic s3_awvalid, s3_awready, s3_wvalid, s3_wready, s3_bvalid, s3_bready;
    logic s3_arvalid, s3_arready, s3_rvalid, s3_rready;

    logic        obs_apb_PSEL, obs_apb_PENABLE, obs_apb_PWRITE;
    logic [31:0] obs_apb_PADDR, obs_apb_PWDATA;
    logic [3:0]  obs_apb_PSTRB;
    logic [2:0]  obs_apb_PPROT;

    logic        chargen_apb_PSEL, chargen_apb_PENABLE, chargen_apb_PWRITE;
    logic [31:0] chargen_apb_PADDR, chargen_apb_PWDATA;
    logic [3:0]  chargen_apb_PSTRB;
    logic [2:0]  chargen_apb_PPROT;
    logic [31:0] chargen_apb_PRDATA;
    logic        chargen_apb_PREADY, chargen_apb_PSLVERR;

    bridge_ddr2_char_axil u_bridge (
        .aclk    (aclk),
        .aresetn (unit_aresetn),

        .host_axi_awaddr  (uart_awaddr),
        .host_axi_awprot  (uart_awprot),
        .host_axi_awvalid (uart_awvalid),
        .host_axi_awready (uart_awready),
        .host_axi_wdata   (uart_wdata),
        .host_axi_wstrb   (uart_wstrb),
        .host_axi_wvalid  (uart_wvalid),
        .host_axi_wready  (uart_wready),
        .host_axi_bresp   (uart_bresp),
        .host_axi_bvalid  (uart_bvalid),
        .host_axi_bready  (uart_bready),
        .host_axi_araddr  (uart_araddr),
        .host_axi_arprot  (uart_arprot),
        .host_axi_arvalid (uart_arvalid),
        .host_axi_arready (uart_arready),
        .host_axi_rdata   (uart_rdata),
        .host_axi_rresp   (uart_rresp),
        .host_axi_rvalid  (uart_rvalid),
        .host_axi_rready  (uart_rready),

        .ddr2_apb_PSEL    (apb_psel),
        .ddr2_apb_PADDR   (apb_paddr_full),
        .ddr2_apb_PENABLE (apb_penable),
        .ddr2_apb_PWRITE  (apb_pwrite),
        .ddr2_apb_PWDATA  (apb_pwdata),
        .ddr2_apb_PSTRB   (apb_pstrb),
        .ddr2_apb_PPROT   (apb_pprot),
        .ddr2_apb_PRDATA  (apb_prdata),
        .ddr2_apb_PREADY  (apb_pready),
        .ddr2_apb_PSLVERR (apb_pslverr),

        .harness_csr_axi_awaddr  (s1_awaddr),
        .harness_csr_axi_awprot  (s1_awprot),
        .harness_csr_axi_awvalid (s1_awvalid),
        .harness_csr_axi_awready (s1_awready),
        .harness_csr_axi_wdata   (s1_wdata),
        .harness_csr_axi_wstrb   (s1_wstrb),
        .harness_csr_axi_wvalid  (s1_wvalid),
        .harness_csr_axi_wready  (s1_wready),
        .harness_csr_axi_bresp   (s1_bresp),
        .harness_csr_axi_bvalid  (s1_bvalid),
        .harness_csr_axi_bready  (s1_bready),
        .harness_csr_axi_araddr  (s1_araddr),
        .harness_csr_axi_arprot  (s1_arprot),
        .harness_csr_axi_arvalid (s1_arvalid),
        .harness_csr_axi_arready (s1_arready),
        .harness_csr_axi_rdata   (s1_rdata),
        .harness_csr_axi_rresp   (s1_rresp),
        .harness_csr_axi_rvalid  (s1_rvalid),
        .harness_csr_axi_rready  (s1_rready),

        .debug_sram_axi_awaddr  (s2_awaddr),
        .debug_sram_axi_awprot  (s2_awprot),
        .debug_sram_axi_awvalid (s2_awvalid),
        .debug_sram_axi_awready (s2_awready),
        .debug_sram_axi_wdata   (s2_wdata),
        .debug_sram_axi_wstrb   (s2_wstrb),
        .debug_sram_axi_wvalid  (s2_wvalid),
        .debug_sram_axi_wready  (s2_wready),
        .debug_sram_axi_bresp   (s2_bresp),
        .debug_sram_axi_bvalid  (s2_bvalid),
        .debug_sram_axi_bready  (s2_bready),
        .debug_sram_axi_araddr  (s2_araddr),
        .debug_sram_axi_arprot  (s2_arprot),
        .debug_sram_axi_arvalid (s2_arvalid),
        .debug_sram_axi_arready (s2_arready),
        .debug_sram_axi_rdata   (s2_rdata),
        .debug_sram_axi_rresp   (s2_rresp),
        .debug_sram_axi_rvalid  (s2_rvalid),
        .debug_sram_axi_rready  (s2_rready),

        .dfi_mon_ram_axi_awaddr  (s3_awaddr),
        .dfi_mon_ram_axi_awprot  (s3_awprot),
        .dfi_mon_ram_axi_awvalid (s3_awvalid),
        .dfi_mon_ram_axi_awready (s3_awready),
        .dfi_mon_ram_axi_wdata   (s3_wdata),
        .dfi_mon_ram_axi_wstrb   (s3_wstrb),
        .dfi_mon_ram_axi_wvalid  (s3_wvalid),
        .dfi_mon_ram_axi_wready  (s3_wready),
        .dfi_mon_ram_axi_bresp   (s3_bresp),
        .dfi_mon_ram_axi_bvalid  (s3_bvalid),
        .dfi_mon_ram_axi_bready  (s3_bready),
        .dfi_mon_ram_axi_araddr  (s3_araddr),
        .dfi_mon_ram_axi_arprot  (s3_arprot),
        .dfi_mon_ram_axi_arvalid (s3_arvalid),
        .dfi_mon_ram_axi_arready (s3_arready),
        .dfi_mon_ram_axi_rdata   (s3_rdata),
        .dfi_mon_ram_axi_rresp   (s3_rresp),
        .dfi_mon_ram_axi_rvalid  (s3_rvalid),
        .dfi_mon_ram_axi_rready  (s3_rready),

        .obs_apb_PSEL     (obs_apb_PSEL),
        .obs_apb_PADDR    (obs_apb_PADDR),
        .obs_apb_PENABLE  (obs_apb_PENABLE),
        .obs_apb_PWRITE   (obs_apb_PWRITE),
        .obs_apb_PWDATA   (obs_apb_PWDATA),
        .obs_apb_PSTRB    (obs_apb_PSTRB),
        .obs_apb_PPROT    (obs_apb_PPROT),
        .obs_apb_PRDATA   (32'h0),
        .obs_apb_PREADY   (1'b1),
        .obs_apb_PSLVERR  (1'b0),

        .chargen_apb_PSEL     (chargen_apb_PSEL),
        .chargen_apb_PADDR    (chargen_apb_PADDR),
        .chargen_apb_PENABLE  (chargen_apb_PENABLE),
        .chargen_apb_PWRITE   (chargen_apb_PWRITE),
        .chargen_apb_PWDATA   (chargen_apb_PWDATA),
        .chargen_apb_PSTRB    (chargen_apb_PSTRB),
        .chargen_apb_PPROT    (chargen_apb_PPROT),
        .chargen_apb_PRDATA   (chargen_apb_PRDATA),
        .chargen_apb_PREADY   (chargen_apb_PREADY),
        .chargen_apb_PSLVERR  (chargen_apb_PSLVERR)
    );

    // harness_csr
    logic         w_start_wr_pulse, w_start_rd_pulse;
    logic         w_clear_stats_pulse, w_freeze_trace, w_soft_reset_pulse;
    logic         w_wr_done, w_rd_done;
    logic         w_wr_error, w_rd_error;
    logic         w_init_done, w_init_fail;
    logic [31:0]  w_dbg_wr_ptr;
    logic         w_dbg_overflow, w_dbg_clear_busy;

    logic         w_gen_any_error, w_gen_crc_match;

    logic         w_timer_clear_pulse;
    logic [31:0]  w_timer_expected_beats;
    logic         w_timer_done, w_timer_running, w_timer_pass;
    logic [63:0]  w_timer_cycles;
    logic [63:0]  w_timer_r_first, w_timer_r_last;
    logic [63:0]  w_timer_w_first, w_timer_w_last;

    logic [15:0]  w_rd_resp_delay_cyc, w_wr_resp_delay_cyc;

    logic         w_perf_clear, w_perf_freeze;
    logic [31:0]  w_obs_rd_prod, w_obs_rd_bp, w_obs_rd_starv, w_obs_rd_idle;
    logic [31:0]  w_obs_wr_prod, w_obs_wr_bp, w_obs_wr_starv, w_obs_wr_idle;
    logic         w_obs_hist_metric, w_obs_hist_bus_sel;
    logic [3:0]   w_obs_hist_bin;
    logic [31:0]  w_obs_rd_hist_count, w_obs_rd_hist_total;
    logic [31:0]  w_obs_wr_hist_count, w_obs_wr_hist_total;

    mem_variant_e w_mem_variant;
    memtype_e     w_memtype;
    always_comb w_memtype = (w_mem_variant == MEMVARIANT_LP) ? MEMTYPE_LPDDR2
                                                             : MEMTYPE_DDR2;
    logic [7:0]   w_t_phy_wrlat, w_t_rddata_en;
    logic         w_rd_in_order;
    logic [3:0]   w_cap_lookahead_max, w_cap_synth_mask;
    logic [3:0]   w_cmd_delay_sel;
    logic [3:0]   w_rddata_delay_sel;
    (* mark_debug = "true" *) logic [DFI_DATA_WIDTH-1:0] w_dfi_rddata_dly;

    harness_csr #(
        .AW              (32),
        .DW              (32),
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .STRIDE_WIDTH    (STRIDE_WIDTH),
        .TXN_COUNT_WIDTH (TXN_COUNT_WIDTH),
        .BURST_LEN_WIDTH (BURST_LEN_WIDTH),
        .BUILD_VERSION   (BUILD_VERSION),
        .CFG_CLK_HZ      (FPGA_CLK_HZ),
        .CFG_DFI_RATE    (DFI_RATE),
        .CFG_DRAM_BL     (DRAM_BL),
        .CFG_ROW_WIDTH   (ROW_WIDTH),
        .CFG_BANK_WIDTH  (DFI_BANK_BUS_W),
        .CFG_AXI_DATA_W  (AXI_DATA_WIDTH),
        .CFG_DRAM_BEAT_W (DRAM_BEAT_WIDTH),
        .CFG_DRAM_DEVICE_W (DRAM_DEVICE_WIDTH)
    ) u_harness_csr (
        .aclk    (aclk),
        .aresetn (unit_aresetn),

        .s_awaddr  (s1_awaddr),  .s_awprot (s1_awprot),
        .s_awvalid (s1_awvalid), .s_awready(s1_awready),
        .s_wdata   (s1_wdata),   .s_wstrb  (s1_wstrb),
        .s_wvalid  (s1_wvalid),  .s_wready (s1_wready),
        .s_bresp   (s1_bresp),   .s_bvalid (s1_bvalid),  .s_bready (s1_bready),
        .s_araddr  (s1_araddr),  .s_arprot (s1_arprot),
        .s_arvalid (s1_arvalid), .s_arready(s1_arready),
        .s_rdata   (s1_rdata),   .s_rresp  (s1_rresp),
        .s_rvalid  (s1_rvalid),  .s_rready (s1_rready),

        .o_clear_stats_pulse (w_clear_stats_pulse),
        .o_freeze_trace      (w_freeze_trace),
        .o_soft_reset_pulse  (w_soft_reset_pulse),

        .i_wr_done         (w_wr_done),
        .i_rd_done         (w_rd_done),
        .i_wr_error        (w_wr_error),
        .i_rd_error        (w_rd_error),
        .i_init_done       (w_init_done),
        .i_init_fail       (w_init_fail),
        .i_dbg_wr_ptr      (w_dbg_wr_ptr),
        .i_dbg_overflow    (w_dbg_overflow),
        .i_dbg_clear_busy  (w_dbg_clear_busy),

        .i_crc_match       (w_gen_crc_match),

        .o_timer_clear_pulse    (w_timer_clear_pulse),
        .o_timer_expected_beats (w_timer_expected_beats),
        .i_timer_done           (w_timer_done),
        .i_timer_running        (w_timer_running),
        .i_timer_pass           (w_timer_pass),
        .i_timer_cycles         (w_timer_cycles),
        .i_timer_r_first        (w_timer_r_first),
        .i_timer_r_last         (w_timer_r_last),
        .i_timer_w_first        (w_timer_w_first),
        .i_timer_w_last         (w_timer_w_last),

        .o_rd_resp_delay_cyc (w_rd_resp_delay_cyc),
        .o_wr_resp_delay_cyc (w_wr_resp_delay_cyc),

        .o_perf_clear         (w_perf_clear),
        .o_perf_freeze        (w_perf_freeze),
        .i_obs_rd_prod        (w_obs_rd_prod),
        .i_obs_rd_bp          (w_obs_rd_bp),
        .i_obs_rd_starv       (w_obs_rd_starv),
        .i_obs_rd_idle        (w_obs_rd_idle),
        .i_obs_wr_prod        (w_obs_wr_prod),
        .i_obs_wr_bp          (w_obs_wr_bp),
        .i_obs_wr_starv       (w_obs_wr_starv),
        .i_obs_wr_idle        (w_obs_wr_idle),
        .o_obs_hist_metric    (w_obs_hist_metric),
        .o_obs_hist_bin       (w_obs_hist_bin),
        .o_obs_hist_bus_sel   (w_obs_hist_bus_sel),
        .i_obs_rd_hist_count  (w_obs_rd_hist_count),
        .i_obs_rd_hist_total  (w_obs_rd_hist_total),
        .i_obs_wr_hist_count  (w_obs_wr_hist_count),
        .i_obs_wr_hist_total  (w_obs_wr_hist_total),

        .o_mem_variant       (w_mem_variant),
        .o_t_phy_wrlat       (w_t_phy_wrlat),
        .o_t_rddata_en       (w_t_rddata_en),
        .o_rd_in_order       (w_rd_in_order),
        .o_cap_lookahead_max (w_cap_lookahead_max),
        .o_cap_synth_mask    (w_cap_synth_mask),
        .o_cmd_delay         (w_cmd_delay_sel),
        .o_rddata_delay      (w_rddata_delay_sel),

        .o_phy_csr_adr       (o_phy_csr_adr),
        .o_phy_csr_we        (o_phy_csr_we),
        .o_phy_csr_dat_w     (o_phy_csr_dat_w),
        .i_phy_csr_dat_r     (i_phy_csr_dat_r)
    );

    // debug_sram
    logic w_debug_sram_dbg_bram_wr_pulse;
    logic w_debug_sram_dbg_busy_wr;
    sdpram_slave_axil_axil #(
        .ADDR_WIDTH (32),
        .DATA_WIDTH (64),
        .MEM_DEPTH  (DEBUG_SRAM_WORDS / 2)
    ) u_debug_sram (
        .aclk(aclk), .aresetn(unit_aresetn),
        .s_axil_awaddr (s2_awaddr), .s_axil_awprot(s2_awprot),
        .s_axil_awvalid(s2_awvalid), .s_axil_awready(s2_awready),
        .s_axil_wdata  (s2_wdata),  .s_axil_wstrb (s2_wstrb),
        .s_axil_wvalid (s2_wvalid), .s_axil_wready(s2_wready),
        .s_axil_bresp  (s2_bresp), .s_axil_bvalid(s2_bvalid), .s_axil_bready(s2_bready),
        .s_axil_araddr (s2_araddr), .s_axil_arprot(s2_arprot),
        .s_axil_arvalid(s2_arvalid), .s_axil_arready(s2_arready),
        .s_axil_rdata  (s2_rdata), .s_axil_rresp (s2_rresp),
        .s_axil_rvalid (s2_rvalid), .s_axil_rready(s2_rready),
        .i_cfg_start_clear (w_clear_stats_pulse & ~w_freeze_trace),
        .o_cfg_done_clear  (),
        .o_dbg_vr(), .o_dbg_fub_vr(),
        .o_dbg_bram_wr(w_debug_sram_dbg_bram_wr_pulse),
        .o_dbg_bram_rd(),
        .o_dbg_busy_wr(w_debug_sram_dbg_busy_wr),
        .o_dbg_busy_rd()
    );

    logic [31:0] r_dbg_wr_ptr;
    logic        r_dbg_overflow;
    `ALWAYS_FF_RST(aclk, unit_aresetn,
        if (`RST_ASSERTED(unit_aresetn)) begin
            r_dbg_wr_ptr   <= '0;
            r_dbg_overflow <= 1'b0;
        end else if (w_clear_stats_pulse) begin
            r_dbg_wr_ptr   <= '0;
            r_dbg_overflow <= 1'b0;
        end else if (w_debug_sram_dbg_bram_wr_pulse && !w_freeze_trace) begin
            if (r_dbg_wr_ptr == 32'hFFFF_FFFF) r_dbg_overflow <= 1'b1;
            else                                r_dbg_wr_ptr <= r_dbg_wr_ptr + 32'd1;
        end
    )
    assign w_dbg_wr_ptr     = r_dbg_wr_ptr;
    assign w_dbg_overflow   = r_dbg_overflow;
    assign w_dbg_clear_busy = w_debug_sram_dbg_busy_wr;

    // dfi_mon_ram
    sdpram_slave_axil_axil #(
        .ADDR_WIDTH (32),
        .DATA_WIDTH (32),
        .MEM_DEPTH  (DFI_MON_RAM_WORDS)
    ) u_dfi_mon_ram (
        .aclk(aclk), .aresetn(unit_aresetn),
        .s_axil_awaddr (s3_awaddr), .s_axil_awprot(s3_awprot),
        .s_axil_awvalid(s3_awvalid), .s_axil_awready(s3_awready),
        .s_axil_wdata  (s3_wdata),  .s_axil_wstrb (s3_wstrb),
        .s_axil_wvalid (s3_wvalid), .s_axil_wready(s3_wready),
        .s_axil_bresp  (s3_bresp), .s_axil_bvalid(s3_bvalid), .s_axil_bready(s3_bready),
        .s_axil_araddr (s3_araddr), .s_axil_arprot(s3_arprot),
        .s_axil_arvalid(s3_arvalid), .s_axil_arready(s3_arready),
        .s_axil_rdata  (s3_rdata), .s_axil_rresp (s3_rresp),
        .s_axil_rvalid (s3_rvalid), .s_axil_rready(s3_rready),
        .i_cfg_start_clear (1'b0),
        .o_cfg_done_clear  (),
        .o_dbg_vr(), .o_dbg_fub_vr(), .o_dbg_bram_wr(), .o_dbg_bram_rd(),
        .o_dbg_busy_wr(), .o_dbg_busy_rd()
    );

    // Datapath soft-reset
    logic [3:0] r_soft_rst_cnt;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (!aresetn)                    r_soft_rst_cnt <= 4'd0;
        else if (w_soft_reset_pulse)     r_soft_rst_cnt <= 4'd15;
        else if (r_soft_rst_cnt != 4'd0) r_soft_rst_cnt <= r_soft_rst_cnt - 4'd1;
    )

    logic dp_aresetn;
    assign dp_aresetn = unit_aresetn & (r_soft_rst_cnt == 4'd0);

    // Granite macro (DUT)
    (* mark_debug = "true" *) logic w_rd_dbg_valid;
    (* mark_debug = "true" *) logic w_rd_dbg_mismatch;
    logic w_rd_dbg_ready;
    (* mark_debug = "true" *) logic [AXI_DATA_WIDTH-1:0] w_rd_dbg_actual;
    (* mark_debug = "true" *) logic [AXI_DATA_WIDTH-1:0] w_rd_dbg_expected;

    logic [DFI_ADDR_BUS_W-1:0] w_c_dfi_address;
    logic [DFI_BANK_BUS_W-1:0] w_c_dfi_bank;
    logic [DFI_CTRL_BUS_W-1:0] w_c_dfi_cas_n, w_c_dfi_ras_n, w_c_dfi_we_n;
    logic [DFI_CS_BUS_W-1:0]   w_c_dfi_cs_n, w_c_dfi_cke, w_c_dfi_odt;
    logic [DFI_RATE-1:0]       w_c_dfi_rddata_en;

    granite_char_macro #(
        .AXI_ADDR_WIDTH    (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH    (AXI_DATA_WIDTH),
        .DRAM_BEAT_WIDTH   (DRAM_BEAT_WIDTH),
        .DRAM_DEVICE_WIDTH (DRAM_DEVICE_WIDTH),
        .DFI_RATE          (DFI_RATE),
        .DRAM_BL           (DRAM_BL),
        .BURST_LEN_MULTIPLE(BURST_LEN_MULTIPLE),
        .AXI_ID_WIDTH      (AXI_ID_WIDTH),
        .AXI_USER_WIDTH    (AXI_USER_WIDTH),
        .ROW_WIDTH         (ROW_WIDTH),
        .WR_CAM_DEPTH      (NUM_ENTRIES),
        .RD_RET_DEPTH      (RD_RET_DEPTH),
        .RD_DBG_FIFO_DEPTH (RD_DBG_FIFO_DEPTH),
        .NUM_GEN           (NUM_GEN),
        .APB_ADDR_WIDTH    (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH    (APB_DATA_WIDTH),
        .HAS_LPDDR2        (HAS_LPDDR2),
        .DFI_CDC_EN        (DFI_CDC_EN),
        .HAS_SNARF        (HAS_SNARF),
        .INTAKE_FIFO_DEPTH(INTAKE_FIFO_DEPTH),
        .AXI_SKID_DEPTH   (AXI_SKID_DEPTH),
        .SHARED_ADDR_MAP  (SHARED_ADDR_MAP),
        .STORE_BACKEND     (STORE_BACKEND),
        .BANK_FIFO_DEPTH   (BANK_FIFO_DEPTH),
        .HEAD2_EN          (HEAD2_EN),
        .FIXED_TIMINGS     (FIXED_TIMINGS)
    ) u_dut (
        .mc_clk   (aclk),
        .mc_rst_n (dp_aresetn),
        .pclk     (aclk),
        .presetn  (unit_aresetn),

        .s_chargen_apb_PSEL    (chargen_apb_PSEL),
        .s_chargen_apb_PENABLE (chargen_apb_PENABLE),
        .s_chargen_apb_PREADY  (chargen_apb_PREADY),
        .s_chargen_apb_PADDR   (chargen_apb_PADDR[APB_ADDR_WIDTH-1:0]),
        .s_chargen_apb_PWRITE  (chargen_apb_PWRITE),
        .s_chargen_apb_PWDATA  (chargen_apb_PWDATA),
        .s_chargen_apb_PSTRB   (chargen_apb_PSTRB[APB_STRB_WIDTH-1:0]),
        .s_chargen_apb_PPROT   (chargen_apb_PPROT[APB_PROT_WIDTH-1:0]),
        .s_chargen_apb_PRDATA  (chargen_apb_PRDATA),
        .s_chargen_apb_PSLVERR (chargen_apb_PSLVERR),

        .gen_wr_started (w_start_wr_pulse),
        .gen_rd_started (w_start_rd_pulse),
        .gen_wr_done    (w_wr_done),
        .gen_rd_done    (w_rd_done),
        .gen_any_error  (w_gen_any_error),
        .gen_crc_match  (w_gen_crc_match),

        .s_apb_PSEL    (apb_psel),
        .s_apb_PENABLE (apb_penable),
        .s_apb_PREADY  (apb_pready),
        .s_apb_PADDR   (apb_paddr_full[APB_ADDR_WIDTH-1:0]),
        .s_apb_PWRITE  (apb_pwrite),
        .s_apb_PWDATA  (apb_pwdata),
        .s_apb_PSTRB   (apb_pstrb[APB_STRB_WIDTH-1:0]),
        .s_apb_PPROT   (apb_pprot[APB_PROT_WIDTH-1:0]),
        .s_apb_PRDATA  (apb_prdata),
        .s_apb_PSLVERR (apb_pslverr),

        .dfi_address_o          (w_c_dfi_address),
        .dfi_bank_o             (w_c_dfi_bank),
        .dfi_cas_n_o            (w_c_dfi_cas_n),
        .dfi_ras_n_o            (w_c_dfi_ras_n),
        .dfi_we_n_o             (w_c_dfi_we_n),
        .dfi_cs_n_o             (w_c_dfi_cs_n),
        .dfi_cke_o              (w_c_dfi_cke),
        .dfi_odt_o              (w_c_dfi_odt),
        .dfi_wrdata_o           (o_dfi_wrdata),
        .dfi_wrdata_mask_o      (o_dfi_wrdata_mask),
        .dfi_wrdata_en_o        (o_dfi_wrdata_en),
        .dfi_rddata_en_o        (w_c_dfi_rddata_en),
        .dfi_rddata_i           (w_dfi_rddata_dly),
        .dfi_rddata_valid_i     (i_dfi_rddata_valid),
        .dfi_dram_clk_disable_o (o_dfi_dram_clk_disable),
        .dfi_init_start_o       (o_dfi_init_start),
        .dfi_init_complete_i    (i_dfi_init_complete),
        .dfi_ctrlupd_req_o      (o_dfi_ctrlupd_req),
        .dfi_ctrlupd_ack_i      (i_dfi_ctrlupd_ack),
        .dfi_phyupd_req_i       (i_dfi_phyupd_req),
        .dfi_phyupd_ack_o       (o_dfi_phyupd_ack),
        .dfi_phyupd_type_i      (i_dfi_phyupd_type),

        .memtype_i             (w_memtype),
        .t_phy_wrlat_i         (w_t_phy_wrlat),
        .t_rddata_en_i         (w_t_rddata_en),
        .rd_in_order_i         (w_rd_in_order),
        .cap_lookahead_max_i   (w_cap_lookahead_max),
        .cap_synth_mask_i      (w_cap_synth_mask),

        .rd_dbg_valid    (w_rd_dbg_valid),
        .rd_dbg_ready    (w_rd_dbg_ready),
        .rd_dbg_actual   (w_rd_dbg_actual),
        .rd_dbg_expected (w_rd_dbg_expected),
        .rd_dbg_mismatch (w_rd_dbg_mismatch),

        .perf_clear       (w_perf_clear),
        .perf_freeze      (w_perf_freeze),
        .perf_wr_prod     (w_obs_wr_prod),
        .perf_wr_bp       (w_obs_wr_bp),
        .perf_wr_starv    (w_obs_wr_starv),
        .perf_wr_idle     (w_obs_wr_idle),
        .perf_rd_prod     (w_obs_rd_prod),
        .perf_rd_bp       (w_obs_rd_bp),
        .perf_rd_starv    (w_obs_rd_starv),
        .perf_rd_idle     (w_obs_rd_idle),
        .i_hist_metric    (w_obs_hist_metric),
        .i_hist_bin       (w_obs_hist_bin),
        .perf_wr_hist_count(w_obs_wr_hist_count),
        .perf_wr_hist_total(w_obs_wr_hist_total),
        .perf_rd_hist_count(w_obs_rd_hist_count),
        .perf_rd_hist_total(w_obs_rd_hist_total)
    );

    dfi_cmd_delay #(
        .DFI_ADDR_BUS_W (DFI_ADDR_BUS_W),
        .DFI_BANK_BUS_W (DFI_BANK_BUS_W),
        .DFI_CTRL_BUS_W (DFI_CTRL_BUS_W),
        .DFI_CS_BUS_W   (DFI_CS_BUS_W),
        .DFI_RATE       (DFI_RATE),
        .MAX_DELAY      (CMD_MAX_DELAY)
    ) u_dfi_cmd_delay (
        .mc_clk      (aclk),
        .mc_rst_n    (aresetn),
        .sel_i       (w_cmd_delay_sel[$clog2(CMD_MAX_DELAY+1)-1:0]),
        .i_address   (w_c_dfi_address),
        .i_bank      (w_c_dfi_bank),
        .i_cas_n     (w_c_dfi_cas_n),
        .i_ras_n     (w_c_dfi_ras_n),
        .i_we_n      (w_c_dfi_we_n),
        .i_cs_n      (w_c_dfi_cs_n),
        .i_cke       (w_c_dfi_cke),
        .i_odt       (w_c_dfi_odt),
        .i_rddata_en (w_c_dfi_rddata_en),
        .o_address   (o_dfi_address),
        .o_bank      (o_dfi_bank),
        .o_cas_n     (o_dfi_cas_n),
        .o_ras_n     (o_dfi_ras_n),
        .o_we_n      (o_dfi_we_n),
        .o_cs_n      (o_dfi_cs_n),
        .o_cke       (o_dfi_cke),
        .o_odt       (o_dfi_odt),
        .o_rddata_en (o_dfi_rddata_en)
    );

    dfi_rddata_delay #(
        .DFI_DATA_WIDTH (DFI_DATA_WIDTH),
        .MAX_DELAY      (15)
    ) u_dfi_rddata_delay (
        .mc_clk   (aclk),
        .mc_rst_n (aresetn),
        .sel_i    (w_rddata_delay_sel),
        .i_rddata (i_dfi_rddata),
        .o_rddata (w_dfi_rddata_dly)
    );

    assign w_rd_dbg_ready = 1'b1;
    assign w_wr_error     = w_gen_any_error;
    assign w_rd_error     = w_gen_any_error | w_rd_dbg_mismatch;
    assign w_init_done    = 1'b1;
    assign w_init_fail    = 1'b0;

    // Characterization timer
    logic [63:0] r_cycles;
    logic        r_running, r_done;
    logic [63:0] r_w_first, r_w_last, r_r_first, r_r_last;
    logic        r_w_first_valid, r_r_first_valid;
    logic        r_w_last_valid, r_r_last_valid;
    logic        r_wr_kicked, r_rd_kicked;

    logic run_start;
    assign run_start = w_start_wr_pulse | w_start_rd_pulse;

    logic w_all_kicked_done;
    assign w_all_kicked_done = (r_wr_kicked | r_rd_kicked)
                             & (~r_wr_kicked | w_wr_done)
                             & (~r_rd_kicked | w_rd_done);

    `ALWAYS_FF_RST(aclk, unit_aresetn,
        if (`RST_ASSERTED(unit_aresetn)) begin
            r_cycles        <= '0;
            r_running       <= 1'b0;
            r_done          <= 1'b0;
            r_w_first       <= '0; r_w_last <= '0;
            r_r_first       <= '0; r_r_last <= '0;
            r_w_first_valid <= 1'b0;
            r_r_first_valid <= 1'b0;
            r_w_last_valid  <= 1'b0;
            r_r_last_valid  <= 1'b0;
            r_wr_kicked     <= 1'b0;
            r_rd_kicked     <= 1'b0;
        end else if (w_timer_clear_pulse) begin
            r_cycles        <= '0;
            r_running       <= 1'b0;
            r_done          <= 1'b0;
            r_w_first       <= '0; r_w_last <= '0;
            r_r_first       <= '0; r_r_last <= '0;
            r_w_first_valid <= 1'b0;
            r_r_first_valid <= 1'b0;
            r_w_last_valid  <= 1'b0;
            r_r_last_valid  <= 1'b0;
            r_wr_kicked     <= 1'b0;
            r_rd_kicked     <= 1'b0;
        end else begin
            if (w_start_wr_pulse) r_wr_kicked <= 1'b1;
            if (w_start_rd_pulse) r_rd_kicked <= 1'b1;
            if (run_start && !r_running) r_running <= 1'b1;
            if (w_start_wr_pulse && !r_w_first_valid) begin
                r_w_first       <= r_cycles;
                r_w_first_valid <= 1'b1;
            end
            if (w_start_rd_pulse && !r_r_first_valid) begin
                r_r_first       <= r_cycles;
                r_r_first_valid <= 1'b1;
            end
            if (r_running) begin
                r_cycles <= r_cycles + 64'd1;
                if (w_wr_done && !r_w_last_valid) begin
                    r_w_last       <= r_cycles;
                    r_w_last_valid <= 1'b1;
                end
                if (w_rd_done && !r_r_last_valid) begin
                    r_r_last       <= r_cycles;
                    r_r_last_valid <= 1'b1;
                end
                if (w_all_kicked_done) begin
                    r_running <= 1'b0;
                    r_done    <= 1'b1;
                end
            end
        end
    )

    assign w_timer_cycles   = r_cycles;
    assign w_timer_running  = r_running;
    assign w_timer_done     = r_done;
    assign w_timer_pass     = r_done
                             & ~w_wr_error & ~w_rd_error
                             & w_gen_crc_match;
    assign w_timer_w_first  = r_w_first;
    assign w_timer_w_last   = r_w_last;
    assign w_timer_r_first  = r_r_first;
    assign w_timer_r_last   = r_r_last;

    // LED status + 7-segment display
    logic [15:0] w_led_status;
    always_comb begin
        w_led_status        = '0;
        w_led_status[0]     = w_init_done;
        w_led_status[1]     = w_wr_error | w_rd_error;
        w_led_status[2]     = w_dbg_overflow;
        w_led_status[3]     = w_timer_done;
        w_led_status[4]     = w_timer_pass;
        w_led_status[5]     = w_timer_running;
        w_led_status[6]     = w_wr_done;
        w_led_status[7]     = w_rd_done;
        w_led_status[8]     = w_gen_crc_match;
        w_led_status[9]     = w_gen_any_error;
        w_led_status[10]    = w_dbg_clear_busy;
    end

    led_status_driver #(
        .FPGA_CLK_HZ   (FPGA_CLK_HZ),
        .LED_UPDATE_HZ (LED_UPDATE_HZ),
        .NUM_LEDS      (16)
    ) u_led_status_driver (
        .aclk    (aclk),
        .aresetn (unit_aresetn),
        .i_status(w_led_status),
        .o_led   (o_led)
    );

    seven_seg_4digit #(
        .FPGA_CLK_HZ (FPGA_CLK_HZ),
        .REFRESH_HZ  (SEVEN_SEG_REFRESH)
    ) u_seven_seg (
        .aclk    (aclk),
        .aresetn (unit_aresetn),
        .i_hex   (r_cycles[15:0]),
        .i_enable(1'b1),
        .o_an    (o_seven_seg_an),
        .o_seg   (o_seven_seg_seg),
        .o_dp    (o_seven_seg_dp)
    );

    /* verilator lint_off UNUSED */
    generate
        if (APB_ADDR_WIDTH < 32) begin : g_apb_addr_unused
            wire _unused_apb_addr = &{1'b0, apb_paddr_full[31:APB_ADDR_WIDTH]};
        end
    endgenerate
    wire _unused_ok = &{1'b0,
        w_timer_expected_beats,
        w_rd_resp_delay_cyc, w_wr_resp_delay_cyc,
        w_rd_dbg_valid, w_rd_dbg_actual, w_rd_dbg_expected,
        1'b0};
    /* verilator lint_on UNUSED */

endmodule : granite_char_harness
