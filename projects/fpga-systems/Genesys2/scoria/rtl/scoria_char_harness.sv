// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: scoria_char_harness
// Purpose: Everything between the board pins and the DFI bus -- the host UART
//          path, the config decode, the harness control block, the scoria char
//          macro, and the two DFI tuning delay lines. The board top adds only
//          clocking, the PHY and the pads.
//
// THE DDR3 SIBLING OF ddr2_char_harness, AND DELIBERATELY THINNER. pumice's is
// ~1000 lines because it carries a 256 KB trace SRAM, a DFI monitor ring and an
// observer expansion slot. None of those is addressed by scoria's host, and
// none of them helps get a first bitstream onto a board. What is here is what
// the host already drives and what bring-up cannot proceed without.
//
// ALMOST ALL OF IT IS SHARED. uart_axil_bridge comes from the converters
// component; harness_csr, dfi_cmd_delay, dfi_rddata_delay, led_status_driver
// and the char engine inside the macro all come from
// projects/fpga-systems/rtl/mem_char_framework. The only scoria-specific RTL
// in this file is the parameter set and the wiring -- which is the point: a
// bandwidth number from this harness is comparable with pumice's because the
// instruments are the same instruments.
//
// THE TWO DELAY LINES ARE NOT OPTIONAL. dfi_cmd_delay and dfi_rddata_delay are
// how a bring-up tuple is found. pumice's working DDR2 set was wrlat 1, rden 6,
// rddata_delay 7, bitslip 0, tap 8 -- discovered by sweeping these from the
// host, after an ILA showed the PHY's read DATA leading its rddata_valid by
// about read_latency cycles (project_ddr2_ila_read_valid_skew). A harness
// without them can only report that reads are wrong, not find out why.
//
// WIDTHS. DRAM_BEAT_WIDTH is the DFI data width PER PHASE and is TWICE the DQ
// width on DDR3 -- 64 over a 32-bit bus -- because a phase carries two
// transfers. DRAM_DEVICE_WIDTH is the DQ bus itself. Conflating them produces a
// 128-bit DFI word that the K7 PHY cannot consume; see dfi_flat_to_k7ddrphy.
//
// The PHY's calibration CSR bus passes straight through to the top, because the
// PHY lives there. harness_csr owns the registers (DFI_TUNING and the
// o_phy_csr_* indirection); this module just carries the wires.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module scoria_char_harness
    // mem_char_pkg for mem_variant_e (harness_csr's o_mem_variant), scoria_pkg
    // for memtype_e (the macro's memtype_i). The two enums encode the same
    // field with different meanings -- MEMTYPE=0 is DDR3 here and DDR2 on
    // pumice -- which is why the cast below is explicit rather than implicit.
    import mem_char_pkg::*;
    import scoria_pkg::memtype_e;
#(
    // ---- host ------------------------------------------------------------
    parameter int CLKS_PER_BIT   = 695,     // 80 MHz / 115200 baud
    // ---- geometry: the Genesys 2 board, 2 x MT41J256M16 ------------------
    parameter int NUM_RANKS      = 1,
    parameter int NUM_BANKS      = 8,
    parameter int ROW_WIDTH      = 15,
    parameter int COL_WIDTH      = 10,
    parameter int DFI_RATE       = 4,       // = PHY nphases; DDR3 is 1:4 only
    parameter int DRAM_BL        = 8,
    parameter int DRAM_BEAT_WIDTH   = 64,   // DFI data PER PHASE (2 x DQ)
    parameter int DRAM_DEVICE_WIDTH = 32,   // the DQ bus
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 64,      // host AXI; geared to the DFI word
    parameter int AXI_ID_WIDTH   = 8,
    parameter int CLK_HZ         = 80_000_000,
    // ---- tuning ranges ---------------------------------------------------
    parameter int CMD_MAX_DELAY  = 15,
    parameter int RDDATA_MAX_DELAY = 15,
    // ---- derived DFI bus widths -- do not override -----------------------
    parameter int DFI_DATA_WIDTH = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DFI_STRB_WIDTH = DFI_DATA_WIDTH / 8,
    parameter int DFI_EN_WIDTH   = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int DFI_ADDR_BUS_W = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W = $clog2(NUM_BANKS) * DFI_RATE,
    parameter int DFI_CTRL_BUS_W = 1 * DFI_RATE,
    parameter int DFI_CS_BUS_W   = NUM_RANKS * DFI_RATE
) (
    input  logic aclk,          // the controller clock (CLK_HZ)
    input  logic aresetn,

    // ---- board ------------------------------------------------------------
    input  logic        i_uart_rx,
    output logic        o_uart_tx,
    output logic [7:0]  o_led,

    // ---- DFI, flat and phase-packed, to dfi_flat_to_k7ddrphy -------------
    output logic [DFI_ADDR_BUS_W-1:0]  o_dfi_address,
    output logic [DFI_BANK_BUS_W-1:0]  o_dfi_bank,
    output logic [DFI_CTRL_BUS_W-1:0]  o_dfi_cas_n,
    output logic [DFI_CTRL_BUS_W-1:0]  o_dfi_ras_n,
    output logic [DFI_CTRL_BUS_W-1:0]  o_dfi_we_n,
    output logic [DFI_CS_BUS_W-1:0]    o_dfi_cs_n,
    output logic [DFI_CS_BUS_W-1:0]    o_dfi_cke,
    output logic [DFI_CS_BUS_W-1:0]    o_dfi_odt,
    output logic                       o_dfi_reset_n,
    output logic [DFI_DATA_WIDTH-1:0]  o_dfi_wrdata,
    output logic [DFI_EN_WIDTH-1:0]    o_dfi_wrdata_en,
    output logic [DFI_STRB_WIDTH-1:0]  o_dfi_wrdata_mask,
    output logic [DFI_EN_WIDTH-1:0]    o_dfi_rddata_en,
    input  logic [DFI_DATA_WIDTH-1:0]  i_dfi_rddata,
    input  logic [DFI_VALID_WIDTH-1:0] i_dfi_rddata_valid,

    // ---- PHY calibration CSRs: owned by harness_csr, PHY lives in the top -
    output logic [9:0]  o_phy_csr_adr,
    output logic        o_phy_csr_we,
    output logic [31:0] o_phy_csr_dat_w,
    input  logic [31:0] i_phy_csr_dat_r
);

    // =====================================================================
    // Soft reset. harness_csr can pulse it to clear every instrument without
    // a board power cycle -- and a runaway generator survives a soft reset
    // unless the engines go down with it, which is why unit_aresetn gates the
    // whole unit and not just the counters.
    // =====================================================================
    logic w_soft_reset_pulse;
    logic r_soft_rst_n;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn))      r_soft_rst_n <= 1'b0;
        else if (w_soft_reset_pulse)     r_soft_rst_n <= 1'b0;
        else                             r_soft_rst_n <= 1'b1;
    )
    logic unit_aresetn;
    assign unit_aresetn = aresetn & r_soft_rst_n;

    // =====================================================================
    // Host: UART -> AXI4-Lite
    // =====================================================================
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
        // NOT unit_aresetn: a soft reset must not drop the host link, or the
        // host cannot read back why it pulsed one.
        .aresetn  (aresetn),
        .i_uart_rx(i_uart_rx),
        .o_uart_tx(o_uart_tx),
        .m_axil_awaddr (uart_awaddr),  .m_axil_awprot (uart_awprot),
        .m_axil_awvalid(uart_awvalid), .m_axil_awready(uart_awready),
        .m_axil_wdata  (uart_wdata),   .m_axil_wstrb  (uart_wstrb),
        .m_axil_wvalid (uart_wvalid),  .m_axil_wready (uart_wready),
        .m_axil_bresp  (uart_bresp),   .m_axil_bvalid (uart_bvalid),
        .m_axil_bready (uart_bready),
        .m_axil_araddr (uart_araddr),  .m_axil_arprot (uart_arprot),
        .m_axil_arvalid(uart_arvalid), .m_axil_arready(uart_arready),
        .m_axil_rdata  (uart_rdata),   .m_axil_rresp  (uart_rresp),
        .m_axil_rvalid (uart_rvalid),  .m_axil_rready (uart_rready)
    );

    // =====================================================================
    // Config decode: 1 x 3 (controller APB, harness_csr AXIL, chargen APB)
    // =====================================================================
    logic         apb_psel, apb_penable, apb_pwrite, apb_pready, apb_pslverr;
    logic [31:0]  apb_paddr_full, apb_pwdata, apb_prdata;
    logic [3:0]   apb_pstrb;
    logic [2:0]   apb_pprot;

    logic         cg_psel, cg_penable, cg_pwrite, cg_pready, cg_pslverr;
    logic [31:0]  cg_paddr_full, cg_pwdata, cg_prdata;
    logic [3:0]   cg_pstrb;
    logic [2:0]   cg_pprot;

    logic        w_unmapped_irq;
    logic [31:0] w_unmapped_addr;
    logic [7:0]  w_unmapped_count;

    logic [31:0] s1_awaddr, s1_wdata, s1_araddr, s1_rdata;
    logic [3:0]  s1_wstrb;
    logic [2:0]  s1_awprot, s1_arprot;
    logic [1:0]  s1_bresp, s1_rresp;
    logic        s1_awvalid, s1_awready, s1_wvalid, s1_wready;
    logic        s1_bvalid, s1_bready, s1_arvalid, s1_arready;
    logic        s1_rvalid, s1_rready;

    bridge_scoria_char_axil u_bridge (
        .aclk    (aclk),
        .aresetn (unit_aresetn),

        .host_axi_awaddr (uart_awaddr),  .host_axi_awprot (uart_awprot),
        .host_axi_awvalid(uart_awvalid), .host_axi_awready(uart_awready),
        .host_axi_wdata  (uart_wdata),   .host_axi_wstrb  (uart_wstrb),
        .host_axi_wvalid (uart_wvalid),  .host_axi_wready (uart_wready),
        .host_axi_bresp  (uart_bresp),   .host_axi_bvalid (uart_bvalid),
        .host_axi_bready (uart_bready),
        .host_axi_araddr (uart_araddr),  .host_axi_arprot (uart_arprot),
        .host_axi_arvalid(uart_arvalid), .host_axi_arready(uart_arready),
        .host_axi_rdata  (uart_rdata),   .host_axi_rresp  (uart_rresp),
        .host_axi_rvalid (uart_rvalid),  .host_axi_rready (uart_rready),

        .scoria_apb_PSEL   (apb_psel),    .scoria_apb_PADDR  (apb_paddr_full),
        .scoria_apb_PENABLE(apb_penable), .scoria_apb_PWRITE (apb_pwrite),
        .scoria_apb_PWDATA (apb_pwdata),  .scoria_apb_PSTRB  (apb_pstrb),
        .scoria_apb_PPROT  (apb_pprot),   .scoria_apb_PRDATA (apb_prdata),
        .scoria_apb_PREADY (apb_pready),  .scoria_apb_PSLVERR(apb_pslverr),

        .harness_csr_axi_awaddr (s1_awaddr),  .harness_csr_axi_awprot (s1_awprot),
        .harness_csr_axi_awvalid(s1_awvalid), .harness_csr_axi_awready(s1_awready),
        .harness_csr_axi_wdata  (s1_wdata),   .harness_csr_axi_wstrb  (s1_wstrb),
        .harness_csr_axi_wvalid (s1_wvalid),  .harness_csr_axi_wready (s1_wready),
        .harness_csr_axi_bresp  (s1_bresp),   .harness_csr_axi_bvalid (s1_bvalid),
        .harness_csr_axi_bready (s1_bready),
        .harness_csr_axi_araddr (s1_araddr),  .harness_csr_axi_arprot (s1_arprot),
        .harness_csr_axi_arvalid(s1_arvalid), .harness_csr_axi_arready(s1_arready),
        .harness_csr_axi_rdata  (s1_rdata),   .harness_csr_axi_rresp  (s1_rresp),
        .harness_csr_axi_rvalid (s1_rvalid),  .harness_csr_axi_rready (s1_rready),

        .chargen_apb_PSEL   (cg_psel),    .chargen_apb_PADDR  (cg_paddr_full),
        .chargen_apb_PENABLE(cg_penable), .chargen_apb_PWRITE (cg_pwrite),
        .chargen_apb_PWDATA (cg_pwdata),  .chargen_apb_PSTRB  (cg_pstrb),
        .chargen_apb_PPROT  (cg_pprot),   .chargen_apb_PRDATA (cg_prdata),
        .chargen_apb_PREADY (cg_pready),  .chargen_apb_PSLVERR(cg_pslverr),

        // UNMAPPED-ACCESS REPORTING, and it is wired on purpose. This bridge
        // deliberately leaves pumice's debug_sram / dfi_mon_ram / obs_apb
        // windows empty (see the .toml), so a host that still thinks they are
        // there will reach the subtractive slave. irq is STICKY and addr holds
        // the FIRST offending address, which is the right shape: a one-cycle
        // pulse is gone before anyone can look, and this is precisely the
        // access nobody expected.
        //
        // irq reaches an LED, so a stray access is visible from across the
        // room during bring-up rather than being inferred from a wrong number.
        // addr and count need a CSR to be READ, and harness_csr has no port
        // for them -- a follow-up, not a blocker, because the LED already says
        // "your address map is wrong" which is the part you cannot guess.
        .unmapped_irq   (w_unmapped_irq),
        .unmapped_addr  (w_unmapped_addr),
        .unmapped_count (w_unmapped_count),
        // Cleared by a soft reset, which is also what clears every instrument.
        .unmapped_clear (w_soft_reset_pulse)
    );

    // =====================================================================
    // harness_csr -- board control, DFI tuning, perf readback
    // =====================================================================
    logic        w_perf_clear, w_perf_freeze;
    logic [3:0]  w_cmd_delay_sel, w_rddata_delay_sel;
    logic [7:0]  w_t_phy_wrlat, w_t_rddata_en;
    logic        w_rd_in_order;
    logic [3:0]  w_cap_lookahead_max, w_cap_synth_mask;
    mem_variant_e w_mem_variant;
    logic        w_obs_hist_metric, w_obs_hist_bus_sel;
    logic [3:0]  w_obs_hist_bin;
    logic [31:0] w_perf_wr_prod, w_perf_wr_bp, w_perf_wr_starv, w_perf_wr_idle;
    logic [31:0] w_perf_rd_prod, w_perf_rd_bp, w_perf_rd_starv, w_perf_rd_idle;
    logic [31:0] w_wr_hist_count, w_wr_hist_total;
    logic [31:0] w_rd_hist_count, w_rd_hist_total;
    logic        w_gen_wr_started, w_gen_rd_started;
    logic        w_gen_wr_done, w_gen_rd_done, w_gen_any_error, w_gen_crc_match;
    logic        w_rd_dbg_valid, w_rd_dbg_mismatch;
    logic [AXI_DATA_WIDTH-1:0] w_rd_dbg_actual, w_rd_dbg_expected;
    logic        w_timer_clear_pulse;
    logic [31:0] w_timer_expected_beats;
    logic [15:0] w_rd_resp_delay_cyc, w_wr_resp_delay_cyc;
    logic        w_clear_stats_pulse, w_freeze_trace;

    harness_csr #(
        .AW                (32),
        .DW                (32),
        .AXI_ID_WIDTH      (AXI_ID_WIDTH),
        // "DDR3", where pumice's default is "DDR2". The host reads this to
        // confirm it is talking to the build it thinks it is.
        .BUILD_ID          (32'h4444_5233),
        .BUILD_VERSION     (1),
        .CFG_DFI_RATE      (DFI_RATE),
        .CFG_DRAM_BL       (DRAM_BL),
        .CFG_ROW_WIDTH     (ROW_WIDTH),
        .CFG_BANK_WIDTH    ($clog2(NUM_BANKS)),
        .CFG_AXI_DATA_W    (AXI_DATA_WIDTH),
        // The two widths kept apart, which is the whole point of today's fix:
        // BEAT is the per-phase DFI slice, DEVICE is the DQ bus.
        .CFG_DRAM_BEAT_W   (DRAM_BEAT_WIDTH),
        .CFG_DRAM_DEVICE_W (DRAM_DEVICE_WIDTH),
        .CFG_CLK_HZ        (CLK_HZ)
    ) u_csr (
        .aclk    (aclk),
        .aresetn (aresetn),          // survives a soft reset, like the UART
        .s_awaddr (s1_awaddr),  .s_awprot (s1_awprot),
        .s_awvalid(s1_awvalid), .s_awready(s1_awready),
        .s_wdata  (s1_wdata),   .s_wstrb  (s1_wstrb),
        .s_wvalid (s1_wvalid),  .s_wready (s1_wready),
        .s_bresp  (s1_bresp),   .s_bvalid (s1_bvalid), .s_bready(s1_bready),
        .s_araddr (s1_araddr),  .s_arprot (s1_arprot),
        .s_arvalid(s1_arvalid), .s_arready(s1_arready),
        .s_rdata  (s1_rdata),   .s_rresp  (s1_rresp),
        .s_rvalid (s1_rvalid),  .s_rready (s1_rready),

        .o_clear_stats_pulse (w_clear_stats_pulse),
        .o_freeze_trace      (w_freeze_trace),
        .o_soft_reset_pulse  (w_soft_reset_pulse),
        .i_wr_done           (w_gen_wr_done),
        .i_rd_done           (w_gen_rd_done),
        .i_wr_error          (w_gen_any_error),
        .i_rd_error          (w_gen_any_error | w_rd_dbg_mismatch),
        // No in-harness init sequencer: scoria's own init_sequencer runs the
        // JEDEC sequence and the host polls it over the controller APB window.
        .i_init_done         (1'b1),
        .i_init_fail         (1'b0),
        .i_dbg_wr_ptr        (32'h0),      // no trace SRAM in this harness
        .i_dbg_overflow      (1'b0),
        .i_dbg_clear_busy    (1'b0),
        .i_crc_match         (w_gen_crc_match),

        .o_timer_clear_pulse    (w_timer_clear_pulse),
        .o_timer_expected_beats (w_timer_expected_beats),
        .i_timer_done    (1'b0),
        .i_timer_running (1'b0),
        .i_timer_pass    (1'b0),
        .i_timer_cycles  (64'h0),
        .i_timer_r_first (64'h0),
        .i_timer_r_last  (64'h0),
        .i_timer_w_first (64'h0),
        .i_timer_w_last  (64'h0),

        .o_rd_resp_delay_cyc (w_rd_resp_delay_cyc),
        .o_wr_resp_delay_cyc (w_wr_resp_delay_cyc),
        .o_perf_clear        (w_perf_clear),
        .o_perf_freeze       (w_perf_freeze),

        .i_obs_rd_prod  (w_perf_rd_prod),  .i_obs_rd_bp    (w_perf_rd_bp),
        .i_obs_rd_starv (w_perf_rd_starv), .i_obs_rd_idle  (w_perf_rd_idle),
        .i_obs_wr_prod  (w_perf_wr_prod),  .i_obs_wr_bp    (w_perf_wr_bp),
        .i_obs_wr_starv (w_perf_wr_starv), .i_obs_wr_idle  (w_perf_wr_idle),
        .o_obs_hist_metric  (w_obs_hist_metric),
        .o_obs_hist_bin     (w_obs_hist_bin),
        .o_obs_hist_bus_sel (w_obs_hist_bus_sel),
        .i_obs_rd_hist_count (w_rd_hist_count),
        .i_obs_rd_hist_total (w_rd_hist_total),
        .i_obs_wr_hist_count (w_wr_hist_count),
        .i_obs_wr_hist_total (w_wr_hist_total),

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

    // =====================================================================
    // The scoria char macro: engine + controller + APB shim
    // =====================================================================
    logic [DFI_ADDR_BUS_W-1:0]  w_c_dfi_address;
    logic [DFI_BANK_BUS_W-1:0]  w_c_dfi_bank;
    logic [DFI_CTRL_BUS_W-1:0]  w_c_dfi_cas_n, w_c_dfi_ras_n, w_c_dfi_we_n;
    logic [DFI_CS_BUS_W-1:0]    w_c_dfi_cs_n, w_c_dfi_cke, w_c_dfi_odt;
    logic [DFI_EN_WIDTH-1:0]    w_c_dfi_rddata_en;
    logic [DFI_DATA_WIDTH-1:0]  w_dfi_rddata_dly;

    scoria_char_macro #(
        .AXI_ADDR_WIDTH    (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH    (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH      (AXI_ID_WIDTH),
        .NUM_RANKS         (NUM_RANKS),
        .NUM_BANKS         (NUM_BANKS),
        .ROW_WIDTH         (ROW_WIDTH),
        .COL_WIDTH         (COL_WIDTH),
        .DFI_RATE          (DFI_RATE),
        .DRAM_BEAT_WIDTH   (DRAM_BEAT_WIDTH),
        .DRAM_DEVICE_WIDTH (DRAM_DEVICE_WIDTH),
        .DRAM_BL           (DRAM_BL)
    ) u_macro (
        .mc_clk   (aclk),
        .mc_rst_n (unit_aresetn),
        .pclk     (aclk),
        .presetn  (unit_aresetn),

        .s_chargen_apb_PSEL   (cg_psel),
        .s_chargen_apb_PENABLE(cg_penable),
        .s_chargen_apb_PREADY (cg_pready),
        .s_chargen_apb_PADDR  (cg_paddr_full[11:0]),
        .s_chargen_apb_PWRITE (cg_pwrite),
        .s_chargen_apb_PWDATA (cg_pwdata),
        .s_chargen_apb_PSTRB  (cg_pstrb),
        .s_chargen_apb_PPROT  (cg_pprot),
        .s_chargen_apb_PRDATA (cg_prdata),
        .s_chargen_apb_PSLVERR(cg_pslverr),

        .gen_wr_started (w_gen_wr_started),
        .gen_rd_started (w_gen_rd_started),
        .gen_wr_done    (w_gen_wr_done),
        .gen_rd_done    (w_gen_rd_done),
        .gen_any_error  (w_gen_any_error),
        .gen_crc_match  (w_gen_crc_match),

        .s_apb_PSEL   (apb_psel),
        .s_apb_PENABLE(apb_penable),
        .s_apb_PREADY (apb_pready),
        .s_apb_PADDR  (apb_paddr_full[11:0]),
        .s_apb_PWRITE (apb_pwrite),
        .s_apb_PWDATA (apb_pwdata),
        .s_apb_PSTRB  (apb_pstrb),
        .s_apb_PPROT  (apb_pprot),
        .s_apb_PRDATA (apb_prdata),
        .s_apb_PSLVERR(apb_pslverr),

        // Command/control DFI leaves through dfi_cmd_delay below; write DATA
        // and the DDR3 control pins go straight out. Delaying the command
        // stream without the data would break their alignment, which is why
        // dfi_cmd_delay carries rddata_en with the commands and the write data
        // is not delayed at all -- the PHY's own write latency covers it.
        .dfi_address_o   (w_c_dfi_address),
        .dfi_bank_o      (w_c_dfi_bank),
        .dfi_cas_n_o     (w_c_dfi_cas_n),
        .dfi_ras_n_o     (w_c_dfi_ras_n),
        .dfi_we_n_o      (w_c_dfi_we_n),
        .dfi_cs_n_o      (w_c_dfi_cs_n),
        .dfi_cke_o       (w_c_dfi_cke),
        .dfi_odt_o       (w_c_dfi_odt),
        .dfi_wrdata_o      (o_dfi_wrdata),
        .dfi_wrdata_en_o   (o_dfi_wrdata_en),
        .dfi_wrdata_mask_o (o_dfi_wrdata_mask),
        .dfi_rddata_en_o   (w_c_dfi_rddata_en),
        .dfi_rddata_i      (w_dfi_rddata_dly),
        .dfi_rddata_valid_i(i_dfi_rddata_valid),
        .dfi_dram_clk_disable_o (),         // no low-power path on this build
        .dfi_init_start_o  (),
        // The PHY has no init handshake of its own; scoria's init_sequencer
        // drives the JEDEC sequence onto the command bus directly, so this is
        // tied complete. On the DV side the BFM's set_init_complete() plays
        // the same role.
        .dfi_init_complete_i (1'b1),
        .dfi_reset_n_o     (o_dfi_reset_n),
        // Driven by the controller, constant at one rank -- see scoria
        // TASK-005. Not wired to the PHY: K7DDRPHY has no per-data-phase CS
        // port, so they terminate here rather than being tied off in the top.
        .dfi_wrdata_cs_n_o (),
        .dfi_rddata_cs_n_o (),
        .dfi_phylvl_req_cs_n_o (),
        .dfi_phylvl_ack_cs_n_i ('0),
        // Write leveling: the SEARCH runs in the HOST (scoria design decision
        // D2), driving the PHY's wlevel_en / wlevel_strobe CSRs. The
        // controller-side leveling interface is therefore unused on this build.
        .dfi_phy_wrlvl_cs_n_o (),
        .dfi_wrlvl_strobe_o   (),
        .dfi_prime_dq_i       (1'b0),
        .dfi_ctrlupd_req_o    (),
        .dfi_ctrlupd_ack_i    (1'b1),
        .dfi_phyupd_req_i     (1'b0),
        .dfi_phyupd_ack_o     (),
        .dfi_phyupd_type_i    ('0),

        .memtype_i           (memtype_e'(w_mem_variant)),
        .t_phy_wrlat_i       (w_t_phy_wrlat),
        .t_rddata_en_i       (w_t_rddata_en),
        .rd_in_order_i       (w_rd_in_order),
        .cap_lookahead_max_i (w_cap_lookahead_max),
        .cap_synth_mask_i    (w_cap_synth_mask),

        .rd_dbg_valid    (w_rd_dbg_valid),
        .rd_dbg_ready    (1'b1),            // always accept
        .rd_dbg_actual   (w_rd_dbg_actual),
        .rd_dbg_expected (w_rd_dbg_expected),
        .rd_dbg_mismatch (w_rd_dbg_mismatch),

        .perf_clear  (w_perf_clear),
        .perf_freeze (w_perf_freeze),
        .perf_wr_prod (w_perf_wr_prod), .perf_wr_bp    (w_perf_wr_bp),
        .perf_wr_starv(w_perf_wr_starv), .perf_wr_idle (w_perf_wr_idle),
        .perf_rd_prod (w_perf_rd_prod), .perf_rd_bp    (w_perf_rd_bp),
        .perf_rd_starv(w_perf_rd_starv), .perf_rd_idle (w_perf_rd_idle),
        .i_hist_metric       (w_obs_hist_metric),
        .i_hist_bin          (w_obs_hist_bin),
        .perf_wr_hist_count  (w_wr_hist_count),
        .perf_wr_hist_total  (w_wr_hist_total),
        .perf_rd_hist_count  (w_rd_hist_count),
        .perf_rd_hist_total  (w_rd_hist_total)
    );

    // =====================================================================
    // The two tuning delay lines. sel=0 is passthrough on both.
    // =====================================================================
    dfi_cmd_delay #(
        .DFI_ADDR_BUS_W (DFI_ADDR_BUS_W),
        .DFI_BANK_BUS_W (DFI_BANK_BUS_W),
        .DFI_CTRL_BUS_W (DFI_CTRL_BUS_W),
        .DFI_CS_BUS_W   (DFI_CS_BUS_W),
        .DFI_RATE       (DFI_RATE),
        .MAX_DELAY      (CMD_MAX_DELAY)
    ) u_dfi_cmd_delay (
        .mc_clk      (aclk),
        .mc_rst_n    (unit_aresetn),
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

    // Read-side mirror: realign the PHY's read DATA with its late
    // rddata_valid, so the controller's valid-gated aligner captures the right
    // beats. On DDR2 an on-silicon ILA showed the data leading the valid by
    // about read_latency cycles and this is what fixed it
    // (project_ddr2_ila_read_valid_skew). The DDR3 PHY is a different one and
    // its skew is unmeasured -- which is the point of making it a CSR.
    dfi_rddata_delay #(
        .DFI_DATA_WIDTH (DFI_DATA_WIDTH),
        .MAX_DELAY      (RDDATA_MAX_DELAY)
    ) u_dfi_rddata_delay (
        .mc_clk   (aclk),
        .mc_rst_n (unit_aresetn),
        .sel_i    (w_rddata_delay_sel),
        .i_rddata (i_dfi_rddata),
        .o_rddata (w_dfi_rddata_dly)
    );

    // =====================================================================
    // Board status
    // =====================================================================
    // The driver takes a PACKED status bus and owns the slow-clock update and
    // the CDC; it does not interpret the bits. Genesys 2 exposes 8 LEDs where
    // the Nexys A7 has 16, so NUM_LEDS is 8 and the map is correspondingly
    // tighter -- the bits chosen are the ones a bring-up session reads from
    // across the room.
    logic [7:0] w_led_status;
    assign w_led_status = {
        w_gen_any_error | w_rd_dbg_mismatch | w_unmapped_irq,  // 7: wrong
        w_rd_dbg_mismatch,                    // 6: and it was read DATA
        w_gen_rd_done,                        // 5: read phase finished
        w_gen_wr_done,                        // 4: write phase finished
        w_gen_rd_started,                     // 3: reads running
        w_gen_wr_started,                     // 2: writes running
        w_unmapped_irq,                       // 1: STRAY ACCESS -- host map wrong
        unit_aresetn                          // 0: out of reset (heartbeat)
    };

    led_status_driver #(
        .FPGA_CLK_HZ (CLK_HZ),
        .NUM_LEDS    (8)
    ) u_led (
        .aclk     (aclk),
        .aresetn  (aresetn),
        .i_status (w_led_status),
        .o_led    (o_led)
    );

endmodule : scoria_char_harness
