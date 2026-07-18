// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: char_engine_harness
// Purpose: DUT-agnostic characterization engine harness — the SAME pattern
//          generator + CRC check + perf meters + bandwidth timer + harness_csr
//          + UART bridge used by the pumice flow (ddr2_char_macro), but exposed
//          as a plain AXI4 MASTER port so it can drive ANY DDR controller. Here
//          it drives litedram_core.user_port_axi_0 (see litedram_char_top),
//          giving an apples-to-apples benchmark vs pumice: identical engines,
//          identical perf taps, identical host program.
//
//   UART -> uart_axil_bridge -> harness_csr -> {wr,rd} engine cfg
//   axi4_master_wr_pattern_gen  -> m_axi AW/W/B  -> DUT
//   axi4_master_rd_crc_check    -> m_axi AR/R    -> DUT
//   axi_bus_meter (W, R) + bandwidth timer -> harness_csr perf/timer
//
// The host waits on harness_csr.i_init_done (<= the DUT's init_done) before
// pulsing start. harness_csr is wired DIRECTLY off the UART bridge (base 0);
// there is no controller-APB slave (litedram self-configures via its BIOS).
`timescale 1ns / 1ps

`include "reset_defs.svh"

module char_engine_harness #(
    parameter int AXI_ID_WIDTH     = 8,
    parameter int AXI_ADDR_WIDTH   = 32,   // engine addr; top wires [26:0] to litedram
    parameter int AXI_DATA_WIDTH   = 64,
    parameter int AXI_USER_WIDTH   = 8,
    parameter int AXI_STRB_WIDTH   = AXI_DATA_WIDTH / 8,
    parameter int BURST_LEN_WIDTH  = 8,
    parameter int TXN_COUNT_WIDTH  = 16,
    parameter int INDEX_WIDTH      = 16,
    parameter int STRIDE_WIDTH     = 24,
    parameter int RD_DBG_FIFO_DEPTH = 32,
    parameter int FPGA_CLK_HZ      = 100_000_000,   // == litedram user_clk freq
    parameter int UART_BAUD        = 115_200,
    parameter int LED_UPDATE_HZ    = 200,
    parameter int CLKS_PER_BIT     = FPGA_CLK_HZ / UART_BAUD,

    parameter int IW = AXI_ID_WIDTH,
    parameter int AW = AXI_ADDR_WIDTH,
    parameter int DW = AXI_DATA_WIDTH,
    parameter int UW = AXI_USER_WIDTH,
    parameter int SW = AXI_STRB_WIDTH
) (
    input  logic                aclk,      // == litedram user_clk
    input  logic                aresetn,   // == ~litedram user_rst

    // Board UART (FTDI) — the harness console (NOT litedram's BIOS uart)
    input  logic                i_uart_rx,
    output logic                o_uart_tx,

    // Status
    output logic [15:0]         o_led,
    output logic [7:0]          o_seven_seg_an,
    output logic [6:0]          o_seven_seg_seg,
    output logic                o_seven_seg_dp,

    // DUT init handshake (<= litedram_core.init_done / init_error)
    input  logic                i_init_done,
    input  logic                i_init_fail,

    // AXI4 master to the DUT (litedram user_port_axi_0)
    output logic [IW-1:0]       m_axi_awid,
    output logic [AW-1:0]       m_axi_awaddr,
    output logic [7:0]          m_axi_awlen,
    output logic [2:0]          m_axi_awsize,
    output logic [1:0]          m_axi_awburst,
    output logic [UW-1:0]       m_axi_awuser,
    output logic                m_axi_awvalid,
    input  logic                m_axi_awready,
    output logic [DW-1:0]       m_axi_wdata,
    output logic [SW-1:0]       m_axi_wstrb,
    output logic                m_axi_wlast,
    output logic [UW-1:0]       m_axi_wuser,
    output logic                m_axi_wvalid,
    input  logic                m_axi_wready,
    input  logic [IW-1:0]       m_axi_bid,
    input  logic [1:0]          m_axi_bresp,
    input  logic [UW-1:0]       m_axi_buser,
    input  logic                m_axi_bvalid,
    output logic                m_axi_bready,
    output logic [IW-1:0]       m_axi_arid,
    output logic [AW-1:0]       m_axi_araddr,
    output logic [7:0]          m_axi_arlen,
    output logic [2:0]          m_axi_arsize,
    output logic [1:0]          m_axi_arburst,
    output logic [UW-1:0]       m_axi_aruser,
    output logic                m_axi_arvalid,
    input  logic                m_axi_arready,
    input  logic [IW-1:0]       m_axi_rid,
    input  logic [DW-1:0]       m_axi_rdata,
    input  logic [1:0]          m_axi_rresp,
    input  logic                m_axi_rlast,
    input  logic [UW-1:0]       m_axi_ruser,
    input  logic                m_axi_rvalid,
    output logic                m_axi_rready
);

    import pumice_pkg::*;   // memtype_e (harness_csr.o_memtype)

    // Soft-reset from CSR is a nicety; the board reset + DUT init dominate.
    // Engines re-arm on cfg_start, so a no-op soft-reset is safe.
    logic unit_aresetn;
    assign unit_aresetn = aresetn;

    // ========================================================================
    // UART -> AXIL bridge
    // ========================================================================
    logic [31:0] uart_awaddr, uart_wdata, uart_araddr, uart_rdata;
    logic [3:0]  uart_wstrb;
    logic [2:0]  uart_awprot, uart_arprot;
    logic [1:0]  uart_bresp, uart_rresp;
    logic        uart_awvalid, uart_awready, uart_wvalid, uart_wready;
    logic        uart_bvalid, uart_bready;
    logic        uart_arvalid, uart_arready, uart_rvalid, uart_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH(32), .AXIL_DATA_WIDTH(32), .CLKS_PER_BIT(CLKS_PER_BIT)
    ) u_uart (
        .aclk(aclk), .aresetn(unit_aresetn),
        .i_uart_rx(i_uart_rx), .o_uart_tx(o_uart_tx),
        .m_axil_awaddr(uart_awaddr), .m_axil_awprot(uart_awprot),
        .m_axil_awvalid(uart_awvalid), .m_axil_awready(uart_awready),
        .m_axil_wdata(uart_wdata), .m_axil_wstrb(uart_wstrb),
        .m_axil_wvalid(uart_wvalid), .m_axil_wready(uart_wready),
        .m_axil_bresp(uart_bresp), .m_axil_bvalid(uart_bvalid), .m_axil_bready(uart_bready),
        .m_axil_araddr(uart_araddr), .m_axil_arprot(uart_arprot),
        .m_axil_arvalid(uart_arvalid), .m_axil_arready(uart_arready),
        .m_axil_rdata(uart_rdata), .m_axil_rresp(uart_rresp),
        .m_axil_rvalid(uart_rvalid), .m_axil_rready(uart_rready)
    );

    // ========================================================================
    // harness_csr cfg / status / perf / timer wires
    // ========================================================================
    logic        w_start_wr_pulse, w_start_rd_pulse, w_clear_stats_pulse;
    logic        w_freeze_trace, w_soft_reset_pulse;
    logic        w_wr_done, w_rd_done, w_wr_error, w_rd_error;
    logic        w_init_done, w_init_fail;
    logic [31:0] w_crc_expected, w_crc_actual;
    logic        w_crc_exp_valid, w_crc_act_valid;
    logic [TXN_COUNT_WIDTH-1:0] w_beats_mismatched;

    logic        w_timer_clear_pulse;
    logic [31:0] w_timer_expected_beats;
    logic        w_timer_done, w_timer_running, w_timer_pass;
    logic [63:0] w_timer_cycles, w_timer_r_first, w_timer_r_last;
    logic [63:0] w_timer_w_first, w_timer_w_last;

    logic [15:0] w_rd_resp_delay_cyc, w_wr_resp_delay_cyc;
    logic        w_perf_clear, w_perf_freeze;
    logic [31:0] w_obs_rd_prod, w_obs_rd_bp, w_obs_rd_starv, w_obs_rd_idle;
    logic [31:0] w_obs_wr_prod, w_obs_wr_bp, w_obs_wr_starv, w_obs_wr_idle;
    logic        w_obs_hist_metric, w_obs_hist_bus_sel;
    logic [3:0]  w_obs_hist_bin;

    // Controller-cfg outputs (unused for litedram — it self-configures)
    memtype_e    w_memtype;
    logic [7:0]  w_t_phy_wrlat, w_t_rddata_en;
    logic        w_rd_in_order;
    logic [3:0]  w_cap_lookahead_max, w_cap_synth_mask, w_cmd_delay_sel, w_rddata_delay_sel;

    // Engine cfg
    logic [AW-1:0]                w_cfg_wr_start_addr, w_cfg_wr_wrap_mask_0, w_cfg_wr_wrap_mask_1;
    logic signed [STRIDE_WIDTH-1:0] w_cfg_wr_stride_0, w_cfg_wr_stride_1;
    logic [BURST_LEN_WIDTH-1:0]   w_cfg_wr_burst_len;
    logic [TXN_COUNT_WIDTH-1:0]   w_cfg_wr_txn_count;
    logic [IW-1:0]                w_cfg_wr_axi_id;
    logic [1:0]                   w_cfg_wr_id_mode, w_cfg_wr_axi_burst;
    logic [2:0]                   w_cfg_wr_axi_size;
    logic [3:0]                   w_cfg_wr_gap;
    logic                         w_cfg_wr_data_mode;
    logic [31:0]                  w_cfg_wr_lfsr_seed, w_cfg_wr_hash_seed0, w_cfg_wr_hash_seed1, w_cfg_wr_hash_seed2;

    logic [AW-1:0]                w_cfg_rd_start_addr, w_cfg_rd_wrap_mask_0, w_cfg_rd_wrap_mask_1;
    logic signed [STRIDE_WIDTH-1:0] w_cfg_rd_stride_0, w_cfg_rd_stride_1;
    logic [BURST_LEN_WIDTH-1:0]   w_cfg_rd_burst_len;
    logic [TXN_COUNT_WIDTH-1:0]   w_cfg_rd_txn_count;
    logic [IW-1:0]                w_cfg_rd_axi_id;
    logic [1:0]                   w_cfg_rd_id_mode, w_cfg_rd_axi_burst;
    logic [2:0]                   w_cfg_rd_axi_size;
    logic [3:0]                   w_cfg_rd_gap;
    logic                         w_cfg_rd_data_mode;
    logic [31:0]                  w_cfg_rd_lfsr_seed, w_cfg_rd_hash_seed0, w_cfg_rd_hash_seed1, w_cfg_rd_hash_seed2;

    // Debug ring not exposed in this flow (tie off).
    logic [31:0] w_dbg_wr_ptr;   assign w_dbg_wr_ptr = '0;
    logic        w_dbg_overflow; assign w_dbg_overflow = 1'b0;
    logic        w_dbg_clear_busy; assign w_dbg_clear_busy = 1'b0;
    // Latency histogram deferred (bandwidth comes from the timer + bus meters).
    logic [31:0] w_obs_rd_hist_count, w_obs_rd_hist_total, w_obs_wr_hist_count, w_obs_wr_hist_total;
    assign w_obs_rd_hist_count = '0; assign w_obs_rd_hist_total = '0;
    assign w_obs_wr_hist_count = '0; assign w_obs_wr_hist_total = '0;

    assign w_init_done = i_init_done;
    assign w_init_fail = i_init_fail;

    harness_csr #(
        .AW(32), .DW(32), .AXI_ID_WIDTH(AXI_ID_WIDTH), .STRIDE_WIDTH(STRIDE_WIDTH),
        .TXN_COUNT_WIDTH(TXN_COUNT_WIDTH), .BURST_LEN_WIDTH(BURST_LEN_WIDTH)
    ) u_harness_csr (
        .aclk(aclk), .aresetn(unit_aresetn),
        .s_awaddr(uart_awaddr), .s_awprot(uart_awprot),
        .s_awvalid(uart_awvalid), .s_awready(uart_awready),
        .s_wdata(uart_wdata), .s_wstrb(uart_wstrb),
        .s_wvalid(uart_wvalid), .s_wready(uart_wready),
        .s_bresp(uart_bresp), .s_bvalid(uart_bvalid), .s_bready(uart_bready),
        .s_araddr(uart_araddr), .s_arprot(uart_arprot),
        .s_arvalid(uart_arvalid), .s_arready(uart_arready),
        .s_rdata(uart_rdata), .s_rresp(uart_rresp),
        .s_rvalid(uart_rvalid), .s_rready(uart_rready),
        .o_start_wr_pulse(w_start_wr_pulse), .o_start_rd_pulse(w_start_rd_pulse),
        .o_clear_stats_pulse(w_clear_stats_pulse), .o_freeze_trace(w_freeze_trace),
        .o_soft_reset_pulse(w_soft_reset_pulse),
        .i_wr_done(w_wr_done), .i_rd_done(w_rd_done),
        .i_wr_error(w_wr_error), .i_rd_error(w_rd_error),
        .i_init_done(w_init_done), .i_init_fail(w_init_fail),
        .i_dbg_wr_ptr(w_dbg_wr_ptr), .i_dbg_overflow(w_dbg_overflow),
        .i_dbg_clear_busy(w_dbg_clear_busy),
        .i_crc_expected(w_crc_expected), .i_crc_actual(w_crc_actual),
        .i_crc_exp_valid(w_crc_exp_valid), .i_crc_act_valid(w_crc_act_valid),
        .i_beats_mismatched(w_beats_mismatched),
        .o_timer_clear_pulse(w_timer_clear_pulse), .o_timer_expected_beats(w_timer_expected_beats),
        .i_timer_done(w_timer_done), .i_timer_running(w_timer_running), .i_timer_pass(w_timer_pass),
        .i_timer_cycles(w_timer_cycles),
        .i_timer_r_first(w_timer_r_first), .i_timer_r_last(w_timer_r_last),
        .i_timer_w_first(w_timer_w_first), .i_timer_w_last(w_timer_w_last),
        .o_rd_resp_delay_cyc(w_rd_resp_delay_cyc), .o_wr_resp_delay_cyc(w_wr_resp_delay_cyc),
        .o_perf_clear(w_perf_clear), .o_perf_freeze(w_perf_freeze),
        .i_obs_rd_prod(w_obs_rd_prod), .i_obs_rd_bp(w_obs_rd_bp),
        .i_obs_rd_starv(w_obs_rd_starv), .i_obs_rd_idle(w_obs_rd_idle),
        .i_obs_wr_prod(w_obs_wr_prod), .i_obs_wr_bp(w_obs_wr_bp),
        .i_obs_wr_starv(w_obs_wr_starv), .i_obs_wr_idle(w_obs_wr_idle),
        .o_obs_hist_metric(w_obs_hist_metric), .o_obs_hist_bin(w_obs_hist_bin),
        .o_obs_hist_bus_sel(w_obs_hist_bus_sel),
        .i_obs_rd_hist_count(w_obs_rd_hist_count), .i_obs_rd_hist_total(w_obs_rd_hist_total),
        .i_obs_wr_hist_count(w_obs_wr_hist_count), .i_obs_wr_hist_total(w_obs_wr_hist_total),
        .o_memtype(w_memtype), .o_t_phy_wrlat(w_t_phy_wrlat), .o_t_rddata_en(w_t_rddata_en),
        .o_rd_in_order(w_rd_in_order), .o_cap_lookahead_max(w_cap_lookahead_max),
        .o_cap_synth_mask(w_cap_synth_mask), .o_cmd_delay(w_cmd_delay_sel),
        .o_rddata_delay(w_rddata_delay_sel),
        /* verilator lint_off PINCONNECTEMPTY */
        .o_phy_csr_adr(), .o_phy_csr_we(), .o_phy_csr_dat_w(),
        /* verilator lint_on PINCONNECTEMPTY */
        .i_phy_csr_dat_r(32'd0),
        .o_cfg_wr_start_addr(w_cfg_wr_start_addr), .o_cfg_wr_stride_0(w_cfg_wr_stride_0),
        .o_cfg_wr_stride_1(w_cfg_wr_stride_1), .o_cfg_wr_wrap_mask_0(w_cfg_wr_wrap_mask_0),
        .o_cfg_wr_wrap_mask_1(w_cfg_wr_wrap_mask_1), .o_cfg_wr_burst_len(w_cfg_wr_burst_len),
        .o_cfg_wr_txn_count(w_cfg_wr_txn_count), .o_cfg_wr_axi_id(w_cfg_wr_axi_id),
        .o_cfg_wr_id_mode(w_cfg_wr_id_mode), .o_cfg_wr_axi_size(w_cfg_wr_axi_size),
        .o_cfg_wr_axi_burst(w_cfg_wr_axi_burst), .o_cfg_wr_gap(w_cfg_wr_gap),
        .o_cfg_wr_data_mode(w_cfg_wr_data_mode), .o_cfg_wr_lfsr_seed(w_cfg_wr_lfsr_seed),
        .o_cfg_wr_hash_seed0(w_cfg_wr_hash_seed0), .o_cfg_wr_hash_seed1(w_cfg_wr_hash_seed1),
        .o_cfg_wr_hash_seed2(w_cfg_wr_hash_seed2),
        .o_cfg_rd_start_addr(w_cfg_rd_start_addr), .o_cfg_rd_stride_0(w_cfg_rd_stride_0),
        .o_cfg_rd_stride_1(w_cfg_rd_stride_1), .o_cfg_rd_wrap_mask_0(w_cfg_rd_wrap_mask_0),
        .o_cfg_rd_wrap_mask_1(w_cfg_rd_wrap_mask_1), .o_cfg_rd_burst_len(w_cfg_rd_burst_len),
        .o_cfg_rd_txn_count(w_cfg_rd_txn_count), .o_cfg_rd_axi_id(w_cfg_rd_axi_id),
        .o_cfg_rd_id_mode(w_cfg_rd_id_mode), .o_cfg_rd_axi_size(w_cfg_rd_axi_size),
        .o_cfg_rd_axi_burst(w_cfg_rd_axi_burst), .o_cfg_rd_gap(w_cfg_rd_gap),
        .o_cfg_rd_data_mode(w_cfg_rd_data_mode), .o_cfg_rd_lfsr_seed(w_cfg_rd_lfsr_seed),
        .o_cfg_rd_hash_seed0(w_cfg_rd_hash_seed0), .o_cfg_rd_hash_seed1(w_cfg_rd_hash_seed1),
        .o_cfg_rd_hash_seed2(w_cfg_rd_hash_seed2)
    );

    // ========================================================================
    // Writer engine -> m_axi AW/W/B
    // ========================================================================
    logic w_bresp_error, w_rresp_error, w_data_error;
    axi4_master_wr_pattern_gen #(
        .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH), .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .AXI_WSTRB_WIDTH(AXI_STRB_WIDTH), .TXN_COUNT_WIDTH(TXN_COUNT_WIDTH),
        .INDEX_WIDTH(INDEX_WIDTH), .STRIDE_WIDTH(STRIDE_WIDTH)
    ) u_wr_engine (
        .aclk(aclk), .aresetn(unit_aresetn),
        .cfg_start_addr(w_cfg_wr_start_addr), .cfg_addr_stride_0(w_cfg_wr_stride_0),
        .cfg_addr_stride_1(w_cfg_wr_stride_1), .cfg_addr_wrap_mask_0(w_cfg_wr_wrap_mask_0),
        .cfg_addr_wrap_mask_1(w_cfg_wr_wrap_mask_1), .cfg_burst_len(w_cfg_wr_burst_len),
        .cfg_txn_count(w_cfg_wr_txn_count), .cfg_axi_id(w_cfg_wr_axi_id),
        .cfg_id_mode(w_cfg_wr_id_mode), .cfg_axi_size(w_cfg_wr_axi_size),
        .cfg_axi_burst(w_cfg_wr_axi_burst), .cfg_lfsr_seed(w_cfg_wr_lfsr_seed),
        .cfg_data_mode(w_cfg_wr_data_mode), .cfg_hash_seed0(w_cfg_wr_hash_seed0),
        .cfg_hash_seed1(w_cfg_wr_hash_seed1), .cfg_hash_seed2(w_cfg_wr_hash_seed2),
        .cfg_wr_gap(w_cfg_wr_gap), .cfg_start(w_start_wr_pulse), .cfg_done(w_wr_done),
        .o_expected_crc(w_crc_expected), .o_expected_crc_valid(w_crc_exp_valid),
        .o_bresp_error(w_bresp_error),
        .m_axi_awid(m_axi_awid), .m_axi_awaddr(m_axi_awaddr), .m_axi_awlen(m_axi_awlen),
        .m_axi_awsize(m_axi_awsize), .m_axi_awburst(m_axi_awburst), .m_axi_awlock(),
        .m_axi_awcache(), .m_axi_awprot(), .m_axi_awqos(), .m_axi_awregion(),
        .m_axi_awuser(m_axi_awuser), .m_axi_awvalid(m_axi_awvalid), .m_axi_awready(m_axi_awready),
        .m_axi_wdata(m_axi_wdata), .m_axi_wstrb(m_axi_wstrb), .m_axi_wlast(m_axi_wlast),
        .m_axi_wuser(m_axi_wuser), .m_axi_wvalid(m_axi_wvalid), .m_axi_wready(m_axi_wready),
        .m_axi_bid(m_axi_bid), .m_axi_bresp(m_axi_bresp), .m_axi_buser(m_axi_buser),
        .m_axi_bvalid(m_axi_bvalid), .m_axi_bready(m_axi_bready)
    );

    // ========================================================================
    // Reader engine -> m_axi AR/R
    // ========================================================================
    axi4_master_rd_crc_check #(
        .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH(AXI_DATA_WIDTH), .AXI_USER_WIDTH(AXI_USER_WIDTH),
        .TXN_COUNT_WIDTH(TXN_COUNT_WIDTH), .INDEX_WIDTH(INDEX_WIDTH),
        .STRIDE_WIDTH(STRIDE_WIDTH), .DBG_FIFO_DEPTH(RD_DBG_FIFO_DEPTH)
    ) u_rd_engine (
        .aclk(aclk), .aresetn(unit_aresetn),
        .cfg_start_addr(w_cfg_rd_start_addr), .cfg_addr_stride_0(w_cfg_rd_stride_0),
        .cfg_addr_stride_1(w_cfg_rd_stride_1), .cfg_addr_wrap_mask_0(w_cfg_rd_wrap_mask_0),
        .cfg_addr_wrap_mask_1(w_cfg_rd_wrap_mask_1), .cfg_burst_len(w_cfg_rd_burst_len),
        .cfg_txn_count(w_cfg_rd_txn_count), .cfg_axi_id(w_cfg_rd_axi_id),
        .cfg_id_mode(w_cfg_rd_id_mode), .cfg_axi_size(w_cfg_rd_axi_size),
        .cfg_axi_burst(w_cfg_rd_axi_burst), .cfg_lfsr_seed(w_cfg_rd_lfsr_seed),
        .cfg_data_mode(w_cfg_rd_data_mode), .cfg_hash_seed0(w_cfg_rd_hash_seed0),
        .cfg_hash_seed1(w_cfg_rd_hash_seed1), .cfg_hash_seed2(w_cfg_rd_hash_seed2),
        .cfg_rd_gap(w_cfg_rd_gap), .cfg_start(w_start_rd_pulse), .cfg_done(w_rd_done),
        .o_actual_crc(w_crc_actual), .o_actual_crc_valid(w_crc_act_valid),
        .o_data_error(w_data_error), .o_rresp_error(w_rresp_error),
        .o_beats_mismatched(w_beats_mismatched),
        .m_axi_arid(m_axi_arid), .m_axi_araddr(m_axi_araddr), .m_axi_arlen(m_axi_arlen),
        .m_axi_arsize(m_axi_arsize), .m_axi_arburst(m_axi_arburst), .m_axi_arlock(),
        .m_axi_arcache(), .m_axi_arprot(), .m_axi_arqos(), .m_axi_arregion(),
        .m_axi_aruser(m_axi_aruser), .m_axi_arvalid(m_axi_arvalid), .m_axi_arready(m_axi_arready),
        .m_axi_rid(m_axi_rid), .m_axi_rdata(m_axi_rdata), .m_axi_rresp(m_axi_rresp),
        .m_axi_rlast(m_axi_rlast), .m_axi_ruser(m_axi_ruser),
        .m_axi_rvalid(m_axi_rvalid), .m_axi_rready(m_axi_rready),
        /* verilator lint_off PINCONNECTEMPTY */
        .dbg_valid(), .dbg_actual(), .dbg_expected(), .dbg_mismatch(),
        /* verilator lint_on PINCONNECTEMPTY */
        .dbg_ready(1'b1)
    );

    assign w_wr_error = w_bresp_error;
    assign w_rd_error = w_rresp_error | w_data_error;

    // ========================================================================
    // Perf: bus meters on the W (write) and R (read) data handshakes
    // ========================================================================
    logic [15:0] w_wr_ch_prod[1], w_wr_ch_bp[1], w_wr_ch_starv[1], w_wr_ch_idle[1];
    logic [3:0]  w_wr_ch_ovf;
    logic [15:0] w_rd_ch_prod[1], w_rd_ch_bp[1], w_rd_ch_starv[1], w_rd_ch_idle[1];
    logic [3:0]  w_rd_ch_ovf;

    axi_bus_meter #(.NUM_CHANNELS(1)) u_meter_wr (
        .aclk(aclk), .aresetn(unit_aresetn),
        .i_clear(w_perf_clear), .i_freeze(w_perf_freeze),
        .i_valid(m_axi_wvalid), .i_ready(m_axi_wready),
        .i_channel_id('0), .i_channel_valid(1'b1),
        .o_agg_productive(w_obs_wr_prod), .o_agg_backpressure(w_obs_wr_bp),
        .o_agg_starvation(w_obs_wr_starv), .o_agg_idle(w_obs_wr_idle),
        .o_ch_productive(w_wr_ch_prod), .o_ch_backpressure(w_wr_ch_bp),
        .o_ch_starvation(w_wr_ch_starv), .o_ch_idle(w_wr_ch_idle), .o_ch_overflow(w_wr_ch_ovf)
    );
    axi_bus_meter #(.NUM_CHANNELS(1)) u_meter_rd (
        .aclk(aclk), .aresetn(unit_aresetn),
        .i_clear(w_perf_clear), .i_freeze(w_perf_freeze),
        .i_valid(m_axi_rvalid), .i_ready(m_axi_rready),
        .i_channel_id('0), .i_channel_valid(1'b1),
        .o_agg_productive(w_obs_rd_prod), .o_agg_backpressure(w_obs_rd_bp),
        .o_agg_starvation(w_obs_rd_starv), .o_agg_idle(w_obs_rd_idle),
        .o_ch_productive(w_rd_ch_prod), .o_ch_backpressure(w_rd_ch_bp),
        .o_ch_starvation(w_rd_ch_starv), .o_ch_idle(w_rd_ch_idle), .o_ch_overflow(w_rd_ch_ovf)
    );

    // ========================================================================
    // Bandwidth timer (verbatim from ddr2_char_harness) — cycles + W/R stamps
    // ========================================================================
    logic [63:0] r_cycles, r_w_first, r_w_last, r_r_first, r_r_last;
    logic        r_running, r_done, r_w_first_valid, r_r_first_valid;
    logic        r_w_last_valid, r_r_last_valid, r_wr_kicked, r_rd_kicked;
    logic run_start, w_all_kicked_done;
    assign run_start = w_start_wr_pulse | w_start_rd_pulse;
    assign w_all_kicked_done = (r_wr_kicked | r_rd_kicked)
                             & (~r_wr_kicked | w_wr_done)
                             & (~r_rd_kicked | w_rd_done);

    `ALWAYS_FF_RST(aclk, unit_aresetn,
        if (`RST_ASSERTED(unit_aresetn)) begin
            r_cycles<='0; r_running<=1'b0; r_done<=1'b0;
            r_w_first<='0; r_w_last<='0; r_r_first<='0; r_r_last<='0;
            r_w_first_valid<=1'b0; r_r_first_valid<=1'b0;
            r_w_last_valid<=1'b0; r_r_last_valid<=1'b0;
            r_wr_kicked<=1'b0; r_rd_kicked<=1'b0;
        end else if (w_timer_clear_pulse) begin
            r_cycles<='0; r_running<=1'b0; r_done<=1'b0;
            r_w_first<='0; r_w_last<='0; r_r_first<='0; r_r_last<='0;
            r_w_first_valid<=1'b0; r_r_first_valid<=1'b0;
            r_w_last_valid<=1'b0; r_r_last_valid<=1'b0;
            r_wr_kicked<=1'b0; r_rd_kicked<=1'b0;
        end else begin
            if (w_start_wr_pulse) r_wr_kicked <= 1'b1;
            if (w_start_rd_pulse) r_rd_kicked <= 1'b1;
            if (run_start && !r_running) r_running <= 1'b1;
            if (w_start_wr_pulse && !r_w_first_valid) begin
                r_w_first <= r_cycles; r_w_first_valid <= 1'b1;
            end
            if (w_start_rd_pulse && !r_r_first_valid) begin
                r_r_first <= r_cycles; r_r_first_valid <= 1'b1;
            end
            if (r_running) begin
                r_cycles <= r_cycles + 64'd1;
                if (w_wr_done && !r_w_last_valid) begin
                    r_w_last <= r_cycles; r_w_last_valid <= 1'b1;
                end
                if (w_rd_done && !r_r_last_valid) begin
                    r_r_last <= r_cycles; r_r_last_valid <= 1'b1;
                end
                if (w_all_kicked_done) begin
                    r_running <= 1'b0; r_done <= 1'b1;
                end
            end
        end
    )

    assign w_timer_cycles  = r_cycles;
    assign w_timer_running = r_running;
    assign w_timer_done    = r_done;
    assign w_timer_pass    = r_done & ~w_wr_error & ~w_rd_error
                           & (w_crc_expected == w_crc_actual);
    assign w_timer_w_first = r_w_first;  assign w_timer_w_last = r_w_last;
    assign w_timer_r_first = r_r_first;  assign w_timer_r_last = r_r_last;

    // ========================================================================
    // LED status + 7-segment
    // ========================================================================
    logic [15:0] w_led_status;
    always_comb begin
        w_led_status        = '0;
        w_led_status[0]     = w_init_done;
        w_led_status[1]     = w_wr_error | w_rd_error;
        w_led_status[3]     = w_timer_done;
        w_led_status[4]     = w_timer_pass;
        w_led_status[5]     = w_timer_running;
        w_led_status[6]     = w_wr_done;
        w_led_status[7]     = w_rd_done;
        w_led_status[8]     = w_crc_exp_valid;
        w_led_status[9]     = w_crc_act_valid;
    end

    led_status_driver #(
        .FPGA_CLK_HZ(FPGA_CLK_HZ), .LED_UPDATE_HZ(LED_UPDATE_HZ), .NUM_LEDS(16)
    ) u_led (
        .aclk(aclk), .aresetn(unit_aresetn),
        .i_status(w_led_status), .o_led(o_led)
    );

    // 7-seg: show the low 16 bits of the timer cycle count.
    seven_seg_4digit #(.FPGA_CLK_HZ(FPGA_CLK_HZ), .REFRESH_HZ(1000)) u_7seg (
        .aclk(aclk), .aresetn(unit_aresetn),
        .i_hex(w_timer_cycles[15:0]), .i_enable(1'b1),
        .o_an(o_seven_seg_an), .o_seg(o_seven_seg_seg), .o_dp(o_seven_seg_dp)
    );

    // Currently-unused CSR outputs (litedram self-configures / no delay shims)
    logic _unused;
    assign _unused = &{1'b0, w_clear_stats_pulse, w_freeze_trace, w_soft_reset_pulse,
                       w_timer_expected_beats, w_rd_resp_delay_cyc, w_wr_resp_delay_cyc,
                       w_memtype, w_t_phy_wrlat, w_t_rddata_en, w_rd_in_order,
                       w_cap_lookahead_max, w_cap_synth_mask, w_cmd_delay_sel,
                       w_rddata_delay_sel, w_obs_hist_metric, w_obs_hist_bin,
                       w_obs_hist_bus_sel, w_timer_cycles[63:16], w_wr_ch_prod[0], w_wr_ch_bp[0],
                       w_wr_ch_starv[0], w_wr_ch_idle[0], w_wr_ch_ovf,
                       w_rd_ch_prod[0], w_rd_ch_bp[0], w_rd_ch_starv[0],
                       w_rd_ch_idle[0], w_rd_ch_ovf, m_axi_bid, m_axi_buser,
                       m_axi_rid, m_axi_ruser};

endmodule : char_engine_harness
