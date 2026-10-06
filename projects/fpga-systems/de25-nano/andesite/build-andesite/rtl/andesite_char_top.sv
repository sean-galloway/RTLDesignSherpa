// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_char_top
// Purpose: andesite_core on the Genesys 2 -- the de25-nano area's first
//          build. The DE25-Nano (Intel, LPDDR4) is the destination board;
//          Genesys 2 is the timing/build vehicle until it lands, so this top
//          deliberately carries NO DRAM PHY: the DFI 4.0 pins stop at an
//          observability XOR tree (the keep-alive net that keeps the whole
//          datapath load-bearing for synthesis) and the LEDs. An on-chip
//          AXI exerciser (andesite_exerciser.sv) starts after init and
//          loops write/read bursts so the timing report covers the whole
//          core, not just the init/refresh command path an idle build
//          would leave behind.
//
//          What this build answers: does andesite_core synthesise, place,
//          route, and close (or how badly does it miss) in Vivado on real
//          silicon-grade constraints? Everything except the PHY -- the one
//          thing a Genesys 2 cannot teach andesite (EMIF-first ruling for
//          the real board stands).
//
//          Clocks: the Genesys 2 has a single 200 MHz LVDS oscillator; an
//          MMCM divides to the andesite sys clock at 100 MHz (10.0 ns MC
//          cycle -- the timing spacings programmed below are recomputed for
//          it, per the derivation discipline in dv/tbclasses/
//          andesite_dram_configs.py). aclk and dfi_clk run 1:1, as the
//          core DV TBs do.
//
//          Model after: Genesys2/scoria/build-scoria/rtl/scoria_char_top.sv
//          (the harness shape; the PHY, host bridges and seq scaffolding
//          stay out until there is something to bring up).

`timescale 1ns / 1ps

module andesite_char_top (
    input  logic        clk200_p,
    input  logic        clk200_n,
    input  logic        cpu_reset_n,   // active-low pushbutton
    output logic [7:0]  led
);

    import andesite_pkg::*;

    // Design-point geometry (mirrors the u_core parameters below).
    localparam int NUM_RANKS = 1;
    localparam int NUM_BANKS = 8;
    localparam int NUM_BG    = 4;
    localparam int ADDRW     = 18;
    localparam int DFI_RATE  = 2;
    localparam int BEATW     = 64;                 // DRAM_BEAT_WIDTH
    localparam int DW        = BEATW * DFI_RATE;   // DFI word = 128
    localparam int SW        = DW / 8;             // strobe/mask width = 16
    localparam int BKW       = $clog2(NUM_BANKS);
    localparam int BGW       = $clog2(NUM_BG);
    localparam int PHW       = $clog2(DFI_RATE);

    // ------------------------------------------------------------------
    // 200 MHz LVDS oscillator -> MMCM -> 100 MHz sys (aclk == dfi_clk, 1:1)
    // ------------------------------------------------------------------
    logic clk200, sys_clk, sys_clk_mmcm, sys_clk_fb, mmcm_locked;

    IBUFDS u_ibufds_clk (
        .I  (clk200_p),
        .IB (clk200_n),
        .O  (clk200)
    );

    // VCO = 200 x 5 = 1000 MHz; CLKOUT0 /10 = 100 MHz.
    MMCME2_BASE #(
        .CLKIN1_PERIOD    (5.0),
        .CLKFBOUT_MULT_F  (5.0),
        .CLKOUT0_DIVIDE_F (10.0),
        .DIVCLK_DIVIDE    (1)
    ) u_mmcm (
        .CLKIN1   (clk200),
        .CLKFBIN  (sys_clk_fb),
        .CLKFBOUT (sys_clk_fb),
        .CLKOUT0  (sys_clk_mmcm),
        .LOCKED   (mmcm_locked),
        .RST      (1'b0),
        .PWRDWN   (1'b0)
    );

    BUFG u_bufg_sys (.I (sys_clk_mmcm), .O (sys_clk));

    // ------------------------------------------------------------------
    // Button reset -> 100 MHz synchronous, active low (scoria pattern)
    // ------------------------------------------------------------------
    logic rst_meta, rst_sync_n;
    always_ff @(posedge sys_clk or negedge cpu_reset_n) begin
        if (!cpu_reset_n) begin
            rst_meta   <= 1'b0;
            rst_sync_n <= 1'b0;
        end else begin
            rst_meta   <= 1'b1;
            rst_sync_n <= rst_meta;
        end
    end

    logic core_rst_n;
    assign core_rst_n = rst_sync_n & mmcm_locked;

    // ------------------------------------------------------------------
    // DFI 4.0 pins: terminate at the observability tree below
    // ------------------------------------------------------------------
    logic [ADDRW-1:0]      dfi_address;
    logic [BKW-1:0]        dfi_bank;
    logic [BGW-1:0]        dfi_bg;
    logic                  dfi_act_n, dfi_ras_n, dfi_cas_n, dfi_we_n;
    logic [NUM_RANKS-1:0]  dfi_cs;
    logic                  dfi_cke, dfi_reset_n, dfi_init_start;
    logic [DW-1:0]         dfi_wrdata;
    logic [SW-1:0]         dfi_wrdata_mask;
    logic                  init_done, init_err, zq_busy;

    // ------------------------------------------------------------------
    // AXI4 wires between the on-chip exerciser and the core's slave
    // ------------------------------------------------------------------
    logic [7:0]  x_awid, x_arid, x_bid, x_rid;
    logic [31:0] x_awaddr, x_araddr;
    logic        x_awvalid, x_awready, x_wvalid, x_wready;
    logic        x_bvalid, x_bready, x_arvalid, x_arready;
    logic        x_rvalid, x_rready, x_wlast, x_rlast;
    logic [DW-1:0] x_wdata, x_rdata;
    logic [SW-1:0] x_wstrb;
    logic [1:0]  x_bresp, x_rresp;
    logic        exerciser_busy;
    logic [7:0]  x_awlen, x_arlen;
    logic [2:0]  x_awsize, x_arsize;
    logic [1:0]  x_awburst, x_arburst;

    // ------------------------------------------------------------------
    // andesite_core -- timing spacings are prog = ceil(ns/10ns) - 1 at the
    // 100 MHz sys clock, derived from the DDR4-1600J ns figures the same
    // way dv/tbclasses/andesite_dram_configs.py derives the TB's.
    // ------------------------------------------------------------------
    andesite_core #(
        .AXI_ID_WIDTH   (8),
        .AXI_ADDR_WIDTH (32),
        .NUM_RANKS      (NUM_RANKS),
        .NUM_BANKS      (NUM_BANKS),
        .NUM_BG         (NUM_BG),
        .ROW_WIDTH      (14),
        .COL_WIDTH      (10),
        .ADDR_WIDTH     (ADDRW),
        .DFI_RATE       (DFI_RATE),
        .DRAM_BEAT_WIDTH   (BEATW),
        .DRAM_DEVICE_WIDTH (BEATW),
        .DRAM_BL        (8)
    ) u_core (
        .aclk    (sys_clk),
        .aresetn (core_rst_n),
        .dfi_clk (sys_clk),
        .dfi_rstn(core_rst_n),

        // ---- config: DDR4, open page, no hashing ----
        .memtype_i      (MEMTYPE_DDR4),
        .page_policy_i  (PAGE_POLICY_OPEN),
        .page_mode_i    (3'd0),
        .page_tr_init_i (8'd0),
        .sched_order_mode_i  (2'd0),
        .sched_row_sel_i     (2'd0),
        .sched_col_sel_i     (2'd0),
        .sched_access_pref_i (2'd0),
        .sched_wr_high_wm_i  (8'h80),
        .sched_wr_batch_max_i(8'd16),
        .sched_wr_low_wm_i   (8'h40),
        .sched_prio_sub_i    (2'd0),
        .sched_qos_en_i      (1'b0),
        .sched_age_thresh_i  (8'd0),

        // stall-cause attribution (unobserved in build 1)
        .stall_bp_o         (),
        .stall_refresh_o    (),
        .stall_turnaround_o (),
        .stall_tccd_o       (),
        .stall_actlimit_o   (),
        .stall_banktimer_o  (),
        .stall_noreq_o      (),
        .stall_zq_o         (),
        .stat_page_hit_o    (),
        .stat_row_hit_o     (),
        .stat_page_miss_o   (),
        .stat_page_empty_o  (),
        .stat_act_o         (),
        .stat_pre_o         (),
        .stat_ref_o         (),
        .stat_ref_busy_o    (),

        .bank_lsb_i (5'd0),
        .hash_en_i  (1'b0),
        .hash_seed_i(8'd0),

        // ---- timings: prog values at the 10.0 ns MC cycle ----
        .t_rcd_i (8'd1),   // tRCD 13.75 ns -> spacing 2
        .t_rp_i  (8'd1),   // tRP  13.75 ns -> spacing 2
        .t_ras_i (8'd3),   // tRAS 35.0  ns -> spacing 4
        .t_rc_i  (8'd4),   // tRC  48.75 ns -> spacing 5
        .t_wr_i  (8'd1),   // tWR  15.0  ns -> spacing 2
        .t_rtp_i (8'd0),   // tRTP 7.5   ns -> spacing 1
        .t_faw_i (8'd2),   // tFAW 30.0  ns -> spacing 3
        .t_rrd_i (8'd0),   // tRRD_S 4.9 ns -> spacing 1
        .t_wtr_i (8'd0),   // tWTR_S 2.5 ns -> spacing 1
        .t_rtw_i (8'd0),
        .t_ccd_i (8'd0),   // legacy single ccd (L/S below are the DDR4 pair)
        .t_ccd_l_i(8'd0),  // tCCD_L 5.625 ns -> spacing 1
        .t_ccd_s_i(8'd0),  // tCCD_S 2.5   ns -> spacing 1
        .t_rrd_l_i(8'd0),
        .t_rrd_s_i(8'd0),
        .t_refi_i (16'd780),  // 7.8 us deadline, floored, no N+1
        .refi_reload_i(1'b0),
        .t_rfc_i  (16'd25),   // tRFC 260 ns -> spacing 26 (window, prog N-1)
        .fgr_factor_i (2'd0), // 1x
        .t_rfc_2x_i   (16'd13),
        .t_rfc_4x_i   (16'd7),
        .refresh_burst_i(4'd1),
        .ref_postpone_i (4'd0),
        .ref_pullin_i   (4'd0),
        .ref_mode_i     (2'd0),
        .ref_trefi_pb_i (16'd0),
        .ref_trfc_pb_i  (8'd0),
        .t_init_wait_i (16'd4),    // TB CSRS tinit1
        .t_dll_wait_i  (16'd192),  // TB CSRS tdllk (test-scaled)
        .t_mrd_wait_i  (8'd2),     // TB CSRS tmrd
        .t_rp_wait_i   (8'd4),     // TB CSRS tinit3
        .t_cke_wait_i  (16'd2),    // TB CSRS tinit4
        .t_mod_wait_i  (16'd6),    // TB CSRS tmod
        .t_zqinit_wait_i(16'd256), // TB CSRS tzqinit

        .dfi_reset_n_o (dfi_reset_n),

        // ---- ZQ: enabled, slow interval ----
        .zq_enable_i   (1'b1),
        .zq_interval_i (32'd10_000_000),
        .t_zqcs_i      (16'd64),
        .t_zq_i        (16'd64),
        .zq_mpc_opcode_i(6'd0),
        .zq_busy_o     (zq_busy),
        .zq_total_o    (),
        .zq_interval_cnt_o (),
        .zq_overdue_o  (),
        .ref_elastic_en_i (1'b0),
        .ref_pullin_idle_streak_i (8'd0),
        .ref_postpone_demand_streak_i(7'd0),
        .ref_tcr_en_i (1'b0),
        .ref_trefi_derate_i (2'd0),
        .zq_placement_i (2'd0),
        .zq_overdue_max_i (13'd0),
        .obs_ref_postpone_events_o (),
        .obs_ref_pullin_events_o   (),

        // ---- training: disabled, PHY-side acks idle-asserted ----
        .wrlvl_strobe_i (1'b0),
        .wrlvl_cs_sel_i (4'd0),
        .t_wldqsen_i (16'd0),
        .t_wlmrd_i   (16'd0),
        .t_wlmrd_max_i(16'd0),
        .t_wlo_i     (16'd0),
        .t_wloe_i    (16'd0),
        .dfi_prime_dq_i (1'b0),
        .dfi_phylvl_ack_cs_n_i (1'b1),
        .dfi_phylvl_req_cs_n_o (),
        .dfi_phy_wrlvl_cs_n_o  (),
        .dfi_wrlvl_strobe_o    (),
        .rdlvl_en_i (1'b0),
        .rdlvl_cs_sel_i (4'd0),
        .csr_mr3_mpr_enter_i (16'd0),
        .csr_mr3_mpr_exit_i  (16'd0),
        .t_mpr_enter_i  (16'd0),
        .t_mpr_exit_i   (16'd0),
        .t_mpr_readout_i(16'd0),
        .tmod_i (16'd0),
        .t_rdlvl_timeout_i (16'd0),
        .mpr_pattern_i (1'b0),
        .dfi_phylvl_req_cs_n_i (1'b1),
        .dfi_phylvl_ack_cs_n_o (),
        .dfi_phy_rdlvl_cs_n_o  (),
        .ca_train_en_i (1'b0),
        .wdq_cal_en_i  (1'b0),
        .chan_sel_i    (1'b0),
        .csr_mpc_ca_enter_i  (16'd0),
        .csr_mpc_ca_exit_i   (16'd0),
        .csr_mpc_wdq_enter_i (16'd0),
        .csr_mpc_wdq_exit_i  (16'd0),
        .t_ca_train_i (16'd0),
        .t_wdq_cal_i  (16'd0),
        .t_ca_timeout_i (16'd0),
        .ca_sample_i  (1'b0),
        .wdq_sample_i (1'b0),

        // ---- MR images: the TB's proven-walking set (0x10 + index) ----
        .mr0_i (16'h0010),
        .mr1_i (16'h0011),
        .mr2_i (16'h0012),
        .mr3_i (16'h0013),
        .mr4_i (16'h0014),
        .mr5_i (16'h0015),
        .mr6_i (16'h0016),
        .init_restart_i (1'b0),

        .rd_phase_i (PHW'(0)),
        .wr_phase_i (PHW'(0)),
        .t_phy_wrlat_i (8'd0),
        .t_rddata_en_i (8'd1),
        .gear_i (2'd0),
        .bl_i   (4'd8),
        .init_done_o (init_done),
        .init_err_o  (init_err),

        .rtt_nom_o  (),
        .rtt_wr_o   (),
        .rtt_park_o (),
        .rd_dbi_en_o (),
        .wr_dbi_en_o (),
        .parity_enable_o (),

        // ---- AXI4 host: the on-chip exerciser (traffic keeps every
        //      datapath cone load-bearing for the timing run) ----
        .s_axi_awid(x_awid), .s_axi_awaddr(x_awaddr), .s_axi_awlen(x_awlen),
        .s_axi_awsize(x_awsize), .s_axi_awburst(x_awburst), .s_axi_awlock(1'd0),
        .s_axi_awcache(4'd0), .s_axi_awprot(3'd0), .s_axi_awqos(4'd0),
        .s_axi_awregion(4'd0), .s_axi_awuser(1'd0), .s_axi_awvalid(x_awvalid),
        .s_axi_awready(x_awready),
        .s_axi_wdata(x_wdata), .s_axi_wstrb(x_wstrb),
        .s_axi_wlast(x_wlast), .s_axi_wuser(1'd0), .s_axi_wvalid(x_wvalid),
        .s_axi_wready(x_wready),
        .s_axi_bid(x_bid), .s_axi_bresp(x_bresp), .s_axi_buser(), .s_axi_bvalid(x_bvalid),
        .s_axi_bready(x_bready),
        .s_axi_arid(x_arid), .s_axi_araddr(x_araddr), .s_axi_arlen(x_arlen),
        .s_axi_arsize(x_arsize), .s_axi_arburst(x_arburst), .s_axi_arlock(1'd0),
        .s_axi_arcache(4'd0), .s_axi_arprot(3'd0), .s_axi_arqos(4'd0),
        .s_axi_arregion(4'd0), .s_axi_aruser(1'd0), .s_axi_arvalid(x_arvalid),
        .s_axi_arready(x_arready),
        .s_axi_rid(x_rid), .s_axi_rdata(x_rdata), .s_axi_rresp(x_rresp),
        .s_axi_rlast(x_rlast), .s_axi_ruser(), .s_axi_rvalid(x_rvalid),
        .s_axi_rready(x_rready),

        .dfi_address_o     (dfi_address),
        .dfi_bank_o        (dfi_bank),
        .dfi_bg_o          (dfi_bg),
        .dfi_act_n_o       (dfi_act_n),
        .dfi_ras_n_o       (dfi_ras_n),
        .dfi_cas_n_o       (dfi_cas_n),
        .dfi_we_n_o        (dfi_we_n),
        .dfi_cs_o          (dfi_cs),
        .dfi_cke_o         (dfi_cke),
        .dfi_parity_in_o   (),
        .dfi_wrdata_o      (dfi_wrdata),
        .dfi_wrdata_en_o   (),
        .dfi_wrdata_mask_o (dfi_wrdata_mask),
        .dfi_wrdata_cs_o   (),
        .dfi_rddata_en_o   (),
        .dfi_rddata_i      ({DW{1'b0}}),
        .dfi_rddata_valid_i({DFI_RATE{1'b0}}),
        .dfi_rddata_dbi_i  ({SW{1'b0}}),
        .dfi_rddata_cs_o   (),
        .dfi_init_start_o  (dfi_init_start),
        .dfi_init_complete_i (1'b1)
    );

    // ------------------------------------------------------------------
    // On-chip traffic generator: starts after init, loops write/read
    // bursts across the bank stride. See andesite_exerciser.sv.
    // ------------------------------------------------------------------
    andesite_exerciser #(
        .AW  (32),
        .DW  (DW),
        .IW  (8),
        .COLW(10)
    ) u_exerciser (
        .clk (sys_clk),
        .rst_n(core_rst_n),
        .enable_i (init_done & ~init_err),
        .m_axi_awid(x_awid), .m_axi_awaddr(x_awaddr), .m_axi_awlen(x_awlen),
        .m_axi_awsize(x_awsize), .m_axi_awburst(x_awburst), .m_axi_awvalid(x_awvalid),
        .m_axi_awready(x_awready),
        .m_axi_wdata(x_wdata), .m_axi_wstrb(x_wstrb), .m_axi_wlast(x_wlast),
        .m_axi_wvalid(x_wvalid), .m_axi_wready(x_wready),
        .m_axi_bid(x_bid), .m_axi_bresp(x_bresp), .m_axi_bvalid(x_bvalid),
        .m_axi_bready(x_bready),
        .m_axi_arid(x_arid), .m_axi_araddr(x_araddr), .m_axi_arlen(x_arlen),
        .m_axi_arsize(x_arsize), .m_axi_arburst(x_arburst), .m_axi_arvalid(x_arvalid),
        .m_axi_arready(x_arready),
        .m_axi_rid(x_rid), .m_axi_rdata(x_rdata), .m_axi_rresp(x_rresp),
        .m_axi_rlast(x_rlast), .m_axi_rvalid(x_rvalid),
        .m_axi_rready(x_rready),
        .exerciser_busy_o(exerciser_busy)
    );

    // ------------------------------------------------------------------
    // Observability. led[3] is the keep-alive net: an XOR reduction over
    // the DFI datapath and control pins, so every flop that feeds the DFI
    // interface stays load-bearing through synthesis. The exerciser makes
    // those pins toggle for real; without the XOR the DFI nets -- and the
    // logic behind them -- would be trimmed and the timing report would
    // describe a core that is not there.
    // ------------------------------------------------------------------
    logic [25:0] heartbeat_cnt;
    always_ff @(posedge sys_clk or negedge core_rst_n) begin
        if (!core_rst_n) heartbeat_cnt <= '0;
        else             heartbeat_cnt <= heartbeat_cnt + 1'b1;
    end

    assign led[0] = heartbeat_cnt[25];                       // ~1.5 Hz at 100 MHz
    assign led[1] = init_done;
    assign led[2] = init_err;
    assign led[3] = ^{dfi_wrdata, dfi_wrdata_mask, dfi_address,
                      dfi_bank, dfi_bg, dfi_cs, dfi_act_n, dfi_ras_n,
                      dfi_cas_n, dfi_we_n, dfi_cke};
    assign led[4] = zq_busy;
    assign led[5] = dfi_reset_n;
    assign led[6] = dfi_init_start;
    assign led[7] = exerciser_busy;                          // traffic alive

endmodule : andesite_char_top
