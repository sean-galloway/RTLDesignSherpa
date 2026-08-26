// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_top
// Purpose: The rearchitected pumice controller top: pumice_core (3 layers) +
//          the PeakRDL-generated pumice_csr register block. Config is driven
//          BY-NAME from the CSR (hwif_out.*) — no config ports — so software
//          programs timings/phases/policy via the register bus. Presents the
//          register cpuif, host AXI, and the DFI 2.1 pin bus.
//
// Documentation: rtl/macro/pumice_csr.rdl (register map)
`timescale 1ns / 1ps

module pumice_top
    import pumice_pkg::*;
#(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int NUM_RANKS      = 1,
    parameter int NUM_BANKS      = 8,
    parameter int ROW_WIDTH      = 14,
    parameter int COL_WIDTH      = 10,
    parameter int DFI_RATE       = 2,
    parameter int DRAM_BEAT_WIDTH = 64,
    parameter int DRAM_DEVICE_WIDTH = DRAM_BEAT_WIDTH,  // physical device word (x16 => 16)
    parameter int BL             = 8,
    parameter int NUM_ENTRIES    = 8,
    parameter int N_SRAM_SLOTS   = 8,
    parameter int CMD_HISTORY_EN = 0,  // DV: arm the scheduler's history scoreboard

    parameter int DW  = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int SW  = DW / 8,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int AW  = AXI_ADDR_WIDTH,
    parameter int PHW = (DFI_RATE > 1) ? $clog2(DFI_RATE) : 1,
    parameter int DFI_DATA_WIDTH = DW,
    parameter int DFI_STRB_WIDTH = DW / 8,
    parameter int DFI_EN_WIDTH   = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int DFI_ADDR_BUS_W = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W = $clog2(NUM_BANKS) * DFI_RATE,
    parameter int DFI_CTRL_BUS_W = 1 * DFI_RATE,
    parameter int DFI_CS_BUS_W   = NUM_RANKS * DFI_RATE,
    parameter int CSR_ADDR_W     = 12
) (
    input  logic aclk, aresetn, dfi_clk, dfi_rstn,

    // ---- register cpuif (PeakRDL passthrough) ----
    input  logic                    s_cpuif_req,
    input  logic                    s_cpuif_req_is_wr,
    input  logic [CSR_ADDR_W-1:0]   s_cpuif_addr,
    input  logic [31:0]             s_cpuif_wr_data,
    input  logic [31:0]             s_cpuif_wr_biten,
    output logic                    s_cpuif_req_stall_wr,
    output logic                    s_cpuif_req_stall_rd,
    output logic                    s_cpuif_rd_ack,
    output logic                    s_cpuif_rd_err,
    output logic [31:0]             s_cpuif_rd_data,
    output logic                    s_cpuif_wr_ack,
    output logic                    s_cpuif_wr_err,

    output logic                    init_done_o,

    // ---- host AXI4 ----
    input  logic [IW-1:0]  s_axi_awid,   input logic [AW-1:0] s_axi_awaddr,
    input  logic [7:0]     s_axi_awlen,  input logic [2:0]    s_axi_awsize,
    input  logic [1:0]     s_axi_awburst,input logic          s_axi_awlock,
    input  logic [3:0]     s_axi_awcache,input logic [2:0]    s_axi_awprot,
    input  logic [3:0]     s_axi_awqos,  input logic [3:0]    s_axi_awregion,
    input  logic           s_axi_awuser, input logic          s_axi_awvalid,
    output logic           s_axi_awready,
    input  logic [DW-1:0]  s_axi_wdata,  input logic [SW-1:0] s_axi_wstrb,
    input  logic           s_axi_wlast,  input logic          s_axi_wuser,
    input  logic           s_axi_wvalid, output logic         s_axi_wready,
    output logic [IW-1:0]  s_axi_bid,    output logic [1:0]   s_axi_bresp,
    output logic           s_axi_buser,  output logic         s_axi_bvalid,
    input  logic           s_axi_bready,
    input  logic [IW-1:0]  s_axi_arid,   input logic [AW-1:0] s_axi_araddr,
    input  logic [7:0]     s_axi_arlen,  input logic [2:0]    s_axi_arsize,
    input  logic [1:0]     s_axi_arburst,input logic          s_axi_arlock,
    input  logic [3:0]     s_axi_arcache,input logic [2:0]    s_axi_arprot,
    input  logic [3:0]     s_axi_arqos,  input logic [3:0]    s_axi_arregion,
    input  logic           s_axi_aruser, input logic          s_axi_arvalid,
    output logic           s_axi_arready,
    output logic [IW-1:0]  s_axi_rid,    output logic [DW-1:0] s_axi_rdata,
    output logic [1:0]     s_axi_rresp,  output logic          s_axi_rlast,
    output logic           s_axi_ruser,  output logic          s_axi_rvalid,
    input  logic           s_axi_rready,

    // ---- DFI 2.1 pin bus ----
    output logic [DFI_ADDR_BUS_W-1:0]  dfi_address_o,
    output logic [DFI_BANK_BUS_W-1:0]  dfi_bank_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_cas_n_o, dfi_ras_n_o, dfi_we_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_cs_n_o, dfi_odt_o,
    output logic [DFI_DATA_WIDTH-1:0]  dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]  dfi_wrdata_mask_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]  dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0] dfi_rddata_valid_i,
    output logic                       dfi_init_start_o,
    input  logic                       dfi_init_complete_i
);

    // ---- CSR register block (PeakRDL) ----
    pumice_csr_pkg::pumice_csr__in_t  hwif_in;
    pumice_csr_pkg::pumice_csr__out_t hwif_out;
    // hwif_in: everything defaults to 0 (unwired status/obs readback), the
    // live telemetry members are assigned below. always_comb so members can
    // be overridden without a second driver on the struct.
    logic [31:0] w_stat_page_hit, w_stat_page_miss, w_stat_page_empty;
    logic [31:0] w_stat_act, w_stat_pre, w_stat_ref;
    always_comb begin
        hwif_in = '{default: '0};
        hwif_in.PAGE_STATS_HIT.count.next    = w_stat_page_hit;
        hwif_in.PAGE_STATS_MISS.count.next   = w_stat_page_miss;
        hwif_in.PAGE_STATS_EMPTY.count.next  = w_stat_page_empty;
        hwif_in.SCHED_STATS_ACT.count.next   = w_stat_act;
        hwif_in.SCHED_STATS_PRE.count.next   = w_stat_pre;
        hwif_in.REF_STATS_REF.count.next     = w_stat_ref;
        // Capability strap: per-bank refresh exists on LPDDR2 only (DDR2 has
        // no REFpb command). Software reads this before selecting mode 2.
        hwif_in.REF_CTRL.perbank_supported.next =
            (w_memtype == MEMTYPE_LPDDR2);
    end

    pumice_csr u_csr (
        .clk(aclk), .rst(~aresetn),
        .s_cpuif_req(s_cpuif_req), .s_cpuif_req_is_wr(s_cpuif_req_is_wr),
        .s_cpuif_addr(s_cpuif_addr), .s_cpuif_wr_data(s_cpuif_wr_data),
        .s_cpuif_wr_biten(s_cpuif_wr_biten),
        .s_cpuif_req_stall_wr(s_cpuif_req_stall_wr),
        .s_cpuif_req_stall_rd(s_cpuif_req_stall_rd),
        .s_cpuif_rd_ack(s_cpuif_rd_ack), .s_cpuif_rd_err(s_cpuif_rd_err),
        .s_cpuif_rd_data(s_cpuif_rd_data),
        .s_cpuif_wr_ack(s_cpuif_wr_ack), .s_cpuif_wr_err(s_cpuif_wr_err),
        .hwif_in(hwif_in), .hwif_out(hwif_out)
    );

    // ---- config from CSR (by-name hwif_out) ----
    memtype_e         w_memtype;
    page_policy_e     w_page_policy;
    assign w_memtype     = memtype_e'(hwif_out.PHY_TIMING.memtype.value);
    // REFRESH_TUNING.page_policy_or uses the SOFTWARE encoding (0=use build
    // default, 1=OPEN, 2=CLOSE, 3=HYBRID) while page_policy_e is OPEN=0/
    // CLOSE=1/HYBRID=2. The old raw cast made software-OPEN run CLOSE and
    // software-CLOSE run HYBRID — the entire open_page/reorder config-axis
    // corruption keyed off this (issue #42).
    localparam page_policy_e PAGE_POLICY_BUILD_DEFAULT = PAGE_POLICY_OPEN;
    always_comb begin
        unique case (hwif_out.REFRESH_TUNING.page_policy_or.value)
            2'd1:    w_page_policy = PAGE_POLICY_OPEN;
            2'd2:    w_page_policy = PAGE_POLICY_CLOSE;
            // 2'd3 was HYBRID -- retired; maps to build default. The adaptive
            // policies are PAGE_POLICY_CFG.policy_mode, not this legacy knob.
            default: w_page_policy = PAGE_POLICY_BUILD_DEFAULT;  // 0/3 = build default
        endcase
    end

    pumice_core #(
        .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW), .NUM_RANKS(NUM_RANKS),
        .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH),
        .DFI_RATE(DFI_RATE), .DRAM_BEAT_WIDTH(DRAM_BEAT_WIDTH),
        .DRAM_DEVICE_WIDTH(DRAM_DEVICE_WIDTH), .BL(BL),
        .NUM_ENTRIES(NUM_ENTRIES), .N_SRAM_SLOTS(N_SRAM_SLOTS),
        .CMD_HISTORY_EN(CMD_HISTORY_EN)
    ) u_core (
        .aclk(aclk), .aresetn(aresetn), .dfi_clk(dfi_clk), .dfi_rstn(dfi_rstn),
        .memtype_i(w_memtype), .page_policy_i(w_page_policy),
        .page_mode_i(hwif_out.PAGE_POLICY_CFG.policy_mode.value),
        .page_scope_i(hwif_out.PAGE_POLICY_CFG.policy_scope.value),
        .page_tr_init_i(hwif_out.PAGE_TIMEOUT_CFG.tr_init.value),
        .page_tr_min_i(hwif_out.PAGE_TIMEOUT_CFG.tr_min.value),
        .page_tr_max_i(hwif_out.PAGE_TIMEOUT_CFG.tr_max.value),
        .page_tr_step_i(hwif_out.PAGE_TIMEOUT_CFG.tr_step.value),
        .page_mc_high_i(hwif_out.PAGE_ADAPT_CFG.mc_high_thr.value),
        .page_mc_low_i(hwif_out.PAGE_ADAPT_CFG.mc_low_thr.value),
        .page_mc_init_i(hwif_out.PAGE_ADAPT_CFG.mc_init.value),
        .page_check_ivl_i(hwif_out.PAGE_ADAPT_CFG.check_interval.value),
        .sched_order_mode_i(hwif_out.SCHED_POLICY.order_mode.value),
        .sched_age_thresh_i(hwif_out.SCHED_POLICY.age_thresh.value),
        .page_ctr_thresh_i(hwif_out.PAGE_POLICY_CFG.ctr_open_max.value),
        .page_ctr_init_i(hwif_out.PAGE_POLICY_CFG.ctr_init.value),
        .page_rbl_thresh_i(hwif_out.PAGE_RBL_CFG.miss_thresh.value),
        .page_rbl_ways_i(hwif_out.PAGE_RBL_CFG.ways.value),
        .page_rbl_sets_i(hwif_out.PAGE_RBL_CFG.sets.value),
        .page_rbl_ivl_i(hwif_out.PAGE_RBL_CFG.reset_interval.value),
        .stat_page_hit_o(w_stat_page_hit), .stat_page_miss_o(w_stat_page_miss),
        .stat_page_empty_o(w_stat_page_empty), .stat_act_o(w_stat_act),
        .stat_pre_o(w_stat_pre), .stat_ref_o(w_stat_ref),
        .bank_lsb_i(hwif_out.ADDR_MAP.bank_lsb.value),
        .hash_en_i(hwif_out.ADDR_MAP.hash_en.value),
        .hash_seed_i(hwif_out.ADDR_MAP.hash_seed.value),
        .t_rcd_i(hwif_out.TIMINGS_RC_RCD_RP_RAS.tRCD.value),
        .t_rp_i (hwif_out.TIMINGS_RC_RCD_RP_RAS.tRP.value),
        .t_ras_i(hwif_out.TIMINGS_RC_RCD_RP_RAS.tRAS.value),
        .t_rc_i (hwif_out.TIMINGS_RC_RCD_RP_RAS.tRC.value),
        .t_wr_i (hwif_out.TIMINGS_CL_CWL_WR.tWR.value),
        .t_rtp_i(hwif_out.TIMINGS_RTP_RTW.tRTP.value),
        .t_faw_i(hwif_out.TIMINGS_RRD_FAW_WTR_CCD.tFAW.value),
        .t_rrd_i(hwif_out.TIMINGS_RRD_FAW_WTR_CCD.tRRD.value),
        .t_wtr_i(hwif_out.TIMINGS_RRD_FAW_WTR_CCD.tWTR.value),
        .t_rtw_i(hwif_out.TIMINGS_RTP_RTW.tRTW.value),
        .t_ccd_i(hwif_out.TIMINGS_RRD_FAW_WTR_CCD.tCCD.value),
        .t_refi_i(hwif_out.TIMINGS_RFC_REFI.tREFI.value),
        .t_rfc_i(hwif_out.TIMINGS_RFC_REFI.tRFC.value),
        .refresh_burst_i(hwif_out.PHY_TIMING.refresh_burst.value),
        .ref_postpone_i(hwif_out.REF_CTRL.postpone_limit.value),
        .ref_pullin_i(hwif_out.REF_CTRL.pullin_limit.value),
        .ref_mode_i(hwif_out.REF_CTRL.mode.value),
        .ref_trefi_pb_i(hwif_out.REF_TIMING_PB.trefi_pb.value),
        .ref_trfc_pb_i(hwif_out.REF_TIMING_PB.trfc_pb.value),
        .t_init_wait_i(hwif_out.INIT_TIMING0.t_init_wait.value),
        .t_dll_wait_i (hwif_out.INIT_TIMING0.t_dll_wait.value),
        .t_mrd_wait_i (hwif_out.INIT_TIMING1.t_mrd_wait.value),
        .t_rp_wait_i  (hwif_out.INIT_TIMING1.t_rp_wait.value),
        .t_rfc_wait_i (hwif_out.INIT_TIMING1.t_rfc_wait.value),
        .mr0_i        (hwif_out.MR0.VAL.value),
        .mr1_i        (hwif_out.MR1.VAL.value),
        .mr2_i        (hwif_out.MR2.VAL.value),
        .mr3_i        (hwif_out.MR3.VAL.value),
        .init_restart_i(hwif_out.CTRL.init_force_restart.value),
        .rd_phase_i(hwif_out.DFI_PHASE.rd_phase.value[PHW-1:0]),
        .wr_phase_i(hwif_out.DFI_PHASE.wr_phase.value[PHW-1:0]),
        .t_phy_wrlat_i(hwif_out.PHY_TIMING.t_phy_wrlat.value),
        .t_rddata_en_i(hwif_out.PHY_TIMING.t_rddata_en.value),
        .gear_i(hwif_out.DFI_PHASE.gear_ratio.value),
        .bl_i(hwif_out.DFI_PHASE.bl.value),
        .cl_o(), .cwl_o(), .bl_o(), .init_done_o(init_done_o),
        .s_axi_awid(s_axi_awid), .s_axi_awaddr(s_axi_awaddr), .s_axi_awlen(s_axi_awlen),
        .s_axi_awsize(s_axi_awsize), .s_axi_awburst(s_axi_awburst), .s_axi_awlock(s_axi_awlock),
        .s_axi_awcache(s_axi_awcache), .s_axi_awprot(s_axi_awprot), .s_axi_awqos(s_axi_awqos),
        .s_axi_awregion(s_axi_awregion), .s_axi_awuser(s_axi_awuser),
        .s_axi_awvalid(s_axi_awvalid), .s_axi_awready(s_axi_awready),
        .s_axi_wdata(s_axi_wdata), .s_axi_wstrb(s_axi_wstrb), .s_axi_wlast(s_axi_wlast),
        .s_axi_wuser(s_axi_wuser), .s_axi_wvalid(s_axi_wvalid), .s_axi_wready(s_axi_wready),
        .s_axi_bid(s_axi_bid), .s_axi_bresp(s_axi_bresp), .s_axi_buser(s_axi_buser),
        .s_axi_bvalid(s_axi_bvalid), .s_axi_bready(s_axi_bready),
        .s_axi_arid(s_axi_arid), .s_axi_araddr(s_axi_araddr), .s_axi_arlen(s_axi_arlen),
        .s_axi_arsize(s_axi_arsize), .s_axi_arburst(s_axi_arburst), .s_axi_arlock(s_axi_arlock),
        .s_axi_arcache(s_axi_arcache), .s_axi_arprot(s_axi_arprot), .s_axi_arqos(s_axi_arqos),
        .s_axi_arregion(s_axi_arregion), .s_axi_aruser(s_axi_aruser),
        .s_axi_arvalid(s_axi_arvalid), .s_axi_arready(s_axi_arready),
        .s_axi_rid(s_axi_rid), .s_axi_rdata(s_axi_rdata), .s_axi_rresp(s_axi_rresp),
        .s_axi_rlast(s_axi_rlast), .s_axi_ruser(s_axi_ruser),
        .s_axi_rvalid(s_axi_rvalid), .s_axi_rready(s_axi_rready),
        .dfi_address_o(dfi_address_o), .dfi_bank_o(dfi_bank_o),
        .dfi_cas_n_o(dfi_cas_n_o), .dfi_ras_n_o(dfi_ras_n_o), .dfi_we_n_o(dfi_we_n_o),
        .dfi_cs_n_o(dfi_cs_n_o), .dfi_odt_o(dfi_odt_o),
        .dfi_wrdata_o(dfi_wrdata_o), .dfi_wrdata_en_o(dfi_wrdata_en_o),
        .dfi_wrdata_mask_o(dfi_wrdata_mask_o),
        .dfi_rddata_en_o(dfi_rddata_en_o), .dfi_rddata_i(dfi_rddata_i),
        .dfi_rddata_valid_i(dfi_rddata_valid_i),
        .dfi_init_start_o(dfi_init_start_o), .dfi_init_complete_i(dfi_init_complete_i)
    );

endmodule : pumice_top
