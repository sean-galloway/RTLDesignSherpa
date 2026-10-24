// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: granite_core
// Purpose: Granite (DDR2/LPDDR2 v2 product) controller core.  Composes the
//          common-ip stack per config/product_config.md:
//            1. mc_axi4_plane          (host AXI; intakes + return ring)
//            2. mc_xddr2_entry_store   (storage-lite N=1 in-order seam)
//            3. mc_init_plane          (JEDEC init + MR shadow + PHY handshake)
//            4. mc_scheduler_plane     (pick machinery + common v2 children,
//                                      external-init mode)
//            5. mc_training_plane      (LPDDR2 ZQ + DQ cal)
//            6. mc_dfi_2p1_plane       (common single async CDC + DFI datapath)
//          No mc_storage_plane, no mc_ras_plane.  CSR/timer ports are simple
//          inputs for now; a product CSR block is a later task.
//
// Documentation: product-ip/granite-ddr2-lpddr2/config/product_config.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module granite_core
    import mc_common_pkg::*;
    import granite_pkg::*;
#(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int NUM_RANKS      = 1,
    parameter int NUM_BANKS      = 8,
    parameter int ROW_WIDTH      = 14,
    parameter int COL_WIDTH      = 10,
    parameter int DFI_RATE       = 2,
    parameter int DRAM_BEAT_WIDTH = 64,
    parameter int DRAM_DEVICE_WIDTH = DRAM_BEAT_WIDTH,
    parameter int DRAM_BL             = 8,
    parameter int NUM_ENTRIES    = GRANITE_SEAM_N,
    parameter int RD_RET_DEPTH   = 32,
    parameter int CMD_DELAY      = 0,
    parameter int AGE_WIDTH      = 16,
    // Scheduler pick core (mc_common_pkg MC_SCHED_*). BANK_PICK is the product
    // core on the per-bank head records (mem-ctrl recovery Phase 2); FRFCFS
    // is the research arbiter the product shipped on until then.
    // Owner, 2026-10-22: granite (the product) carries the BANK_PICK core;
    // pumice (research) carries FR-FCFS. Both stay selectable.
    parameter int SCHED_CORE     = mc_common_pkg::MC_SCHED_BANK_PICK,
    // Storage backend (recovery plan 2.4, Phase 4 -- pumice TASK-050):
    //   1 = mc_bank_fifo_store: per-bank FIFOs of slots, records read off the
    //       FIFO fronts; linear in NUM_ENTRIES, and the same-row-behind flag
    //       is one stored bit per queue position (compared once, at push),
    //       so there is no match matrix anywhere in this backend (report
    //       5.10 items 1 and 4). Pairs with BANK_PICK only.
    //   0 = mc_xddr2_entry_store + mc_bank_head_records: the flat pool with
    //       the N x N age matrix (4 785 LUT at N = 8 in context, report 5.10).
    parameter int STORE_BACKEND  = 1,
    parameter int BANK_FIFO_DEPTH = 0,   // FIFO store queue depth per (direction, bank); 0 = NUM_ENTRIES (pool-only admission, the measured default)
    // LPDDR2 training plane (ZQ calibration, DQ calibration) built in. 1 =
    // the research default; a DDR2-only build sets 0 and the plane's generate
    // branches tie the LPDDR2 machinery off (231 LUT / 518 FF on the board,
    // mem-ctrl recovery Phase 3 report 5.10).
    parameter bit HAS_LPDDR2     = 1'b1,
    // Compile-time JEDEC timings (mem-ctrl recovery Phase 3 report 5.10,
    // item 3). 1 = the scheduler plane's timers compare against the T_*
    // constants below and the TIMINGS CSRs are ignored -- a one-part product
    // does not retune at runtime, and a comparator against a constant is a
    // fraction of one against a register. 0 = the CSR inputs (research
    // default; every TB programs its own set). The defaults are the Nexys A7
    // DDR2 part at the 75 MHz board clock, pumice_device.ddr2_timings_
    // mc_cycles(75e6) with the board read-path alignment (t_rddata_en 6,
    // rddata_delay 7, t_phy_wrlat 1); tRTW carries the PHY DQ-occupancy floor.
    parameter bit FIXED_TIMINGS  = 1'b0,
    parameter int T_RCD  = 2,   parameter int T_RP  = 2,  parameter int T_RAS = 4,
    parameter int T_RC   = 5,   parameter int T_WR  = 4,  parameter int T_RTP = 2,
    parameter int T_FAW  = 4,   parameter int T_RRD = 2,  parameter int T_WTR = 4,
    parameter int T_RTW  = 20,  parameter int T_CCD = 1,
    parameter int T_REFI = 585, parameter int T_RFC = 11,


    parameter int BYTE_OFFSET_WIDTH = $clog2(DRAM_DEVICE_WIDTH / 8),
    parameter int BL_SHIFT   = (DRAM_BEAT_WIDTH > DRAM_DEVICE_WIDTH)
                             ? $clog2(DRAM_BEAT_WIDTH / DRAM_DEVICE_WIDTH) : 0,
    parameter int BL_PUMICE  = DRAM_BL >> BL_SHIFT,

    parameter int BURST_WORDS = (BL_PUMICE >= DFI_RATE) ? (BL_PUMICE / DFI_RATE) : 1,
    parameter int N_SUBCMD    = (DFI_RATE > BL_PUMICE) ? (DFI_RATE / BL_PUMICE) : 1,
    parameter int SUB_COL_STRIDE = DRAM_BL,
    parameter int SUB_PHASE_STRIDE = (N_SUBCMD > 1) ? (DFI_RATE / N_SUBCMD) : 1,

    parameter int DFI_DATA_WIDTH = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DW  = DFI_DATA_WIDTH,
    parameter int SW  = DW / 8,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int AW  = AXI_ADDR_WIDTH,
    parameter int UW  = 1,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int PHW = (DFI_RATE > 1) ? $clog2(DFI_RATE) : 1,
    parameter int N_LU = NUM_BANKS,
    parameter int DFI_STRB_WIDTH = DW / 8,
    parameter int DFI_EN_WIDTH   = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int DFI_ADDR_BUS_W = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W = BKW * DFI_RATE,
    parameter int DFI_CTRL_BUS_W = 1 * DFI_RATE,
    parameter int DFI_CS_BUS_W   = NUM_RANKS * DFI_RATE
) (
    input  logic                       aclk,
    input  logic                       aresetn,
    input  logic                       dfi_clk,
    input  logic                       dfi_rstn,

    // ---- config (ports; CSR rebuild is a follow-up) ----
    input  memtype_e                   memtype_i,
    input  page_policy_e               page_policy_i,

    input  logic [2:0]                 page_mode_i,
    input  logic [7:0]                 page_tr_init_i,
    input  logic [1:0]                 sched_order_mode_i,
    input  logic [1:0]                 sched_row_sel_i,
    input  logic [1:0]                 sched_col_sel_i,
    input  logic [1:0]                 sched_access_pref_i,
    input  logic [7:0]                 sched_wr_high_wm_i,
    input  logic [7:0]                 sched_wr_batch_max_i,
    input  logic [7:0]                 sched_wr_low_wm_i,
    input  logic [1:0]                 sched_prio_sub_i,
    input  logic                       sched_qos_en_i,
    input  logic [7:0]                 sched_age_thresh_i,

    input  logic [4:0]                 bank_lsb_i,
    input  logic                       hash_en_i,
    input  logic [7:0]                 hash_seed_i,
    input  logic [7:0]                 t_rcd_i, t_rp_i, t_ras_i, t_rc_i, t_wr_i, t_rtp_i,
    input  logic [7:0]                 t_faw_i, t_rrd_i, t_wtr_i, t_rtw_i, t_ccd_i,
    input  logic [15:0]                t_refi_i,
    input  logic                       refi_reload_i,
    input  logic [15:0]                t_rfc_i,
    input  logic [3:0]                 refresh_burst_i,
    input  logic [15:0]                ref_trefi_pb_i,
    input  logic [7:0]                 ref_trfc_pb_i,
    input  logic [15:0]                t_init_wait_i, t_dll_wait_i,
    input  logic [7:0]                 t_mrd_wait_i, t_rp_wait_i, t_rfc_wait_i,
    input  logic [15:0]                mr0_i, mr1_i, mr2_i, mr3_i,
    input  logic [7:0]                 lp_mr1_op_i, lp_mr2_op_i, lp_mr3_op_i,
    input  logic                       init_restart_i,
    input  logic [PHW-1:0]             rd_phase_i, wr_phase_i,
    input  logic [7:0]                 t_phy_wrlat_i, t_rddata_en_i,
    input  logic [1:0]                 gear_i,
    input  logic [3:0]                 bl_i,
    output logic [3:0]                 cl_o, cwl_o, bl_o,
    output logic                       init_done_o,

    // ---- training plane controls / status ----
    input  logic                       zq_en_i,
    input  logic                       zq_defer_en_i,
    input  logic [31:0]                zq_interval_i,
    input  logic [15:0]                t_zqcs_i,
    input  logic [15:0]                t_zqcl_i,
    input  logic [12:0]                zq_overdue_max_i,
    input  logic                       cal_start_i,
    input  logic                       cal_abort_i,
    input  logic [15:0]                t_mrr_i,
    input  logic [15:0]                t_readout_i,
    output logic [DFI_DATA_WIDTH-1:0]  mrr32_data_o,
    output logic [DFI_DATA_WIDTH-1:0]  mrr40_data_o,
    output logic                       cal_busy_o,
    output logic                       cal_done_o,
    output logic                       cal_err_o,
    output logic                       zq_busy_o,
    output logic                       zq_overdue_o,
    output logic [15:0]                zqcs_total_o,

    // ---- host AXI4 ----
    input  logic [IW-1:0]  s_axi_awid,   input logic [AW-1:0] s_axi_awaddr,
    input  logic [7:0]     s_axi_awlen,  input logic [2:0]    s_axi_awsize,
    input  logic [1:0]     s_axi_awburst,input logic          s_axi_awlock,
    input  logic [3:0]     s_axi_awcache,input logic [2:0]    s_axi_awprot,
    input  logic [3:0]     s_axi_awqos,  input logic [3:0]    s_axi_awregion,
    input  logic [UW-1:0]  s_axi_awuser, input logic          s_axi_awvalid,
    output logic           s_axi_awready,
    input  logic [DW-1:0]  s_axi_wdata,  input logic [SW-1:0] s_axi_wstrb,
    input  logic           s_axi_wlast,  input logic [UW-1:0] s_axi_wuser,
    input  logic           s_axi_wvalid, output logic         s_axi_wready,
    output logic [IW-1:0]  s_axi_bid,    output logic [1:0]   s_axi_bresp,
    output logic [UW-1:0]  s_axi_buser,  output logic         s_axi_bvalid,
    input  logic           s_axi_bready,
    input  logic [IW-1:0]  s_axi_arid,   input logic [AW-1:0] s_axi_araddr,
    input  logic [7:0]     s_axi_arlen,  input logic [2:0]    s_axi_arsize,
    input  logic [1:0]     s_axi_arburst,input logic          s_axi_arlock,
    input  logic [3:0]     s_axi_arcache,input logic [2:0]    s_axi_arprot,
    input  logic [3:0]     s_axi_arqos,  input logic [3:0]    s_axi_arregion,
    input  logic [UW-1:0]  s_axi_aruser, input logic          s_axi_arvalid,
    output logic           s_axi_arready,
    output logic [IW-1:0]  s_axi_rid,    output logic [DW-1:0] s_axi_rdata,
    output logic [1:0]     s_axi_rresp,  output logic          s_axi_rlast,
    output logic [UW-1:0]  s_axi_ruser,  output logic          s_axi_rvalid,
    input  logic           s_axi_rready,

    // ---- DFI 2.1 pin bus ----
    output logic [DFI_ADDR_BUS_W-1:0]  dfi_address_o,
    output logic [DFI_BANK_BUS_W-1:0]  dfi_bank_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_cas_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_ras_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_we_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_cs_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_odt_o,
    output logic [DFI_DATA_WIDTH-1:0]  dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]  dfi_wrdata_mask_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]  dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0] dfi_rddata_valid_i,
    output logic                       dfi_init_start_o,
    input  logic                       dfi_init_complete_i
);

    localparam int PTRW = (NUM_ENTRIES > 1) ? $clog2(NUM_ENTRIES) : 1;
    localparam int CMD_DW = $bits(dram_op_e) + RKW + BKW + ROW_WIDTH + COL_WIDTH + 1 + 1;
    localparam int WD_DW  = 1 + DFI_STRB_WIDTH + DFI_DATA_WIDTH;
    localparam int RD_DW  = 1 + 2 + DFI_DATA_WIDTH;

    localparam int SUBW_MAX = $clog2(N_SUBCMD + 1);
    localparam int CMD_DELAY_EFF = (CMD_DELAY == 0) ? (5 + 2 * BURST_WORDS) : CMD_DELAY;

    // JEDEC timings as the scheduler plane sees them: the CSR inputs, or the
    // T_* constants under FIXED_TIMINGS. The CSR ports stay either way so the
    // top's wiring is identical; synthesis folds the constant comparators.
    logic [7:0]  w_t_rcd, w_t_rp, w_t_ras, w_t_rc, w_t_wr, w_t_rtp, w_t_faw;
    logic [7:0]  w_t_rrd, w_t_wtr, w_t_rtw, w_t_ccd_raw;
    logic [15:0] w_t_refi, w_t_rfc;
    assign w_t_rcd     = FIXED_TIMINGS ? 8'(T_RCD)   : t_rcd_i;
    assign w_t_rp      = FIXED_TIMINGS ? 8'(T_RP)    : t_rp_i;
    assign w_t_ras     = FIXED_TIMINGS ? 8'(T_RAS)   : t_ras_i;
    assign w_t_rc      = FIXED_TIMINGS ? 8'(T_RC)    : t_rc_i;
    assign w_t_wr      = FIXED_TIMINGS ? 8'(T_WR)    : t_wr_i;
    assign w_t_rtp     = FIXED_TIMINGS ? 8'(T_RTP)   : t_rtp_i;
    assign w_t_faw     = FIXED_TIMINGS ? 8'(T_FAW)   : t_faw_i;
    assign w_t_rrd     = FIXED_TIMINGS ? 8'(T_RRD)   : t_rrd_i;
    assign w_t_wtr     = FIXED_TIMINGS ? 8'(T_WTR)   : t_wtr_i;
    assign w_t_rtw     = FIXED_TIMINGS ? 8'(T_RTW)   : t_rtw_i;
    assign w_t_ccd_raw = FIXED_TIMINGS ? 8'(T_CCD)   : t_ccd_i;
    assign w_t_refi    = FIXED_TIMINGS ? 16'(T_REFI) : t_refi_i;
    assign w_t_rfc     = FIXED_TIMINGS ? 16'(T_RFC)  : t_rfc_i;

    logic [7:0] w_t_ccd_eff;
    assign w_t_ccd_eff = (w_t_ccd_raw < 8'(BURST_WORDS)) ? 8'(BURST_WORDS) : w_t_ccd_raw;

    logic [3:0]          w_bl_pumice;
    logic [4:0]          w_active_rate;
    logic [SUBW_MAX-1:0] w_n_subcmd;
    logic [COL_WIDTH-1:0] w_sub_col_stride;
    logic [PHW-1:0]      w_sub_phase_stride;
    always_comb begin
        w_bl_pumice   = bl_i >> BL_SHIFT;
        w_active_rate = 5'(1) << gear_i;
        if ((w_bl_pumice != '0) && (w_active_rate > 5'(w_bl_pumice)))
            w_n_subcmd = SUBW_MAX'(w_active_rate / 5'(w_bl_pumice));
        else
            w_n_subcmd = SUBW_MAX'(1);
        w_sub_col_stride = COL_WIDTH'(bl_i);
        w_sub_phase_stride = PHW'(w_bl_pumice);
    end

    // ---- scheduler <-> entry store per-entry vectors ----
    logic [NUM_ENTRIES-1:0]             w_wr_sch_v,     w_rd_sch_v;
    logic [NUM_ENTRIES*BKW-1:0]         w_wr_sch_bank,  w_rd_sch_bank;
    logic [NUM_ENTRIES*ROW_WIDTH-1:0]   w_wr_sch_row,   w_rd_sch_row;
    logic [NUM_ENTRIES*COL_WIDTH-1:0]   w_wr_sch_col,   w_rd_sch_col;
    logic [NUM_ENTRIES*NUM_ENTRIES-1:0] w_wr_sch_older, w_rd_sch_older;
    logic [NUM_ENTRIES-1:0]             w_wr_sch_agex,  w_rd_sch_agex;
    logic [NUM_ENTRIES*4-1:0]           w_wr_sch_qos,   w_rd_sch_qos;
    logic [15:0]                        w_wr_sch_hrel,  w_rd_sch_hrel;
    // per-bank head records (storage -> scheduler contract), derived from the
    // entry store's per-entry vectors and registered by mc_bank_head_records
    logic [NUM_ENTRIES-1:0]             w_wr_sch_pend;
    mc_head_rec_t [NUM_BANKS-1:0]       w_wr_head, w_wr_head2, w_rd_head, w_rd_head2;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0]                w_bank_row_active;
    logic [NUM_RANKS-1:0][NUM_BANKS-1:0][ROW_WIDTH-1:0] w_bank_open_row;
    logic                      w_wr_commit_v, w_wr_commit_rdy;
    logic w_wr_commit_rdy_now;
    logic [PTRW-1:0]           w_wr_commit_slot;
    logic                      w_rd_issue_v, w_rd_issue_rdy;
    logic [PTRW-1:0]           w_rd_issue_slot;

    // ---- entry store wr commit-data -> DFI wrdata ----
    logic                      w_cm_v, w_cm_rdy, w_cm_last;
    logic [DW-1:0]             w_cm_data;
    logic [SW-1:0]             w_cm_strb;

    // ---- DFI rddata -> AXI4 return ring ----
    logic                      w_ret_v, w_ret_rdy, w_ret_last;
    logic [DW-1:0]             w_ret_data;
    logic [1:0]                w_ret_resp;
    logic                      w_rd_ret_busy;

    // ---- scheduler cmd stream -> DFI cmd ----
    logic                      w_cmd_v, w_cmd_rdy;
    dram_op_e                  w_cmd_op;
    logic [RKW-1:0]            w_cmd_rank;
    logic [BKW-1:0]            w_cmd_bank;
    logic [ROW_WIDTH-1:0]      w_cmd_row;
    logic [COL_WIDTH-1:0]      w_cmd_col;
    logic                      w_cmd_ap, w_cmd_mrr;
    logic [CMD_DW-1:0]         w_cmd_data;
    assign w_cmd_data = {w_cmd_mrr, w_cmd_ap, w_cmd_col, w_cmd_row, w_cmd_bank, w_cmd_rank, w_cmd_op};

    // ---- scheduler <-> training plane ----
    logic                      w_trn_req, w_trn_grant;
    dram_op_e                  w_trn_op;
    logic [BKW-1:0]            w_trn_bank;
    logic [ROW_WIDTH-1:0]      w_trn_row;
    logic                      w_trn_mrr;
    logic                      w_cal_busy;

    // ---- DFI plane <-> training plane calibration sideband ----
    logic                      w_cal_expect;
    logic [DFI_DATA_WIDTH-1:0] w_cal_data;
    logic                      w_cal_valid;

    // ---- init handshake init plane <-> DFI ----
    logic                      w_init_start, w_init_complete;

    // ---- init plane -> scheduler plane init command injection ----
    logic                      w_init_cmd_v;
    dram_op_e                  w_init_cmd_op;
    logic [BKW-1:0]            w_init_cmd_bank;
    logic [ROW_WIDTH-1:0]      w_init_cmd_row;

    // ---- AXI4 plane <-> entry store inter-plane nets ----
    logic                aw_push_valid, aw_push_ready;
    logic [BKW-1:0]      aw_push_bank;  logic [ROW_WIDTH-1:0] aw_push_row;
    logic [COL_WIDTH-1:0] aw_push_col;  logic [IW-1:0]        aw_push_id;
    logic                aw_push_agg,   aw_push_last;
    logic                wd_valid, wd_ready, wd_last;
    logic [DW-1:0]       wd_data;       logic [SW-1:0]        wd_strb;
    logic                wr_done_valid; logic [IW-1:0]        wr_done_id;

    logic                snarf_probe_valid;
    logic [BKW-1:0]      snarf_bank;    logic [ROW_WIDTH-1:0] snarf_row;
    logic [COL_WIDTH-1:0] snarf_col;
    logic [IW-1:0]       snarf_id;      logic [7:0]           snarf_len;
    logic                snarf_hit,     snarf_accept;
    logic                snarf_rd_valid, snarf_rd_ready, snarf_rd_last;
    logic [DW-1:0]       snarf_rd_data;
    logic                ar_push_valid, ar_push_ready;
    logic                rt_alloc_ready, rd_cam_ins_ready;
    logic [$clog2(RD_RET_DEPTH)-1:0] rt_alloc_ticket, rd_iss_ticket;
    logic                rd_iss_valid, rd_iss_ready;
    logic [BKW-1:0]      ar_push_bank;  logic [ROW_WIDTH-1:0] ar_push_row;
    logic [COL_WIDTH-1:0] ar_push_col;  logic [IW-1:0]        ar_push_id;
    logic [3:0]          ar_push_qos;   logic [3:0]           aw_push_qos;

    // ======================================================================
    // Plane 1: AXI4 interface
    // ======================================================================
    mc_axi4_plane #(
        .AXI_ID_WIDTH  (IW),
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW),
        .AXI_USER_WIDTH(UW),
        .DRAM_BEAT_WIDTH  (DW),
        .NUM_RANKS        (NUM_RANKS),
        .NUM_BANKS        (NUM_BANKS),
        .ROW_WIDTH        (ROW_WIDTH),
        .COL_WIDTH        (COL_WIDTH),
        .BYTE_OFFSET_WIDTH(BYTE_OFFSET_WIDTH),
        .AXI_BEATS_PER_BURST   (BURST_WORDS),
        .NUM_ENTRIES      (NUM_ENTRIES),
        .N_SRAM_SLOTS     (NUM_ENTRIES),
        .RD_RET_DEPTH     (RD_RET_DEPTH),
        .N_SCHED_LU       (N_LU),
        .AGE_WIDTH        (AGE_WIDTH)
    ) u_axi_plane (
        .aclk          (aclk),
        .aresetn       (aresetn),
        .bank_lsb_i    (bank_lsb_i),
        .hash_en_i     (hash_en_i),
        .hash_seed_i   (hash_seed_i),
        .s_axi_awid    (s_axi_awid),
        .s_axi_awaddr  (s_axi_awaddr),
        .s_axi_awlen   (s_axi_awlen),
        .s_axi_awsize  (s_axi_awsize),
        .s_axi_awburst (s_axi_awburst),
        .s_axi_awlock  (s_axi_awlock),
        .s_axi_awcache (s_axi_awcache),
        .s_axi_awprot  (s_axi_awprot),
        .s_axi_awqos   (s_axi_awqos),
        .s_axi_awregion(s_axi_awregion),
        .s_axi_awuser  (s_axi_awuser),
        .s_axi_awvalid (s_axi_awvalid),
        .s_axi_awready (s_axi_awready),
        .s_axi_wdata   (s_axi_wdata),
        .s_axi_wstrb   (s_axi_wstrb),
        .s_axi_wlast   (s_axi_wlast),
        .s_axi_wuser   (s_axi_wuser),
        .s_axi_wvalid  (s_axi_wvalid),
        .s_axi_wready  (s_axi_wready),
        .s_axi_bid     (s_axi_bid),
        .s_axi_bresp   (s_axi_bresp),
        .s_axi_buser   (s_axi_buser),
        .s_axi_bvalid  (s_axi_bvalid),
        .s_axi_bready  (s_axi_bready),
        .s_axi_arid    (s_axi_arid),
        .s_axi_araddr  (s_axi_araddr),
        .s_axi_arlen   (s_axi_arlen),
        .s_axi_arsize  (s_axi_arsize),
        .s_axi_arburst (s_axi_arburst),
        .s_axi_arlock  (s_axi_arlock),
        .s_axi_arcache (s_axi_arcache),
        .s_axi_arprot  (s_axi_arprot),
        .s_axi_arqos   (s_axi_arqos),
        .s_axi_arregion(s_axi_arregion),
        .s_axi_aruser  (s_axi_aruser),
        .s_axi_arvalid (s_axi_arvalid),
        .s_axi_arready (s_axi_arready),
        .s_axi_rid     (s_axi_rid),
        .s_axi_rdata   (s_axi_rdata),
        .s_axi_rresp   (s_axi_rresp),
        .s_axi_rlast   (s_axi_rlast),
        .s_axi_ruser   (s_axi_ruser),
        .s_axi_rvalid  (s_axi_rvalid),
        .s_axi_rready  (s_axi_rready),
        .aw_push_valid_o    (aw_push_valid),
        .aw_push_ready_i    (aw_push_ready),
        .aw_push_bank_o     (aw_push_bank),
        .aw_push_row_o      (aw_push_row),
        .aw_push_col_o      (aw_push_col),
        .aw_push_id_o       (aw_push_id),
        .aw_push_qos_o      (aw_push_qos),
        .aw_push_agg_o      (aw_push_agg),
        .aw_push_last_o     (aw_push_last),
        .wd_valid_o         (wd_valid),
        .wd_ready_i         (wd_ready),
        .wd_data_o          (wd_data),
        .wd_strb_o          (wd_strb),
        .wd_last_o          (wd_last),
        .wr_done_valid_i    (wr_done_valid),
        .wr_done_id_i       (wr_done_id),
        .snarf_probe_valid_o(snarf_probe_valid),
        .snarf_probe_bank_o (snarf_bank),
        .snarf_probe_row_o  (snarf_row),
        .snarf_probe_col_o  (snarf_col),
        .snarf_probe_id_o   (snarf_id),
        .snarf_probe_len_o  (snarf_len),
        .snarf_hit_i        (snarf_hit),
        .snarf_accept_o     (snarf_accept),
        .snarf_rd_valid_i   (snarf_rd_valid),
        .snarf_rd_ready_o   (snarf_rd_ready),
        .snarf_rd_data_i    (snarf_rd_data),
        .snarf_rd_last_i    (snarf_rd_last),
        .ar_push_valid_o    (ar_push_valid),
        .ar_push_ready_i    (ar_push_ready),
        .ar_push_bank_o     (ar_push_bank),
        .ar_push_row_o      (ar_push_row),
        .ar_push_col_o      (ar_push_col),
        .ar_push_id_o       (ar_push_id),
        .ar_push_qos_o      (ar_push_qos),
        .rt_alloc_ready_o   (rt_alloc_ready),
        .rt_alloc_ticket_o  (rt_alloc_ticket),
        .rd_iss_ready_o     (rd_iss_ready),
        .rd_iss_valid_i     (rd_iss_valid),
        .rd_iss_ticket_i    (rd_iss_ticket),
        .rd_cam_ins_ready_i (rd_cam_ins_ready),
        .rd_dfi_ret_valid_i (w_ret_v),
        .rd_dfi_ret_ready_o (w_ret_rdy),
        .rd_dfi_ret_data_i  (w_ret_data),
        .rd_dfi_ret_resp_i  (w_ret_resp),
        .rd_dfi_ret_last_i  (w_ret_last),
        .busy_o             ()
    );

    // ======================================================================
    // Plane 1b: storage backend. STORE_BACKEND selects the per-bank FIFO store
    // (default) or the entry store + records; both present the plane contract.
    // ======================================================================
    generate if (STORE_BACKEND != 0) begin : g_fifo_store
        if (SCHED_CORE != mc_common_pkg::MC_SCHED_BANK_PICK) begin : g_bad_core
            $error("granite_core: STORE_BACKEND=1 (mc_bank_fifo_store) produces head records only -- SCHED_CORE must be BANK_PICK");
        end
        mc_bank_fifo_store #(
            .NUM_ENTRIES        (NUM_ENTRIES),
            .BANK_FIFO_DEPTH    (BANK_FIFO_DEPTH),
            .AXI_ID_WIDTH       (IW),
            .AXI_DATA_WIDTH     (DW),
            .NUM_RANKS          (NUM_RANKS),
            .NUM_BANKS          (NUM_BANKS),
            .ROW_WIDTH          (ROW_WIDTH),
            .COL_WIDTH          (COL_WIDTH),
            .AXI_BEATS_PER_BURST(BURST_WORDS),
            .RD_RET_DEPTH       (RD_RET_DEPTH),
            .WR_DATA_BUF_WORDS  (GRANITE_WR_DATA_BUF_WORDS)
        ) u_fifo_store (
            .aclk               (aclk),
            .aresetn            (aresetn),
            .aw_push_valid_i    (aw_push_valid),
            .aw_push_ready_o    (aw_push_ready),
            .aw_push_bank_i     (aw_push_bank),
            .aw_push_row_i      (aw_push_row),
            .aw_push_col_i      (aw_push_col),
            .aw_push_id_i       (aw_push_id),
            .aw_push_qos_i      (aw_push_qos),
            .aw_push_agg_i      (aw_push_agg),
            .aw_push_last_i     (aw_push_last),
            .wd_valid_i         (wd_valid),
            .wd_ready_o         (wd_ready),
            .wd_data_i          (wd_data),
            .wd_strb_i          (wd_strb),
            .wd_last_i          (wd_last),
            .wr_done_valid_o    (wr_done_valid),
            .wr_done_id_o       (wr_done_id),
            .snarf_probe_valid_i(snarf_probe_valid),
            .snarf_probe_bank_i (snarf_bank),
            .snarf_probe_row_i  (snarf_row),
            .snarf_probe_col_i  (snarf_col),
            .snarf_probe_id_i   (snarf_id),
            .snarf_probe_len_i  (snarf_len),
            .snarf_hit_o        (snarf_hit),
            .snarf_accept_i     (snarf_accept),
            .snarf_rd_valid_o   (snarf_rd_valid),
            .snarf_rd_ready_i   (snarf_rd_ready),
            .snarf_rd_data_o    (snarf_rd_data),
            .snarf_rd_last_o    (snarf_rd_last),
            .ar_push_valid_i    (ar_push_valid),
            .ar_push_ready_o    (ar_push_ready),
            .ar_push_bank_i     (ar_push_bank),
            .ar_push_row_i      (ar_push_row),
            .ar_push_col_i      (ar_push_col),
            .ar_push_id_i       (ar_push_id),
            .ar_push_qos_i      (ar_push_qos),
            .rt_alloc_ready_i   (rt_alloc_ready),
            .rt_alloc_ticket_i  (rt_alloc_ticket),
            .rd_iss_ready_i     (rd_iss_ready),
            .rd_iss_valid_o     (rd_iss_valid),
            .rd_iss_ticket_o    (rd_iss_ticket),
            .rd_cam_ins_ready_o (rd_cam_ins_ready),
            .sched_age_thresh_i (sched_age_thresh_i),
            .wr_commit_valid_i  (w_wr_commit_v),
            .wr_commit_ready_o  (w_wr_commit_rdy),
            .wr_commit_ready_now_o (w_wr_commit_rdy_now),
            .wr_commit_slot_i   (w_wr_commit_slot),
            .rd_issue_valid_i   (w_rd_issue_v),
            .rd_issue_ready_o   (w_rd_issue_rdy),
            .rd_issue_slot_i    (w_rd_issue_slot),
            .bank_row_active_i  (w_bank_row_active[0]),
            .bank_open_row_i    (w_bank_open_row[0]),
            .wr_head_o          (w_wr_head),
            .wr_head2_o         (w_wr_head2),
            .rd_head_o          (w_rd_head),
            .rd_head2_o         (w_rd_head2),
            .wr_cm_rd_valid_o   (w_cm_v),
            .wr_cm_rd_ready_i   (w_cm_rdy),
            .wr_cm_rd_data_o    (w_cm_data),
            .wr_cm_rd_strb_o    (w_cm_strb),
            .wr_cm_rd_last_o    (w_cm_last),
            .busy_o             ()
        );
        // The FR-FCFS core's N-wide vectors do not exist on this backend; the
        // scheduler plane's BANK_PICK branch sinks them.
        assign w_wr_sch_v     = '0;
        assign w_wr_sch_pend  = '0;
        assign w_wr_sch_bank  = '0;
        assign w_wr_sch_row   = '0;
        assign w_wr_sch_col   = '0;
        assign w_wr_sch_older = '0;
        assign w_wr_sch_agex  = '0;
        assign w_wr_sch_qos   = '0;
        assign w_wr_sch_hrel  = '0;
        assign w_rd_sch_v     = '0;
        assign w_rd_sch_bank  = '0;
        assign w_rd_sch_row   = '0;
        assign w_rd_sch_col   = '0;
        assign w_rd_sch_older = '0;
        assign w_rd_sch_agex  = '0;
        assign w_rd_sch_qos   = '0;
        assign w_rd_sch_hrel  = '0;
    end else begin : g_entry_store
        // ======================================================================
        // Plane 1b: storage-lite entry store (N=1 in-order seam)
        // ======================================================================
        mc_xddr2_entry_store #(
            .NUM_ENTRIES        (NUM_ENTRIES),
            .AXI_ID_WIDTH       (IW),
            .AXI_DATA_WIDTH     (DW),
            .NUM_RANKS          (NUM_RANKS),
            .NUM_BANKS          (NUM_BANKS),
            .ROW_WIDTH          (ROW_WIDTH),
            .COL_WIDTH          (COL_WIDTH),
            .AXI_BEATS_PER_BURST(BURST_WORDS),
            .RD_RET_DEPTH       (RD_RET_DEPTH),
            .WR_DATA_BUF_WORDS  (GRANITE_WR_DATA_BUF_WORDS)
        ) u_entry_store (
            .aclk               (aclk),
            .aresetn            (aresetn),
            .aw_push_valid_i    (aw_push_valid),
            .aw_push_ready_o    (aw_push_ready),
            .aw_push_bank_i     (aw_push_bank),
            .aw_push_row_i      (aw_push_row),
            .aw_push_col_i      (aw_push_col),
            .aw_push_id_i       (aw_push_id),
            .aw_push_qos_i      (aw_push_qos),
            .aw_push_agg_i      (aw_push_agg),
            .aw_push_last_i     (aw_push_last),
            .wd_valid_i         (wd_valid),
            .wd_ready_o         (wd_ready),
            .wd_data_i          (wd_data),
            .wd_strb_i          (wd_strb),
            .wd_last_i          (wd_last),
            .wr_done_valid_o    (wr_done_valid),
            .wr_done_id_o       (wr_done_id),
            .snarf_probe_valid_i(snarf_probe_valid),
            .snarf_probe_bank_i (snarf_bank),
            .snarf_probe_row_i  (snarf_row),
            .snarf_probe_col_i  (snarf_col),
            .snarf_probe_id_i   (snarf_id),
            .snarf_probe_len_i  (snarf_len),
            .snarf_hit_o        (snarf_hit),
            .snarf_accept_i     (snarf_accept),
            .snarf_rd_valid_o   (snarf_rd_valid),
            .snarf_rd_ready_i   (snarf_rd_ready),
            .snarf_rd_data_o    (snarf_rd_data),
            .snarf_rd_last_o    (snarf_rd_last),
            .ar_push_valid_i    (ar_push_valid),
            .ar_push_ready_o    (ar_push_ready),
            .ar_push_bank_i     (ar_push_bank),
            .ar_push_row_i      (ar_push_row),
            .ar_push_col_i      (ar_push_col),
            .ar_push_id_i       (ar_push_id),
            .ar_push_qos_i      (ar_push_qos),
            .rt_alloc_ready_i   (rt_alloc_ready),
            .rt_alloc_ticket_i  (rt_alloc_ticket),
            .rd_iss_ready_i     (rd_iss_ready),
            .rd_iss_valid_o     (rd_iss_valid),
            .rd_iss_ticket_o    (rd_iss_ticket),
            .rd_cam_ins_ready_o (rd_cam_ins_ready),
            .sched_age_thresh_i (sched_age_thresh_i),
            .wr_commit_valid_i  (w_wr_commit_v),
            .wr_commit_ready_o  (w_wr_commit_rdy),
            .wr_commit_ready_now_o  (w_wr_commit_rdy_now),
            .wr_commit_slot_i   (w_wr_commit_slot),
            .rd_issue_valid_i   (w_rd_issue_v),
            .rd_issue_ready_o   (w_rd_issue_rdy),
            .rd_issue_slot_i    (w_rd_issue_slot),
            .wr_sch_valid_o     (w_wr_sch_v),
            .wr_sch_pend_o      (w_wr_sch_pend),
            .wr_sch_bank_o      (w_wr_sch_bank),
            .wr_sch_row_o       (w_wr_sch_row),
            .wr_sch_col_o       (w_wr_sch_col),
            .wr_sch_older_o     (w_wr_sch_older),
            .wr_sch_age_exceed_o(w_wr_sch_agex),
            .wr_sch_qos_o       (w_wr_sch_qos),
            .wr_sch_head_rel_o  (w_wr_sch_hrel),
            .rd_sch_valid_o     (w_rd_sch_v),
            .rd_sch_bank_o      (w_rd_sch_bank),
            .rd_sch_row_o       (w_rd_sch_row),
            .rd_sch_col_o       (w_rd_sch_col),
            .rd_sch_older_o     (w_rd_sch_older),
            .rd_sch_age_exceed_o(w_rd_sch_agex),
            .rd_sch_qos_o       (w_rd_sch_qos),
            .rd_sch_head_rel_o  (w_rd_sch_hrel),
            .wr_cm_rd_valid_o   (w_cm_v),
            .wr_cm_rd_ready_i   (w_cm_rdy),
            .wr_cm_rd_data_o    (w_cm_data),
            .wr_cm_rd_strb_o    (w_cm_strb),
            .wr_cm_rd_last_o    (w_cm_last),
            .busy_o             ()
        );

        // ---- per-bank head records, registered at the storage edge ----
        mc_bank_head_records #(
            .NUM_ENTRIES (NUM_ENTRIES),
            .NUM_BANKS   (NUM_BANKS),
            .ROW_WIDTH   (ROW_WIDTH),
            .COL_WIDTH   (COL_WIDTH)
        ) u_wr_heads (
            .clk              (aclk),
            .rst_n            (aresetn),
            .bank_row_active_i(w_bank_row_active[0]),
            .bank_open_row_i  (w_bank_open_row[0]),
            .sch_valid_i      (w_wr_sch_v),
            .sch_pend_i       (w_wr_sch_pend),
            .sch_bank_i       (w_wr_sch_bank),
            .sch_row_i        (w_wr_sch_row),
            .sch_col_i        (w_wr_sch_col),
            .sch_older_i      (w_wr_sch_older),
            .sch_age_exceed_i (w_wr_sch_agex),
            .head_o           (w_wr_head),
            .head2_o          (w_wr_head2)
        );

        mc_bank_head_records #(
            .NUM_ENTRIES (NUM_ENTRIES),
            .NUM_BANKS   (NUM_BANKS),
            .ROW_WIDTH   (ROW_WIDTH),
            .COL_WIDTH   (COL_WIDTH)
        ) u_rd_heads (
            .clk              (aclk),
            .rst_n            (aresetn),
            .bank_row_active_i(w_bank_row_active[0]),
            .bank_open_row_i  (w_bank_open_row[0]),
            .sch_valid_i      (w_rd_sch_v),
            .sch_pend_i       ('0),
            .sch_bank_i       (w_rd_sch_bank),
            .sch_row_i        (w_rd_sch_row),
            .sch_col_i        (w_rd_sch_col),
            .sch_older_i      (w_rd_sch_older),
            .sch_age_exceed_i (w_rd_sch_agex),
            .head_o           (w_rd_head),
            .head2_o          (w_rd_head2)
        );
    end endgenerate

    // ======================================================================
    // Plane 2a: init plane (JEDEC sequencing + MR shadow + PHY handshake)
    // ======================================================================
    mc_init_plane #(
        .NUM_RANKS (NUM_RANKS),
        .NUM_BANKS (NUM_BANKS),
        .ROW_WIDTH (ROW_WIDTH)
    ) u_init_plane (
        .mc_clk             (aclk),
        .mc_rst_n           (aresetn),
        .memtype_i          (memtype_i),
        .t_init_wait_i      (t_init_wait_i),
        .t_dll_wait_i       (t_dll_wait_i),
        .t_mrd_wait_i       (t_mrd_wait_i),
        .t_rp_wait_i        (t_rp_wait_i),
        .t_rfc_wait_i       (t_rfc_wait_i),
        .mr0_i              (mr0_i),
        .mr1_i              (mr1_i),
        .mr2_i              (mr2_i),
        .mr3_i              (mr3_i),
        .lp_mr1_op_i        (lp_mr1_op_i),
        .lp_mr2_op_i        (lp_mr2_op_i),
        .lp_mr3_op_i        (lp_mr3_op_i),
        .init_restart_i     (init_restart_i),
        .dfi_init_start_o   (w_init_start),
        .dfi_init_complete_i(w_init_complete),
        .init_cmd_valid_o   (w_init_cmd_v),
        .init_cmd_op_o      (w_init_cmd_op),
        .init_cmd_bank_o    (w_init_cmd_bank),
        .init_cmd_row_o     (w_init_cmd_row),
        .init_busy_o        (),
        .init_done_o        (init_done_o),
        .init_state_o       (),
        .cl_o               (cl_o),
        .cwl_o              (cwl_o),
        .bl_o               (bl_o)
    );

    // ======================================================================
    // Plane 2: command scheduler (external-init mode; init lives in u_init_plane)
    // ======================================================================
    mc_scheduler_plane #(
        .NUM_RANKS     (NUM_RANKS),
        .NUM_BANKS     (NUM_BANKS),
        .ROW_WIDTH     (ROW_WIDTH),
        .COL_WIDTH     (COL_WIDTH),
        .AXI_ID_WIDTH  (IW),
        .NUM_ENTRIES   (NUM_ENTRIES),
        .AGE_WIDTH     (AGE_WIDTH),
        .CMD_DELAY     (CMD_DELAY_EFF),
        .HAS_ZQ        (1'b0),
        // Init is owned by u_init_plane; the scheduler plane takes its
        // external-init mode (the same mode scoria's wrapper uses).
        .HAS_INIT_SEQUENCER(1'b0),
        .HAS_MODE_REGISTER (1'b0),
        .MAINT_EXTRA_WIDTH(1),
        .CLOSE_ON_DRAIN(1'b1),
        .SCHED_CORE    (SCHED_CORE),
        .HAS_CMD_HISTORY(1'b0),
        .REF_HAS_POSTPONE(1'b0),
        .REF_HAS_PULLIN  (1'b0),
        .REF_HAS_REFPB   (1'b0),
        .REF_HAS_DRAIN_BURST(1'b0)
    ) u_sched_plane (
        .aclk               (aclk),
        .aresetn            (aresetn),
        .page_policy_i      (page_policy_i),
        .memtype_i          (memtype_i),
        .page_mode_i        (page_mode_i),
        .page_tr_init_i     (page_tr_init_i),
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
        .t_rcd_i            (w_t_rcd),
        .t_rp_i             (w_t_rp),
        .t_ras_i            (w_t_ras),
        .t_rc_i             (w_t_rc),
        .t_wr_i             (w_t_wr),
        .t_rtp_i            (w_t_rtp),
        .t_faw_i            (w_t_faw),
        .t_rrd_i            (w_t_rrd),
        .t_wtr_i            (w_t_wtr),
        .t_rtw_i            (w_t_rtw),
        .t_ccd_i            (w_t_ccd_eff),
        .t_ccd_l_i          (8'd0),
        .t_ccd_s_i          (8'd0),
        .t_rrd_l_i          (8'd0),
        .t_rrd_s_i          (8'd0),
        .t_refi_i           (w_t_refi),
        .refi_reload_i      (refi_reload_i),
        .t_rfc_i            (w_t_rfc),
        .refresh_burst_i    (refresh_burst_i),
        .ref_postpone_i     (4'd0),
        .ref_pullin_i       (4'd0),
        .ref_mode_i         (2'd0),
        .ref_trefi_pb_i     (ref_trefi_pb_i),
        .ref_trfc_pb_i      (ref_trfc_pb_i),
        .t_init_wait_i      (t_init_wait_i),
        .t_dll_wait_i       (t_dll_wait_i),
        .t_mrd_wait_i       (t_mrd_wait_i),
        .t_rp_wait_i        (t_rp_wait_i),
        .t_rfc_wait_i       (t_rfc_wait_i),
        .mr0_i              (mr0_i),
        .mr1_i              (mr1_i),
        .mr2_i              (mr2_i),
        .mr3_i              (mr3_i),
        .init_restart_i     (init_restart_i),
        .dfi_init_start_o   (),
        .dfi_init_complete_i(1'b0),
        .init_done_o        (),
        .cl_o               (),
        .cwl_o              (),
        .bl_o               (),
        .refresh_grant_o    (),
        .init_done_i        (init_done_o),
        .init_cmd_valid_i   (w_init_cmd_v),
        .init_cmd_op_i      (w_init_cmd_op),
        .init_cmd_bank_i    (w_init_cmd_bank),
        .init_cmd_row_i     (w_init_cmd_row),
        .refresh_req_i      (1'b0),
        .refresh_drain_i    (1'b0),
        .refresh_kind_i     (1'b0),
        .refresh_bank_i     ('0),
        .ap_mode_en_i       (1'b0),
        .ap_close_i         ('0),
        .timeout_pre_req_i  (1'b0),
        .timeout_pre_bank_i ('0),
        .wr_sch_valid_i     (w_wr_sch_v),
        .wr_sch_bank_i      (w_wr_sch_bank),
        .wr_sch_row_i       (w_wr_sch_row),
        .wr_sch_col_i       (w_wr_sch_col),
        .wr_sch_older_i     (w_wr_sch_older),
        .wr_sch_pend_i      (w_wr_sch_pend),
        .rd_sch_pend_i      ('0),
        .wr_sch_age_exceed_i(w_wr_sch_agex),
        .wr_sch_qos_i       (w_wr_sch_qos),
        .wr_sch_head_rel_i  (w_wr_sch_hrel),
        .wr_head_i          (w_wr_head),
        .wr_head2_i         (w_wr_head2),
        .wr_commit_ready_i  (w_wr_commit_rdy),
        .wr_commit_ready_now_i  (w_wr_commit_rdy_now),
        .wr_commit_valid_o  (w_wr_commit_v),
        .wr_commit_slot_o   (w_wr_commit_slot),
        .rd_sch_valid_i     (w_rd_sch_v),
        .rd_sch_bank_i      (w_rd_sch_bank),
        .rd_sch_row_i       (w_rd_sch_row),
        .rd_sch_col_i       (w_rd_sch_col),
        .rd_sch_older_i     (w_rd_sch_older),
        .rd_sch_age_exceed_i(w_rd_sch_agex),
        .rd_sch_qos_i       (w_rd_sch_qos),
        .rd_sch_head_rel_i  (w_rd_sch_hrel),
        .rd_head_i          (w_rd_head),
        .rd_head2_i         (w_rd_head2),
        .rd_issue_ready_i   (w_rd_issue_rdy),
        .rd_issue_valid_o   (w_rd_issue_v),
        .rd_issue_slot_o    (w_rd_issue_slot),
        .rd_ret_busy_i      (w_rd_ret_busy),
        .sched_order_mode_i (sched_order_mode_i),
        .sched_row_sel_i    (sched_row_sel_i),
        .sched_col_sel_i    (sched_col_sel_i),
        .sched_access_pref_i(sched_access_pref_i),
        .sched_wr_high_wm_i (sched_wr_high_wm_i),
        .sched_wr_batch_max_i(sched_wr_batch_max_i),
        .sched_wr_low_wm_i  (sched_wr_low_wm_i),
        .sched_prio_sub_i   (sched_prio_sub_i),
        .sched_qos_en_i     (sched_qos_en_i),
        .cmd_valid_o        (w_cmd_v),
        .cmd_ready_i        (w_cmd_rdy),
        .cmd_op_o           (w_cmd_op),
        .cmd_rank_o         (w_cmd_rank),
        .cmd_bank_o         (w_cmd_bank),
        .cmd_row_o          (w_cmd_row),
        .cmd_col_o          (w_cmd_col),
        .cmd_ap_o           (w_cmd_ap),
        .cmd_extra_o        (w_cmd_mrr),
        .maint_req_i        (w_trn_req),
        .maint_grant_o      (w_trn_grant),
        .maint_op_i         (w_trn_op),
        .maint_bank_i       (w_trn_bank),
        .maint_row_i        (w_trn_row),
        .maint_col_i        ('0),
        .maint_extra_i      (w_trn_mrr),
        .maint_busy_i       (w_cal_busy),
        .bank_row_active_o  (w_bank_row_active),
        .bank_open_row_o    (w_bank_open_row),
        .busy_o             (),
        .cmd_accept_o       (),
        .cmd_accept_op_o    (),
        .cmd_bg_o           (),
        .zq_req_i           (1'b0),
        .zq_grant_o         (),
        .t_zqcs_i           (16'd0)
    );

    // ======================================================================
    // Plane 2b: training plane (LPDDR2 ZQ + DQ cal)
    // ======================================================================
    mc_training_plane #(
        .NUM_SLOTS      (2),
        .BKW            (BKW),
        .ROW_WIDTH      (ROW_WIDTH),
        .EXTRA_WIDTH    (1),
        .CAL_DATA_WIDTH (DFI_DATA_WIDTH),
        .HAS_LP_ZQ      (HAS_LPDDR2),
        .HAS_LP_DQ_CAL  (HAS_LPDDR2)
    ) u_train_plane (
        .mc_clk          (aclk),
        .mc_rst_n        (aresetn),
        .init_done_i     (init_done_o),
        .memtype_i       (memtype_i),
        .zq_en_i         (zq_en_i),
        .zq_defer_en_i   (zq_defer_en_i),
        .zq_interval_i   (zq_interval_i),
        .t_zqcs_i        (t_zqcs_i),
        .t_zqcl_i        (t_zqcl_i),
        .zq_overdue_max_i(zq_overdue_max_i),
        .cal_start_i     (cal_start_i),
        .cal_abort_i     (cal_abort_i),
        .t_mrr_i         (t_mrr_i),
        .t_readout_i     (t_readout_i),
        .trn_cmd_req_o   (w_trn_req),
        .trn_cmd_grant_i (w_trn_grant),
        .trn_cmd_op_o    (w_trn_op),
        .trn_cmd_bank_o  (w_trn_bank),
        .trn_cmd_row_o   (w_trn_row),
        .trn_cmd_mrr_o   (w_trn_mrr),
        .dfi_clk         (dfi_clk),
        .dfi_rstn        (dfi_rstn),
        .cal_expect_o    (w_cal_expect),
        .cal_data_i      (w_cal_data),
        .cal_valid_i     (w_cal_valid),
        .cal_busy_o      (w_cal_busy),
        .cal_done_o      (cal_done_o),
        .cal_err_o       (cal_err_o),
        .mrr32_data_o    (mrr32_data_o),
        .mrr40_data_o    (mrr40_data_o),
        .zq_busy_o       (zq_busy_o),
        .zq_overdue_o    (zq_overdue_o),
        .zqcs_total_o    (zqcs_total_o)
    );

    // ======================================================================
    // Plane 3: DFI plane
    // ======================================================================
    mc_dfi_2p1_plane #(
        .NUM_RANKS       (NUM_RANKS),
        .NUM_BANKS       (NUM_BANKS),
        .ROW_WIDTH       (ROW_WIDTH),
        .COL_WIDTH       (COL_WIDTH),
        .DFI_RATE        (DFI_RATE),
        .DRAM_BEAT_WIDTH (DRAM_BEAT_WIDTH),
        .DFI_BEATS_PER_BURST  (BL_PUMICE),
        .N_SUBCMD        (N_SUBCMD),
        .SUB_COL_STRIDE  (SUB_COL_STRIDE),
        .SUB_PHASE_STRIDE(SUB_PHASE_STRIDE),
        .SUBW_MAX        (SUBW_MAX),
        .BURST_WORDS     (BURST_WORDS),
        .RD_MAX_OUTSTANDING(RD_RET_DEPTH),
        .RD_FIFO_DEPTH   (RD_RET_DEPTH * BURST_WORDS),
        .WD_FIFO_DEPTH   (32),
        .CMD_HISTORY_EN  (0),
        .HIST_T_RFC      (0),
        .HIST_T_RTW      (0),
        .HIST_T_WTR      (0)
    ) u_dfi_plane (
        .ctl_clk            (aclk),
        .ctl_rstn           (aresetn),
        .cmd_valid_i        (w_cmd_v),
        .cmd_ready_o        (w_cmd_rdy),
        .cmd_data_i         (w_cmd_data),
        .wd_valid_i         (w_cm_v),
        .wd_ready_o         (w_cm_rdy),
        .wd_data_i          ({w_cm_last, w_cm_strb, w_cm_data}),
        .rd_valid_o         (w_ret_v),
        .rd_ready_i         (w_ret_rdy),
        .rd_data_o          ({w_ret_last, w_ret_resp, w_ret_data}),
        .rd_ret_busy_o      (w_rd_ret_busy),
        .init_start_i       (w_init_start),
        .init_complete_o    (w_init_complete),
        .dfi_clk            (dfi_clk),
        .dfi_rstn           (dfi_rstn),
        .memtype_i          (memtype_i),
        .rd_phase_i         (rd_phase_i),
        .wr_phase_i         (wr_phase_i),
        .t_phy_wrlat_i      (t_phy_wrlat_i),
        .t_rddata_en_i      (t_rddata_en_i),
        .gear_i             (gear_i),
        .n_subcmd_i         (w_n_subcmd),
        .sub_col_stride_i   (w_sub_col_stride),
        .sub_phase_stride_i (w_sub_phase_stride),
        .dfi_address_o      (dfi_address_o),
        .dfi_bank_o         (dfi_bank_o),
        .dfi_cas_n_o        (dfi_cas_n_o),
        .dfi_ras_n_o        (dfi_ras_n_o),
        .dfi_we_n_o         (dfi_we_n_o),
        .dfi_cs_n_o         (dfi_cs_n_o),
        .dfi_odt_o          (dfi_odt_o),
        .dfi_wrdata_o       (dfi_wrdata_o),
        .dfi_wrdata_en_o    (dfi_wrdata_en_o),
        .dfi_wrdata_mask_o  (dfi_wrdata_mask_o),
        .dfi_rddata_en_o    (dfi_rddata_en_o),
        .dfi_rddata_i       (dfi_rddata_i),
        .dfi_rddata_valid_i (dfi_rddata_valid_i),
        .cal_expect_i       (w_cal_expect),
        .cal_data_o         (w_cal_data),
        .cal_valid_o        (w_cal_valid),
        .dfi_init_start_o   (dfi_init_start_o),
        .dfi_init_complete_i(dfi_init_complete_i)
    );

endmodule : granite_core
