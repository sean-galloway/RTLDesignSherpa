// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: scoria_core_tb
// Purpose: cocotb-side DV wrapper around scoria_core. Two jobs, both of them
//          naming conventions rather than logic:
//
//          1. The DFI bus is aliased onto `phy_dfi_*` nets, because that is
//             what the CocoTBFramework `DFISlavePHY` BFM binds to -- it builds
//             its bus as `f"{side}_dfi"` with side fixed to "phy", so the
//             names are not negotiable from the Python side. scoria_core's own
//             ports are `dfi_*_o` / `dfi_*_i`.
//          2. scoria_core's observable counters (stall_*, stat_*, zq_*,
//             wrlvl_*, ...) are brought out as INTERNAL nets rather than left
//             dangling. An unconnected output is how 35 OBS_* registers in
//             this family read zero for months with no test noticing.
//
//          Unlike pumice's equivalent this wrapper does NOT have to replace a
//          CSR front end: scoria_core already takes its configuration on
//          direct ports, so the TB drives them and the CSR path is
//          scoria_top's problem.
//
//          The port declarations are GENERATED from scoria_core's own port
//          block, so a width or a name cannot drift from the RTL. The
//          instantiation uses `.*` for every signal that keeps its name and
//          explicit connections only for the renamed DFI group -- which means
//          adding a port to scoria_core breaks THIS file at elaboration
//          instead of silently leaving a new input floating.

`timescale 1ns / 1ps

module scoria_core_tb
    import scoria_pkg::*;
#(
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int NUM_RANKS      = 1,
    parameter int NUM_CS         = NUM_RANKS,
    parameter int NUM_BANKS      = 8,
    parameter int ROW_WIDTH      = 15,
    parameter int COL_WIDTH      = 10,
    parameter int DFI_RATE       = 4,
    parameter int DRAM_BEAT_WIDTH = 32,
    parameter int DRAM_DEVICE_WIDTH = DRAM_BEAT_WIDTH,
    parameter int DRAM_BL        = 8,
    parameter int NUM_ENTRIES    = 8,
    parameter int N_SRAM_SLOTS   = NUM_ENTRIES,
    parameter int RD_RET_DEPTH   = 32,
    parameter int CMD_DELAY      = 0,
    parameter int AGE_WIDTH      = 16,
    parameter int CMD_HISTORY_EN = 0,
    parameter int HIST_T_RFC_CORE = 0,
    parameter int HIST_T_RTW_CORE = 0,
    parameter int HIST_T_WTR_CORE = 0,
    // Derived, mirroring scoria_core so the net declarations below match its
    // ports exactly.
    parameter int BKW  = $clog2(NUM_BANKS),
    parameter int IW   = AXI_ID_WIDTH,
    parameter int AW   = AXI_ADDR_WIDTH,
    parameter int UW   = 1,
    parameter int DFI_DATA_WIDTH  = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DW   = DFI_DATA_WIDTH,
    parameter int SW   = DW / 8,
    parameter int PHW  = (DFI_RATE > 1) ? $clog2(DFI_RATE) : 1,
    parameter int DFI_STRB_WIDTH  = DW / 8,
    parameter int DFI_EN_WIDTH    = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int DFI_ADDR_BUS_W  = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W  = BKW * DFI_RATE,
    parameter int DFI_CTRL_BUS_W  = 1 * DFI_RATE,
    parameter int DFI_CS_BUS_W    = NUM_RANKS * DFI_RATE
) (
    input logic aclk,
    input logic aresetn,
    input logic dfi_clk,
    input logic dfi_rstn,
    input memtype_e memtype_i,
    input page_policy_e page_policy_i,
    input logic [2:0] page_mode_i,
    input logic [7:0] page_tr_init_i,
    input logic [1:0] sched_order_mode_i,
    input logic [1:0] sched_row_sel_i,
    input logic [1:0] sched_col_sel_i,
    input logic [1:0] sched_access_pref_i,
    input logic [7:0] sched_wr_high_wm_i,
    input logic [7:0] sched_wr_batch_max_i,
    input logic [7:0] sched_wr_low_wm_i,
    input logic [1:0] sched_prio_sub_i,
    input logic sched_qos_en_i,
    input logic [7:0] sched_age_thresh_i,
    input logic [4:0] bank_lsb_i,
    input logic hash_en_i,
    input logic [7:0] hash_seed_i,
    input logic [7:0] t_rcd_i,
    input logic [7:0] t_rp_i,
    input logic [7:0] t_ras_i,
    input logic [7:0] t_rc_i,
    input logic [7:0] t_wr_i,
    input logic [7:0] t_rtp_i,
    input logic [7:0] t_faw_i,
    input logic [7:0] t_rrd_i,
    input logic [7:0] t_wtr_i,
    input logic [7:0] t_rtw_i,
    input logic [7:0] t_ccd_i,
    input logic [15:0] t_refi_i,
    input logic refi_reload_i,
    input logic [15:0] t_rfc_i,
    input logic [3:0] refresh_burst_i,
    input logic [3:0] ref_postpone_i,
    input logic [3:0] ref_pullin_i,
    input logic [1:0] ref_mode_i,
    input logic [15:0] ref_trefi_pb_i,
    input logic [7:0] ref_trfc_pb_i,
    input logic [15:0] t_init_wait_i,
    input logic [15:0] t_dll_wait_i,
    input logic [7:0] t_mrd_wait_i,
    input logic [7:0] t_rp_wait_i,
    input logic [7:0] t_rfc_wait_i,
    input logic [15:0] t_xpr_wait_i,
    input logic [15:0] t_zqinit_wait_i,
    input logic zq_enable_i,
    input logic [31:0] zq_interval_i,
    input logic [15:0] t_zqcs_i,
    input logic wrlvl_strobe_i,
    input logic [3:0] wrlvl_cs_sel_i,
    input logic [15:0] t_wldqsen_i,
    input logic [15:0] t_wlmrd_i,
    input logic [15:0] t_wlmrd_max_i,
    input logic [15:0] t_wlo_i,
    input logic [15:0] t_wloe_i,
    input logic [NUM_CS-1:0] dfi_phylvl_ack_cs_n_i,
    input logic dfi_prime_dq_i,
    input logic [15:0] mr0_i,
    input logic [15:0] mr1_i,
    input logic [15:0] mr2_i,
    input logic [15:0] mr3_i,
    input logic init_restart_i,
    input logic [PHW-1:0] rd_phase_i,
    input logic [PHW-1:0] wr_phase_i,
    input logic [7:0] t_phy_wrlat_i,
    input logic [7:0] t_rddata_en_i,
    input logic [1:0] gear_i,
    input logic [3:0] bl_i,
    input logic [IW-1:0] s_axi_awid,
    input logic [AW-1:0] s_axi_awaddr,
    input logic [7:0] s_axi_awlen,
    input logic [2:0] s_axi_awsize,
    input logic [1:0] s_axi_awburst,
    input logic s_axi_awlock,
    input logic [3:0] s_axi_awcache,
    input logic [2:0] s_axi_awprot,
    input logic [3:0] s_axi_awqos,
    input logic [3:0] s_axi_awregion,
    input logic [UW-1:0] s_axi_awuser,
    input logic s_axi_awvalid,
    output logic s_axi_awready,
    input logic [DW-1:0] s_axi_wdata,
    input logic [SW-1:0] s_axi_wstrb,
    input logic s_axi_wlast,
    input logic [UW-1:0] s_axi_wuser,
    input logic s_axi_wvalid,
    output logic s_axi_wready,
    output logic [IW-1:0] s_axi_bid,
    output logic [1:0] s_axi_bresp,
    output logic [UW-1:0] s_axi_buser,
    output logic s_axi_bvalid,
    input logic s_axi_bready,
    input logic [IW-1:0] s_axi_arid,
    input logic [AW-1:0] s_axi_araddr,
    input logic [7:0] s_axi_arlen,
    input logic [2:0] s_axi_arsize,
    input logic [1:0] s_axi_arburst,
    input logic s_axi_arlock,
    input logic [3:0] s_axi_arcache,
    input logic [2:0] s_axi_arprot,
    input logic [3:0] s_axi_arqos,
    input logic [3:0] s_axi_arregion,
    input logic [UW-1:0] s_axi_aruser,
    input logic s_axi_arvalid,
    output logic s_axi_arready,
    output logic [IW-1:0] s_axi_rid,
    output logic [DW-1:0] s_axi_rdata,
    output logic [1:0] s_axi_rresp,
    output logic s_axi_rlast,
    output logic [UW-1:0] s_axi_ruser,
    output logic s_axi_rvalid,
    input logic s_axi_rready
);

    // ---- observable counters: brought out, never dangled ------------------
logic [31:0] stall_bp_o;
    logic [31:0] stall_refresh_o;
    logic [31:0] stall_turnaround_o;
    logic [31:0] stall_tccd_o;
    logic [31:0] stall_actlimit_o;
    logic [31:0] stall_banktimer_o;
    logic [31:0] stall_noreq_o;
    logic [31:0] stall_zq_o;
    logic [31:0] stat_page_hit_o;
    logic [31:0] stat_row_hit_o [NUM_BANKS];
    logic [31:0] stat_page_miss_o;
    logic [31:0] stat_page_empty_o;
    logic [31:0] stat_act_o;
    logic [31:0] stat_pre_o;
    logic [31:0] stat_ref_o;
    logic [31:0] stat_ref_busy_o;
    logic dram_reset_n_o;
    logic [4:0] mr_wr_o;
    logic wrlvl_en_o;
    logic zq_busy_o;
    logic [15:0] zq_total_o;
    logic [31:0] zq_interval_cnt_o;
    logic zq_overdue_o;
    logic [NUM_CS-1:0] dfi_phylvl_req_cs_n_o;
    logic [NUM_CS-1:0] dfi_phy_wrlvl_cs_n_o;
    logic dfi_wrlvl_strobe_o;
    logic wrlvl_result_valid_o;
    logic wrlvl_result_o;
    logic [15:0] wrlvl_attempts_o;
    logic [15:0] wrlvl_flips_o;
    logic wrlvl_timeout_o;
    logic wrlvl_ever_done_o;
    logic [2:0] wrlvl_state_o;
    logic [3:0] cl_o;
    logic [3:0] cwl_o;
    logic [3:0] bl_o;
    logic init_done_o;

    // ---- the DFI bus under the names DFISlavePHY binds ---------------------
    logic [DFI_ADDR_BUS_W-1:0] phy_dfi_address;   // core dfi_address_o (output)
    logic [DFI_BANK_BUS_W-1:0] phy_dfi_bank;   // core dfi_bank_o (output)
    logic [DFI_CTRL_BUS_W-1:0] phy_dfi_cas_n;   // core dfi_cas_n_o (output)
    logic [DFI_CTRL_BUS_W-1:0] phy_dfi_ras_n;   // core dfi_ras_n_o (output)
    logic [DFI_CTRL_BUS_W-1:0] phy_dfi_we_n;   // core dfi_we_n_o (output)
    logic [DFI_CS_BUS_W-1:0] phy_dfi_cs_n;   // core dfi_cs_n_o (output)
    logic [DFI_CS_BUS_W-1:0] phy_dfi_odt;   // core dfi_odt_o (output)
    logic [DFI_DATA_WIDTH-1:0] phy_dfi_wrdata;   // core dfi_wrdata_o (output)
    logic [DFI_EN_WIDTH-1:0] phy_dfi_wrdata_en;   // core dfi_wrdata_en_o (output)
    logic [DFI_STRB_WIDTH-1:0] phy_dfi_wrdata_mask;   // core dfi_wrdata_mask_o (output)
    logic [DFI_EN_WIDTH-1:0] phy_dfi_rddata_en;   // core dfi_rddata_en_o (output)
    logic [DFI_DATA_WIDTH-1:0] phy_dfi_rddata;   // core dfi_rddata_i (input)
    logic [DFI_VALID_WIDTH-1:0] phy_dfi_rddata_valid;   // core dfi_rddata_valid_i (input)
    logic phy_dfi_init_start;   // core dfi_init_start_o (output)
    logic phy_dfi_init_complete;   // core dfi_init_complete_i (input)

    // DFI signals scoria does not drive. The BFM expects the full v2.1/v3.1
    // signal set, so they are declared and tied off here rather than omitted.
    // phy_dfi_cke and phy_dfi_dram_clk_disable are the two that matter: the
    // controller has NO port for either (scoria-ddr3-lpddr3 TASK-003), so the
    // DRAM is held permanently powered and clocked -- which is parity with
    // LiteDRAM's DDR3 core on this board. If power-down is ever wired, these
    // two tie-offs are what have to go.
    logic                       phy_dfi_error, phy_dfi_error_info;
    logic                       phy_dfi_crc_alert;
    logic                       phy_dfi_ctrlupd_req, phy_dfi_ctrlupd_ack;
    logic                       phy_dfi_phyupd_req, phy_dfi_phyupd_ack;
    logic [1:0]                 phy_dfi_phyupd_type;
    logic                       phy_dfi_disconnect_req;
    logic                       phy_dfi_freq_change_req, phy_dfi_freq_change_ack;
    logic                       phy_dfi_parity_check, phy_dfi_phymstr_req;
    logic                       phy_dfi_training_active, phy_dfi_training_phase;
    logic [DFI_CS_BUS_W-1:0]    phy_dfi_cke, phy_dfi_dram_clk_disable;

    // ---- DFI v3.1 signals scoria does not present under their DFI names ---
    // The BFM checks the required set for the declared version/memory type and
    // names what is absent, which surfaced three:
    //
    // dfi_reset_n      scoria HAS this -- it just calls it dram_reset_n_o and
    //                  documents it as "a device PIN". DFI v3.1 carries DRAM
    //                  RESET# as part of the control interface, so for a v3.1
    //                  claim the DFI name is the right one and this is an
    //                  alias rather than a tie-off.
    // dfi_wrdata_cs_n  per-data-phase chip select, new in v3.1. scoria does
    // dfi_rddata_cs_n  not drive either: it qualifies commands with
    //                  dfi_cs_n and has one rank. Tied to 0 = rank 0
    //                  selected, which is correct for NUM_RANKS=1 and would
    //                  have to be driven for real multi-rank.
    logic                       phy_dfi_reset_n;
    logic [DFI_CS_BUS_W-1:0]    phy_dfi_wrdata_cs_n, phy_dfi_rddata_cs_n;

    assign phy_dfi_reset_n      = dram_reset_n_o;
    assign phy_dfi_wrdata_cs_n  = '0;
    assign phy_dfi_rddata_cs_n  = '0;

    assign phy_dfi_error            = 1'b0;
    assign phy_dfi_error_info       = 1'b0;
    assign phy_dfi_crc_alert        = 1'b0;
    assign phy_dfi_ctrlupd_req      = 1'b0;
    assign phy_dfi_ctrlupd_ack      = 1'b0;
    assign phy_dfi_phyupd_req       = 1'b0;
    assign phy_dfi_phyupd_ack       = 1'b0;
    assign phy_dfi_phyupd_type      = 2'b0;
    assign phy_dfi_disconnect_req   = 1'b0;
    assign phy_dfi_freq_change_req  = 1'b0;
    assign phy_dfi_freq_change_ack  = 1'b0;
    assign phy_dfi_parity_check     = 1'b0;
    assign phy_dfi_phymstr_req      = 1'b0;
    assign phy_dfi_training_active  = 1'b0;
    assign phy_dfi_training_phase   = 1'b0;
    assign phy_dfi_cke              = '1;
    assign phy_dfi_dram_clk_disable = '0;

    // ---- the DUT -----------------------------------------------------------
    // `.*` carries every port whose name is unchanged; the DFI group is named
    // explicitly because it is renamed. A new scoria_core port with no match
    // here is an elaboration error, which is the behaviour we want.
    scoria_core #(
        .AXI_ID_WIDTH(AXI_ID_WIDTH), .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
        .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS),
        .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH),
        .DFI_RATE(DFI_RATE), .DRAM_BEAT_WIDTH(DRAM_BEAT_WIDTH),
        .DRAM_DEVICE_WIDTH(DRAM_DEVICE_WIDTH), .DRAM_BL(DRAM_BL),
        .NUM_ENTRIES(NUM_ENTRIES), .N_SRAM_SLOTS(N_SRAM_SLOTS),
        .RD_RET_DEPTH(RD_RET_DEPTH), .CMD_DELAY(CMD_DELAY),
        .AGE_WIDTH(AGE_WIDTH), .CMD_HISTORY_EN(CMD_HISTORY_EN),
        .HIST_T_RFC_CORE(HIST_T_RFC_CORE),
        .HIST_T_RTW_CORE(HIST_T_RTW_CORE),
        .HIST_T_WTR_CORE(HIST_T_WTR_CORE)
    ) u_core (
        .*,
        .dfi_address_o       (phy_dfi_address),
        .dfi_bank_o          (phy_dfi_bank),
        .dfi_cas_n_o         (phy_dfi_cas_n),
        .dfi_ras_n_o         (phy_dfi_ras_n),
        .dfi_we_n_o          (phy_dfi_we_n),
        .dfi_cs_n_o          (phy_dfi_cs_n),
        .dfi_odt_o           (phy_dfi_odt),
        .dfi_wrdata_o        (phy_dfi_wrdata),
        .dfi_wrdata_en_o     (phy_dfi_wrdata_en),
        .dfi_wrdata_mask_o   (phy_dfi_wrdata_mask),
        .dfi_rddata_en_o     (phy_dfi_rddata_en),
        .dfi_rddata_i        (phy_dfi_rddata),
        .dfi_rddata_valid_i  (phy_dfi_rddata_valid),
        .dfi_init_start_o    (phy_dfi_init_start),
        .dfi_init_complete_i (phy_dfi_init_complete)
    );

endmodule : scoria_core_tb
