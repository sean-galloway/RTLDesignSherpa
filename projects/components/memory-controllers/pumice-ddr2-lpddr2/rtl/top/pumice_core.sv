// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_core
// Purpose: The rearchitected pumice DDR2/LPDDR2 controller core. Wires the
//          three layers built bottom-up this cycle:
//            1. pumice_axi4_ifc          (host AXI + wr/rd CAMs)
//            2. pumice_mem_cmd_scheduler (bank timers + arbiter + refresh/init)
//            3. pumice_dfi_layer         (single async CDC + DFI datapath)
//
//          Host AXI + scheduler + CAMs run on aclk; the DFI phase-packer + PHY
//          run on dfi_clk; the ONE clock crossing lives in pumice_dfi_layer's
//          CDC (async gaxi FIFOs only). Internal data unit = the DFI word
//          (DFI_DATA_WIDTH); the host AXI data width is the DFI word too (an
//          external 64<->128 dwidth shim is a separate edge concern).
//
//          Config (timings / phases / policy) is delivered on ports here; a
//          by-name CSR register block is a clean-rebuild follow-up.
//
// Documentation: rtl/PUMICE_DFI_LAYER_UARCH.md (+ the IFC / scheduler specs)
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_core
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
    // Physical DRAM device word width. When < DRAM_BEAT_WIDTH (e.g. an x16
    // device behind a 32b pumice beat) one pumice beat packs
    // DRAM_BEAT_WIDTH/DRAM_DEVICE_WIDTH physical beats. Default == beat => the
    // legacy 1:1 behaviour (no column/burst scaling).
    parameter int DRAM_DEVICE_WIDTH = DRAM_BEAT_WIDTH,
    parameter int BL             = 8,        // burst length, JEDEC device beats (MR0)
    parameter int NUM_ENTRIES    = 8,
    parameter int N_SRAM_SLOTS   = 8,
    parameter int AGE_WIDTH      = 16,

    // Narrow-device derivations: addr_mapper column stride is the physical
    // device word (BYTE_OFFSET_WIDTH), and the JEDEC burst length scales down
    // to pumice DRAM beats (BL_PUMICE). Ratio 1 => BYTE_OFFSET_WIDTH=log2(beat
    // bytes) and BL_PUMICE=BL, i.e. exactly the legacy values.
    parameter int BYTE_OFFSET_WIDTH = $clog2(DRAM_DEVICE_WIDTH / 8),
    parameter int BL_SHIFT   = (DRAM_BEAT_WIDTH > DRAM_DEVICE_WIDTH)
                             ? $clog2(DRAM_BEAT_WIDTH / DRAM_DEVICE_WIDTH) : 0,
    parameter int BL_PUMICE  = BL >> BL_SHIFT,

    // internal data unit = DFI word
    parameter int DFI_DATA_WIDTH = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DW  = DFI_DATA_WIDTH,      // host AXI data width == DFI word
    parameter int SW  = DW / 8,
    parameter int IW  = AXI_ID_WIDTH,
    parameter int AW  = AXI_ADDR_WIDTH,
    parameter int UW  = 1,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int PHW = (DFI_RATE > 1) ? $clog2(DFI_RATE) : 1,
    parameter int N_LU = NUM_BANKS,
    // DFI geometry
    parameter int DFI_STRB_WIDTH = DW / 8,
    parameter int DFI_EN_WIDTH   = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int DFI_ADDR_BUS_W = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W = BKW * DFI_RATE,
    parameter int DFI_CTRL_BUS_W = 1 * DFI_RATE,
    parameter int DFI_CS_BUS_W   = NUM_RANKS * DFI_RATE
) (
    // ---- controller clock (host AXI + scheduler + CAMs) ----
    input  logic                       aclk,
    input  logic                       aresetn,
    // ---- DFI/PHY clock ----
    input  logic                       dfi_clk,
    input  logic                       dfi_rstn,

    // ---- config (ports; CSR rebuild is a follow-up) ----
    input  memtype_e                   memtype_i,
    input  page_policy_e               page_policy_i,
    input  logic [4:0]                 bank_lsb_i,
    input  logic                       hash_en_i,
    input  logic [7:0]                 hash_seed_i,
    input  logic [7:0]                 t_rcd_i, t_rp_i, t_ras_i, t_rc_i, t_wr_i, t_rtp_i,
    input  logic [7:0]                 t_faw_i, t_rrd_i, t_wtr_i, t_rtw_i, t_ccd_i,
    input  logic [15:0]                t_refi_i,
    input  logic [3:0]                 refresh_burst_i,
    input  logic [15:0]                t_init_wait_i, t_dll_wait_i,
    input  logic [7:0]                 t_mrd_wait_i, t_rp_wait_i, t_rfc_wait_i,
    input  logic [PHW-1:0]             rd_phase_i, wr_phase_i,
    input  logic [7:0]                 t_phy_wrlat_i, t_rddata_en_i,
    output logic [3:0]                 cl_o, cwl_o, bl_o,
    output logic                       init_done_o,

    // ---- host AXI4 (data width = DFI word; external dwidth shim separate) ----
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

    // ---- DFI 2.1 pin bus (to PHY) ----
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

    localparam int PTRW = $clog2(NUM_ENTRIES);
    localparam int CMD_DW = 4 + RKW + BKW + ROW_WIDTH + COL_WIDTH + 1;
    localparam int WD_DW  = 1 + DFI_STRB_WIDTH + DFI_DATA_WIDTH;
    localparam int RD_DW  = 1 + 2 + DFI_DATA_WIDTH;

    // ---- scheduler <-> IFC CAM nets ----
    logic [N_LU-1:0]           w_wr_lu_v, w_wr_lu_hit, w_rd_lu_v, w_rd_lu_hit;
    logic [N_LU*BKW-1:0]       w_wr_lu_bank, w_rd_lu_bank;
    logic [N_LU*ROW_WIDTH-1:0] w_wr_lu_row,  w_rd_lu_row;
    logic [N_LU*PTRW-1:0]      w_wr_lu_slot, w_rd_lu_slot;
    logic [N_LU*COL_WIDTH-1:0] w_wr_lu_col,  w_rd_lu_col;
    logic [N_LU*IW-1:0]        w_wr_lu_id,   w_rd_lu_id;
    logic [N_LU*AGE_WIDTH-1:0] w_wr_lu_age,  w_rd_lu_age;
    logic                      w_wr_old_v, w_rd_old_v;
    logic [BKW-1:0]            w_wr_old_bank, w_rd_old_bank;
    logic [ROW_WIDTH-1:0]      w_wr_old_row,  w_rd_old_row;
    logic [PTRW-1:0]           w_wr_old_slot, w_rd_old_slot;
    logic                      w_wr_commit_v, w_wr_commit_rdy;
    logic [PTRW-1:0]           w_wr_commit_slot;
    logic                      w_rd_issue_v, w_rd_issue_rdy;
    logic [PTRW-1:0]           w_rd_issue_slot;

    // ---- IFC wr commit-data -> DFI wrdata ; DFI rddata -> IFC rd return ----
    logic                      w_cm_v, w_cm_rdy, w_cm_last;
    logic [DW-1:0]             w_cm_data;
    logic [SW-1:0]             w_cm_strb;
    logic                      w_ret_v, w_ret_rdy, w_ret_last;
    logic [DW-1:0]             w_ret_data;
    logic [1:0]                w_ret_resp;

    // ---- scheduler cmd stream -> DFI cmd (packed) ----
    logic                      w_cmd_v, w_cmd_rdy;
    dram_op_e                  w_cmd_op;
    logic [RKW-1:0]            w_cmd_rank;
    logic [BKW-1:0]            w_cmd_bank;
    logic [ROW_WIDTH-1:0]      w_cmd_row;
    logic [COL_WIDTH-1:0]      w_cmd_col;
    logic                      w_cmd_ap;
    logic [CMD_DW-1:0]         w_cmd_data;
    assign w_cmd_data = {w_cmd_ap, w_cmd_col, w_cmd_row, w_cmd_bank, w_cmd_rank, w_cmd_op};

    // ---- init handshake scheduler <-> DFI (ctl side) ----
    logic                      w_init_start, w_init_complete;

    // ======================================================================
    // Layer 1: AXI interface + CAMs
    // ======================================================================
    pumice_axi4_ifc #(
        .AXI_ID_WIDTH(IW), .AXI_ADDR_WIDTH(AW), .AXI_DATA_WIDTH(DW), .AXI_USER_WIDTH(UW),
        .DRAM_BEAT_WIDTH(DW), .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS),
        .ROW_WIDTH(ROW_WIDTH), .COL_WIDTH(COL_WIDTH), .BYTE_OFFSET_WIDTH(BYTE_OFFSET_WIDTH),
        .BL(BL_PUMICE / DFI_RATE), .NUM_ENTRIES(NUM_ENTRIES), .N_SRAM_SLOTS(N_SRAM_SLOTS),
        .N_SCHED_LU(N_LU), .AGE_WIDTH(AGE_WIDTH)
    ) u_ifc (
        .aclk(aclk), .aresetn(aresetn),
        .bank_lsb_i(bank_lsb_i), .hash_en_i(hash_en_i), .hash_seed_i(hash_seed_i),
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
        // wr CAM sched ports
        .wr_oldest_valid_o(w_wr_old_v), .wr_oldest_bank_o(w_wr_old_bank),
        .wr_oldest_row_o(w_wr_old_row), .wr_oldest_col_o(), .wr_oldest_id_o(),
        .wr_oldest_slot_o(w_wr_old_slot),
        .wr_sched_lu_valid_i(w_wr_lu_v), .wr_sched_lu_bank_i(w_wr_lu_bank),
        .wr_sched_lu_row_i(w_wr_lu_row), .wr_sched_lu_hit_o(w_wr_lu_hit),
        .wr_sched_lu_slot_o(w_wr_lu_slot), .wr_sched_lu_col_o(w_wr_lu_col),
        .wr_sched_lu_id_o(w_wr_lu_id), .wr_sched_lu_age_o(w_wr_lu_age),
        .wr_commit_valid_i(w_wr_commit_v), .wr_commit_ready_o(w_wr_commit_rdy),
        .wr_commit_slot_i(w_wr_commit_slot),
        .wr_cm_rd_valid_o(w_cm_v), .wr_cm_rd_ready_i(w_cm_rdy),
        .wr_cm_rd_data_o(w_cm_data), .wr_cm_rd_strb_o(w_cm_strb), .wr_cm_rd_last_o(w_cm_last),
        // rd CAM sched ports
        .rd_oldest_valid_o(w_rd_old_v), .rd_oldest_bank_o(w_rd_old_bank),
        .rd_oldest_row_o(w_rd_old_row), .rd_oldest_col_o(), .rd_oldest_id_o(),
        .rd_oldest_slot_o(w_rd_old_slot),
        .rd_sched_lu_valid_i(w_rd_lu_v), .rd_sched_lu_bank_i(w_rd_lu_bank),
        .rd_sched_lu_row_i(w_rd_lu_row), .rd_sched_lu_hit_o(w_rd_lu_hit),
        .rd_sched_lu_slot_o(w_rd_lu_slot), .rd_sched_lu_col_o(w_rd_lu_col),
        .rd_sched_lu_id_o(w_rd_lu_id), .rd_sched_lu_age_o(w_rd_lu_age),
        .rd_issue_valid_i(w_rd_issue_v), .rd_issue_ready_o(w_rd_issue_rdy),
        .rd_issue_slot_i(w_rd_issue_slot),
        .rd_dfi_ret_valid_i(w_ret_v), .rd_dfi_ret_ready_o(w_ret_rdy),
        .rd_dfi_ret_data_i(w_ret_data), .rd_dfi_ret_resp_i(w_ret_resp),
        .rd_dfi_ret_last_i(w_ret_last),
        .busy_o()
    );

    // ======================================================================
    // Layer 2: command scheduler
    // ======================================================================
    pumice_mem_cmd_scheduler #(
        .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH),
        .COL_WIDTH(COL_WIDTH), .AXI_ID_WIDTH(IW), .NUM_ENTRIES(NUM_ENTRIES),
        .AGE_WIDTH(AGE_WIDTH)
    ) u_sched (
        .aclk(aclk), .aresetn(aresetn),
        .page_policy_i(page_policy_i), .memtype_i(memtype_i),
        .t_rcd_i(t_rcd_i), .t_rp_i(t_rp_i), .t_ras_i(t_ras_i), .t_rc_i(t_rc_i),
        .t_wr_i(t_wr_i), .t_rtp_i(t_rtp_i), .t_faw_i(t_faw_i), .t_rrd_i(t_rrd_i),
        .t_wtr_i(t_wtr_i), .t_rtw_i(t_rtw_i), .t_ccd_i(t_ccd_i),
        .t_refi_i(t_refi_i), .refresh_burst_i(refresh_burst_i),
        .t_init_wait_i(t_init_wait_i), .t_dll_wait_i(t_dll_wait_i),
        .t_mrd_wait_i(t_mrd_wait_i), .t_rp_wait_i(t_rp_wait_i), .t_rfc_wait_i(t_rfc_wait_i),
        .dfi_init_start_o(w_init_start), .dfi_init_complete_i(w_init_complete),
        .init_done_o(init_done_o), .cl_o(cl_o), .cwl_o(cwl_o), .bl_o(bl_o),
        // wr CAM oldest + commit
        .wr_oldest_valid_i(w_wr_old_v), .wr_oldest_bank_i(w_wr_old_bank),
        .wr_oldest_row_i(w_wr_old_row), .wr_oldest_slot_i(w_wr_old_slot),
        .wr_commit_valid_o(w_wr_commit_v), .wr_commit_slot_o(w_wr_commit_slot),
        // rd CAM oldest + issue
        .rd_oldest_valid_i(w_rd_old_v), .rd_oldest_bank_i(w_rd_old_bank),
        .rd_oldest_row_i(w_rd_old_row), .rd_oldest_slot_i(w_rd_old_slot),
        .rd_issue_valid_o(w_rd_issue_v), .rd_issue_slot_o(w_rd_issue_slot),
        // scheduler lookup ports (wired to the IFC's wr/rd_sched_lu_*)
        .wr_lu_valid_o(w_wr_lu_v), .wr_lu_bank_o(w_wr_lu_bank), .wr_lu_row_o(w_wr_lu_row),
        .wr_lu_hit_i(w_wr_lu_hit), .wr_lu_slot_i(w_wr_lu_slot), .wr_lu_col_i(w_wr_lu_col),
        .wr_lu_id_i(w_wr_lu_id), .wr_lu_age_i(w_wr_lu_age),
        .rd_lu_valid_o(w_rd_lu_v), .rd_lu_bank_o(w_rd_lu_bank), .rd_lu_row_o(w_rd_lu_row),
        .rd_lu_hit_i(w_rd_lu_hit), .rd_lu_slot_i(w_rd_lu_slot), .rd_lu_col_i(w_rd_lu_col),
        .rd_lu_id_i(w_rd_lu_id), .rd_lu_age_i(w_rd_lu_age),
        // command stream out
        .cmd_valid_o(w_cmd_v), .cmd_ready_i(w_cmd_rdy), .cmd_op_o(w_cmd_op),
        .cmd_rank_o(w_cmd_rank), .cmd_bank_o(w_cmd_bank), .cmd_row_o(w_cmd_row),
        .cmd_col_o(w_cmd_col), .cmd_ap_o(w_cmd_ap), .busy_o()
    );

    // ======================================================================
    // Layer 3: DFI layer (single CDC + datapath)
    // ======================================================================
    pumice_dfi_layer #(
        .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH),
        .COL_WIDTH(COL_WIDTH), .DFI_RATE(DFI_RATE), .DRAM_BEAT_WIDTH(DRAM_BEAT_WIDTH),
        .BL(BL_PUMICE)
    ) u_dfi (
        .ctl_clk(aclk), .ctl_rstn(aresetn),
        .cmd_valid_i(w_cmd_v), .cmd_ready_o(w_cmd_rdy), .cmd_data_i(w_cmd_data),
        .wd_valid_i(w_cm_v), .wd_ready_o(w_cm_rdy),
        .wd_data_i({w_cm_last, w_cm_strb, w_cm_data}),
        .rd_valid_o(w_ret_v), .rd_ready_i(w_ret_rdy), .rd_data_o({w_ret_last, w_ret_resp, w_ret_data}),
        .init_start_i(w_init_start), .init_complete_o(w_init_complete),
        .dfi_clk(dfi_clk), .dfi_rstn(dfi_rstn), .memtype_i(memtype_i),
        .rd_phase_i(rd_phase_i), .wr_phase_i(wr_phase_i),
        .t_phy_wrlat_i(t_phy_wrlat_i), .t_rddata_en_i(t_rddata_en_i),
        .dfi_address_o(dfi_address_o), .dfi_bank_o(dfi_bank_o),
        .dfi_cas_n_o(dfi_cas_n_o), .dfi_ras_n_o(dfi_ras_n_o), .dfi_we_n_o(dfi_we_n_o),
        .dfi_cs_n_o(dfi_cs_n_o), .dfi_odt_o(dfi_odt_o),
        .dfi_wrdata_o(dfi_wrdata_o), .dfi_wrdata_en_o(dfi_wrdata_en_o),
        .dfi_wrdata_mask_o(dfi_wrdata_mask_o),
        .dfi_rddata_en_o(dfi_rddata_en_o), .dfi_rddata_i(dfi_rddata_i),
        .dfi_rddata_valid_i(dfi_rddata_valid_i),
        .dfi_init_start_o(dfi_init_start_o), .dfi_init_complete_i(dfi_init_complete_i)
    );

endmodule : pumice_core
