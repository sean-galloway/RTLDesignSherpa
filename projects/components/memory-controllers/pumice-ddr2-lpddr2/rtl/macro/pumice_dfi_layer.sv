// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_dfi_layer
// Purpose: The pumice DFI layer. Holds the single controller<->PHY crossing
//          (pumice_dfi_cdc, async gaxi FIFOs only) and the dfi_clk-domain
//          command path + write serializer + read aligner. Presents the
//          controller-clock command/wrdata/rddata streams on one side and the
//          DFI 2.1 pin bus on the other.
//
//   ctl_clk : cmd (from scheduler), wrdata (from wr CAM), rddata (to rd CAM),
//             init_start/init_complete
//   dfi_clk : DFI command bus, dfi_wrdata/en/mask, dfi_rddata/en/valid,
//             dfi_init_start/complete
//
// Internal datapath unit = the DFI word (dfi_wrdata width, all DFI_RATE phases).
// One FIFO word = one DFI cycle => bubble-free.
//
// Documentation: rtl/PUMICE_DFI_LAYER_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_dfi_layer
    import pumice_pkg::*;
#(
    parameter int NUM_RANKS      = 1,
    parameter int NUM_BANKS      = 8,
    parameter int ROW_WIDTH      = 14,
    parameter int COL_WIDTH      = 10,
    parameter int DFI_RATE       = 2,
    parameter int DRAM_BEAT_WIDTH = 64,
    parameter int BL             = 8,     // DRAM beats per burst
    parameter int CMD_FIFO_DEPTH = 8,
    parameter int WD_FIFO_DEPTH  = 16,
    parameter int RD_FIFO_DEPTH  = 16,
    parameter int N_FLOP_CROSS   = 2,

    // ---- derived DFI geometry ----
    parameter int DFI_DATA_WIDTH = DRAM_BEAT_WIDTH * DFI_RATE,
    parameter int DFI_STRB_WIDTH = DFI_DATA_WIDTH / 8,
    parameter int DFI_EN_WIDTH   = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int DFI_ADDR_WIDTH = ROW_WIDTH,
    parameter int DFI_BANK_WIDTH = $clog2(NUM_BANKS),
    parameter int DFI_CTRL_WIDTH = 1,
    parameter int DFI_CS_WIDTH   = NUM_RANKS,
    parameter int DFI_ADDR_BUS_W = DFI_ADDR_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W = DFI_BANK_WIDTH * DFI_RATE,
    parameter int DFI_CTRL_BUS_W = DFI_CTRL_WIDTH * DFI_RATE,
    parameter int DFI_CS_BUS_W   = DFI_CS_WIDTH * DFI_RATE,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int PHW = (DFI_RATE > 1) ? $clog2(DFI_RATE) : 1,
    parameter int BL_WORDS = BL / DFI_RATE,
    // Read aligner outstanding-read tracking depth (exposed). Size >= the read
    // CAM depth so op_ready never deasserts in steady state; the valid/ready
    // handshake to command issue is the just-in-case backpressure.
    parameter int RD_MAX_OUTSTANDING = 16,
    // rddata_en window width (DQ-bus occupancy of one read). Defaults to
    // BL_WORDS (legacy); set separately when the DRAM beat != device word.
    parameter int RD_EN_CYC = BL_WORDS,
    // FIFO payloads
    parameter int CMD_DW = 4 + RKW + BKW + ROW_WIDTH + COL_WIDTH + 1,
    parameter int WD_DW  = 1 + DFI_STRB_WIDTH + DFI_DATA_WIDTH,   // {last,strb,data}
    parameter int RD_DW  = 1 + 2 + DFI_DATA_WIDTH                 // {last,resp,data}
) (
    //=========================================================================
    // Controller domain (ctl_clk)
    //=========================================================================
    input  logic                       ctl_clk,
    input  logic                       ctl_rstn,

    // cmd in (from scheduler cmd stream)
    input  logic                       cmd_valid_i,
    output logic                       cmd_ready_o,
    input  logic [CMD_DW-1:0]          cmd_data_i,
    // wrdata in (from wr CAM drain; DFI-word granular {last,strb,data})
    input  logic                       wd_valid_i,
    output logic                       wd_ready_o,
    input  logic [WD_DW-1:0]           wd_data_i,
    // rddata out (to rd CAM dfi_ret; {last,resp,data})
    output logic                       rd_valid_o,
    input  logic                       rd_ready_i,
    output logic [RD_DW-1:0]           rd_data_o,
    // init handshake (controller side)
    input  logic                       init_start_i,
    output logic                       init_complete_o,

    //=========================================================================
    // PHY DFI domain (dfi_clk)
    //=========================================================================
    input  logic                       dfi_clk,
    input  logic                       dfi_rstn,
    input  memtype_e                   memtype_i,
    input  logic [PHW-1:0]             rd_phase_i,
    input  logic [PHW-1:0]             wr_phase_i,
    input  logic [7:0]                 t_phy_wrlat_i,
    input  logic [7:0]                 t_rddata_en_i,
    // Active DFI gear = log2(active DFI rate). DFI_RATE is the compile-time MAX
    // rate that sizes every bus; gear_i selects how many of those phases are
    // active. active_rate = 1 << gear_i. At gear_i = log2(DFI_RATE) (board /
    // default) the mask is all-ones and the DFI en outputs are UNCHANGED.
    input  logic [1:0]                 gear_i,

    // DFI command bus
    output logic [DFI_ADDR_BUS_W-1:0]  dfi_address_o,
    output logic [DFI_BANK_BUS_W-1:0]  dfi_bank_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_cas_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_ras_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_we_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_cs_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_odt_o,
    // DFI write data
    output logic [DFI_DATA_WIDTH-1:0]  dfi_wrdata_o,
    output logic [DFI_EN_WIDTH-1:0]    dfi_wrdata_en_o,
    output logic [DFI_STRB_WIDTH-1:0]  dfi_wrdata_mask_o,
    // DFI read data
    output logic [DFI_EN_WIDTH-1:0]    dfi_rddata_en_o,
    input  logic [DFI_DATA_WIDTH-1:0]  dfi_rddata_i,
    input  logic [DFI_VALID_WIDTH-1:0] dfi_rddata_valid_i,
    // DFI init handshake (to/from PHY)
    output logic                       dfi_init_start_o,
    input  logic                       dfi_init_complete_i
);

    // ---- CDC dfi-side nets ----
    logic               pcmd_valid, pcmd_ready;  logic [CMD_DW-1:0] pcmd_data;
    logic               pwd_valid,  pwd_ready;   logic [WD_DW-1:0]  pwd_data;
    logic               prd_valid,  prd_ready;   logic [RD_DW-1:0]  prd_data;
    logic               pinit_start;

    // ---- fire strobes ----
    logic               w_wr_fire, w_rd_fire, w_rd_op_ready;
    logic [RKW-1:0]     w_fire_rank;

    // ---- active-gear phase mask ------------------------------------------
    // active_rate = 1 << gear_i (number of low DFI phases that are active).
    // Sized to hold DFI_RATE. When active_rate == DFI_RATE (gear_i =
    // log2(DFI_RATE), the board/default), w_phase_active is all-ones and the
    // en outputs below are bit-identical to the un-masked fub outputs.
    localparam int RATEW = $clog2(DFI_RATE) + 1;
    logic [RATEW-1:0]        w_active_rate;
    assign w_active_rate = (RATEW'(1) << gear_i);

    logic [DFI_EN_WIDTH-1:0] w_phase_active;
    always_comb begin
        for (int p = 0; p < DFI_EN_WIDTH; p++)
            w_phase_active[p] = (RATEW'(p) < w_active_rate);
    end

    // fub-driven (un-masked) DFI en; gated to the active phases at the output.
    logic [DFI_EN_WIDTH-1:0] w_dfi_wrdata_en, w_dfi_rddata_en;
    assign dfi_wrdata_en_o = w_dfi_wrdata_en & w_phase_active;
    assign dfi_rddata_en_o = w_dfi_rddata_en & w_phase_active;

    // ---- unpack wrdata / pack rddata ----
    logic                      w_wd_last;
    logic [DFI_STRB_WIDTH-1:0] w_wd_strb;
    logic [DFI_DATA_WIDTH-1:0] w_wd_data;
    assign {w_wd_last, w_wd_strb, w_wd_data} = pwd_data;

    logic                      w_rd_last;
    logic [1:0]                w_rd_resp;
    logic [DFI_DATA_WIDTH-1:0] w_rd_data;
    assign prd_data = {w_rd_last, w_rd_resp, w_rd_data};

    // ======================================================================
    // Single CDC (async gaxi FIFOs only)
    // ======================================================================
    pumice_dfi_cdc #(
        .CMD_DW(CMD_DW), .WD_DW(WD_DW), .RD_DW(RD_DW),
        .CMD_DEPTH(CMD_FIFO_DEPTH), .WD_DEPTH(WD_FIFO_DEPTH), .RD_DEPTH(RD_FIFO_DEPTH),
        .N_FLOP_CROSS(N_FLOP_CROSS)
    ) u_cdc (
        .ctl_clk(ctl_clk), .ctl_rstn(ctl_rstn),
        .cmd_valid_i(cmd_valid_i), .cmd_ready_o(cmd_ready_o), .cmd_data_i(cmd_data_i),
        .wd_valid_i(wd_valid_i), .wd_ready_o(wd_ready_o), .wd_data_i(wd_data_i),
        .init_start_i(init_start_i),
        .rd_valid_o(rd_valid_o), .rd_ready_i(rd_ready_i), .rd_data_o(rd_data_o),
        .init_complete_o(init_complete_o),
        .dfi_clk(dfi_clk), .dfi_rstn(dfi_rstn),
        .pcmd_valid_o(pcmd_valid), .pcmd_ready_i(pcmd_ready), .pcmd_data_o(pcmd_data),
        .pwd_valid_o(pwd_valid), .pwd_ready_i(pwd_ready), .pwd_data_o(pwd_data),
        .pinit_start_o(pinit_start),
        .prd_valid_i(prd_valid), .prd_ready_o(prd_ready), .prd_data_i(prd_data),
        .pinit_complete_i(dfi_init_complete_i)
    );

    assign dfi_init_start_o = pinit_start;

    // ======================================================================
    // Command path (dfi_clk): cmd FIFO -> DFI command bus + fire strobes
    // ======================================================================
    pumice_dfi_cmd_path #(
        .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH),
        .COL_WIDTH(COL_WIDTH), .DFI_RATE(DFI_RATE), .COL_BURST_CYC(BL_WORDS),
        .DFI_ADDR_WIDTH(DFI_ADDR_WIDTH),
        .DFI_BANK_WIDTH(DFI_BANK_WIDTH), .DFI_CTRL_WIDTH(DFI_CTRL_WIDTH),
        .DFI_CS_WIDTH(DFI_CS_WIDTH)
    ) u_cmd (
        .dfi_clk(dfi_clk), .dfi_rstn(dfi_rstn), .memtype_i(memtype_i),
        .rd_phase_i(rd_phase_i), .wr_phase_i(wr_phase_i),
        .cmd_valid_i(pcmd_valid), .cmd_ready_o(pcmd_ready), .cmd_data_i(pcmd_data),
        .dfi_address_o(dfi_address_o), .dfi_bank_o(dfi_bank_o),
        .dfi_cas_n_o(dfi_cas_n_o), .dfi_ras_n_o(dfi_ras_n_o), .dfi_we_n_o(dfi_we_n_o),
        .dfi_cs_n_o(dfi_cs_n_o), .dfi_odt_o(dfi_odt_o),
        .wr_fire_o(w_wr_fire), .rd_fire_o(w_rd_fire), .fire_rank_o(w_fire_rank),
        .rd_op_ready_i(w_rd_op_ready)
    );

    // ======================================================================
    // Write serializer (dfi_clk): wrdata FIFO -> dfi_wrdata at t_phy_wrlat
    // ======================================================================
    pumice_dfi_wr_serializer #(
        .DFI_DATA_WIDTH(DFI_DATA_WIDTH), .DFI_RATE(DFI_RATE)
    ) u_wr (
        .dfi_clk(dfi_clk), .dfi_rstn(dfi_rstn), .t_phy_wrlat_i(t_phy_wrlat_i),
        .wr_fire_i(w_wr_fire),
        .wd_valid_i(pwd_valid), .wd_ready_o(pwd_ready),
        .wd_data_i(w_wd_data), .wd_strb_i(w_wd_strb), .wd_last_i(w_wd_last),
        .dfi_wrdata_o(dfi_wrdata_o), .dfi_wrdata_en_o(w_dfi_wrdata_en),
        .dfi_wrdata_mask_o(dfi_wrdata_mask_o)
    );

    // ======================================================================
    // Read aligner (dfi_clk): dfi_rddata -> rddata FIFO at t_rddata_en
    // ======================================================================
    pumice_dfi_rd_aligner #(
        .DFI_DATA_WIDTH(DFI_DATA_WIDTH), .DFI_RATE(DFI_RATE),
        .DFI_VALID_WIDTH(DFI_VALID_WIDTH), .BL_WORDS(BL_WORDS),
        .EN_CYC(RD_EN_CYC), .MAX_OUTSTANDING(RD_MAX_OUTSTANDING)
    ) u_rd (
        .dfi_clk(dfi_clk), .dfi_rstn(dfi_rstn), .t_rddata_en_i(t_rddata_en_i),
        .op_valid_i(w_rd_fire), .op_ready_o(w_rd_op_ready),
        .dfi_rddata_en_o(w_dfi_rddata_en), .dfi_rddata_i(dfi_rddata_i),
        .dfi_rddata_valid_i(dfi_rddata_valid_i),
        .rd_valid_o(prd_valid), .rd_ready_i(prd_ready),
        .rd_data_o(w_rd_data), .rd_resp_o(w_rd_resp), .rd_last_o(w_rd_last)
    );

    wire unused = &{1'b0, w_fire_rank, 1'b0};

endmodule : pumice_dfi_layer
