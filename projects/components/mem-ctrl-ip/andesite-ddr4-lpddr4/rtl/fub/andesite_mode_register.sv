// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_mode_register
// Purpose: MR0-MR6 image store per memtype, with derived policy outputs
//
// Documentation:
//   projects/components/mem-ctrl-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//   ch02_blocks/03_mode_register.md (Table 2.5 parameters; Table 2.6 ports;
//   Table 2.7 semantics -- bit maps per JESD79-4 confirmed at HAS Q1)
//
// The block is registers plus a mux; the programming order is the
// init_sequencer's property (MAS Purpose section). Bit selects live in one
// Q1 block below: the six review-verified positions carry their citation;
// the four placeholders are wiring-until-Q1 -- the JESD79-4/JESD209-4
// cold-storage read (HAS Q1) changes the constant, never the structure,
// and the testbench shares the placeholder constants.
//
// Author: sean galloway
// Created: 2026-10-04

`timescale 1ns / 1ps

module andesite_mode_register #(
    parameter int DATA_WIDTH      = 16,
    parameter int RANKS           = 1,
    parameter int DDR4_MR_COUNT   = 7,
    parameter int LPDDR4_MR_COUNT = 64,   // working bound; MR space per JESD209-4 (Q1)
    parameter int RANK_W          = (RANKS > 1) ? $clog2(RANKS) : 1
) (
    input  logic                     clk,
    input  logic                     rst_n,

    input  andesite_pkg::memtype_e   memtype_i,
    input  logic [RANK_W-1:0]        rank_i,
    input  logic                     wr_en_i,
    input  logic [5:0]               wr_addr_i,
    input  logic [DATA_WIDTH-1:0]    wr_data_i,
    input  logic                     rd_en_i,
    input  logic [5:0]               rd_addr_i,
    output logic [DATA_WIDTH-1:0]    rd_data_o,

    output logic [5:0]               mr_sel_o,
    output logic [DATA_WIDTH-1:0]    mr_data_o,

    output logic [1:0]               mpr_page_o,
    output logic [1:0]               fgr_factor_o,
    output logic [2:0]               rtt_nom_o,
    output logic [2:0]               rtt_wr_o,
    output logic [2:0]               rtt_park_o,
    output logic                     rd_dbi_en_o,
    output logic                     wr_dbi_en_o,
    output logic [1:0]               ca_parity_lat_o,
    output logic                     wrlvl_en_o,
    output logic [2:0]               lpddr4_odt_o
);

    import andesite_pkg::*;

    // ------------------------------------------------------------------
    // Q1 BIT-MAP BLOCK. Verified positions cite the review (Micron/Alliance
    // datasheets, 2026-10-04 tranche review); placeholders are marked.
    // HAS Q1 (cold-storage read) confirms or corrects every select here.
    // ------------------------------------------------------------------
    localparam int MR3_FGR_LSB            = 6;    // [8:6], review-verified (Micron MR3)
    localparam int MR1_RTT_NOM_LSB        = 8;    // [10:8], carried DDR3->DDR4
    localparam int MR2_RTT_WR_LSB         = 9;    // [11:9], review-verified
    localparam int MR5_RTT_PARK_LSB       = 6;    // [8:6], review-verified
    localparam int MR5_CA_PARITY_LAT_LSB  = 0;    // field review-verified (Alliance); the output is the [1:0] slice, encoding map Q1
    localparam int MR1_WRLVL_BIT          = 7;    // carried DDR3
    // Placeholders -- wiring verified against the TB constants, positions
    // TBC at Q1:
    localparam int MR5_RD_DBI_BIT         = 12;
    localparam int MR5_WR_DBI_BIT         = 11;
    localparam int MR3_MPR_PAGE_LSB       = 1;
    localparam int LPDDR4_ODT_IMG         = 11;   // LPDDR4 MR index carrying DQ-ODT

    logic [DATA_WIDTH-1:0] r_ddr4_img    [RANKS][DDR4_MR_COUNT];
    logic [DATA_WIDTH-1:0] r_lpddr4_img  [RANKS][LPDDR4_MR_COUNT];

    logic [DATA_WIDTH-1:0] w_mr3;
    logic [DATA_WIDTH-1:0] w_mr1;
    logic [DATA_WIDTH-1:0] w_mr2;
    logic [DATA_WIDTH-1:0] w_mr5;
    logic [2:0]            w_fgr3;

    // Image store: one write port, memtype-selected bank.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int r = 0; r < RANKS; r++) begin
                for (int m = 0; m < DDR4_MR_COUNT; m++)
                    r_ddr4_img[r][m] <= '0;
                for (int m = 0; m < LPDDR4_MR_COUNT; m++)
                    r_lpddr4_img[r][m] <= '0;
            end
        end else if (wr_en_i) begin
            if (memtype_i == MEMTYPE_DDR4)
                r_ddr4_img[rank_i][wr_addr_i[2:0]] <= wr_data_i;
            else
                r_lpddr4_img[rank_i][wr_addr_i] <= wr_data_i;
        end
    end

    // Readback: registered, one-cycle latency.
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rd_data_o <= '0;
        else if (rd_en_i) begin
            if (memtype_i == MEMTYPE_DDR4)
                rd_data_o <= r_ddr4_img[rank_i][rd_addr_i[2:0]];
            else
                rd_data_o <= r_lpddr4_img[rank_i][rd_addr_i];
        end
    end

    // MRS command presentation: registered copy of the last write (the
    // sequencer writes the MR image, then issues OP_MRS against it).
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mr_sel_o  <= '0;
            mr_data_o <= '0;
        end else if (wr_en_i) begin
            mr_sel_o  <= wr_addr_i;
            mr_data_o <= wr_data_i;
        end
    end

    // Derived outputs (single-rank design point consumes rank_i's bank).
    assign w_mr3   = r_ddr4_img[rank_i][3];
    assign w_mr1   = r_ddr4_img[rank_i][1];
    assign w_mr2   = r_ddr4_img[rank_i][2];
    assign w_mr5   = r_ddr4_img[rank_i][5];
    assign w_fgr3  = w_mr3[MR3_FGR_LSB +: 3];

    assign mpr_page_o     = w_mr3[MR3_MPR_PAGE_LSB +: 2];
    // FGR encodings 000/001/010 (1x/2x/4x; reserved codes per JESD79-4, Q1
    // confirmation pending); anything above clamps
    // to 4x, the same posture scoria's TCR took for illegal derate codes.
    assign fgr_factor_o   = (w_fgr3 > 3'd2) ? 2'd2 : w_fgr3[1:0];
    assign rtt_nom_o      = w_mr1[MR1_RTT_NOM_LSB +: 3];
    assign rtt_wr_o       = w_mr2[MR2_RTT_WR_LSB +: 3];
    assign rtt_park_o     = w_mr5[MR5_RTT_PARK_LSB +: 3];
    assign rd_dbi_en_o    = w_mr5[MR5_RD_DBI_BIT];
    assign wr_dbi_en_o    = w_mr5[MR5_WR_DBI_BIT];
    assign ca_parity_lat_o = w_mr5[MR5_CA_PARITY_LAT_LSB +: 2];
    assign wrlvl_en_o     = w_mr1[MR1_WRLVL_BIT];
    assign lpddr4_odt_o   = r_lpddr4_img[rank_i][LPDDR4_ODT_IMG][2:0];

endmodule : andesite_mode_register
