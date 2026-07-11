// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pumice_dfi_cmd_path
// Purpose: DFI-domain command path. Pops the abstract command stream (from the
//          CDC cmd FIFO), unpacks {op,rank,bank,row,col,ap}, and drives the
//          multi-phase DFI command bus via the silicon-proven dfi_cmd_formatter.
//          Emits wr_fire/rd_fire strobes (+ op) so the write serializer / read
//          aligner can schedule their data phases relative to the command.
//
// Runs entirely on dfi_clk (the CDC is the only crossing). One command per DFI
// cycle; for BL8 @ nphases=4 that is full DQ bandwidth.
//
// Documentation: rtl/PUMICE_DFI_LAYER_UARCH.md
`timescale 1ns / 1ps

`include "reset_defs.svh"

module pumice_dfi_cmd_path
    import pumice_pkg::*;
#(
    parameter int NUM_RANKS      = 1,
    parameter int NUM_BANKS      = 8,
    parameter int ROW_WIDTH      = 14,
    parameter int COL_WIDTH      = 10,
    parameter int BURST_LEN_WIDTH = 8,
    parameter int DFI_RATE       = 4,
    // DQ-bus occupancy of one column burst in DFI cycles (= BL/DFI_RATE = the
    // burst's DFI-word count). A column (RD/WR) command owns the shared DQ bus
    // for this many cycles, so the next column command must be held that long or
    // its burst data collides with the previous burst. 1 => no pacing (issue a
    // column every cycle, valid only when BL == DFI_RATE).
    parameter int COL_BURST_CYC  = 1,
    parameter int DFI_ADDR_WIDTH = 14,
    parameter int DFI_BANK_WIDTH = 3,
    parameter int DFI_CTRL_WIDTH = 1,
    parameter int DFI_CS_WIDTH   = NUM_RANKS,

    parameter int DFI_ADDR_BUS_W = DFI_ADDR_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W = DFI_BANK_WIDTH * DFI_RATE,
    parameter int DFI_CTRL_BUS_W = DFI_CTRL_WIDTH * DFI_RATE,
    parameter int DFI_CS_BUS_W   = DFI_CS_WIDTH * DFI_RATE,
    parameter int RKW = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW = $clog2(NUM_BANKS),
    parameter int PHW = (DFI_RATE > 1) ? $clog2(DFI_RATE) : 1,
    // Packed command word: {ap, col, row, bank, rank, op}  (matches the
    // scheduler's cmd FIFO packing).
    parameter int CMD_DW = 4 + RKW + BKW + ROW_WIDTH + COL_WIDTH + 1
) (
    input  logic                       dfi_clk,
    input  logic                       dfi_rstn,
    input  memtype_e                   memtype_i,
    input  logic [PHW-1:0]             rd_phase_i,
    input  logic [PHW-1:0]             wr_phase_i,

    // ---- abstract command in (from CDC cmd FIFO) ----
    input  logic                       cmd_valid_i,
    output logic                       cmd_ready_o,
    input  logic [CMD_DW-1:0]          cmd_data_i,

    // ---- DFI command bus (to dfi_signal_pack / PHY) ----
    output logic [DFI_ADDR_BUS_W-1:0]  dfi_address_o,
    output logic [DFI_BANK_BUS_W-1:0]  dfi_bank_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_cas_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_ras_n_o,
    output logic [DFI_CTRL_BUS_W-1:0]  dfi_we_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_cs_n_o,
    output logic [DFI_CS_BUS_W-1:0]    dfi_odt_o,

    // ---- fire strobes to the data paths (1-cycle, on accepted command) ----
    output logic                       wr_fire_o,   // WR / WRA issued
    output logic                       rd_fire_o,   // RD / RDA issued
    output logic [RKW-1:0]             fire_rank_o
);

    // ---- unpack the command word ----
    logic                w_ap;
    logic [COL_WIDTH-1:0] w_col;
    logic [ROW_WIDTH-1:0] w_row;
    logic [BKW-1:0]       w_bank;
    logic [RKW-1:0]       w_rank;
    dram_op_e             w_op;
    assign {w_ap, w_col, w_row, w_bank, w_rank, w_op} = cmd_data_i;

    // ---- DQ-bus occupancy pacing (column commands only) --------------------
    // A column command's burst owns the DQ bus for COL_BURST_CYC DFI cycles.
    // Hold the NEXT column command until that window clears; ACT/PRE/REF do not
    // touch the DQ bus and flow freely. In-order: a stalled column at the FIFO
    // head backpressures everything behind it (and, via the CDC, the arbiter).
    localparam int PCW = (COL_BURST_CYC <= 1) ? 1 : $clog2(COL_BURST_CYC);
    logic          w_is_wr, w_is_rd, w_is_col;
    assign w_is_wr  = (w_op == OP_WR) || (w_op == OP_WRA);
    assign w_is_rd  = (w_op == OP_RD) || (w_op == OP_RDA);
    assign w_is_col = w_is_wr || w_is_rd;

    logic [PCW-1:0] r_col_pace;
    logic           w_col_ok, w_gate;
    assign w_col_ok = (r_col_pace == '0);
    assign w_gate   = (!w_is_col) || w_col_ok;   // may present head to formatter

    logic w_fmt_ready;
    logic w_fire;
    assign w_fire = cmd_valid_i && cmd_ready_o;

    // dfi_cmd_formatter drives the multi-phase command bus. Gate its valid (and
    // the FIFO pop) with w_gate so a paced-out column command stays queued.
    dfi_cmd_formatter #(
        .NUM_RANKS(NUM_RANKS), .NUM_BANKS(NUM_BANKS), .ROW_WIDTH(ROW_WIDTH),
        .COL_WIDTH(COL_WIDTH), .BURST_LEN_WIDTH(BURST_LEN_WIDTH),
        .DFI_RATE(DFI_RATE), .DFI_ADDR_WIDTH(DFI_ADDR_WIDTH),
        .DFI_BANK_WIDTH(DFI_BANK_WIDTH), .DFI_CTRL_WIDTH(DFI_CTRL_WIDTH),
        .DFI_CS_WIDTH(DFI_CS_WIDTH)
    ) u_fmt (
        .mc_clk(dfi_clk), .mc_rst_n(dfi_rstn), .memtype_i(memtype_i),
        .cmd_valid_i(cmd_valid_i && w_gate), .cmd_ready_o(w_fmt_ready),
        .cmd_op_i(w_op), .cmd_rank_i(w_rank), .cmd_bank_i(w_bank),
        .cmd_row_i(w_row), .cmd_col_i(w_col), .cmd_len_i('0),
        .rd_phase_i(rd_phase_i), .wr_phase_i(wr_phase_i),
        .dfi_address_o(dfi_address_o), .dfi_bank_o(dfi_bank_o),
        .dfi_cas_n_o(dfi_cas_n_o), .dfi_ras_n_o(dfi_ras_n_o), .dfi_we_n_o(dfi_we_n_o),
        .dfi_cs_n_o(dfi_cs_n_o), .dfi_odt_o(dfi_odt_o)
    );

    assign cmd_ready_o = w_fmt_ready && w_gate;   // pop FIFO only when allowed

    // DQ-occupancy pacing counter: loaded to COL_BURST_CYC-1 on an accepted
    // column command, read same-cycle via w_col_ok. COL_BURST_CYC==1 => loads 0
    // => never blocks (a column every cycle).
    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) begin
            r_col_pace <= '0;
        end else begin
            if (r_col_pace != '0) r_col_pace <= r_col_pace - 1'b1;
            if (w_fire && w_is_col) r_col_pace <= PCW'(COL_BURST_CYC - 1);
        end
    )

    // Fire strobes (registered 1 cycle to align with the formatter's registered
    // command outputs — the command lands on the bus the cycle after accept).
    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) begin
            wr_fire_o   <= 1'b0;
            rd_fire_o   <= 1'b0;
            fire_rank_o <= '0;
        end else begin
            wr_fire_o   <= w_fire && w_is_wr;
            rd_fire_o   <= w_fire && w_is_rd;
            fire_rank_o <= w_rank;
        end
    )

endmodule : pumice_dfi_cmd_path
