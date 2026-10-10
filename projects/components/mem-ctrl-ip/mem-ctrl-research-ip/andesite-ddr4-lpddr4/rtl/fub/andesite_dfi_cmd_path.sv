// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_dfi_cmd_path
// Purpose: DFI-clock-domain command formatter wrapper. Accepts the widened
//          scheduler command word {ap,col,row,bg,bank,rank,op}, presents each
//          accepted command to the P1 single-shot formatter for exactly one
//          cycle, and exposes the registered DFI 4.0 pin vector plus fire
//          strobes aligned with those registered pins. Structural holds
//          only (aligner readiness, staged write data); every JEDEC spacing
//          lives in the scheduler.
//
// Carried shape: scoria_dfi_cmd_path's registered pipeline, its read/write
// hold classes, and its fire-strobe contract -- WITHOUT the per-sub phase
// fan-out. DDR4 single-channel commands have no sub-word framing, and
// andesite's formatter slot is the P1 single-shot block (no valid/ready, no
// phases). The container widens scoria's word by bg[1:0] between row and
// bank: {ap,col,row,bg,bank,rank,op}.
//
// Documentation:
//   projects/components/mem-ctrl-ip/mem-ctrl-research-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//
// Author: sean galloway
// Created: 2026-10-05 (macro integration pass, TASK-016 t3)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module andesite_dfi_cmd_path
    import andesite_pkg::*;
#(
    parameter int NUM_RANKS  = 1,
    parameter int NUM_BANKS  = 8,
    parameter int NUM_BG     = 4,
    parameter int ROW_WIDTH  = 14,
    parameter int COL_WIDTH  = 10,
    parameter int ADDR_WIDTH = 18,
    parameter int BANK_WIDTH = $clog2(NUM_BANKS),
    parameter int BG_WIDTH   = 2,
    // Optional issued-command-history scoreboard (audit-only). Carried as a
    // parameter for parity with the scoria shape; the DFI-boundary audit is
    // not instantiated here in v1 -- the macro's armed checker already
    // audits the stream, and adding the boundary copy back is a layer-task
    // decision, not this block's.
    parameter int CMD_HISTORY_EN = 0,
    // Derived widths live in the parameter list (not body localparams) because
    // the port list below uses CMD_DW and RKW -- iverilog and the repo's
    // declared-before-use gate reject body localparams referenced from ports.
    parameter int RKW    = (NUM_RANKS > 1) ? $clog2(NUM_RANKS) : 1,
    parameter int BKW    = $clog2(NUM_BANKS),
    parameter int BGW    = (NUM_BG > 1) ? $clog2(NUM_BG) : 1,
    parameter int CMD_DW = $bits(dram_op_e) + RKW + BKW + BGW
                         + ROW_WIDTH + COL_WIDTH + 1
) (
    input  logic                    dfi_clk,
    input  logic                    dfi_rstn,

    input  memtype_e                memtype_i,
    input  logic                    parity_en_i,

    // widened scheduler command word, valid/ready
    input  logic                    cmd_valid_i,
    output logic                    cmd_ready_o,
    input  logic [CMD_DW-1:0]       cmd_data_i,

    // structural backpressure (from the aligner / the staged write token)
    input  logic                    rd_op_ready_i,
    input  logic                    wr_op_ready_i,

    // fire strobes, registered to align with the registered pin vector
    output logic                    wr_fire_o,
    output logic                    rd_fire_o,
    output logic [RKW-1:0]          fire_rank_o,
    // write accepted (pop the staged write-data token)
    output logic                    wr_accept_o,

    // DFI 4.0 command surface (registered)
    output logic [ADDR_WIDTH-1:0]   dfi_address_o,
    output logic [BANK_WIDTH-1:0]   dfi_bank_o,
    output logic [BG_WIDTH-1:0]     dfi_bg_o,
    output logic                    dfi_act_n_o,
    output logic                    dfi_ras_n_o,
    output logic                    dfi_cas_n_o,
    output logic                    dfi_we_n_o,
    output logic [NUM_RANKS-1:0]    dfi_cs_o,
    output logic                    dfi_cke_o,
    output logic                    dfi_parity_in_o
);

    // ---- unpack {ap, col, row, bg, bank, rank, op} ------------------------
    logic                      w_ap;
    logic [COL_WIDTH-1:0]      w_col;
    logic [ROW_WIDTH-1:0]      w_row;
    logic [BGW-1:0]            w_bg;
    logic [BKW-1:0]            w_bank;
    logic [RKW-1:0]            w_rank;
    dram_op_e                  w_op;
    assign {w_ap, w_col, w_row, w_bg, w_bank, w_rank, w_op} = cmd_data_i;

    wire w_is_rd = (w_op == OP_RD) || (w_op == OP_RDA);
    wire w_is_wr = (w_op == OP_WR) || (w_op == OP_WRA);

    // ---- structural holds -------------------------------------------------
    // A read is held only while the aligner has no slot; a write only until
    // its data token is staged. Nothing else ever stalls -- this block never
    // inserts an idle cycle (scoria TASK-007's contract, carried).
    assign cmd_ready_o = !(w_is_rd && !rd_op_ready_i)
                      && !(w_is_wr && !wr_op_ready_i);
    wire w_accept = cmd_valid_i && cmd_ready_o;
    assign wr_accept_o = w_accept && w_is_wr;

    // ---- present exactly one cycle ----------------------------------------
    // The P1 formatter registers whatever it sees every clock, so the accepted
    // word is presented for exactly one cycle and OP_NOP rides between
    // commands (the formatter's NOP posture is all-deselected).
    //
    // Address routing by op class:
    //  * MRS / ZQCL: the payload (MR image / ZQCL's A10) rides the stream ROW
    //    field -- the arbiter's init-forwarding path puts init_cmd_row there.
    //    Scoria's formatter documented the identical convention (MR data on
    //    the row field, never the truncated column).
    //  * RD/RDA/WR/WRA: the auto-precharge flag is address bit 10 (JESD79-4
    //    A10); the carried AP bit merges in. The P1 formatter takes AP as an
    //    address input, not a pin.
    //  * PREA forces A10, PRE clears it.
    dram_op_e                 f_op;
    logic [BANK_WIDTH-1:0]    f_bank;
    logic [BG_WIDTH-1:0]      f_bg;
    logic [ADDR_WIDTH-1:0]    f_row, f_col;
    logic [RKW-1:0]           f_rank;
    always_comb begin
        f_op   = OP_NOP;
        f_bank = '0;
        f_bg   = '0;
        f_row  = '0;
        f_col  = '0;
        f_rank = '0;
        if (w_accept) begin
            f_op   = w_op;
            f_bank = BANK_WIDTH'(w_bank);
            f_bg   = BG_WIDTH'(w_bg);
            f_row  = ADDR_WIDTH'(w_row);
            unique case (w_op)
                OP_MRS, OP_ZQCL:
                    f_col = ADDR_WIDTH'(w_row);
                OP_RD, OP_RDA, OP_WR, OP_WRA:
                    f_col = ADDR_WIDTH'(w_col) | (ADDR_WIDTH'(w_ap) << 10);
                OP_PREA:
                    f_col = ADDR_WIDTH'(1 << 10);
                OP_PRE:
                    f_col = ADDR_WIDTH'(w_col) & ~(ADDR_WIDTH'(1) << 10);
                default:
                    f_col = ADDR_WIDTH'(w_col);
            endcase
            f_rank = w_rank;
        end
    end

    andesite_dfi_cmd_formatter #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .BANK_WIDTH (BANK_WIDTH),
        .BG_WIDTH   (BG_WIDTH),
        .RANKS      (NUM_RANKS),
        .RANK_W     (RKW)
    ) u_formatter (
        .clk           (dfi_clk),
        .rst_n         (dfi_rstn),
        .op_i          (f_op),
        .bank_i        (f_bank),
        .bg_i          (f_bg),
        .row_i         (f_row),
        .col_i         (f_col),
        .rank_i        (f_rank),
        .memtype_i     (memtype_i),
        .parity_en_i   (parity_en_i),
        .dfi_cs        (dfi_cs_o),
        .dfi_act_n     (dfi_act_n_o),
        .dfi_ras_n     (dfi_ras_n_o),
        .dfi_cas_n     (dfi_cas_n_o),
        .dfi_we_n      (dfi_we_n_o),
        .dfi_bank      (dfi_bank_o),
        .dfi_bg        (dfi_bg_o),
        .dfi_address   (dfi_address_o),
        .dfi_cke       (dfi_cke_o),
        .dfi_parity_in (dfi_parity_in_o)
    );

    // ---- fire strobes: registered one cycle, aligned with the registered
    // pin vector the serializer/aligner consume (scoria's contract).
    `ALWAYS_FF_RST(dfi_clk, dfi_rstn,
        if (`RST_ASSERTED(dfi_rstn)) begin
            wr_fire_o   <= 1'b0;
            rd_fire_o   <= 1'b0;
            fire_rank_o <= '0;
        end else begin
            wr_fire_o   <= w_accept && w_is_wr;
            rd_fire_o   <= w_accept && w_is_rd;
            fire_rank_o <= w_rank;
        end
    )

endmodule : andesite_dfi_cmd_path
