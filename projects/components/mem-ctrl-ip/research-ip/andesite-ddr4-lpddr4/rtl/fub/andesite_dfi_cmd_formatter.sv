// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: andesite_dfi_cmd_formatter
// Purpose: Internal-opcode to DFI 4.0 DDR4 command-pin encoding
//
// Documentation:
//   projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/docs/andesite_mas/
//   ch02_blocks/01_cmd_formatter.md (Table 2.2 ports; Table 2.3 truth table,
//   the kmap citation anchor)
//
// The truth table is the contract (docs/kmaps/generated/01_ddr4_command_table.md
// derives from it and the workbook diffs this RTL against the minimal cover).
// AP (A10) is an address input, not a pin: RDA/WRA/PREA/ZQCL share the
// RD/WR/PRE/ZQ pin encodings with col_i[10] set. Signal names follow the
// DFI 4.0 catalog (*_cs, no *_cs_n; TASK-005 study). LPDDR4 drives the DDR4
// pins to the deselected idle posture; the CA-bus submodule is the
// TASK-008 follow-on, not a half-built branch.
//
// Author: sean galloway
// Created: 2026-10-04

`timescale 1ns / 1ps

module andesite_dfi_cmd_formatter #(
    parameter int ADDR_WIDTH = 18,
    parameter int BANK_WIDTH = 2,
    parameter int BG_WIDTH   = 2,
    parameter int RANKS      = 1,
    // RANKS==1 still needs a one-bit index port.
    parameter int RANK_W     = (RANKS > 1) ? $clog2(RANKS) : 1
) (
    input  logic                      clk,
    input  logic                      rst_n,

    input  andesite_pkg::dram_op_e    op_i,
    input  logic [BANK_WIDTH-1:0]     bank_i,
    input  logic [BG_WIDTH-1:0]       bg_i,
    input  logic [ADDR_WIDTH-1:0]     row_i,
    input  logic [ADDR_WIDTH-1:0]     col_i,
    input  logic [RANK_W-1:0]         rank_i,
    input  andesite_pkg::memtype_e    memtype_i,
    input  logic                      parity_en_i,

    output logic [RANKS-1:0]          dfi_cs,        // active low; v4.0 name
    output logic                      dfi_act_n,
    output logic                      dfi_ras_n,
    output logic                      dfi_cas_n,
    output logic                      dfi_we_n,
    output logic [BANK_WIDTH-1:0]     dfi_bank,
    output logic [BG_WIDTH-1:0]       dfi_bg,
    output logic [ADDR_WIDTH-1:0]     dfi_address,
    output logic                      dfi_cke,
    output logic                      dfi_parity_in
);

    import andesite_pkg::*;

    // Combinational encode per the anchored truth table. Default is the
    // NOP/DES posture (all command pins high).
    logic                    c_act_n, c_ras_n, c_cas_n, c_we_n;
    logic [RANKS-1:0]        c_cs;
    logic                    w_ddr4_en;

    always_comb begin
        w_ddr4_en = (memtype_i == MEMTYPE_DDR4);

        c_act_n = 1'b1;
        c_ras_n = 1'b1;
        c_cas_n = 1'b1;
        c_we_n  = 1'b1;

        if (w_ddr4_en) begin
            unique case (op_i)
                OP_ACT:                c_act_n = 1'b0;
                OP_RD, OP_RDA:         c_cas_n = 1'b0;
                OP_WR, OP_WRA: begin
                    c_cas_n = 1'b0;
                    c_we_n  = 1'b0;
                end
                OP_MRS: begin
                    c_act_n = 1'b0;
                    c_ras_n = 1'b0;
                    c_cas_n = 1'b0;
                    c_we_n  = 1'b0;
                end
                OP_REF: begin
                    c_act_n = 1'b0;
                    c_ras_n = 1'b0;
                    c_cas_n = 1'b0;
                end
                OP_PRE, OP_PREA: begin
                    c_ras_n = 1'b0;
                    c_we_n  = 1'b0;
                end
                OP_ZQCS, OP_ZQCL: begin
                    c_we_n  = 1'b0;
                end
                // REFPB/SREFE/SREFX/DPDE/OP_MPC: no DDR4 pin encoding (REFPB
                // and MPC are LPDDR4-breadth; SREF/DPD ride the dormant pair).
                default: ;
            endcase
        end

        // Chip select: one-hot-low decode of the rank index. Non-DDR4
        // deselects the DDR4 bus entirely (LPDDR4 breadth: CA-bus path).
        c_cs = {RANKS{1'b1}};
        if (w_ddr4_en)
            c_cs[rank_i] = 1'b0;
    end

    // Registered pipeline (MAS Timing section: one stage).
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            dfi_cs        <= {RANKS{1'b1}};
            dfi_act_n     <= 1'b1;
            dfi_ras_n     <= 1'b1;
            dfi_cas_n     <= 1'b1;
            dfi_we_n      <= 1'b1;
            dfi_bank      <= '0;
            dfi_bg        <= '0;
            dfi_address   <= '0;
            dfi_cke       <= 1'b0;
            dfi_parity_in <= 1'b0;
        end else begin
            dfi_cs        <= c_cs;
            dfi_act_n     <= c_act_n;
            dfi_ras_n     <= c_ras_n;
            dfi_cas_n     <= c_cas_n;
            dfi_we_n      <= c_we_n;
            dfi_bank      <= bank_i;
            dfi_bg        <= bg_i;
            // ACT carries the row; every other command carries col_i
            // (column address for RD/WR, MR data for MRS, A10 variants
            // for PREA/RDA/WRA/ZQCL).
            dfi_address   <= (op_i == OP_ACT) ? row_i : col_i;
            dfi_cke       <= (memtype_i == MEMTYPE_DDR4);
            // CA parity over the command pins plus the bits that travel on
            // the same edge. Qualified by parity_en_i (set by the init
            // sequence per MAS ch02 02_init_sequencer).
            dfi_parity_in <= parity_en_i &
                             (^{c_act_n, c_ras_n, c_cas_n, c_we_n,
                                bank_i, bg_i,
                                ((op_i == OP_ACT) ? row_i : col_i)});
        end
    end

endmodule : andesite_dfi_cmd_formatter
