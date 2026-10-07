// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_imm_gen
// Purpose: RV32I immediate sign-extension unit for I/S/B/U/J formats.
//
// Documentation: projects/components/riscv-ip/README.md
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-06

`timescale 1ns / 1ps

module kestrel_imm_gen (
    input  logic [31:0]          insn,
    input  kestrel_pkg::imm_sel_e sel,
    output logic [31:0]          imm
);

    import kestrel_pkg::*;

    localparam int XLEN              = 32;
    localparam int IMM_I_SIGN_BITS   = 20;
    localparam int IMM_S_SIGN_BITS   = 20;
    localparam int IMM_B_SIGN_BITS   = 20;
    localparam int IMM_J_SIGN_BITS   = 12;
    localparam int IMM_U_LOW_BITS    = 12;
    localparam int IMM_B_J_LSB_BITS  = 1;
    localparam int IMM_S_LO_BITS     = 5;
    localparam int IMM_S_HI_BITS     = 7;
    localparam int IMM_B_MID_BITS    = 6;
    localparam int IMM_B_LO_BITS     = 4;
    localparam int IMM_J_MID_BITS    = 8;
    localparam int IMM_J_HI_BITS     = 10;

    always_comb begin
        unique case (sel)
            I: imm = {{IMM_I_SIGN_BITS{insn[31]}}, insn[31:20]};
            S: imm = {{IMM_S_SIGN_BITS{insn[31]}},
                      insn[31:25],
                      insn[11:7]};
            B: imm = {{IMM_B_SIGN_BITS{insn[31]}},
                      insn[7],
                      insn[30:25],
                      insn[11:8],
                      {IMM_B_J_LSB_BITS{1'b0}}};
            U: imm = {insn[31:12], {IMM_U_LOW_BITS{1'b0}}};
            J: imm = {{IMM_J_SIGN_BITS{insn[31]}},
                      insn[19:12],
                      insn[20],
                      insn[30:21],
                      {IMM_B_J_LSB_BITS{1'b0}}};
            default: imm = '0;
        endcase
    end

endmodule : kestrel_imm_gen
