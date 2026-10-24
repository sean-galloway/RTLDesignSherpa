// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rv32i_imm_gen
// Purpose: RV32I immediate sign-extension unit for I/S/B/U/J formats.
//          Shared by kestrel and gatling.
//
// Documentation: projects/components/riscv-ip/common-rv32i/README.md
// Subsystem: riscv-ip/common-rv32i
//
// Author: sean galloway
// Created: 2026-10-06
//
// Notes:
//   - All five formats are built in parallel from the raw instruction bits
//     and one is picked by the major opcode (insn[6:2]) alone, so the
//     immediate is ready as early as the register-file read instead of
//     waiting on rv32i_decode's full opcode/funct3/funct7 truth table
//     (2026-10-20, the block-RAM critical path ran decode -> imm_sel ->
//     imm -> operand B in series).  The format is a function of the opcode
//     alone in RV32I; for encodings decode halts on, the value is unused.

`timescale 1ns / 1ps

module rv32i_imm_gen (
    input  logic [31:0] insn,
    output logic [31:0] imm
);

    localparam int IMM_I_SIGN_BITS   = 20;
    localparam int IMM_S_SIGN_BITS   = 20;
    localparam int IMM_B_SIGN_BITS   = 20;
    localparam int IMM_J_SIGN_BITS   = 12;
    localparam int IMM_U_LOW_BITS    = 12;
    localparam int IMM_B_J_LSB_BITS  = 1;

    // Major opcodes (insn[6:2]) that are not I-format
    localparam logic [4:0] OPC_STORE  = 5'b01000;
    localparam logic [4:0] OPC_BRANCH = 5'b11000;
    localparam logic [4:0] OPC_LUI    = 5'b01101;
    localparam logic [4:0] OPC_AUIPC  = 5'b00101;
    localparam logic [4:0] OPC_JAL    = 5'b11011;

    logic [31:0] imm_i, imm_s, imm_b, imm_u, imm_j;

    assign imm_i = {{IMM_I_SIGN_BITS{insn[31]}}, insn[31:20]};
    assign imm_s = {{IMM_S_SIGN_BITS{insn[31]}}, insn[31:25], insn[11:7]};
    assign imm_b = {{IMM_B_SIGN_BITS{insn[31]}}, insn[7], insn[30:25], insn[11:8],
                    {IMM_B_J_LSB_BITS{1'b0}}};
    assign imm_u = {insn[31:12], {IMM_U_LOW_BITS{1'b0}}};
    assign imm_j = {{IMM_J_SIGN_BITS{insn[31]}}, insn[19:12], insn[20], insn[30:21],
                    {IMM_B_J_LSB_BITS{1'b0}}};

    always_comb begin
        unique case (insn[6:2])
            OPC_STORE:          imm = imm_s;
            OPC_BRANCH:         imm = imm_b;
            OPC_LUI, OPC_AUIPC: imm = imm_u;
            OPC_JAL:            imm = imm_j;
            default:            imm = imm_i;   // OP-IMM, LOAD, JALR (and don't-cares)
        endcase
    end

endmodule : rv32i_imm_gen
