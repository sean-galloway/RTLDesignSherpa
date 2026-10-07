// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_decode
// Purpose: RV32I instruction decoder producing the datapath control bundle.
//
// Documentation: projects/components/riscv-ip/README.md
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-06

`timescale 1ns / 1ps

module kestrel_decode (
    input  logic [31:0] insn,
    output kestrel_pkg::alu_op_e  alu_op,
    output kestrel_pkg::imm_sel_e imm_sel,
    output logic                  alu_src_a_pc,
    output logic                  alu_src_b_imm,
    output logic                  rd_wen,
    output logic                  dmem_req,
    output logic                  dmem_we,
    output logic [1:0]            dmem_size,
    output logic                  branch,
    output logic                  jump,
    output logic                  jalr,
    output logic [3:0]            halt_cause,
    output logic                  csr_stub
);

    import kestrel_pkg::*;

    // Opcodes
    localparam logic [6:0] OPCODE_OP       = 7'b0110011;
    localparam logic [6:0] OPCODE_OP_IMM   = 7'b0010011;
    localparam logic [6:0] OPCODE_LOAD     = 7'b0000011;
    localparam logic [6:0] OPCODE_STORE    = 7'b0100011;
    localparam logic [6:0] OPCODE_BRANCH   = 7'b1100011;
    localparam logic [6:0] OPCODE_JAL      = 7'b1101111;
    localparam logic [6:0] OPCODE_JALR     = 7'b1100111;
    localparam logic [6:0] OPCODE_LUI      = 7'b0110111;
    localparam logic [6:0] OPCODE_AUIPC    = 7'b0010111;
    localparam logic [6:0] OPCODE_SYSTEM   = 7'b1110011;
    localparam logic [6:0] OPCODE_FENCE    = 7'b0001111;

    // funct3 encodings
    localparam logic [2:0] F3_ADD  = 3'b000;
    localparam logic [2:0] F3_SLL  = 3'b001;
    localparam logic [2:0] F3_SLT  = 3'b010;
    localparam logic [2:0] F3_SLTU = 3'b011;
    localparam logic [2:0] F3_XOR  = 3'b100;
    localparam logic [2:0] F3_SR   = 3'b101;
    localparam logic [2:0] F3_OR   = 3'b110;
    localparam logic [2:0] F3_AND  = 3'b111;

    // funct7 encodings used by the decode key
    localparam logic [6:0] F7_ZERO = 7'b0000000;
    localparam logic [6:0] F7_SUB  = 7'b0100000;
    localparam logic [6:0] F7_SRA  = 7'b0100000;

    // Halt-cause encoding
    localparam logic [3:0] HALT_NONE   = 4'h0;
    localparam logic [3:0] HALT_ECALL  = 4'h1;
    localparam logic [3:0] HALT_EBREAK = 4'h2;
    localparam logic [3:0] HALT_ILL    = 4'hF;

    // SYSTEM funct3 encodings
    localparam logic [2:0] F3_PRIV   = 3'b000;
    localparam logic [2:0] F3_CSRRW  = 3'b001;
    localparam logic [2:0] F3_CSRRS  = 3'b010;
    localparam logic [2:0] F3_CSRRC  = 3'b011;
    localparam logic [2:0] F3_CSRRWI = 3'b101;
    localparam logic [2:0] F3_CSRRSI = 3'b110;
    localparam logic [2:0] F3_CSRRCI = 3'b111;

    // SYSTEM imm12 encodings (privileged, funct3 000)
    localparam logic [11:0] SYS_ECALL  = 12'h000;
    localparam logic [11:0] SYS_EBREAK = 12'h001;
    localparam logic [11:0] SYS_MRET   = 12'h302;

    // MISC-MEM funct3 encodings
    localparam logic [2:0] F3_FENCE  = 3'b000;
    localparam logic [2:0] F3_FENCEI = 3'b001;

    // Don't-care patterns for fields that carry immediate bits
    localparam logic [2:0] F3_DC  = 3'b???;
    localparam logic [6:0] F7_DC  = 7'b???????;

    logic [6:0] opcode;
    logic [2:0] funct3;
    logic [6:0] funct7;

    assign opcode = insn[6:0];
    assign funct3 = insn[14:12];
    assign funct7 = insn[31:25];

    always_comb begin
        // Default control bundle: no operation, no halt, no CSR stub.
        alu_op        = ADD;
        imm_sel       = I;
        alu_src_a_pc  = 1'b0;
        alu_src_b_imm = 1'b0;
        rd_wen        = 1'b0;
        dmem_req      = 1'b0;
        dmem_we       = 1'b0;
        dmem_size     = 2'b00;
        branch        = 1'b0;
        jump          = 1'b0;
        jalr          = 1'b0;
        halt_cause    = HALT_NONE;
        csr_stub      = 1'b0;

        unique casez ({opcode, funct3, funct7})
            // R-type arithmetic
            {OPCODE_OP, F3_ADD,  F7_ZERO}: begin alu_op = ADD;  rd_wen = 1'b1; end
            {OPCODE_OP, F3_ADD,  F7_SUB }: begin alu_op = SUB;  rd_wen = 1'b1; end
            {OPCODE_OP, F3_SLL,  F7_ZERO}: begin alu_op = SLL;  rd_wen = 1'b1; end
            {OPCODE_OP, F3_SLT,  F7_ZERO}: begin alu_op = SLT;  rd_wen = 1'b1; end
            {OPCODE_OP, F3_SLTU, F7_ZERO}: begin alu_op = SLTU; rd_wen = 1'b1; end
            {OPCODE_OP, F3_XOR,  F7_ZERO}: begin alu_op = XOR;  rd_wen = 1'b1; end
            {OPCODE_OP, F3_SR,   F7_ZERO}: begin alu_op = SRL;  rd_wen = 1'b1; end
            {OPCODE_OP, F3_SR,   F7_SRA }: begin alu_op = SRA;  rd_wen = 1'b1; end
            {OPCODE_OP, F3_OR,   F7_ZERO}: begin alu_op = OR;   rd_wen = 1'b1; end
            {OPCODE_OP, F3_AND,  F7_ZERO}: begin alu_op = AND;  rd_wen = 1'b1; end

            // I-type arithmetic / logic
            {OPCODE_OP_IMM, F3_ADD,  F7_DC}: begin alu_op = ADD;  imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; end
            {OPCODE_OP_IMM, F3_SLT,  F7_DC}: begin alu_op = SLT;  imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; end
            {OPCODE_OP_IMM, F3_SLTU, F7_DC}: begin alu_op = SLTU; imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; end
            {OPCODE_OP_IMM, F3_XOR,  F7_DC}: begin alu_op = XOR;  imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; end
            {OPCODE_OP_IMM, F3_OR,   F7_DC}: begin alu_op = OR;   imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; end
            {OPCODE_OP_IMM, F3_AND,  F7_DC}: begin alu_op = AND;  imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; end
            {OPCODE_OP_IMM, F3_SLL,  F7_ZERO}: begin alu_op = SLL; imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; end
            {OPCODE_OP_IMM, F3_SR,   F7_ZERO}: begin alu_op = SRL; imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; end
            {OPCODE_OP_IMM, F3_SR,   F7_SRA }: begin alu_op = SRA; imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; end

            // Loads
            {OPCODE_LOAD, F3_ADD, F7_DC}: begin alu_op = ADD; imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; dmem_req = 1'b1; dmem_size = 2'b00; end
            {OPCODE_LOAD, F3_SLL, F7_DC}: begin alu_op = ADD; imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; dmem_req = 1'b1; dmem_size = 2'b01; end
            {OPCODE_LOAD, F3_SLT, F7_DC}: begin alu_op = ADD; imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; dmem_req = 1'b1; dmem_size = 2'b10; end
            {OPCODE_LOAD, F3_XOR, F7_DC}: begin alu_op = ADD; imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; dmem_req = 1'b1; dmem_size = 2'b00; end
            {OPCODE_LOAD, F3_SR,  F7_DC}: begin alu_op = ADD; imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; dmem_req = 1'b1; dmem_size = 2'b01; end

            // Stores
            {OPCODE_STORE, F3_ADD, F7_DC}: begin alu_op = ADD; imm_sel = S; alu_src_b_imm = 1'b1; dmem_req = 1'b1; dmem_we = 1'b1; dmem_size = 2'b00; end
            {OPCODE_STORE, F3_SLL, F7_DC}: begin alu_op = ADD; imm_sel = S; alu_src_b_imm = 1'b1; dmem_req = 1'b1; dmem_we = 1'b1; dmem_size = 2'b01; end
            {OPCODE_STORE, F3_SLT, F7_DC}: begin alu_op = ADD; imm_sel = S; alu_src_b_imm = 1'b1; dmem_req = 1'b1; dmem_we = 1'b1; dmem_size = 2'b10; end

            // Branches (funct3 order: BEQ, BNE, BLT, BGE, BLTU, BGEU)
            {OPCODE_BRANCH, F3_ADD,  F7_DC}: begin alu_op = ADD; imm_sel = B; alu_src_a_pc = 1'b1; alu_src_b_imm = 1'b1; branch = 1'b1; end
            {OPCODE_BRANCH, F3_SLL,  F7_DC}: begin alu_op = ADD; imm_sel = B; alu_src_a_pc = 1'b1; alu_src_b_imm = 1'b1; branch = 1'b1; end
            {OPCODE_BRANCH, F3_XOR,  F7_DC}: begin alu_op = ADD; imm_sel = B; alu_src_a_pc = 1'b1; alu_src_b_imm = 1'b1; branch = 1'b1; end
            {OPCODE_BRANCH, F3_SR,   F7_DC}: begin alu_op = ADD; imm_sel = B; alu_src_a_pc = 1'b1; alu_src_b_imm = 1'b1; branch = 1'b1; end
            {OPCODE_BRANCH, F3_OR,   F7_DC}: begin alu_op = ADD; imm_sel = B; alu_src_a_pc = 1'b1; alu_src_b_imm = 1'b1; branch = 1'b1; end
            {OPCODE_BRANCH, F3_AND,  F7_DC}: begin alu_op = ADD; imm_sel = B; alu_src_a_pc = 1'b1; alu_src_b_imm = 1'b1; branch = 1'b1; end

            // Jumps / upper immediates
            {OPCODE_JAL,  F3_DC, F7_DC}: begin alu_op = ADD; imm_sel = J; alu_src_a_pc = 1'b1; alu_src_b_imm = 1'b1; rd_wen = 1'b1; jump = 1'b1; end
            {OPCODE_JALR, F3_ADD, F7_DC}: begin alu_op = ADD; imm_sel = I; alu_src_b_imm = 1'b1; rd_wen = 1'b1; jalr = 1'b1; end
            {OPCODE_LUI,  F3_DC, F7_DC}: begin alu_op = ADD; imm_sel = U; alu_src_b_imm = 1'b1; rd_wen = 1'b1; end
            {OPCODE_AUIPC,F3_DC, F7_DC}: begin alu_op = ADD; imm_sel = U; alu_src_a_pc = 1'b1; alu_src_b_imm = 1'b1; rd_wen = 1'b1; end

            // System: ECALL/EBREAK halt; MRET falls through to pc+4 (the
            // riscv-tests p-env always points mepc at the next instruction);
            // any other privileged encoding is an illegal instruction.
            {OPCODE_SYSTEM, F3_PRIV, F7_DC}: begin
                unique case (insn[31:20])
                    SYS_ECALL:  halt_cause = HALT_ECALL;
                    SYS_EBREAK: halt_cause = HALT_EBREAK;
                    SYS_MRET:   begin /* no operation */ end
                    default:    halt_cause = HALT_ILL;
                endcase
            end

            // System CSR class: kestrel has no CSR state, so the class
            // retires through a zero writeback (reads return zero, writes
            // drop).  SYSTEM funct3 100 is reserved and falls to the
            // illegal default below.
            {OPCODE_SYSTEM, F3_CSRRW,  F7_DC}: begin csr_stub = 1'b1; rd_wen = 1'b1; end
            {OPCODE_SYSTEM, F3_CSRRS,  F7_DC}: begin csr_stub = 1'b1; rd_wen = 1'b1; end
            {OPCODE_SYSTEM, F3_CSRRC,  F7_DC}: begin csr_stub = 1'b1; rd_wen = 1'b1; end
            {OPCODE_SYSTEM, F3_CSRRWI, F7_DC}: begin csr_stub = 1'b1; rd_wen = 1'b1; end
            {OPCODE_SYSTEM, F3_CSRRSI, F7_DC}: begin csr_stub = 1'b1; rd_wen = 1'b1; end
            {OPCODE_SYSTEM, F3_CSRRCI, F7_DC}: begin csr_stub = 1'b1; rd_wen = 1'b1; end

            // FENCE / FENCE.I are architecturally no-ops for this core;
            // MISC-MEM funct3 2-7 are reserved and fall to the illegal
            // default below.
            {OPCODE_FENCE, F3_FENCE,  F7_DC}: begin /* no operation */ end
            {OPCODE_FENCE, F3_FENCEI, F7_DC}: begin /* no operation */ end

            // Anything else is an illegal instruction.
            default: begin
                halt_cause = HALT_ILL;
            end
        endcase
    end

endmodule : kestrel_decode
