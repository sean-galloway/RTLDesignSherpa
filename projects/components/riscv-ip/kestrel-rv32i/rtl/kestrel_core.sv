// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_core
// Purpose: Single-cycle RV32I core — PC register, decode truth table,
//          immediate generator, ALU, register file, writeback, next-PC mux,
//          halt, and first-class RVFI retire ports.
//
// Documentation: projects/components/riscv-ip/README.md
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-06

`timescale 1ns / 1ps

`include "reset_defs.svh"

module kestrel_core #(
    parameter logic [31:0] RESET_ADDR = 32'h0000_0000
) (
    input  logic        clk,
    input  logic        rst_n,
    output logic [31:0] imem_addr,
    input  logic [31:0] imem_rdata,
    output logic        dmem_req,
    output logic [31:0] dmem_addr,
    input  logic [31:0] dmem_rdata,
    output logic [3:0]  dmem_wstrb,
    output logic [31:0] dmem_wdata,
    output logic        halt,
    output logic [3:0]  halt_cause,
    output logic        rvfi_valid,
    output logic [63:0] rvfi_order,
    output logic [31:0] rvfi_pc_rdata,
    output logic [31:0] rvfi_pc_wdata,
    output logic [31:0] rvfi_insn,
    output logic        rvfi_trap,
    output logic [4:0]  rvfi_rs1_addr,
    output logic [4:0]  rvfi_rs2_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,
    output logic [4:0]  rvfi_rd_addr,
    output logic [31:0] rvfi_rd_wdata,
    output logic [31:0] rvfi_mem_addr,
    output logic [3:0]  rvfi_mem_rmask,
    output logic [3:0]  rvfi_mem_wmask,
    output logic [31:0] rvfi_mem_rdata,
    output logic [31:0] rvfi_mem_wdata
);

    import kestrel_pkg::*;

    localparam logic [31:0] PC_INCR     = 32'd4;
    localparam logic [6:0]  OPCODE_LUI  = 7'b0110111;

    // funct3 encodings selecting the branch condition
    localparam logic [2:0] F3_BEQ       = 3'b000;
    localparam logic [2:0] F3_BNE       = 3'b001;
    localparam logic [2:0] F3_BLT       = 3'b100;
    localparam logic [2:0] F3_BGE       = 3'b101;
    localparam logic [2:0] F3_BLTU      = 3'b110;
    localparam logic [2:0] F3_BGEU      = 3'b111;

    // The PC register and the RVFI retirement counter are the only state
    // besides the register file (Task 8 adds the halt holding register).
    logic [31:0] pc;
    logic [31:0] next_pc;
    logic [63:0] retire_count;

    // Fetch
    logic [31:0] insn;
    logic [6:0]  opcode;
    logic [2:0]  funct3;

    assign imem_addr = pc;
    assign insn      = imem_rdata;
    assign opcode    = insn[6:0];
    assign funct3    = insn[14:12];

    // Decode truth table (control bundle only; no state).
    alu_op_e    alu_op;
    imm_sel_e   imm_sel;
    logic       alu_src_a_pc;
    logic       alu_src_b_imm;
    logic       rd_wen;
    logic       branch;
    logic       jump;
    logic       jalr;
    logic [3:0] dec_halt_cause;

    kestrel_decode u_decode (
        .insn          (insn),
        .alu_op        (alu_op),
        .imm_sel       (imm_sel),
        .alu_src_a_pc  (alu_src_a_pc),
        .alu_src_b_imm (alu_src_b_imm),
        .rd_wen        (rd_wen),
        .dmem_req      (),
        .dmem_we       (),
        .dmem_size     (),
        .branch        (branch),
        .jump          (jump),
        .jalr          (jalr),
        .halt_cause    (dec_halt_cause)
    );

    // Immediate generator.
    logic [31:0] imm;

    kestrel_imm_gen u_imm_gen (
        .insn (insn),
        .sel  (imm_sel),
        .imm  (imm)
    );

    // Register file: combinational reads, single synchronous write, x0 tied.
    logic [31:0] rs1_data;
    logic [31:0] rs2_data;
    logic [31:0] rd_wdata;

    kestrel_regfile u_regfile (
        .clk      (clk),
        .rst_n    (rst_n),
        .rs1_addr (insn[19:15]),
        .rs1_data (rs1_data),
        .rs2_addr (insn[24:20]),
        .rs2_data (rs2_data),
        .rd_addr  (insn[11:7]),
        .rd_data  (rd_wdata),
        .rd_wen   (rd_wen)
    );

    // Source muxes: PC vs rs1, immediate vs rs2.
    logic [31:0] alu_src_a;
    logic [31:0] alu_src_b;

    assign alu_src_a = alu_src_a_pc  ? pc       : rs1_data;
    assign alu_src_b = alu_src_b_imm ? imm      : rs2_data;

    // ALU: datapath arithmetic only. The eq/lt/ltu flags are deliberately
    // left unconnected — with src_a=PC for branches they would compare
    // pc against imm, so branch decisions come from the dedicated
    // comparator below (Task 4 review ruling, SDD ledger).
    logic [31:0] alu_y;

    kestrel_alu u_alu (
        .op  (alu_op),
        .a   (alu_src_a),
        .b   (alu_src_b),
        .y   (alu_y),
        .eq  (),
        .lt  (),
        .ltu ()
    );

    // Writeback: LUI takes its immediate straight from imm_gen (the ALU is
    // not involved in U-immediates); AUIPC reaches the ALU with src_a=PC and
    // uses the ALU result here.
    assign rd_wdata = (opcode == OPCODE_LUI) ? imm : alu_y;

    // Dedicated branch comparator: eq/lt/ltu computed from rs1_data/rs2_data
    // with the funct3 condition select, in parallel with the ALU computing
    // the pc+imm target. Wired now (ruling above); first exercised by the
    // Task 6 branch programs.
    logic cmp_eq;
    logic cmp_lt;
    logic cmp_ltu;
    logic branch_cond;
    logic branch_taken;

    assign cmp_eq  = (rs1_data == rs2_data);
    assign cmp_lt  = ($signed(rs1_data) < $signed(rs2_data));
    assign cmp_ltu = (rs1_data < rs2_data);

    always_comb begin
        unique case (funct3)
            F3_BEQ:  branch_cond = cmp_eq;
            F3_BNE:  branch_cond = ~cmp_eq;
            F3_BLT:  branch_cond = cmp_lt;
            F3_BGE:  branch_cond = ~cmp_lt;
            F3_BLTU: branch_cond = cmp_ltu;
            F3_BGEU: branch_cond = ~cmp_ltu;
            default: branch_cond = 1'b0;
        endcase
    end

    assign branch_taken = branch & branch_cond;

    // Next-PC mux. Branches/jumps are wired now; this slice's programs are
    // straight-line and Task 6 brings their golden vectors.
    always_comb begin
        if (jump) begin
            next_pc = jalr ? (rs1_data + imm) : (pc + imm);
        end else if (branch_taken) begin
            next_pc = pc + imm;
        end else begin
            next_pc = pc + PC_INCR;
        end
    end

    // dmem is tied to harmless defaults: loads/stores land in Task 7.
    assign dmem_req   = 1'b0;
    assign dmem_addr  = '0;
    assign dmem_wstrb = '0;
    assign dmem_wdata = '0;

    // Halt is combinational from decode in this slice; Task 8 adds the
    // holding register that keeps halt raised after the decode input clears.
    assign halt       = |dec_halt_cause;
    assign halt_cause = dec_halt_cause;

    // PC register: hold on halt, run otherwise.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            pc <= RESET_ADDR;
        end else begin
            pc <= halt ? pc : next_pc;
        end
    )

    // RVFI retirement order: 0, 1, 2, ... one per retired instruction.
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            retire_count <= '0;
        end else begin
            if (rvfi_valid) begin
                retire_count <= retire_count + 64'd1;
            end
        end
    )

    // RVFI aggregation. rd fields are zeroed when decode is not writing a
    // register; mem fields are zero until Task 7 populates them; rs fields
    // always reflect the register-file read ports (x0 reads return 0
    // naturally because the regfile discards x0 writes).
    assign rvfi_valid     = rst_n & ~halt;
    assign rvfi_order     = retire_count;
    assign rvfi_pc_rdata  = pc;
    assign rvfi_pc_wdata  = next_pc;
    assign rvfi_insn      = insn;
    assign rvfi_trap      = 1'b0;
    assign rvfi_rs1_addr  = insn[19:15];
    assign rvfi_rs2_addr  = insn[24:20];
    assign rvfi_rs1_rdata = rs1_data;
    assign rvfi_rs2_rdata = rs2_data;
    assign rvfi_rd_addr   = rd_wen ? insn[11:7] : 5'd0;
    assign rvfi_rd_wdata  = rd_wen ? rd_wdata  : 32'd0;
    assign rvfi_mem_addr  = 32'd0;
    assign rvfi_mem_rmask = 4'd0;
    assign rvfi_mem_wmask = 4'd0;
    assign rvfi_mem_rdata = 32'd0;
    assign rvfi_mem_wdata = 32'd0;

endmodule : kestrel_core
