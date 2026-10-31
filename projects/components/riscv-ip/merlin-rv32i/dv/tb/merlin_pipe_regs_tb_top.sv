// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: merlin_pipe_regs_tb_top
// Purpose: Thin cocotb wrapper that instantiates each of the four merlin
//          pipeline registers and breaks their packed-struct ports into flat
//          scalar vectors.  cocotb drives the flat ports; the wrapper
//          assembles/disassembles the merlin_pkg structs for the DUTs.
//
//          Per-register stall and flush controls let the test exercise each
//          stage boundary independently with a single Verilator build.
//
// Documentation: projects/components/riscv-ip/merlin-rv32i/PRD.md
// Subsystem: riscv-ip/merlin-rv32i
//
// Author: sean galloway
// Created: 2026-10-31

`timescale 1ns / 1ps

`include "reset_defs.svh"

module merlin_pipe_regs_tb_top (
    input logic clk,
    input logic rst_n,

    // Per-register control
    input logic if_id_stall,
    input logic if_id_flush,
    input logic id_ex_stall,
    input logic id_ex_flush,
    input logic ex_mem_stall,
    input logic ex_mem_flush,
    input logic mem_wb_stall,
    input logic mem_wb_flush,

    // IF/ID inputs
    input logic [31:0] if_id_pc_i,
    input logic [31:0] if_id_insn_i,
    input logic        if_id_valid_i,

    // IF/ID outputs
    output logic [31:0] if_id_pc_o,
    output logic [31:0] if_id_insn_o,
    output logic        if_id_valid_o,

    // ID/EX inputs
    input logic [31:0] id_ex_pc_i,
    input logic [31:0] id_ex_rs1_data_i,
    input logic [31:0] id_ex_rs2_data_i,
    input logic [31:0] id_ex_imm_i,
    input logic [ 4:0] id_ex_rs1_addr_i,
    input logic [ 4:0] id_ex_rs2_addr_i,
    input logic [ 4:0] id_ex_rd_addr_i,
    input logic [ 2:0] id_ex_funct3_i,
    input logic [ 3:0] id_ex_alu_op_i,
    input logic        id_ex_alu_src_a_pc_i,
    input logic        id_ex_alu_src_b_imm_i,
    input logic        id_ex_rd_wen_i,
    input logic [ 1:0] id_ex_wb_sel_i,
    input logic        id_ex_dmem_req_i,
    input logic        id_ex_dmem_we_i,
    input logic        id_ex_branch_i,
    input logic        id_ex_jump_i,
    input logic        id_ex_jalr_i,
    input logic [ 3:0] id_ex_halt_cause_i,
    input logic        id_ex_csr_stub_i,
    input logic        id_ex_valid_i,

    // ID/EX outputs
    output logic [31:0] id_ex_pc_o,
    output logic [31:0] id_ex_rs1_data_o,
    output logic [31:0] id_ex_rs2_data_o,
    output logic [31:0] id_ex_imm_o,
    output logic [ 4:0] id_ex_rs1_addr_o,
    output logic [ 4:0] id_ex_rs2_addr_o,
    output logic [ 4:0] id_ex_rd_addr_o,
    output logic [ 2:0] id_ex_funct3_o,
    output logic [ 3:0] id_ex_alu_op_o,
    output logic        id_ex_alu_src_a_pc_o,
    output logic        id_ex_alu_src_b_imm_o,
    output logic        id_ex_rd_wen_o,
    output logic [ 1:0] id_ex_wb_sel_o,
    output logic        id_ex_dmem_req_o,
    output logic        id_ex_dmem_we_o,
    output logic        id_ex_branch_o,
    output logic        id_ex_jump_o,
    output logic        id_ex_jalr_o,
    output logic [ 3:0] id_ex_halt_cause_o,
    output logic        id_ex_csr_stub_o,
    output logic        id_ex_valid_o,

    // EX/MEM inputs
    input logic [31:0] ex_mem_pc_i,
    input logic [31:0] ex_mem_next_pc_i,
    input logic [31:0] ex_mem_alu_y_i,
    input logic [31:0] ex_mem_store_data_i,
    input logic [ 4:0] ex_mem_rd_addr_i,
    input logic        ex_mem_rd_wen_i,
    input logic [ 1:0] ex_mem_wb_sel_i,
    input logic [ 2:0] ex_mem_funct3_i,
    input logic        ex_mem_dmem_req_i,
    input logic        ex_mem_dmem_we_i,
    input logic        ex_mem_ls_misalign_i,
    input logic [ 3:0] ex_mem_halt_cause_i,
    input logic        ex_mem_csr_stub_i,
    input logic        ex_mem_valid_i,

    // EX/MEM outputs
    output logic [31:0] ex_mem_pc_o,
    output logic [31:0] ex_mem_next_pc_o,
    output logic [31:0] ex_mem_alu_y_o,
    output logic [31:0] ex_mem_store_data_o,
    output logic [ 4:0] ex_mem_rd_addr_o,
    output logic        ex_mem_rd_wen_o,
    output logic [ 1:0] ex_mem_wb_sel_o,
    output logic [ 2:0] ex_mem_funct3_o,
    output logic        ex_mem_dmem_req_o,
    output logic        ex_mem_dmem_we_o,
    output logic        ex_mem_ls_misalign_o,
    output logic [ 3:0] ex_mem_halt_cause_o,
    output logic        ex_mem_csr_stub_o,
    output logic        ex_mem_valid_o,

    // MEM/WB inputs
    input logic [31:0] mem_wb_pc_i,
    input logic [31:0] mem_wb_next_pc_i,
    input logic [31:0] mem_wb_alu_y_i,
    input logic [31:0] mem_wb_load_data_i,
    input logic [ 4:0] mem_wb_rd_addr_i,
    input logic        mem_wb_rd_wen_i,
    input logic [ 1:0] mem_wb_wb_sel_i,
    input logic        mem_wb_csr_stub_i,
    input logic [ 3:0] mem_wb_halt_cause_i,
    input logic        mem_wb_valid_i,

    // MEM/WB outputs
    output logic [31:0] mem_wb_pc_o,
    output logic [31:0] mem_wb_next_pc_o,
    output logic [31:0] mem_wb_alu_y_o,
    output logic [31:0] mem_wb_load_data_o,
    output logic [ 4:0] mem_wb_rd_addr_o,
    output logic        mem_wb_rd_wen_o,
    output logic [ 1:0] mem_wb_wb_sel_o,
    output logic        mem_wb_csr_stub_o,
    output logic [ 3:0] mem_wb_halt_cause_o,
    output logic        mem_wb_valid_o
);

  import merlin_pkg::*;

  // Struct assemblies for DUT inputs
  if_id_t  if_id_d;
  id_ex_t  id_ex_d;
  ex_mem_t ex_mem_d;
  mem_wb_t mem_wb_d;

  // Struct assemblies for DUT outputs
  if_id_t  if_id_q;
  id_ex_t  id_ex_q;
  ex_mem_t ex_mem_q;
  mem_wb_t mem_wb_q;

  // IF/ID input assembly
  assign if_id_d.pc            = if_id_pc_i;
  assign if_id_d.insn          = if_id_insn_i;
  assign if_id_d.valid         = if_id_valid_i;

  // IF/ID output disassembly
  assign if_id_pc_o            = if_id_q.pc;
  assign if_id_insn_o          = if_id_q.insn;
  assign if_id_valid_o         = if_id_q.valid;

  // ID/EX input assembly
  assign id_ex_d.pc            = id_ex_pc_i;
  assign id_ex_d.rs1_data      = id_ex_rs1_data_i;
  assign id_ex_d.rs2_data      = id_ex_rs2_data_i;
  assign id_ex_d.imm           = id_ex_imm_i;
  assign id_ex_d.rs1_addr      = id_ex_rs1_addr_i;
  assign id_ex_d.rs2_addr      = id_ex_rs2_addr_i;
  assign id_ex_d.rd_addr       = id_ex_rd_addr_i;
  assign id_ex_d.funct3        = id_ex_funct3_i;
  assign id_ex_d.alu_op        = rv32i_pkg::alu_op_e'(id_ex_alu_op_i);
  assign id_ex_d.alu_src_a_pc  = id_ex_alu_src_a_pc_i;
  assign id_ex_d.alu_src_b_imm = id_ex_alu_src_b_imm_i;
  assign id_ex_d.rd_wen        = id_ex_rd_wen_i;
  assign id_ex_d.wb_sel        = id_ex_wb_sel_i;
  assign id_ex_d.dmem_req      = id_ex_dmem_req_i;
  assign id_ex_d.dmem_we       = id_ex_dmem_we_i;
  assign id_ex_d.branch        = id_ex_branch_i;
  assign id_ex_d.jump          = id_ex_jump_i;
  assign id_ex_d.jalr          = id_ex_jalr_i;
  assign id_ex_d.halt_cause    = id_ex_halt_cause_i;
  assign id_ex_d.csr_stub      = id_ex_csr_stub_i;
  assign id_ex_d.valid         = id_ex_valid_i;

  // ID/EX output disassembly
  assign id_ex_pc_o            = id_ex_q.pc;
  assign id_ex_rs1_data_o      = id_ex_q.rs1_data;
  assign id_ex_rs2_data_o      = id_ex_q.rs2_data;
  assign id_ex_imm_o           = id_ex_q.imm;
  assign id_ex_rs1_addr_o      = id_ex_q.rs1_addr;
  assign id_ex_rs2_addr_o      = id_ex_q.rs2_addr;
  assign id_ex_rd_addr_o       = id_ex_q.rd_addr;
  assign id_ex_funct3_o        = id_ex_q.funct3;
  assign id_ex_alu_op_o        = id_ex_q.alu_op;
  assign id_ex_alu_src_a_pc_o  = id_ex_q.alu_src_a_pc;
  assign id_ex_alu_src_b_imm_o = id_ex_q.alu_src_b_imm;
  assign id_ex_rd_wen_o        = id_ex_q.rd_wen;
  assign id_ex_wb_sel_o        = id_ex_q.wb_sel;
  assign id_ex_dmem_req_o      = id_ex_q.dmem_req;
  assign id_ex_dmem_we_o       = id_ex_q.dmem_we;
  assign id_ex_branch_o        = id_ex_q.branch;
  assign id_ex_jump_o          = id_ex_q.jump;
  assign id_ex_jalr_o          = id_ex_q.jalr;
  assign id_ex_halt_cause_o    = id_ex_q.halt_cause;
  assign id_ex_csr_stub_o      = id_ex_q.csr_stub;
  assign id_ex_valid_o         = id_ex_q.valid;

  // EX/MEM input assembly
  assign ex_mem_d.pc           = ex_mem_pc_i;
  assign ex_mem_d.next_pc      = ex_mem_next_pc_i;
  assign ex_mem_d.alu_y        = ex_mem_alu_y_i;
  assign ex_mem_d.store_data   = ex_mem_store_data_i;
  assign ex_mem_d.rd_addr      = ex_mem_rd_addr_i;
  assign ex_mem_d.rd_wen       = ex_mem_rd_wen_i;
  assign ex_mem_d.wb_sel       = ex_mem_wb_sel_i;
  assign ex_mem_d.funct3       = ex_mem_funct3_i;
  assign ex_mem_d.dmem_req     = ex_mem_dmem_req_i;
  assign ex_mem_d.dmem_we      = ex_mem_dmem_we_i;
  assign ex_mem_d.ls_misalign  = ex_mem_ls_misalign_i;
  assign ex_mem_d.halt_cause   = ex_mem_halt_cause_i;
  assign ex_mem_d.csr_stub     = ex_mem_csr_stub_i;
  assign ex_mem_d.valid        = ex_mem_valid_i;

  // EX/MEM output disassembly
  assign ex_mem_pc_o           = ex_mem_q.pc;
  assign ex_mem_next_pc_o      = ex_mem_q.next_pc;
  assign ex_mem_alu_y_o        = ex_mem_q.alu_y;
  assign ex_mem_store_data_o   = ex_mem_q.store_data;
  assign ex_mem_rd_addr_o      = ex_mem_q.rd_addr;
  assign ex_mem_rd_wen_o       = ex_mem_q.rd_wen;
  assign ex_mem_wb_sel_o       = ex_mem_q.wb_sel;
  assign ex_mem_funct3_o       = ex_mem_q.funct3;
  assign ex_mem_dmem_req_o     = ex_mem_q.dmem_req;
  assign ex_mem_dmem_we_o      = ex_mem_q.dmem_we;
  assign ex_mem_ls_misalign_o  = ex_mem_q.ls_misalign;
  assign ex_mem_halt_cause_o   = ex_mem_q.halt_cause;
  assign ex_mem_csr_stub_o     = ex_mem_q.csr_stub;
  assign ex_mem_valid_o        = ex_mem_q.valid;

  // MEM/WB input assembly
  assign mem_wb_d.pc           = mem_wb_pc_i;
  assign mem_wb_d.next_pc      = mem_wb_next_pc_i;
  assign mem_wb_d.alu_y        = mem_wb_alu_y_i;
  assign mem_wb_d.load_data    = mem_wb_load_data_i;
  assign mem_wb_d.rd_addr      = mem_wb_rd_addr_i;
  assign mem_wb_d.rd_wen       = mem_wb_rd_wen_i;
  assign mem_wb_d.wb_sel       = mem_wb_wb_sel_i;
  assign mem_wb_d.csr_stub     = mem_wb_csr_stub_i;
  assign mem_wb_d.halt_cause   = mem_wb_halt_cause_i;
  assign mem_wb_d.valid        = mem_wb_valid_i;

  // MEM/WB output disassembly
  assign mem_wb_pc_o           = mem_wb_q.pc;
  assign mem_wb_next_pc_o      = mem_wb_q.next_pc;
  assign mem_wb_alu_y_o        = mem_wb_q.alu_y;
  assign mem_wb_load_data_o    = mem_wb_q.load_data;
  assign mem_wb_rd_addr_o      = mem_wb_q.rd_addr;
  assign mem_wb_rd_wen_o       = mem_wb_q.rd_wen;
  assign mem_wb_wb_sel_o       = mem_wb_q.wb_sel;
  assign mem_wb_csr_stub_o     = mem_wb_q.csr_stub;
  assign mem_wb_halt_cause_o   = mem_wb_q.halt_cause;
  assign mem_wb_valid_o        = mem_wb_q.valid;

  merlin_if_id u_if_id (
      .clk  (clk),
      .rst_n(rst_n),
      .stall(if_id_stall),
      .flush(if_id_flush),
      .d_i  (if_id_d),
      .q_o  (if_id_q)
  );

  merlin_id_ex u_id_ex (
      .clk  (clk),
      .rst_n(rst_n),
      .stall(id_ex_stall),
      .flush(id_ex_flush),
      .d_i  (id_ex_d),
      .q_o  (id_ex_q)
  );

  merlin_ex_mem u_ex_mem (
      .clk  (clk),
      .rst_n(rst_n),
      .stall(ex_mem_stall),
      .flush(ex_mem_flush),
      .d_i  (ex_mem_d),
      .q_o  (ex_mem_q)
  );

  merlin_mem_wb u_mem_wb (
      .clk  (clk),
      .rst_n(rst_n),
      .stall(mem_wb_stall),
      .flush(mem_wb_flush),
      .d_i  (mem_wb_d),
      .q_o  (mem_wb_q)
  );

endmodule : merlin_pipe_regs_tb_top
