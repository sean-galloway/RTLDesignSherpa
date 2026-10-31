// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: merlin_pkg
// Purpose: Pipeline-stage register bundles and local control vocabulary for
//          the merlin 5-stage pipelined RV32I core.  Each typedef is the
//          contract across one stage boundary; later stages extend the bundle
//          with their own resolved control bits.
//
//          Imports rv32i_pkg for the shared ALU op enum and halt-cause
//          constants so the stage bundles can carry them directly.
//
// Documentation: projects/components/riscv-ip/merlin-rv32i/PRD.md
// Subsystem: riscv-ip/merlin-rv32i
//
// Author: sean galloway
// Created: 2026-10-31

`timescale 1ns / 1ps

package merlin_pkg;

  import rv32i_pkg::*;

  // Writeback source select: which value drives the regfile write port.
  localparam logic [1:0] WB_ALU = 2'b00;
  localparam logic [1:0] WB_LOAD = 2'b01;
  localparam logic [1:0] WB_LINK = 2'b10;
  localparam logic [1:0] WB_LUI = 2'b11;

  // IF/ID boundary: the fetched instruction and its PC.
  typedef struct packed {
    logic [31:0] pc;
    logic [31:0] insn;
    logic        valid;
  } if_id_t;

  // ID/EX boundary: decoded control bundle plus register-file read data.
  typedef struct packed {
    logic [31:0] pc;
    logic [31:0] rs1_data;
    logic [31:0] rs2_data;
    logic [31:0] imm;
    logic [4:0]  rs1_addr;
    logic [4:0]  rs2_addr;
    logic [4:0]  rd_addr;
    logic [2:0]  funct3;
    alu_op_e     alu_op;
    logic        alu_src_a_pc;
    logic        alu_src_b_imm;
    logic        rd_wen;
    logic [1:0]  wb_sel;
    logic        dmem_req;
    logic        dmem_we;
    logic        branch;
    logic        jump;
    logic        jalr;
    logic [3:0]  halt_cause;
    logic        csr_stub;
    logic        valid;
  } id_ex_t;

  // EX/MEM boundary: ALU result, branch target, and data-memory control.
  typedef struct packed {
    logic [31:0] pc;
    logic [31:0] next_pc;
    logic [31:0] alu_y;
    logic [31:0] store_data;
    logic [4:0]  rd_addr;
    logic        rd_wen;
    logic [1:0]  wb_sel;
    logic [2:0]  funct3;
    logic        dmem_req;
    logic        dmem_we;
    logic        ls_misalign;
    logic [3:0]  halt_cause;
    logic        csr_stub;
    logic        valid;
  } ex_mem_t;

  // MEM/WB boundary: final writeback value selected from ALU, load, or link.
  typedef struct packed {
    logic [31:0] pc;
    logic [31:0] next_pc;
    logic [31:0] alu_y;
    logic [31:0] load_data;
    logic [4:0]  rd_addr;
    logic        rd_wen;
    logic [1:0]  wb_sel;
    logic        csr_stub;
    logic [3:0]  halt_cause;
    logic        valid;
  } mem_wb_t;

endpackage : merlin_pkg
