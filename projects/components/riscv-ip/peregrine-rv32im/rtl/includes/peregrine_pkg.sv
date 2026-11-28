// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: peregrine_pkg
// Purpose: Pipeline-register structs, select encodings, exception codes and
//          CSR addresses for the peregrine RV32IM core.  The structs are
//          merlin's plus the trap fields: an exception cause rides with its
//          instruction from the stage that detects it to MEM, where the
//          trap is committed (PRD §4.3).
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-23

`timescale 1ns / 1ps

package peregrine_pkg;

  import rv32i_pkg::*;

  // Writeback source select (merlin's encoding).
  localparam logic [1:0] WB_ALU  = 2'b00;
  localparam logic [1:0] WB_LOAD = 2'b01;
  localparam logic [1:0] WB_LINK = 2'b10;
  localparam logic [1:0] WB_LUI  = 2'b11;

  // Forwarding source select for register-file read ports A/B.
  localparam logic [1:0] FWD_IDEX  = 2'b00;
  localparam logic [1:0] FWD_EXMEM = 2'b01;
  localparam logic [1:0] FWD_MEMWB = 2'b10;

  // In-pipeline exception code.  The values are rv32i_pkg's halt causes
  // (decode raises ecall/ebreak/illegal in that encoding); MEM maps them to
  // mcause.  EXC_NONE is the bubble value the pipeline registers flush to.
  localparam logic [3:0] EXC_NONE   = HALT_NONE;
  localparam logic [3:0] EXC_ECALL  = HALT_ECALL;
  localparam logic [3:0] EXC_EBREAK = HALT_EBREAK;
  localparam logic [3:0] EXC_IALIGN = HALT_IALIGN;
  localparam logic [3:0] EXC_LALIGN = HALT_LALIGN;
  localparam logic [3:0] EXC_SALIGN = HALT_SALIGN;
  localparam logic [3:0] EXC_ILL    = HALT_ILL;
  // Instruction access fault (TASK-005): the fetch's I$ fill was answered
  // SLVERR / DECERR.  Raised in ID from the IF/ID fault bit; not one of
  // rv32i_pkg's halt causes (6 is free there).  Load and store access
  // faults need no code: they arrive with the D-side response at WB.
  localparam logic [3:0] EXC_IFAULT = 4'h6;

  // mcause exception codes (privileged spec, table 3.6).
  localparam logic [30:0] MCAUSE_IALIGN  = 31'd0;
  localparam logic [30:0] MCAUSE_IFAULT  = 31'd1;   // instruction access fault
  localparam logic [30:0] MCAUSE_ILL     = 31'd2;
  localparam logic [30:0] MCAUSE_EBREAK  = 31'd3;
  localparam logic [30:0] MCAUSE_LALIGN  = 31'd4;
  localparam logic [30:0] MCAUSE_LFAULT  = 31'd5;   // load access fault
  localparam logic [30:0] MCAUSE_SALIGN  = 31'd6;
  localparam logic [30:0] MCAUSE_SFAULT  = 31'd7;   // store/AMO access fault
  localparam logic [30:0] MCAUSE_ECALL_M = 31'd11;
  // Interrupt codes (mcause[31] = 1).
  localparam logic [30:0] MCAUSE_MSI     = 31'd3;
  localparam logic [30:0] MCAUSE_MTI     = 31'd7;
  localparam logic [30:0] MCAUSE_MEI     = 31'd11;
  // Platform local interrupt 16 (TASK-005): amber's failed dirty
  // write-back, an imprecise bus-error report (codes >= 16 are the
  // platform's, privileged spec 3.1.9).
  localparam logic [30:0] MCAUSE_BUSERR  = 31'd16;

  // CSR addresses implemented (PRD P6).
  localparam logic [11:0] CSR_MSTATUS    = 12'h300;
  localparam logic [11:0] CSR_MISA       = 12'h301;
  localparam logic [11:0] CSR_MIE        = 12'h304;
  localparam logic [11:0] CSR_MTVEC      = 12'h305;
  localparam logic [11:0] CSR_MSTATUSH   = 12'h310;
  localparam logic [11:0] CSR_MSCRATCH   = 12'h340;
  localparam logic [11:0] CSR_MEPC       = 12'h341;
  localparam logic [11:0] CSR_MCAUSE     = 12'h342;
  localparam logic [11:0] CSR_MTVAL      = 12'h343;
  localparam logic [11:0] CSR_MIP        = 12'h344;
  // Custom machine read/write CSR (TASK-005; 0x7C0-0x7FF is the
  // custom M-mode range).  Read: the failed write-back's line address in
  // [31:2], bit 1 = overflow (another failed while it was held), bit 0 =
  // valid (= mip.16).  Any write clears the status (the value is ignored).
  localparam logic [11:0] CSR_MBUSERR    = 12'h7C0;
  localparam logic [11:0] CSR_MVENDORID  = 12'hF11;
  localparam logic [11:0] CSR_MARCHID    = 12'hF12;
  localparam logic [11:0] CSR_MIMPID     = 12'hF13;
  localparam logic [11:0] CSR_MHARTID    = 12'hF14;
  localparam logic [11:0] CSR_MCONFIGPTR = 12'hF15;

  // IF/ID boundary.  pred_* is the predictor's guess for this instruction
  // (payload), checked against the resolved outcome in EX.
  typedef struct packed {
    logic [31:0] pc;
    logic [31:0] insn;
    logic        pred_taken;
    logic [31:0] pred_target;
    logic        ifault;        // the fetch's I$ fill failed (TASK-005)
    logic        valid;
  } if_id_t;

  // ID/EX boundary.  csr_op is a control field (reset/flush); mret and
  // m_op are payload, read only under valid.
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
    logic [3:0]  exc_cause;
    logic        csr_op;
    logic        mret;
    logic        m_op;          // M extension: funct3 selects the operation
    logic        pred_taken;    // the predictor's guess (payload)
    logic [31:0] pred_target;
    logic [31:0] br_target;     // pc + imm: a branch / JAL target, from ID
    logic        br_tgt_hit;    // pred_target == br_target (TASK-001 stage 7)
    logic [31:0] jalr_x;        // pred_target - imm: a JALR guess is right iff
                                // rs1 is jalr_x or jalr_x + 1 (stage 7)
    logic        valid;
    logic [31:0] insn;
  } id_ex_t;

  // EX/MEM boundary.  csr_wen and csr_wdata are the CSR write the MEM
  // commit performs; alu_y already carries the CSR's old value as rd's.
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
    logic [3:0]  exc_cause;
    logic        csr_op;
    logic        csr_wen;
    logic [31:0] csr_wdata;
    logic        mret;
    logic        m_op;          // payload: an M instruction is not interruptible in MEM
    logic        irq_take;      // an M instruction interrupted in EX (TASK-007)
    logic        bp_pred_taken; // observation: the prediction and its outcome
    logic [31:0] bp_pred_target;
    logic        bp_mispredict;
    logic        valid;
    logic [31:0] insn;
    logic [31:0] imm;
    logic [31:0] rs1_rdata;
    logic [31:0] rs2_rdata;
  } ex_mem_t;

  // MEM/WB boundary.  trap marks the instruction that trapped in MEM: it
  // retires on RVFI with no rd write and no memory access.
  typedef struct packed {
    logic [31:0] pc;
    logic [31:0] next_pc;
    logic [31:0] alu_y;
    logic [4:0]  rd_addr;
    logic        rd_wen;
    logic [1:0]  wb_sel;
    logic [2:0]  funct3;
    logic        trap;
    logic        is_mem;
    logic [3:0]  exc_cause;
    logic        bp_pred_taken; // observation, reported at retire
    logic [31:0] bp_pred_target;
    logic        bp_mispredict;
    logic        valid;
    logic [31:0] insn;
    logic [31:0] imm;
    logic [31:0] rs1_rdata;
    logic [31:0] rs2_rdata;
  } mem_wb_t;

endpackage : peregrine_pkg
