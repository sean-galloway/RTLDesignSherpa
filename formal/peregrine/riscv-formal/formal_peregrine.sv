// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rvfi_wrapper (formal_peregrine.sv)
// Purpose: riscv-formal RVFI wrapper for peregrine_core, the cacheless
//          build (CACHE_EN=0, PRD P12).  imem/dmem read data are free formal
//          inputs; the three interrupt lines are tied low; privilege/ixl
//          tie off to M-mode/RV32.  Shaped like
//          formal/merlin/riscv-formal/formal_merlin.sv.
//
//          peregrine retires in WB and aggregates RVFI there, as merlin
//          does.  What differs from merlin:
//          - there is no halt: ecall, ebreak, an illegal instruction, a
//            misaligned target or access trap and redirect to mtvec, and the
//            trapping instruction retires as an rvfi_trap beat whose
//            pc_wdata is the trap target.  riscv-formal checks those beats
//            like any other (the pc_fwd / pc_bwd / reg / causal chain runs
//            through them), so the harness does not exclude traps; only
//            interrupts are off (rvfi_intr is not reported, and the
//            directed interrupt suite owns them, PRD P12);
//          - the branch predictor (BP_EN=1) is live with its BTB and BHT
//            left at whatever initial contents the solver picks (both are
//            memories with no reset), so every check also says the guess
//            never changes an architectural result;
//          - M instructions run on the iterative unit under
//            RISCV_FORMAL_ALTOPS (see peregrine_mdu), with the real
//            hold-in-EX timing; MUL_DSP is 0 unless PEREGRINE_MUL_DSP is
//            defined (checks_dsp.cfg).
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-25

`timescale 1ns / 1ps

// Defaults so this file parses standalone; the riscv-formal flow provides
// the same values from its generated defines.sv first.
`ifndef RISCV_FORMAL_NRET
`define RISCV_FORMAL_NRET 1
`endif
`ifndef RISCV_FORMAL_XLEN
`define RISCV_FORMAL_XLEN 32
`endif
`ifndef RISCV_FORMAL_ILEN
`define RISCV_FORMAL_ILEN 32
`endif

`include "rvfi_macros.vh"

module rvfi_wrapper (
    input  logic clock,
    input  logic reset,
    `RVFI_OUTPUTS
);

`ifdef PEREGRINE_MUL_DSP
    localparam bit MUL_DSP = 1'b1;
`else
    localparam bit MUL_DSP = 1'b0;
`endif

    // Free formal memory read data (picorv32 wrapper shape, no array).
    (* keep *) `rvformal_rand_reg [31:0] imem_rdata;
    (* keep *) `rvformal_rand_reg [31:0] dmem_rdata;

    (* keep *) wire [31:0] imem_addr;
    (* keep *) wire        dmem_req;
    (* keep *) wire [31:0] dmem_addr;
    (* keep *) wire [3:0]  dmem_wstrb;
    (* keep *) wire [31:0] dmem_wdata;

    (* keep *) wire [4:0]  core_rvfi_rs1_addr;
    (* keep *) wire [4:0]  core_rvfi_rs2_addr;
    (* keep *) wire [31:0] core_rvfi_rs1_rdata;
    (* keep *) wire [31:0] core_rvfi_rs2_rdata;

    // Memory wait: free, at most two consecutive wait cycles (merlin's
    // bound, the registered-read wrapper's worst case), which keeps the
    // liveness check meaningful.
    (* keep *) `rvformal_rand_reg mem_wait_any;
    reg  [1:0] wait_run;
    wire       mem_wait = mem_wait_any && (wait_run < 2'd2);

    always @(posedge clock) begin
        if (reset)         wait_run <= 2'd0;
        else if (mem_wait) wait_run <= wait_run + 2'd1;
        else               wait_run <= 2'd0;
    end

    peregrine_core #(
        .RESET_ADDR (32'h0000_0000),
        .MUL_DSP    (MUL_DSP),
        .BP_EN      (1'b1),
        .CACHE_EN   (1'b0)
    ) u_core (
        .clk                 (clock),
        .rst_n               (~reset),
        .mem_wait            (mem_wait),
        .imem_addr           (imem_addr),
        .imem_addr_next      (),
        .imem_addr_next_nw   (),
        .imem_rdata          (imem_rdata),
        .dmem_req            (dmem_req),
        .dmem_addr           (dmem_addr),
        .dmem_rdata          (dmem_rdata),
        .dmem_wstrb          (dmem_wstrb),
        .dmem_wdata          (dmem_wdata),
        .dmem_req_pre        (),
        .fencei_req          (),
        // bus errors (TASK-005): the cached build's only; tied off here
        .imem_fault          (1'b0),
        .dmem_fault          (1'b0),
        .irq_buserr          (1'b0),
        .buserr_info         (32'd0),
        .buserr_clear        (),
        .irq_software        (1'b0),
        .irq_timer           (1'b0),
        .irq_external        (1'b0),
        .rvfi_valid          (rvfi_valid),
        .rvfi_order          (rvfi_order),
        .rvfi_pc_rdata       (rvfi_pc_rdata),
        .rvfi_pc_wdata       (rvfi_pc_wdata),
        .rvfi_insn           (rvfi_insn),
        .rvfi_trap           (rvfi_trap),
        .rvfi_rs1_addr       (core_rvfi_rs1_addr),
        .rvfi_rs2_addr       (core_rvfi_rs2_addr),
        .rvfi_rs1_rdata      (core_rvfi_rs1_rdata),
        .rvfi_rs2_rdata      (core_rvfi_rs2_rdata),
        .rvfi_rd_addr        (rvfi_rd_addr),
        .rvfi_rd_wdata       (rvfi_rd_wdata),
        .rvfi_mem_addr       (rvfi_mem_addr),
        .rvfi_mem_rmask      (rvfi_mem_rmask),
        .rvfi_mem_wmask      (rvfi_mem_wmask),
        .rvfi_mem_rdata      (rvfi_mem_rdata),
        .rvfi_mem_wdata      (rvfi_mem_wdata),
        .rvfi_trap_cause     (),
        .rvfi_bp_pred_taken  (),
        .rvfi_bp_pred_target (),
        .rvfi_bp_mispredict  ()
    );

    assign rvfi_halt = 1'b0;
    assign rvfi_intr = 1'b0;
    assign rvfi_mode = 2'b11;   // M-mode
    assign rvfi_ixl  = 2'b01;   // XLEN = 32

    // Source-register correction.  peregrine (like merlin) reports rs1/rs2
    // from the encoding bits on every beat; riscv-formal reads any non-zero
    // rvfi_rs*_addr as an architectural read.  A source is reported only
    // for the opcodes that read it (a positive list, so an illegal or
    // unknown encoding reads nothing): rs1 for JALR, branches, loads,
    // stores, OP-IMM, OP and the register-form CSR instructions; rs2 for
    // branches, stores and OP (which includes the M extension).
    localparam logic [6:0] OPCODE_JALR   = 7'b1100111;
    localparam logic [6:0] OPCODE_BRANCH = 7'b1100011;
    localparam logic [6:0] OPCODE_LOAD   = 7'b0000011;
    localparam logic [6:0] OPCODE_STORE  = 7'b0100011;
    localparam logic [6:0] OPCODE_OP_IMM = 7'b0010011;
    localparam logic [6:0] OPCODE_OP     = 7'b0110011;
    localparam logic [6:0] OPCODE_SYSTEM = 7'b1110011;

    wire [6:0] opcode = rvfi_insn[6:0];
    wire [2:0] funct3 = rvfi_insn[14:12];

    wire rs1_used = (opcode == OPCODE_JALR)   || (opcode == OPCODE_BRANCH) ||
                    (opcode == OPCODE_LOAD)   || (opcode == OPCODE_STORE)  ||
                    (opcode == OPCODE_OP_IMM) || (opcode == OPCODE_OP)     ||
                    ((opcode == OPCODE_SYSTEM) && (funct3[1:0] != 2'b00) && !funct3[2]);
    wire rs2_used = (opcode == OPCODE_BRANCH) || (opcode == OPCODE_STORE) ||
                    (opcode == OPCODE_OP);

    assign rvfi_rs1_addr  = rs1_used ? core_rvfi_rs1_addr  : 5'd0;
    assign rvfi_rs2_addr  = rs2_used ? core_rvfi_rs2_addr  : 5'd0;
    assign rvfi_rs1_rdata = rs1_used ? core_rvfi_rs1_rdata : 32'd0;
    assign rvfi_rs2_rdata = rs2_used ? core_rvfi_rs2_rdata : 32'd0;

endmodule : rvfi_wrapper
