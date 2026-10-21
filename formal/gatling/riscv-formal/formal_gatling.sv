// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rvfi_wrapper (formal_gatling.sv)
// Purpose: riscv-formal RVFI wrapper for gatling_core, observing CONTEXT 0.
//          riscv-formal checks one hart's retirement stream; the barrel
//          interleaves four.  The wrapper reports context 0's retirements
//          only and leaves the other three completely free: their
//          instructions (imem_rdata), their load data (dmem_rdata) and their
//          run bits are unconstrained formal inputs every cycle.  So beyond
//          the RV32I insn checks on context 0, the reg / pc_fwd / pc_bwd
//          consistency checks prove that NOTHING the other contexts execute,
//          and no way they are started or stopped, can disturb context 0's
//          registers or its PC -- the barrel's isolation, for all programs.
//
//          Context 0 is held running (hart_run[0] = 1): stopping it restarts
//          its stream at RESET_ADDR with order 0, which is not a retirement
//          stream riscv-formal can check.  Run control of the observed
//          context is covered in DV (test_gatling_core run_control).
//          Context 0 is not special in the RTL -- the rotation treats all
//          four alike -- so its proof stands for each.
//
// Documentation: projects/components/riscv-ip/gatling-rv32itetrad/docs/gatling_mas
// Subsystem: riscv-ip/gatling-rv32itetrad
//
// Author: sean galloway
// Created: 2026-10-21

`timescale 1ns / 1ps

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

    // Free formal inputs: every context's fetched word and load data, and
    // the run bits of contexts 1-3.
    (* keep *) `rvformal_rand_reg [31:0] imem_rdata;
    (* keep *) `rvformal_rand_reg [31:0] dmem_rdata;
    (* keep *) `rvformal_rand_reg [2:0]  run_others;

    (* keep *) wire [1:0]  imem_ctx;
    (* keep *) wire [31:0] imem_addr;
    (* keep *) wire        dmem_req;
    (* keep *) wire [1:0]  dmem_ctx;
    (* keep *) wire [31:0] dmem_addr;
    (* keep *) wire [3:0]  dmem_wstrb;
    (* keep *) wire [31:0] dmem_wdata;
    (* keep *) wire [3:0]  halted;
    (* keep *) wire [15:0] halt_cause;

    wire        core_valid;
    wire [1:0]  core_ctx;

    gatling_core u_core (
        .clk            (clock),
        .rst_n          (~reset),
        .hart_run       ({run_others, 1'b1}),
        .imem_ctx       (imem_ctx),
        .imem_addr      (imem_addr),
        .imem_rdata     (imem_rdata),
        .dmem_req       (dmem_req),
        .dmem_ctx       (dmem_ctx),
        .dmem_addr      (dmem_addr),
        .dmem_rdata     (dmem_rdata),
        .dmem_wstrb     (dmem_wstrb),
        .dmem_wdata     (dmem_wdata),
        .halted         (halted),
        .halt_cause     (halt_cause),
        .rvfi_valid     (core_valid),
        .rvfi_ctx       (core_ctx),
        .rvfi_order     (rvfi_order),
        .rvfi_pc_rdata  (rvfi_pc_rdata),
        .rvfi_pc_wdata  (rvfi_pc_wdata),
        .rvfi_insn      (rvfi_insn),
        .rvfi_trap      (rvfi_trap),
        .rvfi_rs1_addr  (rvfi_rs1_addr),
        .rvfi_rs2_addr  (rvfi_rs2_addr),
        .rvfi_rs1_rdata (rvfi_rs1_rdata),
        .rvfi_rs2_rdata (rvfi_rs2_rdata),
        .rvfi_rd_addr   (rvfi_rd_addr),
        .rvfi_rd_wdata  (rvfi_rd_wdata),
        .rvfi_mem_addr  (rvfi_mem_addr),
        .rvfi_mem_rmask (rvfi_mem_rmask),
        .rvfi_mem_wmask (rvfi_mem_wmask),
        .rvfi_mem_rdata (rvfi_mem_rdata),
        .rvfi_mem_wdata (rvfi_mem_wdata)
    );

    // Context 0's retirements only.  A context halts on its trap beat and
    // retires nothing after it: rvfi_halt.
    assign rvfi_valid = core_valid && (core_ctx == 2'd0);
    assign rvfi_halt  = rvfi_valid && rvfi_trap;
    assign rvfi_intr  = 1'b0;
    assign rvfi_mode  = 2'b11;   // M-mode
    assign rvfi_ixl   = 2'b01;   // XLEN = 32

endmodule : rvfi_wrapper
