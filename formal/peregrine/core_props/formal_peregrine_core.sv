// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: formal_peregrine_core
// Purpose: Harness for the properties spliced into peregrine_core
//          (peregrine_core_props.svh, the predictor training rule;
//          riscv-ip/peregrine-rv32im TASK-001 stage 5).  The cacheless core
//          (CACHE_EN=0, BP_EN=1) with every input free: instruction and
//          load data, mem_wait (any pattern), and the three interrupt lines,
//          so traps, interrupts, mret, M-unit holds and memory waits all
//          reach the predictor's write port.  Reset is held for the first
//          two cycles; the core's own 3-flop synchronizer follows.
//          The predictor is shrunk to BTB 4 / BHT 8 for the solver (the
//          write rule does not depend on the size; a small table aliases
//          more, which is what the kill and stale-entry cases need).
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-25

`timescale 1ns / 1ps

module formal_peregrine_core (
    input  logic        clk,
    input  logic        mem_wait,
    input  logic [31:0] imem_rdata,
    input  logic [31:0] dmem_rdata,
    input  logic        irq_software,
    input  logic        irq_timer,
    input  logic        irq_external
);

    logic [1:0] r_rst_cnt = 2'd0;
    logic       rst_n;

    always_ff @(posedge clk) begin
        if (r_rst_cnt != 2'd2) r_rst_cnt <= r_rst_cnt + 2'd1;
    end
    assign rst_n = (r_rst_cnt == 2'd2);

    peregrine_core #(
        .RESET_ADDR (32'h0000_0000),
        .MUL_DSP    (1'b0),
        .BP_EN       (1'b1),
        .BTB_ENTRIES (4),
        .BHT_ENTRIES (8),
        .CACHE_EN    (1'b0)
    ) u_core (
        .clk                 (clk),
        .rst_n               (rst_n),
        .mem_wait            (mem_wait),
        .imem_addr           (),
        .imem_addr_next      (),
        .imem_addr_next_nw   (),
        .imem_rdata          (imem_rdata),
        .dmem_req            (),
        .dmem_addr           (),
        .dmem_rdata          (dmem_rdata),
        .dmem_wstrb          (),
        .dmem_wdata          (),
        .dmem_req_pre        (),
        .fencei_req          (),
        // bus errors (TASK-005): the cached build's only; tied off here
        .imem_fault          (1'b0),
        .dmem_fault          (1'b0),
        .irq_buserr          (1'b0),
        .buserr_info         (32'd0),
        .buserr_clear        (),
        .irq_software        (irq_software),
        .irq_timer           (irq_timer),
        .irq_external        (irq_external),
        .rvfi_valid          (),
        .rvfi_order          (),
        .rvfi_pc_rdata       (),
        .rvfi_pc_wdata       (),
        .rvfi_insn           (),
        .rvfi_trap           (),
        .rvfi_rs1_addr       (),
        .rvfi_rs2_addr       (),
        .rvfi_rs1_rdata      (),
        .rvfi_rs2_rdata      (),
        .rvfi_rd_addr        (),
        .rvfi_rd_wdata       (),
        .rvfi_mem_addr       (),
        .rvfi_mem_rmask      (),
        .rvfi_mem_wmask      (),
        .rvfi_mem_rdata      (),
        .rvfi_mem_wdata      (),
        .rvfi_trap_cause     (),
        .rvfi_bp_pred_taken  (),
        .rvfi_bp_pred_target (),
        .rvfi_bp_mispredict  ()
    );

endmodule : formal_peregrine_core
