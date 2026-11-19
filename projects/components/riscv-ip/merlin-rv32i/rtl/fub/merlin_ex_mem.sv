// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: merlin_ex_mem
// Purpose: EX/MEM pipeline register.  Carries the ALU result, branch target,
//          store data, and data-memory control into the memory stage.  Flush
//          injects the bubble record (valid=0, halt_cause=HALT_NONE, rd_wen=0,
//          dmem_req=0, dmem_we=0, ls_misalign=0, csr_stub=0).
//
// Documentation: projects/components/riscv-ip/merlin-rv32i/PRD.md
// Subsystem: riscv-ip/merlin-rv32i
//
// Author: sean galloway
// Created: 2026-10-31
//
// Parameters: None
//
// Notes:
//   - Flush wins over stall.
//   - Only the control fields reset and flush (valid, rd_wen, dmem_req,
//     dmem_we, ls_misalign, halt_cause, csr_stub).
//     The payload is a plain enable flop with no reset and no flush clear,
//     so a bubble carries a stale payload; every consumer in merlin_core
//     gates on valid (or on a control field that is cleared).  An async
//     clear on the payload put a reset on ~680 flops and folded the
//     synchronous flush into a LUT in front of each one (riscv-ip
//     common-rv32i ISSUE-001 row 2).
//
// Related Modules:
//   - merlin_if_id, merlin_id_ex, merlin_mem_wb (siblings)
//   - merlin_pkg (struct definitions)
//
// Test:
//   - projects/components/riscv-ip/merlin-rv32i/dv/tests/test_merlin_pipe_regs.py

`timescale 1ns / 1ps

`include "reset_defs.svh"

module merlin_ex_mem (
    input  logic                clk,
    input  logic                rst_n,
    input  logic                stall,
    input  logic                flush,
    input  merlin_pkg::ex_mem_t d_i,
    output merlin_pkg::ex_mem_t q_o
);

  import merlin_pkg::*;

  // Payload: captured unless stalled; no reset, no flush clear.
  ex_mem_t r_payload;

  always_ff @(posedge clk) begin
      if (!stall) r_payload <= d_i;
  end

  // Control: reset and flush to the bubble value (all zero).
  logic [$bits(d_i.valid)-1:0] r_valid;
  logic [$bits(d_i.rd_wen)-1:0] r_rd_wen;
  logic [$bits(d_i.dmem_req)-1:0] r_dmem_req;
  logic [$bits(d_i.dmem_we)-1:0] r_dmem_we;
  logic [$bits(d_i.ls_misalign)-1:0] r_ls_misalign;
  logic [$bits(d_i.halt_cause)-1:0] r_halt_cause;
  logic [$bits(d_i.csr_stub)-1:0] r_csr_stub;

  `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_valid       <= '0;
            r_rd_wen      <= '0;
            r_dmem_req    <= '0;
            r_dmem_we     <= '0;
            r_ls_misalign <= '0;
            r_halt_cause  <= '0;
            r_csr_stub    <= '0;
        end else if (flush) begin
            r_valid       <= '0;
            r_rd_wen      <= '0;
            r_dmem_req    <= '0;
            r_dmem_we     <= '0;
            r_ls_misalign <= '0;
            r_halt_cause  <= '0;
            r_csr_stub    <= '0;
        end else if (!stall) begin
            r_valid       <= d_i.valid;
            r_rd_wen      <= d_i.rd_wen;
            r_dmem_req    <= d_i.dmem_req;
            r_dmem_we     <= d_i.dmem_we;
            r_ls_misalign <= d_i.ls_misalign;
            r_halt_cause  <= d_i.halt_cause;
            r_csr_stub    <= d_i.csr_stub;
        end)

  always_comb begin
        q_o = r_payload;
        q_o.valid       = r_valid;
        q_o.rd_wen      = r_rd_wen;
        q_o.dmem_req    = r_dmem_req;
        q_o.dmem_we     = r_dmem_we;
        q_o.ls_misalign = r_ls_misalign;
        q_o.halt_cause  = r_halt_cause;
        q_o.csr_stub    = r_csr_stub;
  end

endmodule : merlin_ex_mem
