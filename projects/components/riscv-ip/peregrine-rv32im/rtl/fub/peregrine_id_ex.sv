// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: peregrine_id_ex
// Purpose: ID/EX pipeline register.  Carries register-file read data, the
//          immediate, decoded control bits, and the PC into the execute stage.
//          Flush injects the bubble record (valid=0, exc_cause=EXC_NONE,
//          rd_wen=0, dmem_req=0, and all other control strobes 0).
//
// Documentation: projects/components/riscv-ip/peregrine-rv32im/PRD.md
// Subsystem: riscv-ip/peregrine-rv32im
//
// Author: sean galloway
// Created: 2026-11-23
//
// Parameters: None
//
// Notes:
//   - Flush wins over stall.
//   - Only the control fields reset and flush (valid, rd_wen, dmem_req,
//     dmem_we, branch, jump, jalr, exc_cause, csr_op).
//     The payload is a plain enable flop with no reset and no flush clear,
//     so a bubble carries a stale payload; every consumer in peregrine_core
//     gates on valid (or on a control field that is cleared).  An async
//     clear on the payload put a reset on ~680 flops and folded the
//     synchronous flush into a LUT in front of each one (riscv-ip
//     common-rv32i ISSUE-001 row 2).
//
// Related Modules:
//   - peregrine_if_id, peregrine_ex_mem, peregrine_mem_wb (siblings)
//   - peregrine_pkg (struct definitions)
//
// Test:
//   - exercised by every peregrine core test (merlin_pipe_regs covers the shape)

`timescale 1ns / 1ps

`include "reset_defs.svh"

module peregrine_id_ex (
    input  logic               clk,
    input  logic               rst_n,
    input  logic               stall,
    input  logic               flush,
    input  peregrine_pkg::id_ex_t d_i,
    output peregrine_pkg::id_ex_t q_o
);

  import peregrine_pkg::*;

  // Payload: captured unless stalled; no reset, no flush clear.
  id_ex_t r_payload;

  always_ff @(posedge clk) begin
      if (!stall) r_payload <= d_i;
  end

  // Control: reset and flush to the bubble value (all zero).
  logic [$bits(d_i.valid)-1:0] r_valid;
  logic [$bits(d_i.rd_wen)-1:0] r_rd_wen;
  logic [$bits(d_i.dmem_req)-1:0] r_dmem_req;
  logic [$bits(d_i.dmem_we)-1:0] r_dmem_we;
  logic [$bits(d_i.branch)-1:0] r_branch;
  logic [$bits(d_i.jump)-1:0] r_jump;
  logic [$bits(d_i.jalr)-1:0] r_jalr;
  logic [$bits(d_i.exc_cause)-1:0] r_exc_cause;
  logic [$bits(d_i.csr_op)-1:0] r_csr_op;

  `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_valid      <= '0;
            r_rd_wen     <= '0;
            r_dmem_req   <= '0;
            r_dmem_we    <= '0;
            r_branch     <= '0;
            r_jump       <= '0;
            r_jalr       <= '0;
            r_exc_cause <= '0;
            r_csr_op   <= '0;
        end else if (flush) begin
            r_valid      <= '0;
            r_rd_wen     <= '0;
            r_dmem_req   <= '0;
            r_dmem_we    <= '0;
            r_branch     <= '0;
            r_jump       <= '0;
            r_jalr       <= '0;
            r_exc_cause <= '0;
            r_csr_op   <= '0;
        end else if (!stall) begin
            r_valid      <= d_i.valid;
            r_rd_wen     <= d_i.rd_wen;
            r_dmem_req   <= d_i.dmem_req;
            r_dmem_we    <= d_i.dmem_we;
            r_branch     <= d_i.branch;
            r_jump       <= d_i.jump;
            r_jalr       <= d_i.jalr;
            r_exc_cause <= d_i.exc_cause;
            r_csr_op   <= d_i.csr_op;
        end)

  always_comb begin
        q_o = r_payload;
        q_o.valid      = r_valid;
        q_o.rd_wen     = r_rd_wen;
        q_o.dmem_req   = r_dmem_req;
        q_o.dmem_we    = r_dmem_we;
        q_o.branch     = r_branch;
        q_o.jump       = r_jump;
        q_o.jalr       = r_jalr;
        q_o.exc_cause = r_exc_cause;
        q_o.csr_op   = r_csr_op;
  end

endmodule : peregrine_id_ex
