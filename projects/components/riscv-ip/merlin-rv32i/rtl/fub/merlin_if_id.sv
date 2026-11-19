// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: merlin_if_id
// Purpose: IF/ID pipeline register.  Captures the fetched instruction and PC
//          on every clock unless stalled; flush injects the bubble record
//          (valid = 0) and overrides a simultaneous stall.
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
//   - Only the control fields reset and flush (valid).
//     The payload is a plain enable flop with no reset and no flush clear,
//     so a bubble carries a stale payload; every consumer in merlin_core
//     gates on valid (or on a control field that is cleared).  An async
//     clear on the payload put a reset on ~680 flops and folded the
//     synchronous flush into a LUT in front of each one (riscv-ip
//     common-rv32i ISSUE-001 row 2).
//
// Related Modules:
//   - merlin_id_ex, merlin_ex_mem, merlin_mem_wb (siblings)
//   - merlin_pkg (struct definitions)
//
// Test:
//   - projects/components/riscv-ip/merlin-rv32i/dv/tests/test_merlin_pipe_regs.py

`timescale 1ns / 1ps

`include "reset_defs.svh"

module merlin_if_id (
    input  logic               clk,
    input  logic               rst_n,
    input  logic               stall,
    input  logic               flush,
    input  merlin_pkg::if_id_t d_i,
    output merlin_pkg::if_id_t q_o
);

  import merlin_pkg::*;

  // Payload: captured unless stalled; no reset, no flush clear.
  if_id_t r_payload;

  always_ff @(posedge clk) begin
      if (!stall) r_payload <= d_i;
  end

  // Control: reset and flush to the bubble value (all zero).
  logic [$bits(d_i.valid)-1:0] r_valid;

  `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_valid <= '0;
        end else if (flush) begin
            r_valid <= '0;
        end else if (!stall) begin
            r_valid <= d_i.valid;
        end)

  always_comb begin
        q_o = r_payload;
        q_o.valid = r_valid;
  end

endmodule : merlin_if_id
