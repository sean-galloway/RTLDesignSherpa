// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: merlin_mem_wb
// Purpose: MEM/WB pipeline register.  Carries the final writeback value
//          (ALU, load, or link), destination register, and control into the
//          writeback stage.  Flush injects the bubble record (valid=0,
//          halt_cause=HALT_NONE, rd_wen=0, csr_stub=0).
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
//   - The bubble record is the all-zero value of mem_wb_t; all strobes are
//     deasserted and halt_cause is HALT_NONE (zero).
//
// Related Modules:
//   - merlin_if_id, merlin_id_ex, merlin_ex_mem (siblings)
//   - merlin_pkg (struct definitions)
//
// Test:
//   - projects/components/riscv-ip/merlin-rv32i/dv/tests/test_merlin_pipe_regs.py

`timescale 1ns / 1ps

`include "reset_defs.svh"

module merlin_mem_wb (
    input  logic                clk,
    input  logic                rst_n,
    input  logic                stall,
    input  logic                flush,
    input  merlin_pkg::mem_wb_t d_i,
    output merlin_pkg::mem_wb_t q_o
);

  import merlin_pkg::*;

  `ALWAYS_FF_RST(clk, rst_n,
                 if (`RST_ASSERTED(rst_n)) begin
            q_o <= '0;
        end else if (flush) begin
            q_o <= '0;
        end else if (!stall) begin
            q_o <= d_i;
        end)

endmodule : merlin_mem_wb
