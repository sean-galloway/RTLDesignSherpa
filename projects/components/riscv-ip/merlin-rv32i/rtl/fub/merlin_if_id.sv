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
//   - The bubble record is the all-zero value of if_id_t; valid is 0 and
//     halt_cause is HALT_NONE (also zero).
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

  `ALWAYS_FF_RST(clk, rst_n,
                 if (`RST_ASSERTED(rst_n)) begin
            q_o <= '0;
        end else if (flush) begin
            q_o <= '0;
        end else if (!stall) begin
            q_o <= d_i;
        end)

endmodule : merlin_if_id
