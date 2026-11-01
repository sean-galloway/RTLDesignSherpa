// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: merlin_hazard_tb_top
// Purpose: Thin cocotb wrapper for the combinational merlin_hazard unit.
//          Breaks the DUT's scalar ports into flat vectors so the Python
//          test can drive and sample them directly without a clock.
//
// Documentation: projects/components/riscv-ip/merlin-rv32i/PRD.md
// Subsystem: riscv-ip/merlin-rv32i
//
// Author: sean galloway
// Created: 2026-11-01

`timescale 1ns / 1ps

module merlin_hazard_tb_top (
    input  logic [4:0] id_rs1_addr,
    input  logic [4:0] id_rs2_addr,
    input  logic [4:0] idex_rd_addr,
    input  logic       idex_rd_wen,
    input  logic       idex_is_load,
    input  logic [4:0] exmem_rd_addr,
    input  logic       exmem_rd_wen,
    input  logic [4:0] memwb_rd_addr,
    input  logic       memwb_rd_wen,
    input  logic       ex_flush,

    output logic [1:0] fwd_a,
    output logic [1:0] fwd_b,
    output logic       stall_ifid,
    output logic       flush_ifid,
    output logic       flush_idex
);

  merlin_hazard u_hazard (
      .id_rs1_addr  (id_rs1_addr),
      .id_rs2_addr  (id_rs2_addr),
      .idex_rd_addr (idex_rd_addr),
      .idex_rd_wen  (idex_rd_wen),
      .idex_is_load (idex_is_load),
      .exmem_rd_addr(exmem_rd_addr),
      .exmem_rd_wen (exmem_rd_wen),
      .memwb_rd_addr(memwb_rd_addr),
      .memwb_rd_wen (memwb_rd_wen),
      .ex_flush     (ex_flush),
      .fwd_a        (fwd_a),
      .fwd_b        (fwd_b),
      .stall_ifid   (stall_ifid),
      .flush_ifid   (flush_ifid),
      .flush_idex   (flush_idex)
  );

endmodule : merlin_hazard_tb_top
