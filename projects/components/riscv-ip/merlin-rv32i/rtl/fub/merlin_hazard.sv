// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: merlin_hazard
// Purpose: Forwarding and interlock unit for the merlin 5-stage pipelined
//          RV32I core.  Compares the two source register addresses currently
//          in ID against the destination addresses pending in EX/MEM and
//          MEM/WB, selects the newest producer for each read port, and raises
//          a load-use stall when the instruction in EX is a load whose
//          destination matches either ID source.  All outputs are purely
//          combinational; this module has no clock or reset.
//
// Documentation: projects/components/riscv-ip/merlin-rv32i/PRD.md
// Subsystem: riscv-ip/merlin-rv32i
//
// Author: sean galloway
// Created: 2026-11-01
//
// Parameters: None
//
// Notes:
//   - EX/MEM takes priority over MEM/WB when both stages write the same
//     destination register.
//   - Register x0 is never forwarded and never causes a stall: rd_addr==0
//     disables both forwarding matches and load-use detection.
//   - ex_flush is broadcast to flush_ifid and flush_idex; the core is
//     responsible for making flush win over stall.
//
// Related Modules:
//   - merlin_pkg (FWD_* encodings and pipeline structs)
//   - merlin_id_ex, merlin_ex_mem, merlin_mem_wb (pipeline registers)
//
// Test:
//   - projects/components/riscv-ip/merlin-rv32i/dv/tests/test_merlin_hazard.py

`timescale 1ns / 1ps

module merlin_hazard (
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

  import merlin_pkg::*;

  // Forwarding source priority: newest producer wins.
  // FWD_EXMEM is the instruction currently in the EX/MEM stage; FWD_MEMWB is
  // the instruction in the MEM/WB stage.  x0 is never a valid producer.
  always_comb begin
    if ((exmem_rd_addr != 5'd0) && exmem_rd_wen && (exmem_rd_addr == id_rs1_addr))
      fwd_a = FWD_EXMEM;
    else if ((memwb_rd_addr != 5'd0) && memwb_rd_wen && (memwb_rd_addr == id_rs1_addr))
      fwd_a = FWD_MEMWB;
    else
      fwd_a = FWD_IDEX;
  end

  always_comb begin
    if ((exmem_rd_addr != 5'd0) && exmem_rd_wen && (exmem_rd_addr == id_rs2_addr))
      fwd_b = FWD_EXMEM;
    else if ((memwb_rd_addr != 5'd0) && memwb_rd_wen && (memwb_rd_addr == id_rs2_addr))
      fwd_b = FWD_MEMWB;
    else
      fwd_b = FWD_IDEX;
  end

  // Load-use interlock: a load in EX whose destination matches either ID
  // source must stall the IF/ID stage for one cycle.
  assign stall_ifid = idex_is_load &&
                      (idex_rd_addr != 5'd0) &&
                      ((idex_rd_addr == id_rs1_addr) ||
                       (idex_rd_addr == id_rs2_addr));

  // Exception / branch flush is broadcast to IF/ID and ID/EX.
  assign flush_ifid = ex_flush;
  assign flush_idex = ex_flush;

endmodule : merlin_hazard
