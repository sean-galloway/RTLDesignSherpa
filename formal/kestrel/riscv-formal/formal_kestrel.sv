// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rvfi_wrapper (formal_kestrel.sv)
// Purpose: riscv-formal RVFI wrapper for kestrel_core. imem/dmem read data
//          are free formal inputs; the Task-8 halt beat maps to rvfi_halt;
//          privilege/ixl outputs tie off to M-mode/RV32. Mirrors
//          vendor/riscv-formal/cores/picorv32/wrapper.sv.
//
// Documentation: projects/components/riscv-ip/README.md
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-06

`timescale 1ns / 1ps

// Defaults so this file parses standalone (pre-commit verilator gate); the
// riscv-formal flow provides the same values from its generated defines.sv
// before reading the wrapper, and `ifndef keeps those authoritative.
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

    // Free formal memory read data. Addresses, strobes, and write data come
    // from the core; read data is unconstrained per cycle. The riscv-formal
    // checks relate the core's reported rvfi_mem_* and register writeback
    // back to the ISA model (picorv32 wrapper shape — no memory array here).
    (* keep *) `rvformal_rand_reg [31:0] imem_rdata;
    (* keep *) `rvformal_rand_reg [31:0] dmem_rdata;

    // Core memory interface.
    (* keep *) wire [31:0] imem_addr;
    (* keep *) wire        dmem_req;
    (* keep *) wire [31:0] dmem_addr;
    (* keep *) wire [3:0]  dmem_wstrb;
    (* keep *) wire [31:0] dmem_wdata;

    // Task-8 halt: the halting instruction (ecall/ebreak/illegal) retires as
    // an rvfi_trap beat and is the last retirement — exactly rvfi_halt
    // semantics, since kestrel has no trap handler to redirect to.
    (* keep *) wire       halt;
    (* keep *) wire [3:0] halt_cause;

    kestrel_core u_kestrel_core (
        .clk            (clock       ),
        .rst_n          (~reset      ),
        .imem_addr      (imem_addr   ),
        .imem_rdata     (imem_rdata  ),
        .dmem_req       (dmem_req    ),
        .dmem_addr      (dmem_addr   ),
        .dmem_rdata     (dmem_rdata  ),
        .dmem_wstrb     (dmem_wstrb  ),
        .dmem_wdata     (dmem_wdata  ),
        .halt           (halt        ),
        .halt_cause     (halt_cause  ),
        .rvfi_valid     (rvfi_valid  ),
        .rvfi_order     (rvfi_order  ),
        .rvfi_pc_rdata  (rvfi_pc_rdata),
        .rvfi_pc_wdata  (rvfi_pc_wdata),
        .rvfi_insn      (rvfi_insn   ),
        .rvfi_trap      (rvfi_trap   ),
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

    // kestrel_core has no halt/intr/mode/ixl RVFI ports; the wrapper
    // generates them. halt is only visible with a retirement beat.
    assign rvfi_halt = rvfi_valid & halt;
    assign rvfi_intr = 1'b0;
    assign rvfi_mode = 2'b11;   // M-mode
    assign rvfi_ixl  = 2'b01;   // XLEN = 32

endmodule : rvfi_wrapper
