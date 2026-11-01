// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rvfi_wrapper (formal_merlin.sv)
// Purpose: riscv-formal RVFI wrapper for merlin_core. imem/dmem read data
//          are free formal inputs; the halting beat maps to rvfi_halt;
//          privilege/ixl outputs tie off to M-mode/RV32. Mirrors
//          vendor/riscv-formal/cores/picorv32/wrapper.sv and
//          formal/kestrel/riscv-formal/formal_kestrel.sv.
//
//          merlin is a 5-stage pipeline that retires in WB.  All rvfi_*
//          outputs are aggregated at the WB stage, so the wrapper binds
//          them directly; memory request timing (MEM stage) is internal to
//          the core and does not change the retire-beat contract.
//
// Documentation: projects/components/riscv-ip/merlin-rv32i/PRD.md
// Subsystem: riscv-ip/merlin-rv32i
//
// Author: sean galloway
// Created: 2026-11-01

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

    // Halt: the halting instruction (ecall/ebreak/illegal/misaligned) retires
    // as an rvfi_trap beat and is the last retirement — exactly rvfi_halt
    // semantics, since merlin has no trap handler to redirect to.
    (* keep *) wire       halt;
    (* keep *) wire [3:0] halt_cause;

    // Raw RVFI source-register fields from the core.  merlin (like kestrel)
    // drives rs1/rs2 address from the encoding bits unconditionally, but
    // riscv-formal's reg check treats any non-zero rvfi_rs1_addr as an
    // architectural read.  In the 5-stage pipeline the ID-stage read can be
    // stale for instructions that do not actually use that source (e.g. LUI
    // bits [19:15] happen to match a recently-written register).  The wrapper
    // therefore masks off unused source addresses/data to match RVFI
    // convention, exactly as if the core had reported them as unused.
    (* keep *) wire [4:0]  core_rvfi_rs1_addr;
    (* keep *) wire [4:0]  core_rvfi_rs2_addr;
    (* keep *) wire [31:0] core_rvfi_rs1_rdata;
    (* keep *) wire [31:0] core_rvfi_rs2_rdata;

    // Memory wait (registered-read block-RAM wrapper): a free input, so every
    // check holds under ANY wait-state pattern, bounded to at most two
    // consecutive wait cycles -- the wrapper's worst case (fetch, then a
    // load read) -- which keeps the liveness check meaningful.
    (* keep *) `rvformal_rand_reg mem_wait_any;
    reg  [1:0] wait_run;
    wire       mem_wait = mem_wait_any && (wait_run < 2'd2);

    always @(posedge clock) begin
        if (reset)         wait_run <= 2'd0;
        else if (mem_wait) wait_run <= wait_run + 2'd1;
        else               wait_run <= 2'd0;
    end

    merlin_core u_merlin_core (
        .clk            (clock       ),
        .rst_n          (~reset      ),
        .mem_wait       (mem_wait    ),
        .imem_addr      (imem_addr   ),
        .imem_addr_next (),
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
        .rvfi_rs1_addr  (core_rvfi_rs1_addr),
        .rvfi_rs2_addr  (core_rvfi_rs2_addr),
        .rvfi_rs1_rdata (core_rvfi_rs1_rdata),
        .rvfi_rs2_rdata (core_rvfi_rs2_rdata),
        .rvfi_rd_addr   (rvfi_rd_addr),
        .rvfi_rd_wdata  (rvfi_rd_wdata),
        .rvfi_mem_addr  (rvfi_mem_addr),
        .rvfi_mem_rmask (rvfi_mem_rmask),
        .rvfi_mem_wmask (rvfi_mem_wmask),
        .rvfi_mem_rdata (rvfi_mem_rdata),
        .rvfi_mem_wdata (rvfi_mem_wdata)
    );

    // merlin_core has no halt/intr/mode/ixl RVFI ports; the wrapper
    // generates them. halt is only visible with a retirement beat.
    assign rvfi_halt = rvfi_valid & halt;
    assign rvfi_intr = 1'b0;
    assign rvfi_mode = 2'b11;   // M-mode
    assign rvfi_ixl  = 2'b01;   // XLEN = 32

    // Source-register correction: zero out unused sources so riscv-formal
    // does not interpret encoding-bit coincidences as architectural reads.
    localparam logic [6:0] OPCODE_LUI    = 7'b0110111;
    localparam logic [6:0] OPCODE_AUIPC  = 7'b0010111;
    localparam logic [6:0] OPCODE_JAL    = 7'b1101111;
    localparam logic [6:0] OPCODE_JALR   = 7'b1100111;
    localparam logic [6:0] OPCODE_LOAD   = 7'b0000011;
    localparam logic [6:0] OPCODE_OP_IMM = 7'b0010011;
    localparam logic [6:0] OPCODE_FENCE  = 7'b0001111;
    localparam logic [6:0] OPCODE_SYSTEM = 7'b1110011;

    wire [6:0] opcode = rvfi_insn[6:0];
    wire [2:0] funct3 = rvfi_insn[14:12];

    wire rs1_used =
        ~((opcode == OPCODE_LUI)  ||
          (opcode == OPCODE_AUIPC)||
          (opcode == OPCODE_JAL)  ||
          (opcode == OPCODE_FENCE)||
          ((opcode == OPCODE_SYSTEM) && (funct3 == 3'b000)) ||  // ECALL/EBREAK/MRET
          ((opcode == OPCODE_SYSTEM) && (funct3[2] == 1'b1)));   // CSRRWI/CSRRSI/CSRRCI

    wire rs2_used =
        ~((opcode == OPCODE_LUI)  ||
          (opcode == OPCODE_AUIPC)||
          (opcode == OPCODE_JAL)  ||
          (opcode == OPCODE_JALR) ||
          (opcode == OPCODE_LOAD) ||
          (opcode == OPCODE_OP_IMM)||
          (opcode == OPCODE_FENCE)||
          (opcode == OPCODE_SYSTEM));

    assign rvfi_rs1_addr  = rs1_used ? core_rvfi_rs1_addr  : 5'd0;
    assign rvfi_rs2_addr  = rs2_used ? core_rvfi_rs2_addr  : 5'd0;
    assign rvfi_rs1_rdata = rs1_used ? core_rvfi_rs1_rdata : 32'd0;
    assign rvfi_rs2_rdata = rs2_used ? core_rvfi_rs2_rdata : 32'd0;

endmodule : rvfi_wrapper
