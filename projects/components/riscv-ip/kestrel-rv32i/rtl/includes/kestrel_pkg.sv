// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_pkg
// Purpose: Shared parameters and enums for the kestrel-rv32i core.
//
// Documentation: projects/components/riscv-ip/README.md
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-06

`timescale 1ns / 1ps

package kestrel_pkg;

    localparam int XLEN = 32;

    typedef enum logic [3:0] {
        ADD,
        SUB,
        AND,
        OR,
        XOR,
        SLL,
        SRL,
        SRA,
        SLT,
        SLTU
    } alu_op_e;

    typedef enum logic [2:0] {
        I,
        S,
        B,
        U,
        J
    } imm_sel_e;

    // Halt-cause encoding, single source of truth for kestrel_decode
    // (ecall/ebreak/illegal) and kestrel_core (misaligned control-flow
    // target, Task 9; misaligned load/store address, 2026-10-20).  Causes
    // 3-5 are raised only in the core: decode cannot see them, they need
    // the resolved next-PC or the access address.
    localparam logic [3:0] HALT_NONE   = 4'h0;
    localparam logic [3:0] HALT_ECALL  = 4'h1;
    localparam logic [3:0] HALT_EBREAK = 4'h2;
    localparam logic [3:0] HALT_IALIGN = 4'h3;
    localparam logic [3:0] HALT_LALIGN = 4'h4;   // load address misaligned
    localparam logic [3:0] HALT_SALIGN = 4'h5;   // store address misaligned
    localparam logic [3:0] HALT_ILL    = 4'hF;

endpackage : kestrel_pkg
