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

endpackage : kestrel_pkg
