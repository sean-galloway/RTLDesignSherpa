// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gatling_pkg
// Purpose: Shared constants for the gatling barrel RV32I engine.  The ISA
//          vocabulary (alu_op_e, the halt-cause encoding) is kestrel's and
//          comes from kestrel_pkg; this package holds only what the barrel
//          adds.
//
// Documentation: projects/components/riscv-ip/gatling-rv32itetrad/docs/gatling_mas
// Subsystem: riscv-ip/gatling-rv32itetrad
//
// Author: sean galloway
// Created: 2026-10-21

`timescale 1ns / 1ps

package gatling_pkg;

    // Four contexts, one per cell of the tetrad (PRD 4.1).  Not a free
    // parameter: the rotation length IS the stage count (F/D/X/W), which is
    // what keeps exactly one instruction of each context in flight and makes
    // the pipeline hazard-free.  More contexts would need more stages or a
    // context in no stage at all.
    localparam int NUM_HARTS = 4;
    localparam int HART_W    = 2;

endpackage : gatling_pkg
