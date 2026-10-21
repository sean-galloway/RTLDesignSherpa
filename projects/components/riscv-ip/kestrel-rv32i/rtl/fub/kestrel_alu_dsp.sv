// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_alu_dsp
// Purpose: kestrel_alu's add / subtract row, marked for DSP48 mapping
//          (kestrel_alu USE_DSP = 1): one DSP48E1 post-adder, no LUTs.
//
// Documentation: projects/components/riscv-ip/kestrel-rv32i/docs/kestrel_mas
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-20
//
// Notes:
//   - The add/sub must be the only thing here.  Measured on xc7a100t
//     (Vivado 2025.1, out of context): `sub ? a - b : a + b` under
//     use_dsp = "yes" maps to one DSP48E1 and 0 LUTs, but a case that also
//     selects AND/OR/XOR maps to no DSP at all (161 LUTs), even with
//     use_dsp = "logic".  So the bitwise rows stay in fabric.
//   - The same function as kestrel_alu's fabric add/sub; only the attribute
//     differs, so simulation and formal see identical logic.

`timescale 1ns / 1ps

(* use_dsp = "yes" *)
module kestrel_alu_dsp (
    input  logic        sub,
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] y
);

    assign y = sub ? (a - b) : (a + b);

endmodule : kestrel_alu_dsp
