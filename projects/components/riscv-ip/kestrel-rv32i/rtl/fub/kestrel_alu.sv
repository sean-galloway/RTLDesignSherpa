// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_alu
// Purpose: RV32I ALU and branch comparator.
//
// Documentation: projects/components/riscv-ip/README.md
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-06
//
// Notes:
//   - Fabric only.  A DSP48E1 variant (seven rows in one slice) was built,
//     verified and measured on the Nexys A7, and removed: it saved no LUTs
//     and cost slices and slack (kestrel MAS, kestrel_alu chapter).

`timescale 1ns / 1ps

module kestrel_alu (
    input  kestrel_pkg::alu_op_e op,
    input  logic [31:0]          a,
    input  logic [31:0]          b,
    output logic [31:0]          y,
    output logic                 eq,
    output logic                 lt,
    output logic                 ltu
);

    import kestrel_pkg::*;

    localparam int SHAMT_WIDTH = 5;
    localparam int PAD_WIDTH   = 31;

    logic signed [31:0] a_signed;
    logic signed [31:0] b_signed;
    logic        [SHAMT_WIDTH-1:0] shamt;

    assign a_signed = $signed(a);
    assign b_signed = $signed(b);
    assign shamt    = b[SHAMT_WIDTH-1:0];

    assign eq  = (a == b);
    assign lt  = (a_signed < b_signed);
    assign ltu = (a < b);

    // The add/sub row (subtract is add of the inverted operand plus a
    // carry-in) and SLT/SLTU (operands extended to 33 bits with the sign
    // bit for SLT and a zero for SLTU, compared signed; the lt/ltu flag
    // ports keep their own compares, unconnected in kestrel_core).
    logic        is_sub;
    logic        slt_signed;
    logic [31:0] y_addsub;
    logic        slt_lt;

    assign is_sub     = (op == SUB);
    assign y_addsub   = a + (b ^ {32{is_sub}}) + {31'd0, is_sub};
    assign slt_signed = (op == SLT);
    assign slt_lt     = ($signed({slt_signed & a[31], a})
                         < $signed({slt_signed & b[31], b}));

    // Result: every row is zero unless selected, and the rows are ORed --
    // no final multiplexer (2026-10-20; the OR-combined result is an idea
    // from the BRISKI barrel core).  An undefined op yields zero, as the
    // old default arm did.
    logic sel_addsub, sel_and, sel_or, sel_xor, sel_sll, sel_srl, sel_sra, sel_slt;

    assign sel_addsub = (op == ADD) || (op == SUB);
    assign sel_and    = (op == AND);
    assign sel_or     = (op == OR);
    assign sel_xor    = (op == XOR);
    assign sel_sll    = (op == SLL);
    assign sel_srl    = (op == SRL);
    assign sel_sra    = (op == SRA);
    assign sel_slt    = (op == SLT) || (op == SLTU);

    assign y = ({32{sel_addsub}} & y_addsub)
             | ({32{sel_and}}    & (a & b))
             | ({32{sel_or}}     & (a | b))
             | ({32{sel_xor}}    & (a ^ b))
             | ({32{sel_sll}}    & (a << shamt))
             | ({32{sel_srl}}    & (a >> shamt))
             | ({32{sel_sra}}    & 32'($signed(a) >>> shamt))
             | ({32{sel_slt}}    & {{PAD_WIDTH{1'b0}}, slt_lt});

endmodule : kestrel_alu
