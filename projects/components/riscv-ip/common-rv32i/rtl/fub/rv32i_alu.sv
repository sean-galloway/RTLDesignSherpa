// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rv32i_alu
// Purpose: RV32I ALU and branch comparator.  Shared by kestrel and gatling.
//
// Documentation: projects/components/riscv-ip/common-rv32i/README.md
// Subsystem: riscv-ip/common-rv32i
//
// Author: sean galloway
// Created: 2026-10-06
//
// Notes:
//   - Fabric only.  A DSP48E1 variant (seven rows in one slice) was built,
//     verified and measured on the Nexys A7, and removed: it saved no LUTs
//     and cost slices and slack (kestrel MAS, rv32i_alu chapter).
//   - One adder and one shifter (2026-11-19, riscv-ip common-rv32i
//     ISSUE-001 row 1): -205 to -306 LUT per core, routed on the Nexys A7.

`timescale 1ns / 1ps

module rv32i_alu (
    input  rv32i_pkg::alu_op_e op,
    input  logic [31:0]          a,
    input  logic [31:0]          b,
    output logic [31:0]          y,
    output logic                 eq,
    output logic                 lt,
    output logic                 ltu
);

    import rv32i_pkg::*;

    localparam int SHAMT_WIDTH = 5;
    localparam int PAD_WIDTH   = 31;

    logic [SHAMT_WIDTH-1:0] shamt;
    assign shamt = b[SHAMT_WIDTH-1:0];

    // Branch flags.  lt/ltu keep their own compares; the cores leave them
    // unconnected and branch on the result of their own comparators.
    assign eq  = (a == b);
    assign lt  = ($signed(a) < $signed(b));
    assign ltu = (a < b);

    // One 33-bit adder serves ADD, SUB, SLT and SLTU (FPGA review,
    // riscv-ip common-rv32i ISSUE-001 row 1).  The operands are extended to
    // 33 bits with the sign bit for SLT and a zero otherwise; subtract is the
    // add of the inverted operand plus a carry-in.  The low 32 bits are the
    // ADD/SUB result, and bit 32 of the extended difference is a < b (signed
    // for SLT, unsigned for SLTU).  Before this, SLT/SLTU had a second
    // 33-bit compare chain beside the adder.
    logic        is_slt;
    logic        is_sub;
    logic        slt_signed;
    logic [32:0] a_ext;
    logic [32:0] b_ext;
    logic [32:0] w_sum;

    assign is_slt     = (op == SLT) || (op == SLTU);
    assign is_sub     = (op == SUB) || is_slt;
    assign slt_signed = (op == SLT);
    assign a_ext      = {slt_signed & a[31], a};
    assign b_ext      = {slt_signed & b[31], b};
    assign w_sum      = a_ext + (b_ext ^ {33{is_sub}}) + {32'd0, is_sub};

    // One right shifter serves SRL, SRA and SLL.  SLL bit-reverses the
    // operand in and the result out, so a left shift is a logical right
    // shift of the reversed word; SRA fills with a[31], SRL and SLL with 0.
    // Before this, each of the three shifts was its own 32-bit barrel.
    logic        is_sll;
    logic        sh_fill;
    logic [31:0] a_rev;
    logic [31:0] sh_in;
    logic [31:0] sh_out;
    logic [31:0] sh_out_rev;

    assign is_sll  = (op == SLL);
    assign sh_fill = (op == SRA) & a[31];
    always_comb begin
        for (int i = 0; i < 32; i++) a_rev[i] = a[31-i];
    end
    assign sh_in  = is_sll ? a_rev : a;
    assign sh_out = 32'($signed({sh_fill, sh_in}) >>> shamt);
    always_comb begin
        for (int i = 0; i < 32; i++) sh_out_rev[i] = sh_out[31-i];
    end

    // Result: every row is zero unless selected, and the rows are ORed --
    // no final multiplexer (2026-10-20; the OR-combined result is an idea
    // from the BRISKI barrel core).  An undefined op yields zero, as the
    // old default arm did.
    logic sel_addsub, sel_and, sel_or, sel_xor, sel_sr;

    assign sel_addsub = (op == ADD) || (op == SUB);
    assign sel_and    = (op == AND);
    assign sel_or     = (op == OR);
    assign sel_xor    = (op == XOR);
    assign sel_sr     = (op == SRL) || (op == SRA);

    assign y = ({32{sel_addsub}} & w_sum[31:0])
             | ({32{sel_and}}    & (a & b))
             | ({32{sel_or}}     & (a | b))
             | ({32{sel_xor}}    & (a ^ b))
             | ({32{sel_sr}}     & sh_out)
             | ({32{is_sll}}     & sh_out_rev)
             | ({32{is_slt}}     & {{PAD_WIDTH{1'b0}}, w_sum[32]});

endmodule : rv32i_alu
