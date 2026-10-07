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

    always_comb begin
        unique case (op)
            ADD:  y = a + b;
            SUB:  y = a - b;
            AND:  y = a & b;
            OR:   y = a | b;
            XOR:  y = a ^ b;
            SLL:  y = a << shamt;
            SRL:  y = a >> shamt;
            SRA:  y = $signed(a) >>> shamt;
            SLT:  y = {{PAD_WIDTH{1'b0}}, lt};
            SLTU: y = {{PAD_WIDTH{1'b0}}, ltu};
            default: y = '0;
        endcase
    end

endmodule : kestrel_alu
