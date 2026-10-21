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
//   - USE_DSP (default 0): 1 builds the add/subtract row in kestrel_alu_dsp,
//     one DSP48E1 post-adder, instead of a CARRY4 chain.  Bitwise, shift and
//     set-less-than rows stay in fabric (Vivado will not infer the DSP's
//     logic unit from a case that mixes them in; see kestrel_alu_dsp).  The attribute affects
//     synthesis only: simulation, lint and formal see the same logic for
//     both settings.

`timescale 1ns / 1ps

module kestrel_alu #(
    parameter bit USE_DSP = 1'b0
) (
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

    // The add/sub row.  With USE_DSP it is kestrel_alu_dsp: one DSP48E1
    // post-adder (module-level use_dsp; Vivado maps a lone add/sub, but not
    // a case that also selects the bitwise rows, which stay in fabric).
    logic [31:0] y_addsub;

    generate
        if (USE_DSP) begin : g_dsp
            kestrel_alu_dsp u_dsp (.sub(op == SUB), .a(a), .b(b), .y(y_addsub));
        end else begin : g_fabric
            assign y_addsub = (op == SUB) ? (a - b) : (a + b);
        end
    endgenerate

    always_comb begin
        unique case (op)
            ADD, SUB: y = y_addsub;
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
