// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_regfile
// Purpose: Thirty-two-entry RV32I register file with combinational read ports
//          and a single synchronous write port that discards writes to x0.
//
// Documentation: projects/components/riscv-ip/README.md
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-06

`timescale 1ns / 1ps

`include "reset_defs.svh"

module kestrel_regfile (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [4:0]  rs1_addr,
    output logic [31:0] rs1_data,
    input  logic [4:0]  rs2_addr,
    output logic [31:0] rs2_data,
    input  logic [4:0]  rd_addr,
    input  logic [31:0] rd_data,
    input  logic        rd_wen
);

    localparam int REG_COUNT      = 32;
    localparam int REG_ADDR_WIDTH = 5;
    localparam logic [REG_ADDR_WIDTH-1:0] X0_ADDR = '0;

    logic [31:0] regs [REG_COUNT];

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            for (int i = 0; i < REG_COUNT; i++) begin
                regs[i] <= '0;
            end
        end else begin
            if (rd_wen && (rd_addr != X0_ADDR)) begin
                regs[rd_addr] <= rd_data;
            end
        end
    )

    assign rs1_data = regs[rs1_addr];
    assign rs2_data = regs[rs2_addr];

endmodule : kestrel_regfile
