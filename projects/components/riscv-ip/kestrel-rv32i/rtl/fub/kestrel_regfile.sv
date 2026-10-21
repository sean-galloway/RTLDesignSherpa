// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_regfile
// Purpose: Thirty-two-entry RV32I register file: two combinational read
//          ports and one synchronous write port over plain storage.
//
// Documentation: projects/components/riscv-ip/README.md
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-06
//
// Notes:
//   - No reset (2026-10-20, owner): the array maps to distributed RAM
//     instead of 1,024 flops.  Registers hold whatever they held -- after
//     power-up, or the previous program after a reload -- until written.
//     Every program initializes each register it reads (the riscv-tests
//     p-env does, INIT_XREG; the golden interpreter flags any program that
//     reads a register it never wrote).
//   - No x0 logic here: entry 0 is ordinary storage.  kestrel_core keeps it
//     zero by writing zero to it in reset and on every write that targets
//     x0, so neither read port needs a zero-select.

`timescale 1ns / 1ps

module kestrel_regfile (
    input  logic        clk,
    input  logic [4:0]  rs1_addr,
    output logic [31:0] rs1_data,
    input  logic [4:0]  rs2_addr,
    output logic [31:0] rs2_data,
    input  logic [4:0]  rd_addr,
    input  logic [31:0] rd_data,
    input  logic        rd_wen
);

    localparam int REG_COUNT = 32;

`ifdef XILINX
    (* ram_style = "distributed" *)
`elsif SYNTH_PRAGMA
    /* synthesis ramstyle = "MLAB" */
`endif
    logic [31:0] regs [REG_COUNT];

    always_ff @(posedge clk) begin
        if (rd_wen) regs[rd_addr] <= rd_data;
    end

    assign rs1_data = regs[rs1_addr];
    assign rs2_data = regs[rs2_addr];

endmodule : kestrel_regfile
