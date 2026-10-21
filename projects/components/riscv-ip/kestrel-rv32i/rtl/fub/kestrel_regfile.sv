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
//
// Notes:
//   - No reset (2026-10-20, owner): the array is plain storage, so it maps
//     to distributed RAM instead of 1,024 flops.  Registers hold whatever
//     they held -- after power-up, or the previous program after a reload
//     -- until written.  Every program must initialize each register it
//     reads (the riscv-tests p-env does, INIT_XREG; the golden interpreter
//     flags any program that reads a register it never wrote).
//   - x0 is not stored: both read ports return zero for address 0, and the
//     write to x0 is discarded.

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

    localparam int REG_COUNT      = 32;
    localparam int REG_ADDR_WIDTH = 5;
    localparam logic [REG_ADDR_WIDTH-1:0] X0_ADDR = '0;

`ifdef XILINX
    (* ram_style = "distributed" *)
`elsif SYNTH_PRAGMA
    /* synthesis ramstyle = "MLAB" */
`endif
    logic [31:0] regs [REG_COUNT];

    always_ff @(posedge clk) begin
        if (rd_wen && (rd_addr != X0_ADDR)) regs[rd_addr] <= rd_data;
    end

    assign rs1_data = (rs1_addr == X0_ADDR) ? 32'd0 : regs[rs1_addr];
    assign rs2_data = (rs2_addr == X0_ADDR) ? 32'd0 : regs[rs2_addr];

endmodule : kestrel_regfile
