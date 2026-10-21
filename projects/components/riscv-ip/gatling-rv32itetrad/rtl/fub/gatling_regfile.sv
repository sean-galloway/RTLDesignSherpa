// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gatling_regfile
// Purpose: The four context register files of the gatling barrel as one
//          128-entry array ({context, register}): two registered read ports
//          and one write port, in block RAM.
//
// Documentation: projects/components/riscv-ip/gatling-rv32itetrad/docs/gatling_mas
// Subsystem: riscv-ip/gatling-rv32itetrad
//
// Author: sean galloway
// Created: 2026-10-21
//
// Notes:
//   - Registered read: the address is presented in the barrel's D stage and
//     the data appears in X, which is when the core needs it -- so block RAM
//     costs no cycle here.  Two read ports over one write port is two copies
//     of the array, each written on every write.
//   - x0 reads zero through a read-side mask registered with the address
//     (rs*_zero_q), applied to the RAM output.  kestrel keeps x0 zero by
//     writing it in reset instead; with four contexts that is four reset
//     writes, and the mask also makes a never-written block RAM read zero
//     for x0 in formal, where the array starts unconstrained.
//   - No reset on the array (SRAM rule): a context register holds whatever
//     it held until written.  The riscv-tests p-env initializes every
//     register it reads.
//   - The barrel never reads and writes the same context in one cycle (D and
//     W hold different contexts), so there is no read-during-write case.

`timescale 1ns / 1ps

module gatling_regfile (
    input  logic        clk,

    // Read: address in D, data in X
    input  logic [1:0]  rs_ctx,
    input  logic [4:0]  rs1_addr,
    input  logic [4:0]  rs2_addr,
    output logic [31:0] rs1_data,
    output logic [31:0] rs2_data,

    // Write (W stage)
    input  logic [1:0]  rd_ctx,
    input  logic [4:0]  rd_addr,
    input  logic [31:0] rd_data,
    input  logic        rd_wen
);

    localparam int ENTRIES = 128;     // 4 contexts x 32 registers

`ifdef XILINX
    (* ram_style = "block" *)
`elsif SYNTH_PRAGMA
    /* synthesis ramstyle = "M10K" */
`endif
    logic [31:0] regs_a [ENTRIES];
`ifdef XILINX
    (* ram_style = "block" *)
`elsif SYNTH_PRAGMA
    /* synthesis ramstyle = "M10K" */
`endif
    logic [31:0] regs_b [ENTRIES];

    logic [31:0] q1, q2;
    logic        rs1_zero_q, rs2_zero_q;

    always_ff @(posedge clk) begin
        if (rd_wen) regs_a[{rd_ctx, rd_addr}] <= rd_data;
        q1 <= regs_a[{rs_ctx, rs1_addr}];
    end

    always_ff @(posedge clk) begin
        if (rd_wen) regs_b[{rd_ctx, rd_addr}] <= rd_data;
        q2 <= regs_b[{rs_ctx, rs2_addr}];
    end

    always_ff @(posedge clk) begin
        rs1_zero_q <= (rs1_addr == 5'd0);
        rs2_zero_q <= (rs2_addr == 5'd0);
    end

    assign rs1_data = rs1_zero_q ? 32'd0 : q1;
    assign rs2_data = rs2_zero_q ? 32'd0 : q2;

endmodule : gatling_regfile
