// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: tc_sram
// Purpose:
//   House stand-in for pulp-platform tech_cells_generic's tc_sram, the
//   technology cell CVA6's sram wrapper (vendor/cva6-dcache/common/local/
//   util/sram.sv -> tc_sram_wrapper -> tc_sram) expects. A synchronous,
//   byte-enabled, single-cycle-read memory in the style Vivado infers block
//   RAM from; NumPorts independent ports (CVA6's data cache uses one), read
//   latency one cycle (the only value the cache's wrapper asks for; the
//   Latency parameter is accepted and not otherwise used). NO_CHANGE read
//   during a write, as upstream's model.
//   tech_cells_generic itself is not vendored: this is the whole of what the
//   reference rig needs from it (cache-ip common-ip TASK-003).
//
// Author: sean galloway
// Created: 2026-11-11
`timescale 1ns / 1ps

module tc_sram #(
    parameter int unsigned NumWords    = 32'd1024,
    parameter int unsigned DataWidth   = 32'd128,
    parameter int unsigned ByteWidth   = 32'd8,
    parameter int unsigned NumPorts    = 32'd2,
    parameter int unsigned Latency     = 32'd1,
    parameter              SimInit     = "none",
    parameter bit          PrintSimCfg = 1'b0,
    parameter int unsigned AddrWidth = (NumWords > 32'd1) ? $clog2(NumWords) : 32'd1,
    parameter int unsigned BeWidth   = (DataWidth + ByteWidth - 32'd1) / ByteWidth
) (
    input  logic                                 clk_i,
    input  logic                                 rst_ni,
    input  logic [NumPorts-1:0]                  req_i,
    input  logic [NumPorts-1:0]                  we_i,
    input  logic [NumPorts-1:0][AddrWidth-1:0]   addr_i,
    input  logic [NumPorts-1:0][DataWidth-1:0]   wdata_i,
    input  logic [NumPorts-1:0][BeWidth-1:0]     be_i,
    output logic [NumPorts-1:0][DataWidth-1:0]   rdata_o
);
    // Plain packed vectors on the ports (no `parameter type`, no initial
    // block): Vivado 2025.1 synthesized the typed-port version of this module
    // to an empty black box without a message (ref cva6 bin 1).
    /* verilator lint_off UNUSEDSIGNAL */
    logic w_unused_rst;
    assign w_unused_rst = rst_ni;   // the array is not reset (block RAM)
    /* verilator lint_on UNUSEDSIGNAL */

    logic [DataWidth-1:0] r_mem [NumWords];

    for (genvar p = 0; p < NumPorts; p++) begin : gen_port
        always_ff @(posedge clk_i) begin
            if (req_i[p]) begin
                if (we_i[p]) begin
                    for (int b = 0; b < BeWidth; b++) begin
                        if (be_i[p][b]) begin
                            r_mem[addr_i[p]][b*ByteWidth +: ByteWidth] <= wdata_i[p][b*ByteWidth +: ByteWidth];
                        end
                    end
                end else begin
                    rdata_o[p] <= r_mem[addr_i[p]];
                end
            end
        end
    end
endmodule : tc_sram
