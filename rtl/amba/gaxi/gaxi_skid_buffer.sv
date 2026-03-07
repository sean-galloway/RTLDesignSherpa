// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gaxi_skid_buffer
// Purpose: Gaxi Skid Buffer module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gaxi_skid_buffer #(
    parameter int DATA_WIDTH = 32,
    parameter int DEPTH = 2, // Must be one of {2, 4, 6, 8}
    /* verilator lint_off UNUSEDPARAM */
    parameter     INSTANCE_NAME = "DEADF1F0",  // verilog_lint: waive explicit-parameter-storage-type
    /* verilator lint_on UNUSEDPARAM */
    parameter int DW = DATA_WIDTH,
    parameter int BUF_WIDTH = DATA_WIDTH * DEPTH,
    parameter int BW = BUF_WIDTH
) (
    // Global Clock and Reset
    input  logic          axi_aclk,
    input  logic          axi_aresetn,

    // input side
    input  logic          wr_valid,
    output logic          wr_ready,
    input  logic [DW-1:0] wr_data,

    // output side
    output logic [3:0]    count,
    output logic          rd_valid,
    input  logic          rd_ready,
    output logic [3:0]    rd_count,
    output logic [DW-1:0] rd_data
);

    logic [BW-1:0]         r_data;
    logic [3:0]            r_data_count;
    logic                  w_wr_xfer;
    logic                  w_rd_xfer;
    logic [DW-1:0]         zeros;

    assign zeros     = 'b0;
    assign w_wr_xfer = wr_valid & wr_ready;
    assign w_rd_xfer = rd_valid & rd_ready;

    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            r_data <= 'b0;
            r_data_count <= 'b0;
        end else begin
            case ({w_wr_xfer, w_rd_xfer})
                2'b10: begin  // Write only
                    r_data[(DW * r_data_count) +: DW] <= wr_data;
                    r_data_count <= r_data_count + 1;
                end
                2'b01: begin  // Read only
                    r_data <= {zeros, r_data[BUF_WIDTH-1:DW]};
                    r_data_count <= r_data_count - 1;
                end
                2'b11: begin  // Simultaneous write and read
                    r_data <= {zeros, r_data[BUF_WIDTH-1:DW]};
                    r_data[(DW * (32'(r_data_count) - 1)) +: DW] <= wr_data;
                end
                default: begin  // 2'b00: No operation
                    // No changes to r_data or r_data_count
                end
            endcase
        end
    )


    `ALWAYS_FF_RST(axi_aclk, axi_aresetn,
        if (`RST_ASSERTED(axi_aresetn)) begin
            wr_ready <= 1'b0;
            rd_valid <= 1'b0;
        end else begin
            wr_ready <= (32'(r_data_count) <= DEPTH-2) ||
                            (32'(r_data_count) == DEPTH-1 && (~w_wr_xfer || w_rd_xfer)) ||
                            (32'(r_data_count) == DEPTH && w_rd_xfer);

            rd_valid <= (r_data_count >= 2) ||
                            (r_data_count == 4'b0001 && (~w_rd_xfer || w_wr_xfer)) ||
                            (r_data_count == 4'b0000 && w_wr_xfer);
        end
    )


    assign rd_data  = r_data[DW-1:0];
    assign rd_count = r_data_count;
    assign count   = r_data_count;

endmodule : gaxi_skid_buffer
