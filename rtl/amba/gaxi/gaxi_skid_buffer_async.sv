// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gaxi_skid_buffer_async
// Purpose: Gaxi Skid Buffer Async module
//
// Documentation: rtl/amba/PRD.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

`include "fifo_defs.svh"

// AXI Skid buffer where all ports are driven or received by a flop
module gaxi_skid_buffer_async #(
    parameter fifo_mem_t MEM_STYLE = FIFO_AUTO,
    parameter int REGISTERED = 0,  // 0 = mux mode, 1 = flop mode
    parameter int DATA_WIDTH    = 32,
    parameter int DEPTH         = 2,
    parameter int N_FLOP_CROSS  = 2,
    parameter     INSTANCE_NAME = "DEADF1F0",  // verilog_lint: waive explicit-parameter-storage-type
    parameter int DW = DATA_WIDTH
) (
    // Global Clock and Reset
    input  logic          axi_wr_aclk,
    input  logic          axi_wr_aresetn,
    input  logic          axi_rd_aclk,
    input  logic          axi_rd_aresetn,

    // input side
    input  logic          wr_valid,
    output logic          wr_ready,
    input  logic [DW-1:0] wr_data,

    // output side
    output logic          rd_valid,
    input  logic          rd_ready,
    output logic [DW-1:0] rd_data
);

    logic           r_xfer_valid;
    logic           r_xfer_ready;
    logic [DW-1:0]  r_xfer_data;

    // Instantiate the axi_skid_buffer module
    gaxi_skid_buffer #(
        .DATA_WIDTH   (DW)
    ) inst_gaxi_skid_buffer (
        .axi_aclk   (axi_wr_aclk),
        .axi_aresetn(axi_wr_aresetn),
        .wr_valid   (wr_valid),
        .wr_ready   (wr_ready),
        .wr_data    (wr_data),
        .rd_valid   (r_xfer_valid),
        .rd_ready   (r_xfer_ready),
        .rd_data    (r_xfer_data),
        .rd_count   (),
        .count     ()
    );

    // Instantiate the axi_fifo_async module
    gaxi_fifo_async #(
        .MEM_STYLE       (MEM_STYLE),
        .DATA_WIDTH      (DW),
        .DEPTH           (DEPTH),
        .N_FLOP_CROSS    (N_FLOP_CROSS),
        .ALMOST_WR_MARGIN(1),
        .ALMOST_RD_MARGIN(1),
        .INSTANCE_NAME   (INSTANCE_NAME),
        .REGISTERED      (REGISTERED)
    ) inst_gaxi_fifo_async (
        .axi_wr_aclk   (axi_wr_aclk),
        .axi_wr_aresetn(axi_wr_aresetn),
        .axi_rd_aclk   (axi_rd_aclk),
        .axi_rd_aresetn(axi_rd_aresetn),
        .wr_valid      (r_xfer_valid),
        .wr_ready      (r_xfer_ready),
        .wr_data       (r_xfer_data),
        .rd_ready      (rd_ready),
        .rd_valid      (rd_valid),
        .rd_data       (rd_data)
    );

    // -------------------------------------------------------------------------
    // Simulation-only: Instance report (grep for FIFO_INSTANCE)
    // -------------------------------------------------------------------------
    // synopsys translate_off
    initial begin
        $display("FIFO_INSTANCE: gaxi_skid_buffer_async %m %s W=%0d D=%0d CDC=%0d", INSTANCE_NAME, DW, DEPTH, N_FLOP_CROSS);
    end
    // synopsys translate_on

endmodule : gaxi_skid_buffer_async
