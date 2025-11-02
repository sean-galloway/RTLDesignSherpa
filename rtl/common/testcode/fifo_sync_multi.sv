// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: fifo_sync_multi
// Purpose: Fifo Sync Multi module
//
// Documentation: rtl/common/PRD.md
// Subsystem: common
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Parameterized Synchronous FIFO -- This works with any depth
module fifo_sync_multi #(
    parameter int REGISTERED = 0,  // 0 = mux mode, 1 = flop mode
    parameter int ADDR_WIDTH = 4,
    parameter int CTRL_WIDTH = 4,
    parameter int DATA_WIDTH = 4,
    parameter int DEPTH = 4,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter INSTANCE_NAME = "DEADF1F0",  // verilog_lint: waive explicit-parameter-storage-type
    parameter int AW = ADDR_WIDTH,
    parameter int CW = CTRL_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int D = DEPTH
) (
    input  logic                    clk,
                                    rst_n,
    input  logic                    write,
    input  logic [AW-1:0]           wr_addr,
    input  logic [CW-1:0]           wr_ctrl,
    input  logic [DW-1:0]           wr_data0,
    input  logic [DW-1:0]           wr_data1,

    output logic                    wr_full,
    output logic                    wr_almost_full,
    input  logic                    read,
    output logic [AW-1:0]           rd_addr,
    output logic [CW-1:0]           rd_ctrl,
    output logic [DW-1:0]           rd_data0,
    output logic [DW-1:0]           rd_data1,
    output logic                    rd_empty,
    output logic                    rd_almost_empty
);

    fifo_sync #(
        .REGISTERED        (REGISTERED),
        .DATA_WIDTH        (AW+CW+DW+DW),
        .DEPTH             (DEPTH),
        .ALMOST_WR_MARGIN  (ALMOST_WR_MARGIN),
        .ALMOST_RD_MARGIN  (ALMOST_RD_MARGIN),
        .INSTANCE_NAME     ("fifo_multi")
    ) u_fifo_sync (
        // Clocks & Reset
        .clk              (clk),
        .rst_n            (rst_n),

        // Write side
        .write            (write),
        .wr_data          ({wr_addr, wr_ctrl, wr_data1, wr_data0}),
        .wr_full          (wr_full),
        .wr_almost_full   (wr_almost_full),

        // Read side
        .read             (read),
        .rd_data          ({rd_addr,  rd_ctrl,  rd_data1,  rd_data0}),
        .rd_empty         (rd_empty),
        .rd_almost_empty  (rd_almost_empty)
    );

endmodule : fifo_sync_multi
