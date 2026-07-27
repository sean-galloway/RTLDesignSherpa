// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gaxi_fifo_async_multi
// Purpose: Gaxi Fifo Async Multi module
//
// Documentation: docs/markdown/rtl-amba/index.md
// Subsystem: amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

// Parameterized Asynchronous FIFO -- any DEPTH with Johnson pointers,
// power-of-2 DEPTH with Gray.
module gaxi_fifo_async_multi #(
    parameter int ADDR_WIDTH = 4,
    parameter int CTRL_WIDTH = 4,
    parameter int DATA_WIDTH = 8,
    // DEPTH defaults to a POWER OF TWO so the default USE_JOHNSON=0 (Gray)
    // elaborates. It was 10, which forced Johnson on by default.
    parameter int DEPTH = 8,
    // Pointer encoding: 0 = Gray (power-of-2 DEPTH), 1 = Johnson (any DEPTH).
    // Gray by default; Johnson is opt-in and must be a conscious choice.
    parameter int USE_JOHNSON = 0,
    parameter int N_FLOP_CROSS = 2,
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter int AW = ADDR_WIDTH,
    parameter int CW = CTRL_WIDTH,
    parameter int DW = DATA_WIDTH,
    parameter int D = DEPTH,
    parameter int PAW = $clog2(DEPTH),
    parameter int JCW = D,  // Johnson Counter Width
    parameter int N = N_FLOP_CROSS
) (
    // clocks and resets
    input  logic            axi_wr_aclk,
                            axi_wr_aresetn,
                            axi_rd_aclk,
                            axi_rd_aresetn,
    input  logic            wr_valid,
    output logic            wr_ready,   // not full
    input  logic [AW-1:0]   wr_addr,
    input  logic [CW-1:0]   wr_ctrl,
    input  logic [DW-1:0]   wr_data0,
    input  logic [DW-1:0]   wr_data1,
    input  logic            rd_ready,
    output logic            rd_valid,   // not empty
    output logic [AW-1:0]   rd_addr,
    output logic [CW-1:0]   rd_ctrl,
    output logic [DW-1:0]   rd_data0,
    output logic [DW-1:0]   rd_data1
    );


    // Payload is the concatenation {wr_addr, wr_ctrl, wr_data1, wr_data0}.
    //
    // Set DATA_WIDTH -- NOT the derived DW alias. gaxi_fifo_async declares
    // `DW = DATA_WIDTH` and sizes its PORTS from DW but its MEMORY from
    // DATA_WIDTH, so overriding DW alone widens the ports while leaving the
    // storage narrow: the FIFO would silently drop the upper bits of every
    // entry. For the same reason D/AW/JCW/N are left derived rather than
    // overridden -- they are aliases, not independent knobs.
    //
    // USE_JOHNSON comes from the port list rather than being hardcoded here --
    // see the rule in vault/handbook/design/cdc.md. Gray by default; pass 1 to
    // use a non-power-of-2 DEPTH.
    gaxi_fifo_async #(
        .DATA_WIDTH        (AW + CW + DW + DW),  // full concatenated payload
        .DEPTH             (DEPTH),
        .USE_JOHNSON       (USE_JOHNSON),
        .N_FLOP_CROSS      (N_FLOP_CROSS),
        .ALMOST_WR_MARGIN  (ALMOST_WR_MARGIN),
        .ALMOST_RD_MARGIN  (ALMOST_RD_MARGIN)
    ) u_gaxi_fifo_async (
        // Clocks and resets
        .axi_wr_aclk     (axi_wr_aclk),    // Write clock
        .axi_wr_aresetn  (axi_wr_aresetn), // Write reset (active low)
        .axi_rd_aclk     (axi_rd_aclk),    // Read clock
        .axi_rd_aresetn  (axi_rd_aresetn), // Read reset (active low)

        // Write interface
        .wr_valid        (wr_valid),       // Write valid signal
        .wr_ready        (wr_ready),       // Write ready (not full)
        .wr_data         ({wr_addr, wr_ctrl, wr_data1, wr_data0}),        // Write data

        // Read interface
        .rd_ready        (rd_ready),       // Read ready signal
        .rd_valid        (rd_valid),       // Read valid (not empty)
        .rd_data         ({rd_addr, rd_ctrl, rd_data1, rd_data0})
    );


endmodule : gaxi_fifo_async_multi
