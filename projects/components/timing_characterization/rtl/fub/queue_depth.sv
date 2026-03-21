// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: queue_depth
// Purpose: FIFO Queue Depth Characterization
//
// Description:
//   Wraps a gaxi_fifo_sync to characterize FIFO timing at various widths
//   and depths. LFSR data is written into the FIFO, and the read output
//   is captured by an output flip-flop. This measures the timing impact
//   of FIFO depth and width on synthesis, including memory inference
//   thresholds (distributed RAM vs. BRAM vs. URAM).
//
//   Structure:
//     i_wr_valid + i_wr_data --> gaxi_fifo_sync --> r_out_flop --> o_rd_data
//                                     ^
//                             i_rd_ready controls read side
//
// Parameters:
//   DATA_WIDTH - FIFO data width in bits (default: 32)
//   DEPTH      - FIFO depth in entries (default: 16, must be power of 2)
//
// Notes:
//   - gaxi_fifo_sync handles all FIFO control logic
//   - Output flop captures read data for timing characterization
//   - Sweep DATA_WIDTH to find BRAM/LUTRAM inference boundaries
//   - Sweep DEPTH to find memory type transitions
//   - o_count exposes FIFO occupancy for monitoring
//
// Documentation: projects/components/timing_characterization/README.md
// Subsystem: timing_characterization
//
// Author: sean galloway
// Created: 2026-03-17

`timescale 1ns / 1ps

`include "fifo_defs.svh"
`include "reset_defs.svh"

module queue_depth #(
    parameter int DATA_WIDTH = 32,
    parameter int DEPTH      = 16,

    // Derived parameters (do not override)
    parameter int AW = $clog2(DEPTH)
) (
    // Clock and Reset
    input  logic                 clk,
    input  logic                 rst_n,

    //=========================================================================
    // Write Interface
    //=========================================================================
    input  logic                 i_wr_valid,
    output logic                 o_wr_ready,
    input  logic [DATA_WIDTH-1:0] i_wr_data,

    //=========================================================================
    // Read Interface
    //=========================================================================
    input  logic                 i_rd_ready,
    output logic                 o_rd_valid,
    output logic [DATA_WIDTH-1:0] o_rd_data,

    //=========================================================================
    // Status
    //=========================================================================
    output logic [AW:0]          o_count
);

    //=========================================================================
    // FIFO Instance
    //=========================================================================

    logic                 w_fifo_rd_valid;
    logic [DATA_WIDTH-1:0] w_fifo_rd_data;

    gaxi_fifo_sync #(
        .DATA_WIDTH     (DATA_WIDTH),
        .DEPTH          (DEPTH),
        .ALMOST_WR_MARGIN (1),
        .ALMOST_RD_MARGIN (1)
    ) u_fifo (
        .axi_aclk      (clk),
        .axi_aresetn    (rst_n),
        .wr_valid       (i_wr_valid),
        .wr_ready       (o_wr_ready),
        .wr_data        (i_wr_data),
        .rd_ready       (i_rd_ready),
        .count          (o_count),
        .rd_valid       (w_fifo_rd_valid),
        .rd_data        (w_fifo_rd_data)
    );

    //=========================================================================
    // Output Flip-Flop
    //=========================================================================
    // Captures FIFO read data for timing characterization

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic [DATA_WIDTH-1:0] r_out_flop;

    `ifdef XILINX
        (* dont_touch = "true" *)
    `elsif INTEL
        /* synthesis preserve */
    `endif
    logic r_out_valid;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_out_flop  <= '0;
            r_out_valid <= 1'b0;
        end else begin
            r_out_valid <= w_fifo_rd_valid;
            if (w_fifo_rd_valid && i_rd_ready) begin
                r_out_flop <= w_fifo_rd_data;
            end
        end
    )

    assign o_rd_data  = r_out_flop;
    assign o_rd_valid = r_out_valid;

endmodule : queue_depth
