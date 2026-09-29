// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: latency_bridge_beats_tb_top
// Purpose: DV wrapper -- latency_bridge_beats behind a REGISTERED=1 gaxi_fifo_sync
//
// The bridge's upstream contract is a registered-read FIFO: s_data is valid the
// cycle AFTER the s_valid/s_ready handshake. A valid/ready BFM drives data WITH
// valid, so pointing a GAXI master straight at s_* exercises the handshake and
// never the data (the bridge samples s_data one cycle late and captures the
// idle value -- every m_data came out 0 and the old test did not look; rapids
// TASK-003). This wrapper puts the real FIFO in front, exactly as
// sram_controller_unit does, so the master writes the FIFO and the bridge
// reads it under its own contract. s_ready and s_valid are brought out for the
// backpressure checks.
//
// Documentation: projects/components/dma-ip/rapids/docs/rapids_beats_mas/ch02_fub_blocks/07_beats_latency_bridge.md
// Subsystem: rapids
//
// Author: sean galloway
// Created: 2026-09-27

`timescale 1ns / 1ps

module latency_bridge_beats_tb_top #(
    parameter int DATA_WIDTH = 64,
    parameter int SKID_DEPTH = 4,
    parameter int FIFO_DEPTH = 8,
    parameter int DW = DATA_WIDTH,
    parameter int FAW = $clog2(FIFO_DEPTH)
) (
    input  logic            clk,
    input  logic            rst_n,

    // GAXI master writes the FIFO (data with valid, the BFM's contract)
    input  logic            wr_valid,
    output logic            wr_ready,
    input  logic [DW-1:0]   wr_data,

    // bridge output, consumed by the GAXI slave
    output logic            m_valid,
    input  logic            m_ready,
    output logic [DW-1:0]   m_data,

    // observability
    output logic            s_valid,        // FIFO not empty (bridge input valid)
    output logic            s_ready,        // bridge accepting a read
    output logic [FAW:0]    fifo_count,
    output logic [2:0]      occupancy,
    output logic            dbg_r_pending,
    output logic            dbg_r_out_valid
);

    logic [DW-1:0] w_fifo_rd_data;

    // The registered-read FIFO the bridge is built for: rd_data lands the
    // cycle after rd_valid && rd_ready.
    gaxi_fifo_sync #(
        .REGISTERED       (1),
        .DATA_WIDTH       (DW),
        .DEPTH            (FIFO_DEPTH),
        .ALMOST_WR_MARGIN (1),
        .ALMOST_RD_MARGIN (1)
    ) u_fifo (
        .axi_aclk    (clk),
        .axi_aresetn (rst_n),
        .wr_valid    (wr_valid),
        .wr_ready    (wr_ready),
        .wr_data     (wr_data),
        .rd_ready    (s_ready),
        .count       (fifo_count),
        .rd_valid    (s_valid),
        .rd_data     (w_fifo_rd_data)
    );

    latency_bridge_beats #(
        .DATA_WIDTH (DW),
        .SKID_DEPTH (SKID_DEPTH)
    ) u_dut (
        .clk             (clk),
        .rst_n           (rst_n),
        .s_valid         (s_valid),
        .s_ready         (s_ready),
        .s_data          (w_fifo_rd_data),
        .m_valid         (m_valid),
        .m_ready         (m_ready),
        .m_data          (m_data),
        .occupancy       (occupancy),
        .dbg_r_pending   (dbg_r_pending),
        .dbg_r_out_valid (dbg_r_out_valid)
    );

endmodule : latency_bridge_beats_tb_top
