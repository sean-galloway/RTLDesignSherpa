// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: control_router
// Purpose: Star fan-out from one HIVE-C command stream to SLAVE_COUNT SERV
//          command egress ports.  Target decode is on tdata[23:16]; 8'hFF is
//          broadcast.  No buffering here -- the only FIFOs are the CDC FIFOs.
//
// Documentation: projects/components/compute-eng-ip/hive-serv/docs/hive_mas/ch02_blocks/04_control_network.md
// Subsystem: hive-serv
//
// Author: sean galloway
// Created: 2026-10-13

`timescale 1ns / 1ps

`include "reset_defs.svh"

/* verilator lint_off UNUSED */
module control_router #(
    parameter int SLAVE_COUNT = 4,
    parameter int DATA_WIDTH  = 34
) (
    input  logic clk,
    input  logic rst_n,

    // Upstream command stream (from control_packetizer)
    input  logic                   s_axis_tvalid,
    output logic                   s_axis_tready,
    input  logic [DATA_WIDTH-1:0]  s_axis_tdata,

    // Downstream write ports to the command CDC FIFOs
    output logic [SLAVE_COUNT-1:0] m_wr_valid,
    input  logic [SLAVE_COUNT-1:0] m_wr_ready,
    output logic [DATA_WIDTH-1:0]  m_wr_data [SLAVE_COUNT]
);

    localparam int IDW = $clog2(SLAVE_COUNT);

    logic [7:0]     target;
    logic [IDW-1:0] tidx;
    logic [7:0]     slave_count_b;
    assign target        = s_axis_tdata[23:16];
    assign tidx          = target[IDW-1:0];
    assign slave_count_b = 8'(SLAVE_COUNT);

    // Write enables qualify the STREAM ACCEPT (valid && ready), so each fifo
    // writes exactly once per accepted beat — unqualified enables would
    // re-write every cycle a master legally holds tvalid high.
    wire accept = s_axis_tvalid && s_axis_tready;

    always_comb begin
        m_wr_valid = '0;
        for (int i = 0; i < SLAVE_COUNT; i++) begin
            m_wr_data[i] = s_axis_tdata;
        end

        if (accept) begin
            if (target == 8'hFF) begin
                // Broadcast: accept only happened because every fifo is ready.
                m_wr_valid = m_wr_ready;
            end else if (target < slave_count_b) begin
                m_wr_valid[tidx] = m_wr_ready[tidx];
            end
        end
    end

    // Invalid targets are dropped (ready high) rather than wedging the master.
    assign s_axis_tready = s_axis_tvalid
                         ? ((target == 8'hFF)      ? (&m_wr_ready)
                          : (target < slave_count_b) ? m_wr_ready[tidx]
                          : 1'b1)
                         : 1'b0;

endmodule : control_router
/* verilator lint_on UNUSED */
