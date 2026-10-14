// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: control_packetizer
// Purpose: One-beat control frame passthrough.  For the HIVE control network a
//          frame is exactly one AXIS beat (tlast is implicit), so encode/decode
//          is a transparent data + tuser pass-through.
//
// Documentation: projects/components/compute-eng-ip/hive-serv/docs/hive_mas/ch02_blocks/04_control_network.md
// Subsystem: hive-serv
//
// Author: sean galloway
// Created: 2026-10-13

`timescale 1ns / 1ps

`include "reset_defs.svh"

/* verilator lint_off UNUSED */
module control_packetizer #(
    parameter int DATA_WIDTH = 32,
    parameter int USER_WIDTH = 2
) (
    input  logic clk,
    input  logic rst_n,

    // Slave AXIS interface
    input  logic                   s_axis_tvalid,
    output logic                   s_axis_tready,
    input  logic [DATA_WIDTH-1:0]  s_axis_tdata,
    input  logic [USER_WIDTH-1:0]  s_axis_tuser,

    // Master AXIS interface
    output logic                   m_axis_tvalid,
    input  logic                   m_axis_tready,
    output logic [DATA_WIDTH-1:0]  m_axis_tdata,
    output logic [USER_WIDTH-1:0]  m_axis_tuser
);

    assign m_axis_tvalid = s_axis_tvalid;
    assign s_axis_tready = m_axis_tready;
    assign m_axis_tdata  = s_axis_tdata;
    assign m_axis_tuser  = s_axis_tuser;

endmodule : control_packetizer
/* verilator lint_on UNUSED */
