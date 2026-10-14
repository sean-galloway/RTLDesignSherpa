// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: hive_ctrl_network
// Purpose: HIVE-C <-> SERV monitor control/status star.  Sub-blocks:
//          control_packetizer (frame encode/decode pass-through),
//          control_router (command fan-out / broadcast),
//          control_arbiter (round-robin uplink aggregation, urgent next-grant),
//          and one gaxi_fifo_async CDC FIFO per slave per direction.
//
// Documentation: projects/components/compute-eng-ip/hive-serv/docs/hive_mas/ch02_blocks/04_control_network.md
// Subsystem: hive-serv
//
// Author: sean galloway
// Created: 2026-10-13
//
// CDC FIFO choice: hive_cdc_fifo (this directory).  The repo's
// gaxi_fifo_async showed stuck full/valid flags at small depths during
// Phase-1 bring-up (vault bug filed with VCD evidence), so the control
// network carries a compact local dual-clock FIFO (binary pointers, Gray
// crossing, combinational rd_valid) until the shared library is fixed.
// Depths per MAS ch01_overview/02_clocking_and_reset.md: 2 entries per
// slave for commands, 4 for the uplink.  Entries are widened to 34/33 bits
// so the AXIS tuser[0] urgent sideband crosses with the frame.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module hive_ctrl_network #(
    parameter int SLAVE_COUNT = 4
) (
    input  logic        m_clk,           // hive_c_clk (master side)
    input  logic        s_clk,           // serv_clk   (slave side)
    input  logic        m_rst_n,
    input  logic        s_rst_n,

    // master command port (HIVE-C injects frames; target 8'hFF = broadcast)
    input  logic         cmd_tvalid,
    output logic         cmd_tready,
    input  logic [31:0]  cmd_tdata,
    input  logic [1:0]   cmd_tuser,

    // slave command egress (one per slave)
    output logic [SLAVE_COUNT-1:0]        s_cmd_tvalid,
    input  logic [SLAVE_COUNT-1:0]        s_cmd_tready,
    output logic [SLAVE_COUNT*32-1:0]     s_cmd_tdata,

    // slave uplink ingress (one per slave)
    input  logic [SLAVE_COUNT-1:0]        s_up_tvalid,
    output logic [SLAVE_COUNT-1:0]        s_up_tready,
    input  logic [SLAVE_COUNT*32-1:0]     s_up_tdata,
    input  logic [SLAVE_COUNT-1:0]        s_up_turgent,

    // master uplink egress (round-robin aggregated)
    output logic        up_tvalid,
    input  logic        up_tready,
    output logic [31:0] up_tdata,
    output logic [1:0]  up_tuser
);

    // MAS §1.2: 2 entries per slave for commands, 4 for the uplink.
    localparam int CMD_FIFO_DEPTH = 2;
    localparam int UP_FIFO_DEPTH  = 4;
    localparam int CMD_FIFO_DW    = 34;          // {cmd_tuser[1:0], cmd_tdata}
    localparam int UP_FIFO_DW     = 33;          // {urgent, up_tdata}

    // -----------------------------------------------------------------------
    // Command path: packetizer -> router -> per-slave CDC FIFOs -> slaves
    // -----------------------------------------------------------------------
    logic                   pkt_cmd_valid;
    logic                   pkt_cmd_ready;
    logic [31:0]            pkt_cmd_data;
    logic [1:0]             pkt_cmd_user;

    control_packetizer u_cmd_pkt (
        .clk            (m_clk),
        .rst_n          (m_rst_n),
        .s_axis_tvalid  (cmd_tvalid),
        .s_axis_tready  (cmd_tready),
        .s_axis_tdata   (cmd_tdata),
        .s_axis_tuser   (cmd_tuser),
        .m_axis_tvalid  (pkt_cmd_valid),
        .m_axis_tready  (pkt_cmd_ready),
        .m_axis_tdata   (pkt_cmd_data),
        .m_axis_tuser   (pkt_cmd_user)
    );

    logic [SLAVE_COUNT-1:0] cmd_fifo_wr_valid;
    logic [SLAVE_COUNT-1:0] cmd_fifo_wr_ready;
    logic [CMD_FIFO_DW-1:0] cmd_fifo_wr_data [SLAVE_COUNT];

    control_router #(
        .SLAVE_COUNT (SLAVE_COUNT),
        .DATA_WIDTH  (CMD_FIFO_DW)
    ) u_router (
        .clk            (m_clk),
        .rst_n          (m_rst_n),
        .s_axis_tvalid  (pkt_cmd_valid),
        .s_axis_tready  (pkt_cmd_ready),
        .s_axis_tdata   ({pkt_cmd_user, pkt_cmd_data}),
        .m_wr_valid     (cmd_fifo_wr_valid),
        .m_wr_ready     (cmd_fifo_wr_ready),
        .m_wr_data      (cmd_fifo_wr_data)
    );

    logic [SLAVE_COUNT-1:0] cmd_fifo_rd_valid;
    logic [SLAVE_COUNT-1:0] cmd_fifo_rd_ready;
    logic [CMD_FIFO_DW-1:0] cmd_fifo_rd_data [SLAVE_COUNT];

    genvar i;
    generate
        for (i = 0; i < SLAVE_COUNT; i++) begin : g_cmd_fifo
            hive_cdc_fifo #(
                .DATA_WIDTH   (CMD_FIFO_DW),
                .DEPTH        (CMD_FIFO_DEPTH),
                .N_FLOP_CROSS (2)
            ) u_cmd_fifo (
                .axi_wr_aclk    (m_clk),
                .axi_wr_aresetn (m_rst_n),
                .axi_rd_aclk    (s_clk),
                .axi_rd_aresetn (s_rst_n),
                .wr_valid       (cmd_fifo_wr_valid[i]),
                .wr_ready       (cmd_fifo_wr_ready[i]),
                .wr_data        (cmd_fifo_wr_data[i]),
                .rd_ready       (cmd_fifo_rd_ready[i]),
                .rd_valid       (cmd_fifo_rd_valid[i]),
                .rd_data        (cmd_fifo_rd_data[i])
            );

            assign s_cmd_tvalid[i]              = cmd_fifo_rd_valid[i];
            assign cmd_fifo_rd_ready[i]         = s_cmd_tready[i];
            assign s_cmd_tdata[i*32 +: 32]      = cmd_fifo_rd_data[i][31:0];
        end
    endgenerate

    // -----------------------------------------------------------------------
    // Uplink path: per-slave CDC FIFOs -> arbiter -> master egress
    // -----------------------------------------------------------------------
    logic [SLAVE_COUNT-1:0] up_fifo_wr_ready;
    logic [SLAVE_COUNT-1:0] up_fifo_rd_valid;
    logic [SLAVE_COUNT-1:0] up_fifo_rd_ready;
    logic [UP_FIFO_DW-1:0]  up_fifo_rd_data [SLAVE_COUNT];

    generate
        for (i = 0; i < SLAVE_COUNT; i++) begin : g_up_fifo
            logic [UP_FIFO_DW-1:0] up_fifo_wr_data;
            assign up_fifo_wr_data = {s_up_turgent[i], s_up_tdata[i*32 +: 32]};
            assign s_up_tready[i]  = up_fifo_wr_ready[i];

            hive_cdc_fifo #(
                .DATA_WIDTH   (UP_FIFO_DW),
                .DEPTH        (UP_FIFO_DEPTH),
                .N_FLOP_CROSS (2)
            ) u_up_fifo (
                .axi_wr_aclk    (s_clk),
                .axi_wr_aresetn (s_rst_n),
                .axi_rd_aclk    (m_clk),
                .axi_rd_aresetn (m_rst_n),
                .wr_valid       (s_up_tvalid[i]),
                .wr_ready       (up_fifo_wr_ready[i]),
                .wr_data        (up_fifo_wr_data),
                .rd_ready       (up_fifo_rd_ready[i]),
                .rd_valid       (up_fifo_rd_valid[i]),
                .rd_data        (up_fifo_rd_data[i])
            );
        end
    endgenerate

    control_arbiter #(
        .SLAVE_COUNT (SLAVE_COUNT),
        .DATA_WIDTH  (UP_FIFO_DW)
    ) u_arbiter (
        .clk            (m_clk),
        .rst_n          (m_rst_n),
        .up_valid       (up_fifo_rd_valid),
        .up_data        (up_fifo_rd_data),
        .up_ready       (up_fifo_rd_ready),
        .m_axis_tvalid  (up_tvalid),
        .m_axis_tready  (up_tready),
        .m_axis_tdata   (up_tdata),
        .m_axis_tuser   (up_tuser)
    );

endmodule : hive_ctrl_network
