// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: control_arbiter
// Purpose: Round-robin uplink arbitration (SLAVE_COUNT -> 1) for the HIVE
//          control network.  Non-preemptive, one frame per grant; a frame
//          with the urgent sideband (tuser[0] of the fifo word) wins the
//          next grant after the current frame completes.  Starvation-free by
//          construction: equal weights, one frame per grant.
//
//          Grant scheme: combinational pick from the last grant, registered
//          hold.  pick_next() is evaluated on the CURRENT request mask, so
//          the grant visible the same cycle requests appear — a registered
//          next_grant sampled at activation could latch a stale pick.  The
//          fifo side (hive_cdc_fifo) drives rd_valid combinationally, so a
//          popped slave's request drops in the same cycle (no stale window).
//
// Documentation: projects/components/compute-eng-ip/hive-serv/docs/hive_mas/ch02_blocks/04_control_network.md
// Subsystem: hive-serv
//
// Author: seang
// Created: 2026-10-13

`timescale 1ns / 1ps

`include "reset_defs.svh"

module control_arbiter #(
    parameter int SLAVE_COUNT = 4,
    parameter int DATA_WIDTH  = 33          // {urgent, 32-bit frame}
) (
    input  logic clk,
    input  logic rst_n,

    input  logic [SLAVE_COUNT-1:0]      up_valid,
    input  logic [DATA_WIDTH-1:0]       up_data [SLAVE_COUNT],
    output logic [SLAVE_COUNT-1:0]      up_ready,

    output logic                        m_axis_tvalid,
    input  logic                        m_axis_tready,
    output logic [31:0]                 m_axis_tdata,
    output logic [1:0]                  m_axis_tuser
);

    localparam int IDW = $clog2(SLAVE_COUNT);

    logic [IDW-1:0]        r_last;
    logic [IDW-1:0]        r_curr;
    logic                  r_active;
    logic [SLAVE_COUNT-1:0] req;
    logic [SLAVE_COUNT-1:0] urgent;

    for (genvar i = 0; i < SLAVE_COUNT; i++) begin : g_map
        assign req[i]    = up_valid[i];
        assign urgent[i] = up_valid[i] & up_data[i][DATA_WIDTH-1];
    end

    // Round-robin search starting just after `start` over `mask`.
    function automatic [IDW-1:0] pick_next(
        input [IDW-1:0]         start,
        input [SLAVE_COUNT-1:0] mask
    );
        int idx;
        bit found;
        pick_next = start; // default if no request
        found = 1'b0;
        for (int offset = 1; offset <= SLAVE_COUNT; offset++) begin
            idx = (32'(start) + 32'(offset)) % SLAVE_COUNT;
            if (!found && mask[idx]) begin
                pick_next = idx[IDW-1:0];
                found = 1'b1;
            end
        end
    endfunction

    // Urgent frames form the pick mask whenever any are waiting (they win the
    // grant after the current frame completes — non-preemptive).
    wire [SLAVE_COUNT-1:0] arb_mask = (|(req & urgent)) ? (req & urgent) : req;
    wire                   w_go     = (arb_mask != '0);
    wire [IDW-1:0]         w_pick   = pick_next(r_last, arb_mask);
    wire [IDW-1:0]         w_grant  = r_active ? r_curr : w_pick;
    wire                   w_active = r_active || w_go;

    wire pop = w_active & m_axis_tvalid & m_axis_tready;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_last   <= '1;            // so the first pick is slave 0
            r_curr   <= '0;
            r_active <= 1'b0;
        end else if (pop) begin
            r_last   <= w_grant;
            r_active <= 1'b0;
        end else if (!r_active && w_go) begin
            r_curr   <= w_pick;
            r_active <= 1'b1;
        end
    end

    // Read exactly one beat when the master accepts the current grant.
    always_comb begin
        up_ready = '0;
        if (w_active && m_axis_tready && req[w_grant]) begin
            up_ready[w_grant] = 1'b1;
        end
    end

    assign m_axis_tvalid   = w_active & req[w_grant];
    assign m_axis_tdata    = up_data[w_grant][31:0];
    assign m_axis_tuser[0] = up_data[w_grant][DATA_WIDTH-1];
    assign m_axis_tuser[1] = 1'b0;

endmodule : control_arbiter
