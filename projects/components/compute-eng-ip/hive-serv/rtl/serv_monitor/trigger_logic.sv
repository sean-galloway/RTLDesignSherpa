// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: trigger_logic
// Purpose: Hardware threshold comparator for congestion detection
//
// Documentation: projects/components/compute-eng-ip/hive-serv/docs/hive_mas/ch02_blocks/03_serv_monitor.md
// Subsystem: hive-serv
//
// Author: sean galloway
// Created: 2026-10-13

`timescale 1ns / 1ps

module trigger_logic #(
    parameter int IBUF_DEPTH = 8
)(
    input  logic        clk,
    input  logic        rst_n,

    input  logic [7:0]  buffer_occupancy [4],
    input  logic [7:0]  cfg_threshold,

    output logic        congestion_flag
);

    // Combinational threshold compare: any direction exceeds the threshold
    always_comb begin
        congestion_flag = 1'b0;
        for (int i = 0; i < 4; i++) begin
            if (buffer_occupancy[i] > cfg_threshold)
                congestion_flag = 1'b1;
        end
    end

endmodule : trigger_logic
