// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axis_injector
// Purpose: 128-bit AXIS master injector for PKT_CONFIG / PKT_STATUS
//
// Documentation: projects/components/compute-eng-ip/hive-serv/docs/hive_mas/ch02_blocks/03_serv_monitor.md
// Subsystem: hive-serv
//
// Author: sean galloway
// Created: 2026-10-13

`timescale 1ns / 1ps

module axis_injector #(
    parameter int TILE_ID = 0
)(
    input  logic        clk,
    input  logic        rst_n,

    // Firmware-facing commit interface
    input  logic [31:0] inj_word [4],
    input  logic        commit,
    input  logic [1:0]  commit_tuser,
    input  logic [7:0]  commit_tdest,

    // AXIS master into per-SERV CDC FIFO
    output logic        inj_tvalid,
    input  logic        inj_tready,
    output logic [127:0] inj_tdata,
    output logic [1:0]  inj_tuser,
    output logic [7:0]  inj_tdest,
    output logic [3:0]  inj_tid,
    output logic        inj_tlast
);

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            inj_tvalid <= 1'b0;
            inj_tdata  <= '0;
            inj_tuser  <= '0;
            inj_tdest  <= '0;
            inj_tid    <= '0;
            inj_tlast  <= 1'b0;
        end else begin
            if (commit) begin
                inj_tvalid <= 1'b1;
                inj_tdata  <= {inj_word[3], inj_word[2], inj_word[1], inj_word[0]};
                inj_tuser  <= commit_tuser;
                inj_tdest  <= commit_tdest;
                inj_tid    <= TILE_ID[3:0];
                inj_tlast  <= 1'b1;
            end else if (inj_tvalid && inj_tready) begin
                inj_tvalid <= 1'b0;
            end
        end
    end

endmodule : axis_injector
