// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: local_mem
// Purpose: 2 KB instruction memory + 2 KB data memory for the per-tile SERV monitor
//
// Documentation: projects/components/compute-eng-ip/hive-serv/docs/hive_mas/ch02_blocks/03_serv_monitor.md
// Subsystem: hive-serv
//
// Author: sean galloway
// Created: 2026-10-13

`timescale 1ns / 1ps

module local_mem #(
    parameter int IMEM_SIZE_BYTES = 2048,
    parameter int DMEM_SIZE_BYTES = 2048
)(
    input  logic        clk,
    input  logic        rst_n,

    // Instruction port (from SERV instruction bus)
    input  logic [31:0] ibus_adr,
    input  logic        ibus_cyc,
    output logic [31:0] ibus_rdt,
    output logic        ibus_ack,

    // Data port (from SERV data bus)
    input  logic [31:0] dbus_adr,
    input  logic [31:0] dbus_dat,
    input  logic [3:0]  dbus_sel,
    input  logic        dbus_we,
    input  logic        dbus_cyc,
    output logic [31:0] dbus_rdt,
    output logic        dbus_ack
);

    localparam int IMEM_WORDS = IMEM_SIZE_BYTES / 4;
    localparam int DMEM_WORDS = DMEM_SIZE_BYTES / 4;
    localparam int IMEM_AW = $clog2(IMEM_WORDS);
    localparam int DMEM_AW = $clog2(DMEM_WORDS);

    // Byte-addressable RAMs, word-aligned accesses only
    logic [31:0] r_imem [IMEM_WORDS];
    logic [31:0] r_dmem [DMEM_WORDS];

    logic [IMEM_AW-1:0] imem_addr;
    logic [DMEM_AW-1:0] dmem_addr;

    assign imem_addr = ibus_adr[IMEM_AW+1:2];
    assign dmem_addr = dbus_adr[DMEM_AW+1:2];

    // Instruction fetch: synchronous read, combinatorial ack
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ibus_rdt <= '0;
        end else if (ibus_cyc) begin
            ibus_rdt <= r_imem[imem_addr];
        end
    end
    assign ibus_ack = ibus_cyc;

    // Data port: synchronous read/write, combinatorial ack
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            dbus_rdt <= '0;
        end else if (dbus_cyc) begin
            if (dbus_we) begin
                if (dbus_sel[0]) r_dmem[dmem_addr][7:0]   <= dbus_dat[7:0];
                if (dbus_sel[1]) r_dmem[dmem_addr][15:8]  <= dbus_dat[15:8];
                if (dbus_sel[2]) r_dmem[dmem_addr][23:16] <= dbus_dat[23:16];
                if (dbus_sel[3]) r_dmem[dmem_addr][31:24] <= dbus_dat[31:24];
            end else begin
                dbus_rdt <= r_dmem[dmem_addr];
            end
        end
    end
    assign dbus_ack = dbus_cyc;

endmodule : local_mem
