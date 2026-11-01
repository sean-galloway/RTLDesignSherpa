// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: merlin_tb_top
// Purpose: merlin_core wrapped with a behavioral 64 KiB unified (von
//          Neumann) word memory.  Programs load at time 0 via +imem=<hex>
//          plusargs into $readmemh word arrays; instruction reads are
//          combinational, data reads are registered to match the core's
//          block-RAM timing contract.
//
//          Data-memory writes honor dmem_wstrb per byte.  The merlin L/S
//          datapath rotates the strobe and data by the byte offset, so this
//          byte-wise merge is the contract that pins rotated-strobe behavior.
//
//          A TB backdoor write port (tb_mem_*) lets the rv32ui battery load
//          images through one Verilator build, and the riscv-tests tohost
//          mailbox is observed on the store port.  `mem_wait` is exposed as
//          a top-level input so the mem_wait-pulse test can stall the core.
//
// Documentation: projects/components/riscv-ip/merlin-rv32i/PRD.md
// Subsystem: riscv-ip/merlin-rv32i
//
// Author: sean galloway
// Created: 2026-11-01

`timescale 1ns / 1ps

`include "reset_defs.svh"

module merlin_tb_top #(
    parameter logic [31:0] RESET_ADDR = 32'h0000_0000
) (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        mem_wait,       // exposed for mem_wait-pulse tests
    output logic        halt,
    output logic [3:0]  halt_cause,
    output logic        dmem_req,
    output logic [31:0] dmem_addr,
    output logic [3:0]  dmem_wstrb,
    output logic [31:0] dmem_wdata,
    output logic        rvfi_valid,
    output logic [63:0] rvfi_order,
    output logic [31:0] rvfi_pc_rdata,
    output logic [31:0] rvfi_pc_wdata,
    output logic [31:0] rvfi_insn,
    output logic        rvfi_trap,
    output logic [4:0]  rvfi_rs1_addr,
    output logic [4:0]  rvfi_rs2_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,
    output logic [4:0]  rvfi_rd_addr,
    output logic [31:0] rvfi_rd_wdata,
    output logic [31:0] rvfi_mem_addr,
    output logic [3:0]  rvfi_mem_rmask,
    output logic [3:0]  rvfi_mem_wmask,
    output logic [31:0] rvfi_mem_rdata,
    output logic [31:0] rvfi_mem_wdata,
    // TB backdoor image loader: write one word per cycle while held in reset.
    input  logic        tb_mem_we,
    input  logic [31:0] tb_mem_addr,
    input  logic [31:0] tb_mem_wdata
);

    localparam int MEM_WORDS      = 65536;
    localparam int MEM_ADDR_MSB   = 17;
    localparam int WORD_ADDR_LSB  = 2;
    localparam int BYTE_LANES     = 4;
    localparam int BYTE_WIDTH     = 8;

    logic [31:0] mem [0:MEM_WORDS-1];

    string imem_file;
    string dmem_file;

    logic [31:0] imem_addr;
    logic [31:0] imem_rdata;
    logic [31:0] dmem_rdata_q;
    logic [31:0] dmem_rdata;

    initial begin
        for (int i = 0; i < MEM_WORDS; i++) begin
            mem[i] = '0;
        end
        if ($value$plusargs("imem=%s", imem_file)) begin
            $readmemh(imem_file, mem);
        end
        if ($value$plusargs("dmem=%s", dmem_file)) begin
            $readmemh(dmem_file, mem);
        end
    end

    assign imem_rdata = mem[imem_addr[MEM_ADDR_MSB:WORD_ADDR_LSB]];

    // Registered-read data memory with store-to-load forwarding.  The core
    // expects block-RAM timing (address in cycle N, data in cycle N+1).  The
    // byte-wise store is applied with blocking assignments before the load
    // word is sampled so a load in MEM sees a store that retires in the same
    // cycle from WB.
    `ALWAYS_FF_RST(clk, rst_n,
        begin
            if (!`RST_ASSERTED(rst_n)) begin
                if (dmem_req && (|dmem_wstrb)) begin
                    for (int b = 0; b < BYTE_LANES; b++) begin
                        if (dmem_wstrb[b]) begin
                            mem[dmem_addr[MEM_ADDR_MSB:WORD_ADDR_LSB]][b*BYTE_WIDTH +: BYTE_WIDTH]
                                = dmem_wdata[b*BYTE_WIDTH +: BYTE_WIDTH];
                        end
                    end
                end
            end
            if (tb_mem_we) begin
                mem[tb_mem_addr[MEM_ADDR_MSB:WORD_ADDR_LSB]] = tb_mem_wdata;
            end
            dmem_rdata_q <= mem[dmem_addr[MEM_ADDR_MSB:WORD_ADDR_LSB]];
        end
    )
    assign dmem_rdata = dmem_rdata_q;

    merlin_core #(
        .RESET_ADDR (RESET_ADDR)
    ) u_merlin_core (
        .clk            (clk),
        .rst_n          (rst_n),
        .mem_wait       (mem_wait),
        .imem_addr      (imem_addr),
        .imem_addr_next (),
        .imem_rdata     (imem_rdata),
        .dmem_req       (dmem_req),
        .dmem_addr      (dmem_addr),
        .dmem_rdata     (dmem_rdata),
        .dmem_wstrb     (dmem_wstrb),
        .dmem_wdata     (dmem_wdata),
        .halt           (halt),
        .halt_cause     (halt_cause),
        .rvfi_valid     (rvfi_valid),
        .rvfi_order     (rvfi_order),
        .rvfi_pc_rdata  (rvfi_pc_rdata),
        .rvfi_pc_wdata  (rvfi_pc_wdata),
        .rvfi_insn      (rvfi_insn),
        .rvfi_trap      (rvfi_trap),
        .rvfi_rs1_addr  (rvfi_rs1_addr),
        .rvfi_rs2_addr  (rvfi_rs2_addr),
        .rvfi_rs1_rdata (rvfi_rs1_rdata),
        .rvfi_rs2_rdata (rvfi_rs2_rdata),
        .rvfi_rd_addr   (rvfi_rd_addr),
        .rvfi_rd_wdata  (rvfi_rd_wdata),
        .rvfi_mem_addr  (rvfi_mem_addr),
        .rvfi_mem_rmask (rvfi_mem_rmask),
        .rvfi_mem_wmask (rvfi_mem_wmask),
        .rvfi_mem_rdata (rvfi_mem_rdata),
        .rvfi_mem_wdata (rvfi_mem_wdata)
    );

endmodule : merlin_tb_top
