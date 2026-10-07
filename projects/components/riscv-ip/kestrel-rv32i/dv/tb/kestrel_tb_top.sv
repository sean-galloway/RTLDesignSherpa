// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_tb_top
// Purpose: kestrel_core wrapped with a behavioral 64 KiB unified (von
//          Neumann) word memory.  Programs load at time 0 via +imem=<hex>
//          (+dmem=<hex>) plusargs into $readmemh word arrays; all reads are
//          combinational.  Unified memory means instruction fetches see
//          data-memory stores (self-modifying code, rv32ui-p-fence_i) with
//          no extra coherence path.
//
//          Data-memory writes honor dmem_wstrb per byte.  The kestrel L/S
//          datapath rotates the strobe and data by the byte offset, so this
//          byte-wise merge is the contract that pins rotated-strobe behavior
//          (Task 7 ruling R4: in-word rotated strobes, bytes that rotate past
//          bit 31 are dropped).
//
//          Task 8 adds a TB backdoor write port (tb_mem_*) so the rv32ui
//          battery can load all 42 vendor images through one Verilator
//          build: the runner asserts reset, streams the normalized image
//          one word per cycle, releases reset, and runs to halt.  The
//          riscv-tests tohost mailbox is observed on the store port
//          (dmem_req/dmem_addr/dmem_wstrb/dmem_wdata are top-level ports).
//
// Documentation: projects/components/riscv-ip/README.md
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-06

`timescale 1ns / 1ps

`include "reset_defs.svh"

module kestrel_tb_top #(
    parameter logic [31:0] RESET_ADDR = 32'h0000_0000
) (
    input  logic        clk,
    input  logic        rst_n,
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
    // TB backdoor image loader (Task 8 battery): write one word per cycle
    // while the core is held in reset.  Not part of the DUT contract.
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
    assign dmem_rdata = mem[dmem_addr[MEM_ADDR_MSB:WORD_ADDR_LSB]];

    // Store port: byte-wise merge using the rotated strobe from the core.
    // Gated by reset so a backdoor image load cannot race a decode of the
    // half-written memory.  The backdoor write sits in the same block (one
    // process drives mem); it is deliberately not reset-gated so the
    // battery can stream images during reset assertion.
    `ALWAYS_FF_RST(clk, rst_n,
        begin
            if (!`RST_ASSERTED(rst_n)) begin
                if (dmem_req && (|dmem_wstrb)) begin
                    for (int b = 0; b < BYTE_LANES; b++) begin
                        if (dmem_wstrb[b]) begin
                            mem[dmem_addr[MEM_ADDR_MSB:WORD_ADDR_LSB]][b*BYTE_WIDTH +: BYTE_WIDTH]
                                <= dmem_wdata[b*BYTE_WIDTH +: BYTE_WIDTH];
                        end
                    end
                end
            end
            if (tb_mem_we) begin
                mem[tb_mem_addr[MEM_ADDR_MSB:WORD_ADDR_LSB]] <= tb_mem_wdata;
            end
        end
    )

    kestrel_core #(
        .RESET_ADDR (RESET_ADDR)
    ) u_kestrel_core (
        .clk            (clk),
        .rst_n          (rst_n),
        .imem_addr      (imem_addr),
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

endmodule : kestrel_tb_top
