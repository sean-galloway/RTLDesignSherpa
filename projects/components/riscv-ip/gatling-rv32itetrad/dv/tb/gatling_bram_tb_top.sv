// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gatling_bram_tb_top
// Purpose: cocotb harness for gatling_core behind gatling_mem_bram: the AXIL
//          slave port for the framework master, and the core's halt/RVFI
//          signals for the trace checks (the same names gatling_tb_top
//          exposes, so one TB class samples both).
//
// Documentation: projects/components/riscv-ip/gatling-rv32itetrad/docs/gatling_mas
// Subsystem: riscv-ip/gatling-rv32itetrad
//
// Author: sean galloway
// Created: 2026-10-21

`timescale 1ns / 1ps

module gatling_bram_tb_top #(
    parameter logic [31:0] RESET_ADDR = 32'h0000_0000,
    parameter int          MEM_WORDS  = 4096            // gatling_mem_bram default (16 KB per context)
) (
    input  logic        clk,
    input  logic        rst_n,

    input  logic [17:0] s_axil_awaddr,
    input  logic [2:0]  s_axil_awprot,
    input  logic        s_axil_awvalid,
    output logic        s_axil_awready,
    input  logic [31:0] s_axil_wdata,
    input  logic [3:0]  s_axil_wstrb,
    input  logic        s_axil_wvalid,
    output logic        s_axil_wready,
    output logic [1:0]  s_axil_bresp,
    output logic        s_axil_bvalid,
    input  logic        s_axil_bready,
    input  logic [17:0] s_axil_araddr,
    input  logic [2:0]  s_axil_arprot,
    input  logic        s_axil_arvalid,
    output logic        s_axil_arready,
    output logic [31:0] s_axil_rdata,
    output logic [1:0]  s_axil_rresp,
    output logic        s_axil_rvalid,
    input  logic        s_axil_rready,

    output logic [3:0]  hart_run,
    output logic [3:0]  halted,
    output logic [15:0] halt_cause,
    output logic        dmem_req,
    output logic [1:0]  dmem_ctx,
    output logic [31:0] dmem_addr,
    output logic [3:0]  dmem_wstrb,
    output logic [31:0] dmem_wdata,

    output logic        rvfi_valid,
    output logic [1:0]  rvfi_ctx,
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
    output logic [31:0] rvfi_mem_wdata
);

    logic [1:0]      imem_ctx;
    logic [31:0]     imem_addr, imem_rdata, dmem_rdata;
    logic [3:0][3:0] w_cause;

    assign halt_cause = w_cause;

    gatling_mem_bram #(
        .MEM_WORDS (MEM_WORDS)
    ) u_mem (
        .aclk           (clk),
        .aresetn        (rst_n),
        .s_axil_awaddr  (s_axil_awaddr),
        .s_axil_awprot  (s_axil_awprot),
        .s_axil_awvalid (s_axil_awvalid),
        .s_axil_awready (s_axil_awready),
        .s_axil_wdata   (s_axil_wdata),
        .s_axil_wstrb   (s_axil_wstrb),
        .s_axil_wvalid  (s_axil_wvalid),
        .s_axil_wready  (s_axil_wready),
        .s_axil_bresp   (s_axil_bresp),
        .s_axil_bvalid  (s_axil_bvalid),
        .s_axil_bready  (s_axil_bready),
        .s_axil_araddr  (s_axil_araddr),
        .s_axil_arprot  (s_axil_arprot),
        .s_axil_arvalid (s_axil_arvalid),
        .s_axil_arready (s_axil_arready),
        .s_axil_rdata   (s_axil_rdata),
        .s_axil_rresp   (s_axil_rresp),
        .s_axil_rvalid  (s_axil_rvalid),
        .s_axil_rready  (s_axil_rready),
        .imem_ctx       (imem_ctx),
        .imem_addr      (imem_addr),
        .imem_rdata     (imem_rdata),
        .dmem_req       (dmem_req),
        .dmem_ctx       (dmem_ctx),
        .dmem_addr      (dmem_addr),
        .dmem_rdata     (dmem_rdata),
        .dmem_wstrb     (dmem_wstrb),
        .dmem_wdata     (dmem_wdata),
        .hart_run       (hart_run),
        .halted         (halted),
        .halt_cause     (w_cause),
        .rvfi_valid     (rvfi_valid),
        .rvfi_ctx       (rvfi_ctx),
        .rvfi_rd_addr   (rvfi_rd_addr),
        .rvfi_rd_wdata  (rvfi_rd_wdata),
        .o_run          (),
        .o_halted       ()
    );

    gatling_core #(
        .RESET_ADDR (RESET_ADDR)
    ) u_core (
        .clk            (clk),
        .rst_n          (rst_n),
        .hart_run       (hart_run),
        .imem_ctx       (imem_ctx),
        .imem_addr      (imem_addr),
        .imem_rdata     (imem_rdata),
        .dmem_req       (dmem_req),
        .dmem_ctx       (dmem_ctx),
        .dmem_addr      (dmem_addr),
        .dmem_rdata     (dmem_rdata),
        .dmem_wstrb     (dmem_wstrb),
        .dmem_wdata     (dmem_wdata),
        .halted         (halted),
        .halt_cause     (w_cause),
        .rvfi_valid     (rvfi_valid),
        .rvfi_ctx       (rvfi_ctx),
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

endmodule : gatling_bram_tb_top
