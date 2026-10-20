// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_bram_tb_top
// Purpose: kestrel_core behind kestrel_mem_bram -- the registered-read (block
//          RAM) board path.  Same ports as kestrel_loader_tb_top so the
//          loader TB class and the rv32ui battery run unchanged; the core's
//          dmem strobe is exposed qualified by !mem_wait, because during a
//          wait cycle the decode is looking at a stale instruction word and
//          the store watch must see each committed store exactly once.
//
// Documentation: projects/components/riscv-ip/README.md
// Subsystem: riscv-ip/kestrel-rv32i
//
// Author: sean galloway
// Created: 2026-10-20

`timescale 1ns / 1ps

module kestrel_bram_tb_top #(
    parameter logic [31:0] RESET_ADDR = 32'h0000_0000
) (
    input  logic        clk,
    input  logic        rst_n,

    // -------------------------------------------------------------------
    // AXIL slave port (driven by the cocotb AXIL4 master BFM)
    // -------------------------------------------------------------------
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

    // -------------------------------------------------------------------
    // Core observability (same contract as kestrel_tb_top)
    // -------------------------------------------------------------------
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

    // -------------------------------------------------------------------
    // Loader-specific observability (load-mode isolation checks)
    // -------------------------------------------------------------------
    output logic        core_rst_n,
    output logic [31:0] imem_addr,
    output logic [31:0] imem_rdata,
    output logic        dbg_busy_wr,
    output logic        dbg_busy_rd
);

    logic [31:0] dmem_rdata;
    logic        w_dmem_req, w_mem_wait, w_halt;
    logic [3:0]  w_halt_cause;

    assign dmem_req    = w_dmem_req & ~w_mem_wait;
    assign halt        = w_halt;
    assign halt_cause  = w_halt_cause;
    assign dbg_busy_wr = 1'b0;
    assign dbg_busy_rd = 1'b0;

    kestrel_mem_bram u_mem (
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
        .imem_addr      (imem_addr),
        .imem_rdata     (imem_rdata),
        .dmem_req       (w_dmem_req),
        .dmem_addr      (dmem_addr),
        .dmem_rdata     (dmem_rdata),
        .dmem_wstrb     (dmem_wstrb),
        .dmem_wdata     (dmem_wdata),
        .mem_wait       (w_mem_wait),
        .core_rst_n     (core_rst_n),
        .halt           (w_halt),
        .halt_cause     (w_halt_cause),
        .rvfi_valid     (rvfi_valid),
        .rvfi_rd_addr   (rvfi_rd_addr),
        .rvfi_rd_wdata  (rvfi_rd_wdata),
        .o_run          (),
        .o_halted       ()
    );

    kestrel_core #(
        .RESET_ADDR (RESET_ADDR)
    ) u_kestrel_core (
        .clk            (clk),
        .rst_n          (core_rst_n),
        .mem_wait       (w_mem_wait),
        .imem_addr      (imem_addr),
        .imem_rdata     (imem_rdata),
        .dmem_req       (w_dmem_req),
        .dmem_addr      (dmem_addr),
        .dmem_rdata     (dmem_rdata),
        .dmem_wstrb     (dmem_wstrb),
        .dmem_wdata     (dmem_wdata),
        .halt           (w_halt),
        .halt_cause     (w_halt_cause),
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

endmodule : kestrel_bram_tb_top
