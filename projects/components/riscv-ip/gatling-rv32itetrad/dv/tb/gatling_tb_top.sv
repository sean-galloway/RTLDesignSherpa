// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gatling_tb_top
// Purpose: cocotb harness for gatling_core: four behavioral registered-read
//          memory banks (one per context, the gatling_mem_bram timing
//          without its AXIL front end), a backdoor image port, and the
//          core's run/halt/RVFI signals at the top level.
//
//          Bank c is context c's whole address space (MEM_WORDS words,
//          aliased above), so four images linked at the same base load side
//          by side.  The backdoor writes one word per cycle into the bank
//          named by tb_mem_ctx while that context is held (hart_run low);
//          it is not part of the DUT contract.
//
// Documentation: projects/components/riscv-ip/gatling-rv32itetrad/docs/gatling_mas
// Subsystem: riscv-ip/gatling-rv32itetrad
//
// Author: sean galloway
// Created: 2026-10-21

`timescale 1ns / 1ps

module gatling_tb_top #(
    parameter logic [31:0] RESET_ADDR = 32'h0000_0000,
    parameter int          MEM_WORDS  = 16384           // 64 KB per context
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic [3:0]       hart_run,

    output logic [3:0]       halted,
    output logic [15:0]      halt_cause,        // {ctx3, ctx2, ctx1, ctx0}, 4 bits each
    output logic             dmem_req,
    output logic [1:0]       dmem_ctx,
    output logic [31:0]      dmem_addr,
    output logic [3:0]       dmem_wstrb,
    output logic [31:0]      dmem_wdata,
    output logic [1:0]       imem_ctx,
    output logic [31:0]      imem_addr,

    output logic             rvfi_valid,
    output logic [1:0]       rvfi_ctx,
    output logic [63:0]      rvfi_order,
    output logic [31:0]      rvfi_pc_rdata,
    output logic [31:0]      rvfi_pc_wdata,
    output logic [31:0]      rvfi_insn,
    output logic             rvfi_trap,
    output logic [4:0]       rvfi_rs1_addr,
    output logic [4:0]       rvfi_rs2_addr,
    output logic [31:0]      rvfi_rs1_rdata,
    output logic [31:0]      rvfi_rs2_rdata,
    output logic [4:0]       rvfi_rd_addr,
    output logic [31:0]      rvfi_rd_wdata,
    output logic [31:0]      rvfi_mem_addr,
    output logic [3:0]       rvfi_mem_rmask,
    output logic [3:0]       rvfi_mem_wmask,
    output logic [31:0]      rvfi_mem_rdata,
    output logic [31:0]      rvfi_mem_wdata,

    // TB backdoor image loader
    input  logic             tb_mem_we,
    input  logic [1:0]       tb_mem_ctx,
    input  logic [31:0]      tb_mem_addr,
    input  logic [31:0]      tb_mem_wdata
);

    localparam int IDX_W = $clog2(MEM_WORDS);

    logic [31:0] mem [4*MEM_WORDS];
    logic [31:0] imem_rdata, dmem_rdata;
    logic [3:0][3:0] w_cause;

    assign halt_cause = w_cause;

    initial begin
        for (int i = 0; i < 4 * MEM_WORDS; i++) mem[i] = '0;
    end

    // Registered reads, one cycle, exactly as gatling_mem_bram's ports.
    always_ff @(posedge clk) begin
        imem_rdata <= mem[{imem_ctx, imem_addr[IDX_W+1:2]}];
        if (dmem_req) begin
            for (int b = 0; b < 4; b++)
                if (dmem_wstrb[b])
                    mem[{dmem_ctx, dmem_addr[IDX_W+1:2]}][b*8 +: 8] <= dmem_wdata[b*8 +: 8];
            dmem_rdata <= mem[{dmem_ctx, dmem_addr[IDX_W+1:2]}];
        end
        if (tb_mem_we) mem[{tb_mem_ctx, tb_mem_addr[IDX_W+1:2]}] <= tb_mem_wdata;
    end

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

endmodule : gatling_tb_top
