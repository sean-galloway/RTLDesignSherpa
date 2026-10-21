// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: gatling_uart_tb_top
// Purpose: UART-equivalence sim top for build-bram: the board top minus its
//          clocking (no MMCM) -- the REAL uart_axil_bridge + gatling_mem_bram
//          + gatling_core, driven over UART by the unmodified host programs
//          in ../../bin/gatling_programs.py.

`timescale 1ns / 1ps

module gatling_uart_tb_top #(
    // 4, not the board's 868: the sim-time budget; the byte stream under
    // test is identical at any baud.
    parameter int          UART_CLKS_PER_BIT = 4,
    parameter logic [31:0] RESET_ADDR        = 32'h8000_0000
) (
    input  logic       aclk,
    input  logic       aresetn,
    input  logic       i_uart_rx,
    output logic       o_uart_tx,
    output logic [3:0] o_run,
    output logic [3:0] o_halted
);

    // -------------------------------------------------------------------------
    // UART -> AXI4-Lite (the memory system decodes addr[17:0])
    // -------------------------------------------------------------------------
    logic [31:0] axil_awaddr, axil_araddr, axil_wdata, axil_rdata;
    logic [2:0]  axil_awprot, axil_arprot;
    logic [3:0]  axil_wstrb;
    logic [1:0]  axil_bresp, axil_rresp;
    logic        axil_awvalid, axil_awready, axil_wvalid, axil_wready, axil_bvalid, axil_bready;
    logic        axil_arvalid, axil_arready, axil_rvalid, axil_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH(32), .AXIL_DATA_WIDTH(32), .CLKS_PER_BIT(UART_CLKS_PER_BIT)
    ) u_uart_bridge (
        .aclk(aclk), .aresetn(aresetn),
        .i_uart_rx(i_uart_rx), .o_uart_tx(o_uart_tx),
        .m_axil_awaddr(axil_awaddr), .m_axil_awprot(axil_awprot),
        .m_axil_awvalid(axil_awvalid), .m_axil_awready(axil_awready),
        .m_axil_wdata(axil_wdata), .m_axil_wstrb(axil_wstrb),
        .m_axil_wvalid(axil_wvalid), .m_axil_wready(axil_wready),
        .m_axil_bresp(axil_bresp), .m_axil_bvalid(axil_bvalid), .m_axil_bready(axil_bready),
        .m_axil_araddr(axil_araddr), .m_axil_arprot(axil_arprot),
        .m_axil_arvalid(axil_arvalid), .m_axil_arready(axil_arready),
        .m_axil_rdata(axil_rdata), .m_axil_rresp(axil_rresp),
        .m_axil_rvalid(axil_rvalid), .m_axil_rready(axil_rready));

    // -------------------------------------------------------------------------
    // gatling behind its block-RAM memory system (as gatling_nexysa7_top)
    // -------------------------------------------------------------------------
    logic [1:0]      imem_ctx, dmem_ctx, rvfi_ctx;
    logic [31:0]     imem_addr, imem_rdata, dmem_addr, dmem_rdata, dmem_wdata;
    logic            dmem_req, rvfi_valid;
    logic [3:0]      dmem_wstrb, hart_run, halted;
    logic [3:0][3:0] halt_cause;
    logic [4:0]      rvfi_rd_addr;
    logic [31:0]     rvfi_rd_wdata;

    gatling_mem_bram u_mem (
        .aclk(aclk), .aresetn(aresetn),
        .s_axil_awaddr(axil_awaddr[17:0]), .s_axil_awprot(axil_awprot),
        .s_axil_awvalid(axil_awvalid), .s_axil_awready(axil_awready),
        .s_axil_wdata(axil_wdata), .s_axil_wstrb(axil_wstrb),
        .s_axil_wvalid(axil_wvalid), .s_axil_wready(axil_wready),
        .s_axil_bresp(axil_bresp), .s_axil_bvalid(axil_bvalid), .s_axil_bready(axil_bready),
        .s_axil_araddr(axil_araddr[17:0]), .s_axil_arprot(axil_arprot),
        .s_axil_arvalid(axil_arvalid), .s_axil_arready(axil_arready),
        .s_axil_rdata(axil_rdata), .s_axil_rresp(axil_rresp),
        .s_axil_rvalid(axil_rvalid), .s_axil_rready(axil_rready),
        .imem_ctx(imem_ctx), .imem_addr(imem_addr), .imem_rdata(imem_rdata),
        .dmem_req(dmem_req), .dmem_ctx(dmem_ctx), .dmem_addr(dmem_addr),
        .dmem_rdata(dmem_rdata), .dmem_wstrb(dmem_wstrb), .dmem_wdata(dmem_wdata),
        .hart_run(hart_run),
        .halted(halted), .halt_cause(halt_cause),
        .rvfi_valid(rvfi_valid), .rvfi_ctx(rvfi_ctx),
        .rvfi_rd_addr(rvfi_rd_addr), .rvfi_rd_wdata(rvfi_rd_wdata),
        .o_run(o_run), .o_halted(o_halted));

    gatling_core #(
        .RESET_ADDR(RESET_ADDR)
    ) u_core (
        .clk(aclk), .rst_n(aresetn), .hart_run(hart_run),
        .imem_ctx(imem_ctx), .imem_addr(imem_addr), .imem_rdata(imem_rdata),
        .dmem_req(dmem_req), .dmem_ctx(dmem_ctx), .dmem_addr(dmem_addr),
        .dmem_rdata(dmem_rdata), .dmem_wstrb(dmem_wstrb), .dmem_wdata(dmem_wdata),
        .halted(halted), .halt_cause(halt_cause),
        .rvfi_valid(rvfi_valid), .rvfi_ctx(rvfi_ctx), .rvfi_order(),
        .rvfi_pc_rdata(), .rvfi_pc_wdata(), .rvfi_insn(), .rvfi_trap(),
        .rvfi_rs1_addr(), .rvfi_rs2_addr(), .rvfi_rs1_rdata(), .rvfi_rs2_rdata(),
        .rvfi_rd_addr(rvfi_rd_addr), .rvfi_rd_wdata(rvfi_rd_wdata),
        .rvfi_mem_addr(), .rvfi_mem_rmask(), .rvfi_mem_wmask(),
        .rvfi_mem_rdata(), .rvfi_mem_wdata());

endmodule : gatling_uart_tb_top
