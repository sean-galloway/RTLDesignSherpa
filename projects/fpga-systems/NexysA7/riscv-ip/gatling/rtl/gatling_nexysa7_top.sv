// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gatling_nexysa7_top
// Purpose: gatling, the four-context barrel RV32I, on the Nexys A7-100T:
//          100 MHz -> MMCM -> harness clock, UART -> AXI4-Lite ->
//          gatling_mem_bram (block RAM, one bank per hart) -> gatling_core,
//          per-hart status on the LEDs
//
// Documentation: projects/fpga-systems/NexysA7/riscv-ip/gatling/README.md
// Subsystem: fpga-systems / riscv-ip
//
// Author: sean galloway
// Created: 2026-10-21

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gatling_nexysa7_top #(
    parameter logic [31:0] RESET_ADDR = 32'h8000_0000   // the riscv-tests link base
) (
    input  logic        sysclk,         // 100 MHz oscillator (E3)
    input  logic        cpu_resetn,     // active-low pushbutton (C12)

    input  logic        uart_tx_in,     // host -> FPGA
    output logic        uart_rx_out,    // FPGA -> host

    output logic [7:0]  led
);

    // Harness clock = 100 MHz * VCO_MULT / CLK_DIV.  100 MHz: VCO 1000 MHz
    // / 10.  Each barrel stage is a fraction of kestrel's single-cycle path
    // (README "Board result").
    localparam int VCO_MULT    = 10;
    localparam int CLK_DIV     = 10;
    localparam int FPGA_CLK_HZ = (100_000_000 * VCO_MULT) / CLK_DIV;
    localparam int UART_BAUD   = 115_200;

    // -------------------------------------------------------------------------
    // 100 MHz -> MMCM -> harness clock
    // -------------------------------------------------------------------------
    logic clk_unbuf, clk, clkfb, clkfb_buf, mmcm_locked;

    MMCME2_BASE #(
        .BANDWIDTH         ("OPTIMIZED"),
        .CLKIN1_PERIOD     (10.000),
        .DIVCLK_DIVIDE     (1),
        .CLKFBOUT_MULT_F   (VCO_MULT),
        .CLKOUT0_DIVIDE_F  (CLK_DIV),
        .CLKOUT0_DUTY_CYCLE(0.500),
        .CLKOUT0_PHASE     (0.000),
        .STARTUP_WAIT      ("FALSE")
    ) u_mmcm (
        .CLKIN1   (sysclk),
        .CLKFBIN  (clkfb_buf),
        .CLKFBOUT (clkfb),
        .CLKFBOUTB(),
        .CLKOUT0  (clk_unbuf),
        .CLKOUT0B (), .CLKOUT1 (), .CLKOUT1B(), .CLKOUT2 (), .CLKOUT2B(),
        .CLKOUT3  (), .CLKOUT3B(), .CLKOUT4 (), .CLKOUT5 (), .CLKOUT6 (),
        .LOCKED   (mmcm_locked),
        .RST      (1'b0),
        .PWRDWN   (1'b0)
    );
    BUFG u_bufg_fb (.I(clkfb),     .O(clkfb_buf));
    BUFG u_bufg_c0 (.I(clk_unbuf), .O(clk));

    // -------------------------------------------------------------------------
    // Reset: held until the MMCM locks, OR the pushbutton; synchronized
    // -------------------------------------------------------------------------
    logic rst_n_raw, sys_rstn;
    assign rst_n_raw = cpu_resetn & mmcm_locked;

    (* ASYNC_REG = "TRUE" *) logic r_rstn_sync0, r_rstn_sync1;
    `ALWAYS_FF_RST(clk, rst_n_raw,
        if (`RST_ASSERTED(rst_n_raw)) begin
            r_rstn_sync0 <= 1'b0;
            r_rstn_sync1 <= 1'b0;
        end else begin
            r_rstn_sync0 <= 1'b1;
            r_rstn_sync1 <= r_rstn_sync0;
        end
    )
    assign sys_rstn = r_rstn_sync1;

    // -------------------------------------------------------------------------
    // UART -> AXI4-Lite (the memory system decodes addr[17:0])
    // -------------------------------------------------------------------------
    localparam int UART_CLKS_PER_BIT = (FPGA_CLK_HZ + UART_BAUD / 2) / UART_BAUD;

    logic [31:0] axil_awaddr, axil_araddr, axil_wdata, axil_rdata;
    logic [2:0]  axil_awprot, axil_arprot;
    logic [3:0]  axil_wstrb;
    logic [1:0]  axil_bresp, axil_rresp;
    logic        axil_awvalid, axil_awready, axil_wvalid, axil_wready, axil_bvalid, axil_bready;
    logic        axil_arvalid, axil_arready, axil_rvalid, axil_rready;

    uart_axil_bridge #(
        .AXIL_ADDR_WIDTH(32), .AXIL_DATA_WIDTH(32), .CLKS_PER_BIT(UART_CLKS_PER_BIT)
    ) u_uart_bridge (
        .aclk(clk), .aresetn(sys_rstn),
        .i_uart_rx(uart_tx_in), .o_uart_tx(uart_rx_out),
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
    // gatling behind its block-RAM memory system
    // -------------------------------------------------------------------------
    logic [1:0]      imem_ctx, dmem_ctx, rvfi_ctx;
    logic [31:0]     imem_addr, imem_rdata, dmem_addr, dmem_rdata, dmem_wdata;
    logic            dmem_req, rvfi_valid;
    logic [3:0]      dmem_wstrb, hart_run, halted;
    logic [3:0][3:0] halt_cause;
    logic [4:0]      rvfi_rd_addr;
    logic [31:0]     rvfi_rd_wdata;
    logic [3:0]      w_run, w_halted;

    gatling_mem_bram u_mem (
        .aclk(clk), .aresetn(sys_rstn),
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
        .o_run(w_run), .o_halted(w_halted));

    gatling_core #(
        .RESET_ADDR(RESET_ADDR)
    ) u_core (
        .clk(clk), .rst_n(sys_rstn), .hart_run(hart_run),
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

    // -------------------------------------------------------------------------
    // LEDs: 0-3 a hart running (on) or halted (blinking), 4 MMCM locked,
    // 5/6 UART activity, 7 heartbeat
    // -------------------------------------------------------------------------
    logic [26:0] r_heartbeat;
    `ALWAYS_FF_RST(clk, sys_rstn,
        if (`RST_ASSERTED(sys_rstn)) r_heartbeat <= '0;
        else                         r_heartbeat <= r_heartbeat + 27'd1;
    )

    for (genvar h = 0; h < 4; h++) begin : g_hart_led
        assign led[h] = (w_run[h] && !w_halted[h]) || (w_halted[h] && r_heartbeat[24]);
    end
    assign led[4] = mmcm_locked;
    assign led[5] = axil_awvalid || axil_arvalid;
    assign led[6] = axil_rvalid  || axil_bvalid;
    assign led[7] = r_heartbeat[26];

endmodule : gatling_nexysa7_top
