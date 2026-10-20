// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: kestrel_genesys2_top
// Purpose: kestrel RV32I on the Genesys 2: 200 MHz LVDS -> MMCM -> harness
//          clock, UART -> AXI4-Lite -> kestrel_mem_bram (block RAM,
//          registered read) -> kestrel_core, status on the LEDs
//
// Documentation: projects/fpga-systems/Genesys2/riscv-ip/kestrel/README.md
// Subsystem: fpga-systems / riscv-ip
//
// Author: sean galloway
// Created: 2026-10-20

`timescale 1ns / 1ps

`include "reset_defs.svh"

module kestrel_genesys2_top #(
    parameter logic [31:0] RESET_ADDR = 32'h8000_0000   // the riscv-tests link base
) (
    input  logic        sysclk_p,       // 200 MHz LVDS (+)
    input  logic        sysclk_n,       // 200 MHz LVDS (-)
    input  logic        cpu_resetn,     // active-low pushbutton (R19)

    input  logic        uart_tx_in,     // host -> FPGA
    output logic        uart_rx_out,    // FPGA -> host

    output logic [7:0]  led
);

    // 80 MHz: the single-cycle path (block-RAM output -> decode -> register
    // write enable, 16 levels) misses 100 MHz by 0.43 ns post-route; it closes
    // near 95 MHz, and 80 is the exact MMCM division that leaves margin.
    localparam int FPGA_CLK_HZ = 80_000_000;
    localparam int UART_BAUD   = 115_200;

    // -------------------------------------------------------------------------
    // 200 MHz LVDS -> MMCM -> 80 MHz (VCO 1200 MHz, CLKOUT0 / 15)
    // -------------------------------------------------------------------------
    logic sysclk_ib, clk_unbuf, clk, clkfb, clkfb_buf, mmcm_locked;

    IBUFDS u_ibufds (.I(sysclk_p), .IB(sysclk_n), .O(sysclk_ib));

    MMCME2_BASE #(
        .BANDWIDTH         ("OPTIMIZED"),
        .CLKIN1_PERIOD     (5.000),
        .DIVCLK_DIVIDE     (1),
        .CLKFBOUT_MULT_F   (6.000),
        .CLKOUT0_DIVIDE_F  (15.000),
        .CLKOUT0_DUTY_CYCLE(0.500),
        .CLKOUT0_PHASE     (0.000),
        .STARTUP_WAIT      ("FALSE")
    ) u_mmcm (
        .CLKIN1   (sysclk_ib),
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
    // UART -> AXI4-Lite (the loader decodes addr[17:0])
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
    // kestrel behind the registered-read memory system
    // -------------------------------------------------------------------------
    logic [31:0] imem_addr, imem_rdata, dmem_addr, dmem_rdata, dmem_wdata;
    logic        dmem_req, mem_wait, core_rst_n, halt, rvfi_valid;
    logic [3:0]  dmem_wstrb, halt_cause;
    logic [4:0]  rvfi_rd_addr;
    logic [31:0] rvfi_rd_wdata;
    logic        w_run, w_halted;

    kestrel_mem_bram u_mem (
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
        .imem_addr(imem_addr), .imem_rdata(imem_rdata),
        .dmem_req(dmem_req), .dmem_addr(dmem_addr), .dmem_rdata(dmem_rdata),
        .dmem_wstrb(dmem_wstrb), .dmem_wdata(dmem_wdata),
        .mem_wait(mem_wait), .core_rst_n(core_rst_n),
        .halt(halt), .halt_cause(halt_cause),
        .rvfi_valid(rvfi_valid), .rvfi_rd_addr(rvfi_rd_addr), .rvfi_rd_wdata(rvfi_rd_wdata),
        .o_run(w_run), .o_halted(w_halted));

    kestrel_core #(
        .RESET_ADDR(RESET_ADDR)
    ) u_core (
        .clk(clk), .rst_n(core_rst_n), .mem_wait(mem_wait),
        .imem_addr(imem_addr), .imem_rdata(imem_rdata),
        .dmem_req(dmem_req), .dmem_addr(dmem_addr), .dmem_rdata(dmem_rdata),
        .dmem_wstrb(dmem_wstrb), .dmem_wdata(dmem_wdata),
        .halt(halt), .halt_cause(halt_cause),
        .rvfi_valid(rvfi_valid), .rvfi_order(), .rvfi_pc_rdata(), .rvfi_pc_wdata(),
        .rvfi_insn(), .rvfi_trap(), .rvfi_rs1_addr(), .rvfi_rs2_addr(),
        .rvfi_rs1_rdata(), .rvfi_rs2_rdata(), .rvfi_rd_addr(rvfi_rd_addr),
        .rvfi_rd_wdata(rvfi_rd_wdata), .rvfi_mem_addr(), .rvfi_mem_rmask(),
        .rvfi_mem_wmask(), .rvfi_mem_rdata(), .rvfi_mem_wdata());

    // -------------------------------------------------------------------------
    // LEDs
    // -------------------------------------------------------------------------
    logic [26:0] r_heartbeat;
    `ALWAYS_FF_RST(clk, sys_rstn,
        if (`RST_ASSERTED(sys_rstn)) r_heartbeat <= '0;
        else                         r_heartbeat <= r_heartbeat + 27'd1;
    )

    assign led[0] = w_run;
    assign led[1] = w_halted;
    assign led[2] = w_halted && (halt_cause == 4'd1);    // stopped on ecall
    assign led[3] = mmcm_locked;
    assign led[4] = 1'b0;
    assign led[5] = axil_awvalid || axil_arvalid;
    assign led[6] = axil_rvalid  || axil_bvalid;
    assign led[7] = r_heartbeat[26];

endmodule : kestrel_genesys2_top
