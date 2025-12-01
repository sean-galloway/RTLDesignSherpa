// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_uart_16550
// Purpose: APB UART 16550 Controller Top Level
//
// Description:
//   Complete APB-accessible NS16550-compatible UART controller with:
//   - 16-byte TX and RX FIFOs
//   - Programmable baud rate
//   - Full modem control
//   - Interrupt support
//   - Optional CDC for async pin domains
//
// Architecture (RLB Standard Pattern):
//   APB -> apb_slave[_cdc] -> CMD/RSP -> peakrdl_to_cmdrsp ->
//     -> uart_16550_regs (PeakRDL) -> hwif -> uart_16550_core
//
// Documentation: projects/components/retro_legacy_blocks/rtl/uart_16550/README.md
// Created: 2025-11-29
// Updated: 2025-11-30 - Changed to 32-bit data width, s_apb_* naming

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb_uart_16550 #(
    // UART Parameters
    parameter int FIFO_DEPTH   = 16,             // FIFO depth (16 for 16550)
    parameter int SYNC_STAGES  = 2,              // Input synchronizer stages

    // CDC Parameters
    parameter int CDC_ENABLE   = 0,              // 1=async clocks, 0=same clock
    parameter int SKID_DEPTH   = 2               // CDC skid buffer depth
) (
    // APB Clock and Reset
    input  logic                        pclk,
    input  logic                        presetn,

    // Optional separate UART clock (when CDC_ENABLE=1)
    input  logic                        uart_clk,
    input  logic                        uart_rstn,

    // APB Slave Interface (consistent s_apb_* naming, 32-bit)
    input  logic                        s_apb_PSEL,
    input  logic                        s_apb_PENABLE,
    output logic                        s_apb_PREADY,
    input  logic [11:0]                 s_apb_PADDR,
    input  logic                        s_apb_PWRITE,
    input  logic [31:0]                 s_apb_PWDATA,
    input  logic [3:0]                  s_apb_PSTRB,
    input  logic [2:0]                  s_apb_PPROT,
    output logic [31:0]                 s_apb_PRDATA,
    output logic                        s_apb_PSLVERR,

    // Serial Interface
    input  logic                        uart_rx,
    output logic                        uart_tx,

    // Modem Control Inputs (directly from pins, active low)
    input  logic                        cts_n,
    input  logic                        dsr_n,
    input  logic                        ri_n,
    input  logic                        dcd_n,

    // Modem Control Outputs
    output logic                        dtr_n,
    output logic                        rts_n,
    output logic                        out1_n,
    output logic                        out2_n,

    // Interrupt Output
    output logic                        irq
);

    // ========================================================================
    // Internal Signals
    // ========================================================================

    // Fixed APB parameters (32-bit, 12-bit address)
    localparam int APB_ADDR_WIDTH = 12;
    localparam int APB_DATA_WIDTH = 32;
    localparam int APB_STRB_WIDTH = APB_DATA_WIDTH / 8;
    localparam int APB_PROT_WIDTH = 3;

    // CMD/RSP interface (APB slave to peakrdl_to_cmdrsp)
    logic                       w_cmd_valid;
    logic                       w_cmd_ready;
    logic                       w_cmd_pwrite;
    logic [APB_ADDR_WIDTH-1:0]  w_cmd_paddr;
    logic [APB_DATA_WIDTH-1:0]  w_cmd_pwdata;
    logic [APB_STRB_WIDTH-1:0]  w_cmd_pstrb;
    logic [APB_PROT_WIDTH-1:0]  w_cmd_pprot;
    logic                       w_rsp_valid;
    logic                       w_rsp_ready;
    logic [APB_DATA_WIDTH-1:0]  w_rsp_prdata;
    logic                       w_rsp_pslverr;

    // PeakRDL regblock interface
    logic                       w_regblk_req;
    logic                       w_regblk_req_is_wr;
    logic [APB_ADDR_WIDTH-1:0]  w_regblk_addr;
    logic [APB_DATA_WIDTH-1:0]  w_regblk_wr_data;
    logic [APB_DATA_WIDTH-1:0]  w_regblk_wr_biten;
    logic                       w_regblk_req_stall_wr;
    logic                       w_regblk_req_stall_rd;
    logic                       w_regblk_rd_ack;
    logic                       w_regblk_rd_err;
    logic [APB_DATA_WIDTH-1:0]  w_regblk_rd_data;
    logic                       w_regblk_wr_ack;
    logic                       w_regblk_wr_err;

    // Clock selection
    logic w_core_clk;
    logic w_core_rstn;

    assign w_core_clk  = CDC_ENABLE ? uart_clk  : pclk;
    assign w_core_rstn = CDC_ENABLE ? uart_rstn : presetn;

    // ========================================================================
    // APB Slave - CMD/RSP Conversion
    // ========================================================================
    generate
        if (CDC_ENABLE) begin : gen_cdc
            apb_slave_cdc #(
                .ADDR_WIDTH (APB_ADDR_WIDTH),
                .DATA_WIDTH (APB_DATA_WIDTH),
                .DEPTH      (SKID_DEPTH)
            ) u_apb_slave_cdc (
                // APB clock domain
                .pclk           (pclk),
                .presetn        (presetn),
                // Core clock domain
                .aclk           (w_core_clk),
                .aresetn        (w_core_rstn),
                // APB interface (s_apb_* naming)
                .s_apb_PSEL     (s_apb_PSEL),
                .s_apb_PENABLE  (s_apb_PENABLE),
                .s_apb_PREADY   (s_apb_PREADY),
                .s_apb_PADDR    (s_apb_PADDR),
                .s_apb_PWRITE   (s_apb_PWRITE),
                .s_apb_PWDATA   (s_apb_PWDATA),
                .s_apb_PSTRB    (s_apb_PSTRB),
                .s_apb_PPROT    (s_apb_PPROT),
                .s_apb_PRDATA   (s_apb_PRDATA),
                .s_apb_PSLVERR  (s_apb_PSLVERR),
                // CMD/RSP interface
                .cmd_valid      (w_cmd_valid),
                .cmd_ready      (w_cmd_ready),
                .cmd_pwrite     (w_cmd_pwrite),
                .cmd_paddr      (w_cmd_paddr),
                .cmd_pwdata     (w_cmd_pwdata),
                .cmd_pstrb      (w_cmd_pstrb),
                .cmd_pprot      (w_cmd_pprot),
                .rsp_valid      (w_rsp_valid),
                .rsp_ready      (w_rsp_ready),
                .rsp_prdata     (w_rsp_prdata),
                .rsp_pslverr    (w_rsp_pslverr)
            );
        end else begin : gen_no_cdc
            apb_slave #(
                .ADDR_WIDTH (APB_ADDR_WIDTH),
                .DATA_WIDTH (APB_DATA_WIDTH)
            ) u_apb_slave (
                .pclk           (pclk),
                .presetn        (presetn),
                // APB interface (s_apb_* naming)
                .s_apb_PSEL     (s_apb_PSEL),
                .s_apb_PENABLE  (s_apb_PENABLE),
                .s_apb_PREADY   (s_apb_PREADY),
                .s_apb_PADDR    (s_apb_PADDR),
                .s_apb_PWRITE   (s_apb_PWRITE),
                .s_apb_PWDATA   (s_apb_PWDATA),
                .s_apb_PSTRB    (s_apb_PSTRB),
                .s_apb_PPROT    (s_apb_PPROT),
                .s_apb_PRDATA   (s_apb_PRDATA),
                .s_apb_PSLVERR  (s_apb_PSLVERR),
                // CMD/RSP interface
                .cmd_valid      (w_cmd_valid),
                .cmd_ready      (w_cmd_ready),
                .cmd_pwrite     (w_cmd_pwrite),
                .cmd_paddr      (w_cmd_paddr),
                .cmd_pwdata     (w_cmd_pwdata),
                .cmd_pstrb      (w_cmd_pstrb),
                .cmd_pprot      (w_cmd_pprot),
                .rsp_valid      (w_rsp_valid),
                .rsp_ready      (w_rsp_ready),
                .rsp_prdata     (w_rsp_prdata),
                .rsp_pslverr    (w_rsp_pslverr)
            );
        end
    endgenerate

    // ========================================================================
    // PeakRDL to CMD/RSP Adapter
    // ========================================================================
    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH (APB_ADDR_WIDTH),
        .DATA_WIDTH (APB_DATA_WIDTH)
    ) u_peakrdl_adapter (
        .aclk               (w_core_clk),
        .aresetn            (w_core_rstn),

        // CMD/RSP input from APB slave
        .cmd_valid          (w_cmd_valid),
        .cmd_ready          (w_cmd_ready),
        .cmd_pwrite         (w_cmd_pwrite),
        .cmd_paddr          (w_cmd_paddr),
        .cmd_pwdata         (w_cmd_pwdata),
        .cmd_pstrb          (w_cmd_pstrb),
        .rsp_valid          (w_rsp_valid),
        .rsp_ready          (w_rsp_ready),
        .rsp_prdata         (w_rsp_prdata),
        .rsp_pslverr        (w_rsp_pslverr),

        // PeakRDL register block interface
        .regblk_req         (w_regblk_req),
        .regblk_req_is_wr   (w_regblk_req_is_wr),
        .regblk_addr        (w_regblk_addr),
        .regblk_wr_data     (w_regblk_wr_data),
        .regblk_wr_biten    (w_regblk_wr_biten),
        .regblk_req_stall_wr(w_regblk_req_stall_wr),
        .regblk_req_stall_rd(w_regblk_req_stall_rd),
        .regblk_rd_ack      (w_regblk_rd_ack),
        .regblk_rd_err      (w_regblk_rd_err),
        .regblk_rd_data     (w_regblk_rd_data),
        .regblk_wr_ack      (w_regblk_wr_ack),
        .regblk_wr_err      (w_regblk_wr_err)
    );

    // ========================================================================
    // UART Configuration Registers + Core
    // ========================================================================
    uart_16550_config_regs #(
        .FIFO_DEPTH     (FIFO_DEPTH),
        .SYNC_STAGES    (SYNC_STAGES),
        .ADDR_WIDTH     (APB_ADDR_WIDTH),
        .DATA_WIDTH     (APB_DATA_WIDTH)
    ) u_uart_config_regs (
        .clk                (w_core_clk),
        .rst_n              (w_core_rstn),

        // PeakRDL regblock interface (from peakrdl_to_cmdrsp)
        .regblk_req         (w_regblk_req),
        .regblk_req_is_wr   (w_regblk_req_is_wr),
        .regblk_addr        (w_regblk_addr),
        .regblk_wr_data     (w_regblk_wr_data),
        .regblk_wr_biten    (w_regblk_wr_biten),
        .regblk_req_stall_wr(w_regblk_req_stall_wr),
        .regblk_req_stall_rd(w_regblk_req_stall_rd),
        .regblk_rd_ack      (w_regblk_rd_ack),
        .regblk_rd_err      (w_regblk_rd_err),
        .regblk_rd_data     (w_regblk_rd_data),
        .regblk_wr_ack      (w_regblk_wr_ack),
        .regblk_wr_err      (w_regblk_wr_err),

        // Serial interface
        .uart_rx            (uart_rx),
        .uart_tx            (uart_tx),

        // Modem
        .cts_n              (cts_n),
        .dsr_n              (dsr_n),
        .ri_n               (ri_n),
        .dcd_n              (dcd_n),
        .dtr_n              (dtr_n),
        .rts_n              (rts_n),
        .out1_n             (out1_n),
        .out2_n             (out2_n),

        // Interrupt
        .irq                (irq)
    );

endmodule : apb_uart_16550
