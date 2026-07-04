// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: ddr2_char_top
// Purpose: FPGA pin-level top for the DDR2/LPDDR2 characterization harness.
//
// Target board: Digilent Nexys A7-100T (xc7a100tcsg324-1)
//
// Pin mapping (typical; final pins fixed by XDC):
//   CLK100MHZ       100 MHz system clock (E3)
//   CPU_RESETN      center pushbutton (C12, active-low)
//   UART_TXD_IN     FTDI -> FPGA RX     (C4)
//   UART_RXD_OUT    FPGA -> FTDI TX     (D4)
//   LED[15:0]       harness status
//   AN[7:0], CA..CG, DP  4-digit 7-segment
//
// DDR2 PHY pins (routed straight to the a7ddrphy that this top
// instantiates alongside the harness) come out via the DDR2_* ports on
// the board; those pin names are set by the XDC.
//
// This top intentionally does nothing beyond pin I/O, clock/reset
// synchronisation, and instantiating ddr2_char_harness. The a7ddrphy
// binding is a separate integration step (deferred — this top is the
// harness landing point that the LiteX-based flow will slot into).

`timescale 1ns / 1ps

`include "reset_defs.svh"

module ddr2_char_top (
    input  logic        CLK100MHZ,
    input  logic        CPU_RESETN,

    input  logic        UART_TXD_IN,
    output logic        UART_RXD_OUT,

    output logic [15:0] LED,

    output logic [7:0]  AN,
    output logic        CA, CB, CC, CD,
    output logic        CE, CF, CG,
    output logic        DP
);

    // =========================================================================
    // Reset synchronisation (async assert, sync deassert)
    // =========================================================================
    (* ASYNC_REG = "TRUE" *) logic r_rst_meta;
    (* ASYNC_REG = "TRUE" *) logic r_rst_sync;
    always_ff @(posedge CLK100MHZ or negedge CPU_RESETN) begin
        if (!CPU_RESETN) begin
            r_rst_meta <= 1'b0;
            r_rst_sync <= 1'b0;
        end else begin
            r_rst_meta <= 1'b1;
            r_rst_sync <= r_rst_meta;
        end
    end

    wire aclk    = CLK100MHZ;
    wire aresetn = r_rst_sync;

    // =========================================================================
    // 7-segment glue: harness emits o_seg[6:0] = {g,f,e,d,c,b,a}. Fan into
    // the board's discrete CA..CG pins.
    // =========================================================================
    logic [6:0] w_seg;
    assign CA = w_seg[0];
    assign CB = w_seg[1];
    assign CC = w_seg[2];
    assign CD = w_seg[3];
    assign CE = w_seg[4];
    assign CF = w_seg[5];
    assign CG = w_seg[6];

    // =========================================================================
    // DFI signals: harness pins them out, but on this bring-up top they
    // are left dangling — the a7ddrphy integration is deferred (LiteX
    // sub-flow will attach). Tie inputs to safe defaults so verilator +
    // synthesis can lint the harness in isolation.
    // =========================================================================
    localparam int DFI_RATE       = 2;
    localparam int DFI_DATA_WIDTH = DFI_RATE * 64;

    // Outputs from harness — left dangling in this pin-only top.
    logic [31:0]                  w_dfi_address;
    logic [2:0]                   w_dfi_bank;
    logic [DFI_RATE-1:0]          w_dfi_cas_n, w_dfi_ras_n, w_dfi_we_n;
    logic [DFI_RATE-1:0]          w_dfi_cs_n, w_dfi_cke, w_dfi_odt;
    logic [DFI_DATA_WIDTH-1:0]    w_dfi_wrdata;
    logic [(DFI_DATA_WIDTH/8)-1:0] w_dfi_wrdata_mask;
    logic [DFI_RATE-1:0]          w_dfi_wrdata_en, w_dfi_rddata_en;
    logic [DFI_RATE-1:0]          w_dfi_dram_clk_disable;
    logic                         w_dfi_init_start;
    logic                         w_dfi_ctrlupd_req, w_dfi_phyupd_ack;

    ddr2_char_harness u_harness (
        .aclk    (aclk),
        .aresetn (aresetn),

        .i_uart_rx (UART_TXD_IN),
        .o_uart_tx (UART_RXD_OUT),

        .o_led           (LED),
        .o_seven_seg_an  (AN),
        .o_seven_seg_seg (w_seg),
        .o_seven_seg_dp  (DP),

        .o_dfi_address          (w_dfi_address),
        .o_dfi_bank             (w_dfi_bank),
        .o_dfi_cas_n            (w_dfi_cas_n),
        .o_dfi_ras_n            (w_dfi_ras_n),
        .o_dfi_we_n             (w_dfi_we_n),
        .o_dfi_cs_n             (w_dfi_cs_n),
        .o_dfi_cke              (w_dfi_cke),
        .o_dfi_odt              (w_dfi_odt),
        .o_dfi_wrdata           (w_dfi_wrdata),
        .o_dfi_wrdata_mask      (w_dfi_wrdata_mask),
        .o_dfi_wrdata_en        (w_dfi_wrdata_en),
        .o_dfi_rddata_en        (w_dfi_rddata_en),
        .i_dfi_rddata           ('0),
        .i_dfi_rddata_valid     ('0),
        .o_dfi_dram_clk_disable (w_dfi_dram_clk_disable),
        .o_dfi_init_start       (w_dfi_init_start),
        .i_dfi_init_complete    (1'b1),
        .o_dfi_ctrlupd_req      (w_dfi_ctrlupd_req),
        .i_dfi_ctrlupd_ack      (1'b0),
        .i_dfi_phyupd_req       (1'b0),
        .o_dfi_phyupd_ack       (w_dfi_phyupd_ack),
        .i_dfi_phyupd_type      (2'b00)
    );

    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0,
        w_dfi_address, w_dfi_bank, w_dfi_cas_n, w_dfi_ras_n, w_dfi_we_n,
        w_dfi_cs_n, w_dfi_cke, w_dfi_odt, w_dfi_wrdata, w_dfi_wrdata_mask,
        w_dfi_wrdata_en, w_dfi_rddata_en,
        w_dfi_dram_clk_disable, w_dfi_init_start,
        w_dfi_ctrlupd_req, w_dfi_phyupd_ack,
        1'b0};
    /* verilator lint_on UNUSED */

endmodule : ddr2_char_top
