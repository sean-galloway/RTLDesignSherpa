// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: ddr2_char_top
// Purpose: FPGA pin-level top for the DDR2/LPDDR2 characterization harness.
//
// Target board: Digilent Nexys A7-100T (xc7a100tcsg324-1)
//
// Pin mapping (from ddr2_char_top.xdc; keep this file's port names in
// lockstep with the XDC or synthesis fails silently):
//
//   CLK100MHZ       100 MHz system clock (E3)
//   CPU_RESETN      center pushbutton (C12, active-low)
//   UART_TXD_IN     FTDI -> FPGA RX     (C4)
//   UART_RXD_OUT    FPGA -> FTDI TX     (D4)
//   LED[15:0]       harness status
//   AN[7:0], CA..CG, DP  4-digit 7-segment
//
//   DDR2 pads:  ddram_a[13:0], ddram_ba[2:0], ddram_ras_n, ddram_cas_n,
//   ddram_we_n, ddram_cs_n, ddram_cke, ddram_odt, ddram_dm[1:0],
//   ddram_dq[15:0], ddram_dqs_p[1:0], ddram_dqs_n[1:0], ddram_clk_p,
//   ddram_clk_n. All pin locations in the XDC.
//
// Instantiates ddr2_char_harness (harness + DUT), the flat-DFI to
// per-phase DFI adapter, and the LiteDRAM a7ddrphy black box. The
// a7ddrphy body is generated at Vivado build time (see
// bin/gen_a7ddrphy.py) — the framework ships only the port-shape stub.

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
    output logic        DP,

    // ---------------- DDR2 pads (Micron MT47H64M16HR-25E) ----------------
    output logic [13:0] ddram_a,
    output logic [2:0]  ddram_ba,
    output logic        ddram_ras_n,
    output logic        ddram_cas_n,
    output logic        ddram_we_n,
    output logic        ddram_cs_n,
    output logic        ddram_cke,
    output logic        ddram_odt,
    output logic [1:0]  ddram_dm,
    inout  wire  [15:0] ddram_dq,
    inout  wire  [1:0]  ddram_dqs_p,
    inout  wire  [1:0]  ddram_dqs_n,
    output logic        ddram_clk_p,
    output logic        ddram_clk_n
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
    // Flat DFI wires (harness <-> adapter <-> a7ddrphy)
    // =========================================================================
    localparam int DFI_RATE       = 2;
    localparam int DFI_DATA_WIDTH = DFI_RATE * 64;
    localparam int DFI_STRB_WIDTH = DFI_DATA_WIDTH / 8;

    logic [31:0]                   w_dfi_address;
    logic [2:0]                    w_dfi_bank;
    logic [DFI_RATE-1:0]           w_dfi_cas_n, w_dfi_ras_n, w_dfi_we_n;
    logic [DFI_RATE-1:0]           w_dfi_cs_n, w_dfi_cke, w_dfi_odt;
    logic [DFI_DATA_WIDTH-1:0]     w_dfi_wrdata;
    logic [DFI_STRB_WIDTH-1:0]     w_dfi_wrdata_mask;
    logic [DFI_RATE-1:0]           w_dfi_wrdata_en;
    logic [DFI_RATE-1:0]           w_dfi_rddata_en;
    logic [DFI_DATA_WIDTH-1:0]     w_dfi_rddata;
    logic [DFI_RATE-1:0]           w_dfi_rddata_valid;
    logic [DFI_RATE-1:0]           w_dfi_dram_clk_disable;
    logic                          w_dfi_init_start;
    logic                          w_dfi_init_complete;
    logic                          w_dfi_ctrlupd_req;
    logic                          w_dfi_phyupd_ack;

    // =========================================================================
    // Harness
    // =========================================================================
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
        .i_dfi_rddata           (w_dfi_rddata),
        .i_dfi_rddata_valid     (w_dfi_rddata_valid),
        .o_dfi_dram_clk_disable (w_dfi_dram_clk_disable),
        .o_dfi_init_start       (w_dfi_init_start),
        .i_dfi_init_complete    (w_dfi_init_complete),
        .o_dfi_ctrlupd_req      (w_dfi_ctrlupd_req),
        .i_dfi_ctrlupd_ack      (1'b0),
        .i_dfi_phyupd_req       (1'b0),
        .o_dfi_phyupd_ack       (w_dfi_phyupd_ack),
        .i_dfi_phyupd_type      (2'b00)
    );

    // =========================================================================
    // Flat DFI  ->  per-phase DFI (into a7ddrphy)
    // =========================================================================
    logic [13:0] w_dfi_p0_address, w_dfi_p1_address;
    logic [2:0]  w_dfi_p0_bank,    w_dfi_p1_bank;
    logic        w_dfi_p0_ras_n,   w_dfi_p1_ras_n;
    logic        w_dfi_p0_cas_n,   w_dfi_p1_cas_n;
    logic        w_dfi_p0_we_n,    w_dfi_p1_we_n;
    logic        w_dfi_p0_cs_n,    w_dfi_p1_cs_n;
    logic        w_dfi_p0_cke,     w_dfi_p1_cke;
    logic        w_dfi_p0_odt,     w_dfi_p1_odt;
    logic        w_dfi_p0_reset_n, w_dfi_p1_reset_n;
    logic        w_dfi_p0_wrdata_en, w_dfi_p1_wrdata_en;
    logic [63:0] w_dfi_p0_wrdata,    w_dfi_p1_wrdata;
    logic [7:0]  w_dfi_p0_wrdata_mask, w_dfi_p1_wrdata_mask;
    logic        w_dfi_p0_rddata_en, w_dfi_p1_rddata_en;
    logic [63:0] w_dfi_p0_rddata,    w_dfi_p1_rddata;
    logic        w_dfi_p0_rddata_valid, w_dfi_p1_rddata_valid;

    dfi_v21_flat_to_a7ddrphy #(
        .DFI_ADDR_W (14),
        .DFI_BANK_W (3),
        .PHASE_DATA (64),
        .PHASE_STRB (8)
    ) u_dfi_adapter (
        .dfi_address_flat        (w_dfi_address),
        .dfi_bank_flat           (w_dfi_bank),
        .dfi_cas_n_flat          (w_dfi_cas_n),
        .dfi_ras_n_flat          (w_dfi_ras_n),
        .dfi_we_n_flat           (w_dfi_we_n),
        .dfi_cs_n_flat           (w_dfi_cs_n),
        .dfi_cke_flat            (w_dfi_cke),
        .dfi_odt_flat            (w_dfi_odt),
        .dfi_wrdata_flat         (w_dfi_wrdata),
        .dfi_wrdata_mask_flat    (w_dfi_wrdata_mask),
        .dfi_wrdata_en_flat      (w_dfi_wrdata_en),
        .dfi_rddata_en_flat      (w_dfi_rddata_en),
        .dfi_rddata_flat         (w_dfi_rddata),
        .dfi_rddata_valid_flat   (w_dfi_rddata_valid),
        .dfi_init_complete_flat  (w_dfi_init_complete),
        .dfi_init_start_flat     (),   // stubbed; a7ddrphy runs cal FSM itself

        .dfi_p0_address     (w_dfi_p0_address),
        .dfi_p0_bank        (w_dfi_p0_bank),
        .dfi_p0_ras_n       (w_dfi_p0_ras_n),
        .dfi_p0_cas_n       (w_dfi_p0_cas_n),
        .dfi_p0_we_n        (w_dfi_p0_we_n),
        .dfi_p0_cs_n        (w_dfi_p0_cs_n),
        .dfi_p0_cke         (w_dfi_p0_cke),
        .dfi_p0_odt         (w_dfi_p0_odt),
        .dfi_p0_reset_n     (w_dfi_p0_reset_n),
        .dfi_p0_wrdata_en   (w_dfi_p0_wrdata_en),
        .dfi_p0_wrdata      (w_dfi_p0_wrdata),
        .dfi_p0_wrdata_mask (w_dfi_p0_wrdata_mask),
        .dfi_p0_rddata_en   (w_dfi_p0_rddata_en),
        .dfi_p0_rddata      (w_dfi_p0_rddata),
        .dfi_p0_rddata_valid(w_dfi_p0_rddata_valid),

        .dfi_p1_address     (w_dfi_p1_address),
        .dfi_p1_bank        (w_dfi_p1_bank),
        .dfi_p1_ras_n       (w_dfi_p1_ras_n),
        .dfi_p1_cas_n       (w_dfi_p1_cas_n),
        .dfi_p1_we_n        (w_dfi_p1_we_n),
        .dfi_p1_cs_n        (w_dfi_p1_cs_n),
        .dfi_p1_cke         (w_dfi_p1_cke),
        .dfi_p1_odt         (w_dfi_p1_odt),
        .dfi_p1_reset_n     (w_dfi_p1_reset_n),
        .dfi_p1_wrdata_en   (w_dfi_p1_wrdata_en),
        .dfi_p1_wrdata      (w_dfi_p1_wrdata),
        .dfi_p1_wrdata_mask (w_dfi_p1_wrdata_mask),
        .dfi_p1_rddata_en   (w_dfi_p1_rddata_en),
        .dfi_p1_rddata      (w_dfi_p1_rddata),
        .dfi_p1_rddata_valid(w_dfi_p1_rddata_valid)
    );

    // =========================================================================
    // Clocking for a7ddrphy — Vivado build overrides these with a real
    // MMCM. For lint/sim we tie them off; the black-box body ignores
    // them so nothing else cares.
    // =========================================================================
    logic sys4x_clk;
    logic sys4x_180_clk;
    logic iodelay_ref_clk;
    assign sys4x_clk       = aclk;
    assign sys4x_180_clk   = aclk;
    assign iodelay_ref_clk = aclk;

    // Convert async-low aresetn to sync-high sys_rst for the PHY.
    logic sys_rst;
    assign sys_rst = ~aresetn;

    // =========================================================================
    // a7ddrphy — LiteDRAM PHY (blackbox in the framework; Vivado swaps
    // in the real LiteDRAM-generated .v at build time).
    // =========================================================================
    a7ddrphy #(
        .NPHASES     (DFI_RATE),
        .DFI_ADDR_W  (14),
        .DFI_BANK_W  (3),
        .DFI_DATA_W  (128),
        .DFI_STRB_W  (16),
        .DDR2_DQ_W   (16),
        .DDR2_DM_W   (2),
        .DDR2_DQS_W  (2)
    ) u_a7ddrphy (
        .sys_clk          (aclk),
        .sys_rst          (sys_rst),
        .sys4x_clk        (sys4x_clk),
        .sys4x_180_clk    (sys4x_180_clk),
        .iodelay_ref_clk  (iodelay_ref_clk),

        .dfi_p0_address      (w_dfi_p0_address),
        .dfi_p0_bank         (w_dfi_p0_bank),
        .dfi_p0_ras_n        (w_dfi_p0_ras_n),
        .dfi_p0_cas_n        (w_dfi_p0_cas_n),
        .dfi_p0_we_n         (w_dfi_p0_we_n),
        .dfi_p0_cs_n         (w_dfi_p0_cs_n),
        .dfi_p0_cke          (w_dfi_p0_cke),
        .dfi_p0_odt          (w_dfi_p0_odt),
        .dfi_p0_reset_n      (w_dfi_p0_reset_n),
        .dfi_p0_wrdata_en    (w_dfi_p0_wrdata_en),
        .dfi_p0_wrdata       (w_dfi_p0_wrdata),
        .dfi_p0_wrdata_mask  (w_dfi_p0_wrdata_mask),
        .dfi_p0_rddata_en    (w_dfi_p0_rddata_en),
        .dfi_p0_rddata       (w_dfi_p0_rddata),
        .dfi_p0_rddata_valid (w_dfi_p0_rddata_valid),

        .dfi_p1_address      (w_dfi_p1_address),
        .dfi_p1_bank         (w_dfi_p1_bank),
        .dfi_p1_ras_n        (w_dfi_p1_ras_n),
        .dfi_p1_cas_n        (w_dfi_p1_cas_n),
        .dfi_p1_we_n         (w_dfi_p1_we_n),
        .dfi_p1_cs_n         (w_dfi_p1_cs_n),
        .dfi_p1_cke          (w_dfi_p1_cke),
        .dfi_p1_odt          (w_dfi_p1_odt),
        .dfi_p1_reset_n      (w_dfi_p1_reset_n),
        .dfi_p1_wrdata_en    (w_dfi_p1_wrdata_en),
        .dfi_p1_wrdata       (w_dfi_p1_wrdata),
        .dfi_p1_wrdata_mask  (w_dfi_p1_wrdata_mask),
        .dfi_p1_rddata_en    (w_dfi_p1_rddata_en),
        .dfi_p1_rddata       (w_dfi_p1_rddata),
        .dfi_p1_rddata_valid (w_dfi_p1_rddata_valid),

        .ddram_a       (ddram_a),
        .ddram_ba      (ddram_ba),
        .ddram_ras_n   (ddram_ras_n),
        .ddram_cas_n   (ddram_cas_n),
        .ddram_we_n    (ddram_we_n),
        .ddram_cs_n    (ddram_cs_n),
        .ddram_cke     (ddram_cke),
        .ddram_odt     (ddram_odt),
        .ddram_dm      (ddram_dm),
        .ddram_dq      (ddram_dq),
        .ddram_dqs_p   (ddram_dqs_p),
        .ddram_dqs_n   (ddram_dqs_n),
        .ddram_clk_p   (ddram_clk_p),
        .ddram_clk_n   (ddram_clk_n)
    );

    // Init handshake into the harness. LiteDRAM's a7ddrphy exposes a
    // dfi_init_complete pulse via its calibration FSM; the stub keeps
    // this low so the harness never leaves reset in lint / sim — swap
    // to a real signal once the LiteDRAM PHY is in place.
    assign w_dfi_init_complete = 1'b0;

    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0,
        w_dfi_dram_clk_disable, w_dfi_init_start,
        w_dfi_ctrlupd_req, w_dfi_phyupd_ack,
        1'b0};
    /* verilator lint_on UNUSED */

endmodule : ddr2_char_top
