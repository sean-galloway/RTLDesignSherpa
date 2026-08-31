// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Cocotb TB wrapper around the FULL ddr2_char_harness (UART bridge + harness_csr
// + 1->N AXIL bridge + the two characterization engines + the pumice controller).
// Unlike ddr2_char_macro_tb_top (which drives engine cfg via direct ports + an
// APB BFM), this exposes the real UART pins so a cocotb UARTMaster/Monitor drives
// the IDENTICAL ASCII W/R byte stream that the host program sends to silicon —
// making sim and FPGA 100% equivalent at the wire.
//
// The DFI side is wired to internal phy_dfi_* nets so the framework DFISlavePHY
// BFM (+ MemoryModel) auto-binds by prefix, exactly as the passing macro sim
// does. There is no a7ddrphy here (its OSERDESE2/ISERDESE2/IDELAYE2 primitives
// do not simulate). This reproduces DIGITAL DFI-handshake behaviour, not the eye.
//
// Baud: CLKS_PER_BIT is lowered for sim (FPGA_CLK_HZ / UART_BAUD = 16) so a
// full command is thousands, not ~170k, sim clocks. This changes bit-timing
// only; the byte stream through the real uart_axil_bridge RTL is unchanged.

`timescale 1ns / 1ps

module ddr2_char_uart_tb_top
    import pumice_pkg::*;
#(
    // ---- UART baud divisor (lowered for sim) ----
    parameter int FPGA_CLK_HZ    = 100_000_000,
    parameter int UART_BAUD      =   6_250_000,   // -> CLKS_PER_BIT = 16
    parameter int UART_CLKS_PER_BIT = FPGA_CLK_HZ / UART_BAUD,

    // ---- AXI / controller sizing (match ddr2_char_harness defaults) ----
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 64,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 8,
    parameter int ROW_WIDTH      = 13,
    parameter int APB_ADDR_WIDTH = 12,
    parameter int APB_DATA_WIDTH = 32,
    parameter int NUM_BANKS      = 8,

    // ---- DFI sizing (rate-2 loopback, GEAR=1 — the known-good macro config) ----
    parameter int DRAM_BEAT_WIDTH = AXI_DATA_WIDTH,
    // Physical DRAM x-width. Default = DRAM_BEAT_WIDTH (ratio 1, legacy). Set to
    // 16 to model the board's x16 device so a JEDEC BL4 = 1 DFI cycle (exercises
    // pumice's burst-length scaling / the x16 over-read fix).
    parameter int DRAM_DEVICE_WIDTH = DRAM_BEAT_WIDTH,
    parameter int DFI_RATE        = 2,
    // JEDEC burst length. Overridden per-test alongside the BFM's
    // beats_per_burst so the DUT framing and the oracle come from ONE value --
    // inheriting the ddr2_char_macro default here let the two silently diverge.
    // Board default: BL8 (72a73fe2 moved DDR2 to BL8 end-to-end -- BL8 is
    // the only legal a7ddrphy burst at nphases=4). Tests pass this
    // explicitly; the default is here so it cannot silently disagree.
    parameter int DRAM_BL         = 8,
    parameter int DFI_ADDR_BUS_W  = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W  = 3 * DFI_RATE,
    parameter int DFI_CTRL_BUS_W  = DFI_RATE,
    parameter int DFI_CS_BUS_W    = DFI_RATE,
    parameter int DFI_DATA_WIDTH  = DFI_RATE * DRAM_BEAT_WIDTH,
    parameter int DFI_STRB_WIDTH  = DFI_DATA_WIDTH / 8,
    parameter int DFI_EN_WIDTH    = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int CMD_MAX_DELAY   = 8
) (
    input  logic aclk,
    input  logic aresetn,
    // UART pins the cocotb UARTMaster/Monitor attach to
    input  logic i_uart_rx,
    output logic o_uart_tx
);

    //=========================================================================
    // PHY-side DFI bus — internal phy_dfi_* nets for the DFISlavePHY BFM.
    //=========================================================================
    logic [DFI_ADDR_BUS_W-1:0]   phy_dfi_address;
    logic [DFI_BANK_BUS_W-1:0]   phy_dfi_bank;
    logic [DFI_CTRL_BUS_W-1:0]   phy_dfi_cas_n;
    logic [DFI_CTRL_BUS_W-1:0]   phy_dfi_ras_n;
    logic [DFI_CTRL_BUS_W-1:0]   phy_dfi_we_n;
    logic [DFI_CS_BUS_W-1:0]     phy_dfi_cs_n;
    logic [DFI_CS_BUS_W-1:0]     phy_dfi_cke;
    logic [DFI_CS_BUS_W-1:0]     phy_dfi_odt;
    logic [DFI_DATA_WIDTH-1:0]   phy_dfi_wrdata;
    logic [DFI_EN_WIDTH-1:0]     phy_dfi_wrdata_en;
    logic [DFI_STRB_WIDTH-1:0]   phy_dfi_wrdata_mask;
    logic [DFI_EN_WIDTH-1:0]     phy_dfi_rddata_en;
    logic [DFI_CS_BUS_W-1:0]     phy_dfi_dram_clk_disable;
    logic                        phy_dfi_init_start;
    logic                        phy_dfi_ctrlupd_req;
    logic                        phy_dfi_phyupd_ack;

    // BFM-driven inputs
    logic [DFI_DATA_WIDTH-1:0]   phy_dfi_rddata;
    logic [DFI_VALID_WIDTH-1:0]  phy_dfi_rddata_valid;
    logic                        phy_dfi_init_complete;
    logic                        phy_dfi_ctrlupd_ack;
    logic                        phy_dfi_phyupd_req;
    logic [1:0]                  phy_dfi_phyupd_type;

    // v3+ signals — declared so the BFM's cocotb-bus binding succeeds.
    logic                        phy_dfi_error;
    logic                        phy_dfi_error_info;
    logic                        phy_dfi_crc_alert;
    logic                        phy_dfi_training_active;
    logic                        phy_dfi_training_phase;
    logic                        phy_dfi_parity_check;
    logic                        phy_dfi_freq_change_ack;
    logic                        phy_dfi_freq_change_req;
    logic                        phy_dfi_disconnect_req;
    logic                        phy_dfi_phymstr_req;

    //=========================================================================
    // DUT — the full harness (real UART bridge + harness_csr + engines + ctrl)
    //=========================================================================
    ddr2_char_harness #(
        .FPGA_CLK_HZ     (FPGA_CLK_HZ),
        .UART_BAUD       (UART_BAUD),        // -> CLKS_PER_BIT = UART_CLKS_PER_BIT
        .AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
        .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .AXI_ID_WIDTH    (AXI_ID_WIDTH),
        .AXI_USER_WIDTH  (AXI_USER_WIDTH),
        .ROW_WIDTH       (ROW_WIDTH),
        .APB_ADDR_WIDTH  (APB_ADDR_WIDTH),
        .APB_DATA_WIDTH  (APB_DATA_WIDTH),
        .DRAM_BEAT_WIDTH (DRAM_BEAT_WIDTH),
        .DRAM_DEVICE_WIDTH (DRAM_DEVICE_WIDTH),
        .DFI_RATE        (DFI_RATE),
        .DRAM_BL         (DRAM_BL),
        .CMD_MAX_DELAY   (CMD_MAX_DELAY)
    ) u_dut (
        .aclk        (aclk),
        .aresetn     (aresetn),

        .i_uart_rx   (i_uart_rx),
        .o_uart_tx   (o_uart_tx),

        // board LEDs / 7-seg — unused in sim
        .o_led           (),
        .o_seven_seg_an  (),
        .o_seven_seg_seg (),
        .o_seven_seg_dp  (),

        // DFI slave bus -> phy_dfi_* nets (DFISlavePHY BFM binds by prefix)
        .o_dfi_address        (phy_dfi_address),
        .o_dfi_bank           (phy_dfi_bank),
        .o_dfi_cas_n          (phy_dfi_cas_n),
        .o_dfi_ras_n          (phy_dfi_ras_n),
        .o_dfi_we_n           (phy_dfi_we_n),
        .o_dfi_cs_n           (phy_dfi_cs_n),
        .o_dfi_cke            (phy_dfi_cke),
        .o_dfi_odt            (phy_dfi_odt),
        .o_dfi_wrdata         (phy_dfi_wrdata),
        .o_dfi_wrdata_mask    (phy_dfi_wrdata_mask),
        .o_dfi_wrdata_en      (phy_dfi_wrdata_en),
        .o_dfi_rddata_en      (phy_dfi_rddata_en),
        .i_dfi_rddata         (phy_dfi_rddata),
        .i_dfi_rddata_valid   (phy_dfi_rddata_valid),
        .o_dfi_dram_clk_disable (phy_dfi_dram_clk_disable),
        .o_dfi_init_start     (phy_dfi_init_start),
        .i_dfi_init_complete  (phy_dfi_init_complete),
        .o_dfi_ctrlupd_req    (phy_dfi_ctrlupd_req),
        .i_dfi_ctrlupd_ack    (phy_dfi_ctrlupd_ack),
        .i_dfi_phyupd_req     (phy_dfi_phyupd_req),
        .o_dfi_phyupd_ack     (phy_dfi_phyupd_ack),
        .i_dfi_phyupd_type    (phy_dfi_phyupd_type),

        // a7ddrphy calibration CSR readback — tie off (BFM has no PHY regs;
        // leveling programs decide on CRC, not the peek value).
        .o_phy_csr_adr        (),
        .o_phy_csr_we         (),
        .o_phy_csr_dat_w      (),
        .i_phy_csr_dat_r      (32'b0)
    );

    // Silence Verilator's unused-net warnings for BFM-only / open DFI lines.
    wire unused = |{ phy_dfi_error, phy_dfi_error_info, phy_dfi_crc_alert,
                     phy_dfi_training_active, phy_dfi_training_phase,
                     phy_dfi_parity_check, phy_dfi_freq_change_ack,
                     phy_dfi_freq_change_req, phy_dfi_disconnect_req,
                     phy_dfi_phymstr_req,
                     phy_dfi_init_start, phy_dfi_dram_clk_disable,
                     phy_dfi_ctrlupd_req, phy_dfi_phyupd_ack };

endmodule : ddr2_char_uart_tb_top
