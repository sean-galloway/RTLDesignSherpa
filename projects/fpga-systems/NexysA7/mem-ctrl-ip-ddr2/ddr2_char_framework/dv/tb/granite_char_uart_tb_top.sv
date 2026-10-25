// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Cocotb TB wrapper around the FULL granite_char_harness (UART bridge +
// harness_csr + 1->N AXIL bridge + the two characterization engines + the
// GRANITE controller). Clone of ddr2_char_uart_tb_top with the harness
// swapped: this is the sim half of the granite silicon/sim equivalence —
// the identical ASCII W/R byte stream the host sends to the FPGA on the
// Nexys A7, driving the REAL engines and the storage-less granite stack.
//
// Why this exists: the 2026-10-12 granite bring-up wedge (multi-beat bursts
// freeze with zero DFI commands, blen=1 passes) does NOT reproduce with a
// BFM AXI master at the exact board geometry — the last unmodeled variable
// is the real engines' AXI flavor. This TB is the environment that can fail
// the way the board fails.
//
// The DFI side is wired to internal phy_dfi_* nets so the framework
// DFISlavePHY BFM (+ MemoryModel) auto-binds by prefix, exactly as the
// pumice whole-harness sim does. There is no a7ddrphy here.

`timescale 1ns / 1ps

module granite_char_uart_tb_top
    import granite_pkg::*;
#(
    parameter int FPGA_CLK_HZ    = 100_000_000,
    // Sim runs the UART as close to the system clock as it will go; see the
    // pumice TB top for the measured CLKS_PER_BIT=4 floor.
    parameter int UART_BAUD      =  25_000_000,   // -> CLKS_PER_BIT = 4
    parameter int UART_CLKS_PER_BIT = FPGA_CLK_HZ / UART_BAUD,

    // ---- AXI / controller sizing (match granite_char_harness defaults) ----
    parameter int AXI_ADDR_WIDTH = 32,
    parameter int AXI_DATA_WIDTH = 64,
    parameter int AXI_ID_WIDTH   = 8,
    parameter int AXI_USER_WIDTH = 8,
    parameter int ROW_WIDTH      = 13,
    parameter int APB_ADDR_WIDTH = 12,
    parameter int APB_DATA_WIDTH = 32,
    parameter int NUM_BANKS      = 8,

    // ---- DFI sizing (board: rate-2, 32b beat, x16 device, BL4) ----
    parameter int DRAM_BEAT_WIDTH = 32,
    parameter int DRAM_DEVICE_WIDTH = 16,
    parameter int DFI_RATE        = 2,
    parameter int DRAM_BL         = 4,
    parameter int DFI_ADDR_BUS_W  = ROW_WIDTH * DFI_RATE,
    parameter int DFI_BANK_BUS_W  = 3 * DFI_RATE,
    parameter int DFI_CTRL_BUS_W  = DFI_RATE,
    parameter int DFI_CS_BUS_W    = DFI_RATE,
    parameter int DFI_DATA_WIDTH  = DFI_RATE * DRAM_BEAT_WIDTH,
    parameter int DFI_STRB_WIDTH  = DFI_DATA_WIDTH / 8,
    parameter int DFI_EN_WIDTH    = DFI_RATE,
    parameter int DFI_VALID_WIDTH = DFI_RATE,
    parameter int CMD_MAX_DELAY   = 8,
    // Generators per direction (the injectors); the perf proxy raises it with
    // TEST_NUM_GEN so eight per direction can run at once (owner, 2026-10-22).
    parameter int NUM_GEN         = 4,
    // granite_core storage / timing knobs (report 5.10); the proxy drives
    // them from TEST_NUM_ENTRIES / TEST_STORE_BACKEND / TEST_BANK_FIFO_DEPTH /
    // TEST_HEAD2_EN / TEST_DFI_CDC_EN / TEST_FIXED_TIMINGS. Defaults are the board build.
    parameter int NUM_ENTRIES     = 8,
    parameter int STORE_BACKEND   = 1,
    parameter int BANK_FIFO_DEPTH = 0,   // 0 = NUM_ENTRIES
    parameter bit HEAD2_EN        = 1'b1,// 0 = one head record per bank (FIFO store)
    parameter bit DFI_CDC_EN      = 1'b0,// the macro ties dfi_clk to mc_clk: no DFI crossing (board default)
    // AXI-plane lean knobs (pumice TASK-054), granite defaults = the measured lean form:
    parameter bit HAS_SNARF        = 1'b0, // 1 = snarf probe / staged admit / source arbiter in the read intake (pumice's CAM store); granite's FIFO store has no snarf
    parameter int INTAKE_FIFO_DEPTH = 0,   // rd-data and wr-data FIFOs in the intakes; 0 = none (the skids feed the ring / store directly; cycle-identical, measured)
    parameter int AXI_SKID_DEPTH   = 2,    // R and W skid depth in the AXI slave shells (2..8); 2 measured cycle-identical to 4
    parameter bit SHARED_ADDR_MAP  = 1'b0, // 1 = one address mapper for both intakes with an alternating grant: -23 percent on the mixed family, so OFF
    // Scheduler / DFI knobs (pumice TASK-055), granite defaults = the measured form:
    parameter bit HAS_PAGE_POLICY   = 1'b1, // 0 = no runtime page-policy engine (close-on-drain alone): measured -8 percent on 8-thread streams, so ON
    parameter int BANK_CAP_MIXED    = 6,    // FIFO store per-bank cap while the other direction holds entries (0 = off)
    parameter int BANK_TW           = 5,    // per-bank timer width (pumice TASK-056): 5 covers DDR2 at <= 100 MHz (tRC 6), measured cycle-identical; 8 = the CSR field width; a CSR value above the range saturates
    parameter int DFI_CMD_FIFO_DEPTH = 4,   // DFI plane command FIFO (8 before; 4 measured cycle-identical on every cell)
    parameter int DFI_WD_FIFO_DEPTH  = 16,  // DFI plane write-data FIFO (32 before; 16 measured cycle-identical)
    parameter int DFI_RD_FIFO_DEPTH  = 4,   // DFI plane read-return FIFO (0 = RD_RET_DEPTH x BURST_WORDS, the whole window, before); 4 holds the
                                            // return in the same-clock form where the ring is always ready; 2 loses beats where dfi_clk runs at 2x aclk
    parameter bit FIXED_TIMINGS   = 1'b0
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
    // DUT — the full granite harness (real UART bridge + harness_csr +
    // engines + the storage-less granite controller)
    //=========================================================================
    granite_char_harness #(
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
        .CMD_MAX_DELAY   (CMD_MAX_DELAY),
        .NUM_GEN         (NUM_GEN),
        .NUM_ENTRIES     (NUM_ENTRIES),
        .STORE_BACKEND   (STORE_BACKEND),
        .BANK_FIFO_DEPTH (BANK_FIFO_DEPTH),
        .HEAD2_EN        (HEAD2_EN),
        .DFI_CDC_EN      (DFI_CDC_EN),
        .HAS_SNARF        (HAS_SNARF),
        .INTAKE_FIFO_DEPTH(INTAKE_FIFO_DEPTH),
        .AXI_SKID_DEPTH   (AXI_SKID_DEPTH),
        .SHARED_ADDR_MAP  (SHARED_ADDR_MAP),
        .HAS_PAGE_POLICY   (HAS_PAGE_POLICY),
        .BANK_TW           (BANK_TW),
        .BANK_CAP_MIXED    (BANK_CAP_MIXED),
        .DFI_CMD_FIFO_DEPTH(DFI_CMD_FIFO_DEPTH),
        .DFI_WD_FIFO_DEPTH (DFI_WD_FIFO_DEPTH),
        .DFI_RD_FIFO_DEPTH (DFI_RD_FIFO_DEPTH),
        .FIXED_TIMINGS   (FIXED_TIMINGS)
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

        // a7ddrphy calibration CSR readback — tie off (BFM has no PHY regs).
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

endmodule : granite_char_uart_tb_top
