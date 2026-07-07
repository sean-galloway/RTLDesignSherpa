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

module ddr2_char_top #(
    // DDR2 chip row-address width. Nexys A7 DDR2 (MT47H64M16, 1Gb x16) = 13
    // (A0-A12). Sizes ddram_a and the DFI/PHY address width; propagates into
    // the controller via the harness so it never issues an out-of-range row.
    parameter int ROW_WIDTH = 13
) (
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
    output logic [ROW_WIDTH-1:0] ddram_a,
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

    // =========================================================================
    // Clock generation for the a7ddrphy (1:2 / nphases=2) at 300 MT/s — the
    // config LiteDRAM proved on this Nexys A7. The nphases=2 PHY serializes at
    // sys2x (DATA_WIDTH=4) and needs sys (75), sys2x (150) and sys2x_dqs
    // (150, 90-deg); CK = sys2x = 150 MHz -> 300 MT/s, CL-3/CWL-2. IDELAYCTRL
    // needs a dedicated 200 MHz ref. Controller + harness run on sys (75).
    //   * DDR2_CHAR_SYNTH: real MMCME2_BASE + BUFGs + IDELAYCTRL (Vivado).
    //   * else (verilator/cocotb): all clocks alias CLK100MHZ, locked=1 —
    //     the a7ddrphy stub ignores the fast clocks anyway.
    // =========================================================================
    wire w_sys, w_sys2x, w_sys2x_dqs, w_idelay;
    wire w_clk_locked;
    // IDELAYCTRL calibration-ready. If this never asserts, every IDELAY tap is
    // uncalibrated -> read DQ is garbage at all taps. Gated into aresetn below
    // (LiteDRAM holds the design in reset until idelayctrl.ready).
    (* mark_debug = "true" *) wire w_idelay_rdy;

`ifdef DDR2_CHAR_SYNTH
    wire w_sys_i, w_sys2x_i, w_sys2x_dqs_i, w_idelay_i, w_clkfb_i, w_clkfb;
    MMCME2_BASE #(
        .CLKIN1_PERIOD   (10.0),   // 100 MHz board clock
        .DIVCLK_DIVIDE   (1),
        .CLKFBOUT_MULT_F (6.0),    // VCO = 600 MHz
        .CLKOUT0_DIVIDE_F(8.0),    // sys        = 75  MHz
        .CLKOUT1_DIVIDE  (4),      // sys2x      = 150 MHz  (= DRAM CK, 300 MT/s)
        .CLKOUT2_DIVIDE  (4),      // sys2x_dqs  = 150 MHz
        .CLKOUT2_PHASE   (90.0),   // DQS 90-deg
        .CLKOUT3_DIVIDE  (3)       // idelay ref = 200 MHz
    ) u_mmcm (
        .CLKIN1   (CLK100MHZ),
        .CLKFBIN  (w_clkfb),
        .CLKFBOUT (w_clkfb_i),
        .CLKFBOUTB(),
        .CLKOUT0  (w_sys_i),      .CLKOUT0B(),
        .CLKOUT1  (w_sys2x_i),    .CLKOUT1B(),
        .CLKOUT2  (w_sys2x_dqs_i),.CLKOUT2B(),
        .CLKOUT3  (w_idelay_i),   .CLKOUT3B(),
        .CLKOUT4  (), .CLKOUT5(), .CLKOUT6(),
        .LOCKED   (w_clk_locked),
        .PWRDWN   (1'b0),
        .RST      (~CPU_RESETN)
    );
    BUFG u_bufg_fb  (.I(w_clkfb_i),      .O(w_clkfb));
    BUFG u_bufg_sys (.I(w_sys_i),        .O(w_sys));
    BUFG u_bufg_2x  (.I(w_sys2x_i),      .O(w_sys2x));
    BUFG u_bufg_2xd (.I(w_sys2x_dqs_i),  .O(w_sys2x_dqs));
    BUFG u_bufg_idly(.I(w_idelay_i),     .O(w_idelay));
    // IODELAY reference (200 MHz, dedicated). One control per I/O bank DQ/DQS use.
    IDELAYCTRL u_idelayctrl (.REFCLK(w_idelay), .RST(~w_clk_locked), .RDY(w_idelay_rdy));
`else
    assign w_sys       = CLK100MHZ;
    assign w_sys2x     = CLK100MHZ;
    assign w_sys2x_dqs = CLK100MHZ;
    assign w_idelay    = CLK100MHZ;
    assign w_idelay_rdy = 1'b1;
    assign w_clk_locked = 1'b1;
`endif

    // Controller + harness run on sys. Hold reset until the MMCM locks AND the
    // IDELAYCTRL has calibrated (idelay_rdy) — LiteDRAM holds its design in
    // reset until idelayctrl.ready so the read IDELAYs are never used
    // uncalibrated. Diagnostic corollary: if RDY never asserts, UART stays dead
    // (the board still programs, DONE high) — a clean on-board signal.
    wire aclk    = w_sys;
    wire aresetn = r_rst_sync & w_clk_locked & w_idelay_rdy;

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
    //
    // a7ddrphy config (Artix-7 x16 DDR2): 1:2 / nphases=2 — matches LiteDRAM's
    // board-proven config. The PHY exposes 4 DFI phase ports but only serializes
    // phases 0,1 (DATA_WIDTH=4, 4 beats/sys-cycle), so the controller drives
    // DFI_RATE=2; the adapter NOPs PHY phases 2,3. DRAM beat = 2*DQ = 32b,
    // DFI_DATA_WIDTH = 32*2 = 64, GEAR = AXI/beat = 2.
    // =========================================================================
    localparam int AXI_DATA_WIDTH  = 64;
    localparam int DRAM_BEAT_WIDTH = 32;
    localparam int DFI_RATE        = 2;
    localparam int DFI_DATA_WIDTH  = DFI_RATE * DRAM_BEAT_WIDTH;   // 64
    localparam int DFI_STRB_WIDTH  = DFI_DATA_WIDTH / 8;           // 16
    localparam int DFI_ADDR_BUS_W  = ROW_WIDTH * DFI_RATE;         // 52
    localparam int DFI_BANK_BUS_W  = 3 * DFI_RATE;                 // 12

    // (* mark_debug *) on the DFI-at-PHY-boundary nets: an ILA on aclk (sys)
    // captures exactly what pumice drives into the a7ddrphy (command + wrdata)
    // and what the PHY returns (rddata/valid) — the analog OSERDES/ISERDES layer
    // is not fabric-visible, but this boundary is the diagnostic surface.
    (* mark_debug = "true" *) logic [DFI_ADDR_BUS_W-1:0]     w_dfi_address;
    (* mark_debug = "true" *) logic [DFI_BANK_BUS_W-1:0]     w_dfi_bank;
    (* mark_debug = "true" *) logic [DFI_RATE-1:0]           w_dfi_cas_n, w_dfi_ras_n, w_dfi_we_n;
    (* mark_debug = "true" *) logic [DFI_RATE-1:0]           w_dfi_cs_n;
    logic [DFI_RATE-1:0]           w_dfi_cke, w_dfi_odt;
    (* mark_debug = "true" *) logic [DFI_DATA_WIDTH-1:0]     w_dfi_wrdata;
    logic [DFI_STRB_WIDTH-1:0]     w_dfi_wrdata_mask;
    (* mark_debug = "true" *) logic [DFI_RATE-1:0]           w_dfi_wrdata_en;
    (* mark_debug = "true" *) logic [DFI_RATE-1:0]           w_dfi_rddata_en;
    (* mark_debug = "true" *) logic [DFI_DATA_WIDTH-1:0]     w_dfi_rddata;
    (* mark_debug = "true" *) logic [DFI_RATE-1:0]           w_dfi_rddata_valid;
    logic [DFI_RATE-1:0]           w_dfi_dram_clk_disable;
    logic                          w_dfi_init_start;
    logic                          w_dfi_init_complete;
    logic                          w_dfi_ctrlupd_req;
    logic                          w_dfi_phyupd_ack;

    // Calibration CSR bus — harness_csr (0x080-0x08C) drives these; firmware
    // runs a7ddrphy read/write leveling over UART. Wired harness -> PHY below.
    logic [9:0]  w_phy_csr_adr;
    logic        w_phy_csr_we;
    logic [31:0] w_phy_csr_dat_w;
    logic [31:0] w_phy_csr_dat_r;

    // =========================================================================
    // Harness
    // =========================================================================
    ddr2_char_harness #(
        .AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
        .DRAM_BEAT_WIDTH (DRAM_BEAT_WIDTH),
        .DFI_RATE        (DFI_RATE),
        .ROW_WIDTH       (ROW_WIDTH),
        .FPGA_CLK_HZ     (75_000_000)   // sys is now 75 MHz -> UART baud divisor
        // DFI command->data alignment is now a runtime CSR (DFI_TUNING.cmd_delay,
        // default 5) — tune live over UART, no rebuild. CMD_MAX_DELAY defaults 8.
    ) u_harness (
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
        .i_dfi_phyupd_type      (2'b00),

        // a7ddrphy calibration CSR bus (firmware leveling over UART)
        .o_phy_csr_adr          (w_phy_csr_adr),
        .o_phy_csr_we           (w_phy_csr_we),
        .o_phy_csr_dat_w        (w_phy_csr_dat_w),
        .i_phy_csr_dat_r        (w_phy_csr_dat_r)
    );

    // =========================================================================
    // Flat DFI  ->  per-phase DFI (into a7ddrphy). 4 phases (p0..p3).
    // =========================================================================
    logic [ROW_WIDTH-1:0] w_p0_addr, w_p1_addr, w_p2_addr, w_p3_addr;
    logic [2:0]  w_p0_bank, w_p1_bank, w_p2_bank, w_p3_bank;
    logic        w_p0_ras_n, w_p1_ras_n, w_p2_ras_n, w_p3_ras_n;
    logic        w_p0_cas_n, w_p1_cas_n, w_p2_cas_n, w_p3_cas_n;
    logic        w_p0_we_n,  w_p1_we_n,  w_p2_we_n,  w_p3_we_n;
    logic        w_p0_cs_n,  w_p1_cs_n,  w_p2_cs_n,  w_p3_cs_n;
    logic        w_p0_cke,   w_p1_cke,   w_p2_cke,   w_p3_cke;
    logic        w_p0_odt,   w_p1_odt,   w_p2_odt,   w_p3_odt;
    logic        w_p0_rst_n, w_p1_rst_n, w_p2_rst_n, w_p3_rst_n;
    logic        w_p0_act_n, w_p1_act_n, w_p2_act_n, w_p3_act_n;
    logic        w_p0_wren,  w_p1_wren,  w_p2_wren,  w_p3_wren;
    logic [31:0] w_p0_wrd,   w_p1_wrd,   w_p2_wrd,   w_p3_wrd;
    logic [3:0]  w_p0_wrm,   w_p1_wrm,   w_p2_wrm,   w_p3_wrm;
    logic        w_p0_rden,  w_p1_rden,  w_p2_rden,  w_p3_rden;
    logic [31:0] w_p0_rdd,   w_p1_rdd,   w_p2_rdd,   w_p3_rdd;
    logic        w_p0_rdv,   w_p1_rdv,   w_p2_rdv,   w_p3_rdv;

    dfi_v21_flat_to_a7ddrphy #(
        .DFI_ADDR_W (ROW_WIDTH),
        .DFI_BANK_W (3),
        .PHASE_DATA (DRAM_BEAT_WIDTH),
        .CTRL_PHASES (DFI_RATE)
    ) u_dfi_adapter (
        .dfi_address_flat      (w_dfi_address),
        .dfi_bank_flat         (w_dfi_bank),
        .dfi_cas_n_flat        (w_dfi_cas_n),
        .dfi_ras_n_flat        (w_dfi_ras_n),
        .dfi_we_n_flat         (w_dfi_we_n),
        .dfi_cs_n_flat         (w_dfi_cs_n),
        .dfi_cke_flat          (w_dfi_cke),
        .dfi_odt_flat          (w_dfi_odt),
        .dfi_wrdata_flat       (w_dfi_wrdata),
        .dfi_wrdata_mask_flat  (w_dfi_wrdata_mask),
        .dfi_wrdata_en_flat    (w_dfi_wrdata_en),
        .dfi_rddata_en_flat    (w_dfi_rddata_en),
        .dfi_rddata_flat       (w_dfi_rddata),
        .dfi_rddata_valid_flat (w_dfi_rddata_valid),

        .dfi_p0_address(w_p0_addr), .dfi_p1_address(w_p1_addr),
        .dfi_p2_address(w_p2_addr), .dfi_p3_address(w_p3_addr),
        .dfi_p0_bank(w_p0_bank), .dfi_p1_bank(w_p1_bank),
        .dfi_p2_bank(w_p2_bank), .dfi_p3_bank(w_p3_bank),
        .dfi_p0_ras_n(w_p0_ras_n), .dfi_p1_ras_n(w_p1_ras_n),
        .dfi_p2_ras_n(w_p2_ras_n), .dfi_p3_ras_n(w_p3_ras_n),
        .dfi_p0_cas_n(w_p0_cas_n), .dfi_p1_cas_n(w_p1_cas_n),
        .dfi_p2_cas_n(w_p2_cas_n), .dfi_p3_cas_n(w_p3_cas_n),
        .dfi_p0_we_n(w_p0_we_n), .dfi_p1_we_n(w_p1_we_n),
        .dfi_p2_we_n(w_p2_we_n), .dfi_p3_we_n(w_p3_we_n),
        .dfi_p0_cs_n(w_p0_cs_n), .dfi_p1_cs_n(w_p1_cs_n),
        .dfi_p2_cs_n(w_p2_cs_n), .dfi_p3_cs_n(w_p3_cs_n),
        .dfi_p0_cke(w_p0_cke), .dfi_p1_cke(w_p1_cke),
        .dfi_p2_cke(w_p2_cke), .dfi_p3_cke(w_p3_cke),
        .dfi_p0_odt(w_p0_odt), .dfi_p1_odt(w_p1_odt),
        .dfi_p2_odt(w_p2_odt), .dfi_p3_odt(w_p3_odt),
        .dfi_p0_reset_n(w_p0_rst_n), .dfi_p1_reset_n(w_p1_rst_n),
        .dfi_p2_reset_n(w_p2_rst_n), .dfi_p3_reset_n(w_p3_rst_n),
        .dfi_p0_act_n(w_p0_act_n), .dfi_p1_act_n(w_p1_act_n),
        .dfi_p2_act_n(w_p2_act_n), .dfi_p3_act_n(w_p3_act_n),
        .dfi_p0_wrdata_en(w_p0_wren), .dfi_p1_wrdata_en(w_p1_wren),
        .dfi_p2_wrdata_en(w_p2_wren), .dfi_p3_wrdata_en(w_p3_wren),
        .dfi_p0_wrdata(w_p0_wrd), .dfi_p1_wrdata(w_p1_wrd),
        .dfi_p2_wrdata(w_p2_wrd), .dfi_p3_wrdata(w_p3_wrd),
        .dfi_p0_wrdata_mask(w_p0_wrm), .dfi_p1_wrdata_mask(w_p1_wrm),
        .dfi_p2_wrdata_mask(w_p2_wrm), .dfi_p3_wrdata_mask(w_p3_wrm),
        .dfi_p0_rddata_en(w_p0_rden), .dfi_p1_rddata_en(w_p1_rden),
        .dfi_p2_rddata_en(w_p2_rden), .dfi_p3_rddata_en(w_p3_rden),
        .dfi_p0_rddata(w_p0_rdd), .dfi_p1_rddata(w_p1_rdd),
        .dfi_p2_rddata(w_p2_rdd), .dfi_p3_rddata(w_p3_rdd),
        .dfi_p0_rddata_valid(w_p0_rdv), .dfi_p1_rddata_valid(w_p1_rdv),
        .dfi_p2_rddata_valid(w_p2_rdv), .dfi_p3_rddata_valid(w_p3_rdv)
    );

    // PHY clocks come from the MMCM block above (sim: all = CLK100MHZ).
    // Per-domain sync-high resets share the single aresetn (already gated
    // on MMCM lock).
    wire sys2x_clk       = w_sys2x;
    wire sys2x_dqs_clk   = w_sys2x_dqs;
    wire sys_rst_p       = ~aresetn;
    wire sys2x_rst_p     = ~aresetn;
    wire sys2x_dqs_rst_p = ~aresetn;

    // =========================================================================
    // a7ddrphy — LiteDRAM PHY. Black box for lint/sim (a7ddrphy_stub.sv);
    // Vivado swaps in rtl-vivado/a7ddrphy/a7ddrphy_generated.v. Paramless:
    // the generated body is fully elaborated (13b addr, 32b/phase, 4:1).
    // =========================================================================
    a7ddrphy u_a7ddrphy (
        .sys_clk         (aclk),
        .sys_rst         (sys_rst_p),
        .sys2x_clk       (sys2x_clk),
        .sys2x_rst       (sys2x_rst_p),
        .sys2x_clk_1     (sys2x_clk),
        .sys2x_rst_1     (sys2x_rst_p),
        .sys2x_dqs_clk   (sys2x_dqs_clk),
        .sys2x_dqs_rst   (sys2x_dqs_rst_p),

        .dfi_p0_address(w_p0_addr), .dfi_p0_bank(w_p0_bank),
        .dfi_p0_cas_n(w_p0_cas_n), .dfi_p0_cs_n(w_p0_cs_n),
        .dfi_p0_ras_n(w_p0_ras_n), .dfi_p0_we_n(w_p0_we_n),
        .dfi_p0_cke(w_p0_cke), .dfi_p0_odt(w_p0_odt),
        .dfi_p0_reset_n(w_p0_rst_n), .dfi_p0_act_n(w_p0_act_n),
        .dfi_p0_wrdata(w_p0_wrd), .dfi_p0_wrdata_en(w_p0_wren),
        .dfi_p0_wrdata_mask(w_p0_wrm), .dfi_p0_rddata_en(w_p0_rden),
        .dfi_p0_rddata(w_p0_rdd), .dfi_p0_rddata_valid(w_p0_rdv),

        .dfi_p1_address(w_p1_addr), .dfi_p1_bank(w_p1_bank),
        .dfi_p1_cas_n(w_p1_cas_n), .dfi_p1_cs_n(w_p1_cs_n),
        .dfi_p1_ras_n(w_p1_ras_n), .dfi_p1_we_n(w_p1_we_n),
        .dfi_p1_cke(w_p1_cke), .dfi_p1_odt(w_p1_odt),
        .dfi_p1_reset_n(w_p1_rst_n), .dfi_p1_act_n(w_p1_act_n),
        .dfi_p1_wrdata(w_p1_wrd), .dfi_p1_wrdata_en(w_p1_wren),
        .dfi_p1_wrdata_mask(w_p1_wrm), .dfi_p1_rddata_en(w_p1_rden),
        .dfi_p1_rddata(w_p1_rdd), .dfi_p1_rddata_valid(w_p1_rdv),

        .dfi_p2_address(w_p2_addr), .dfi_p2_bank(w_p2_bank),
        .dfi_p2_cas_n(w_p2_cas_n), .dfi_p2_cs_n(w_p2_cs_n),
        .dfi_p2_ras_n(w_p2_ras_n), .dfi_p2_we_n(w_p2_we_n),
        .dfi_p2_cke(w_p2_cke), .dfi_p2_odt(w_p2_odt),
        .dfi_p2_reset_n(w_p2_rst_n), .dfi_p2_act_n(w_p2_act_n),
        .dfi_p2_wrdata(w_p2_wrd), .dfi_p2_wrdata_en(w_p2_wren),
        .dfi_p2_wrdata_mask(w_p2_wrm), .dfi_p2_rddata_en(w_p2_rden),
        .dfi_p2_rddata(w_p2_rdd), .dfi_p2_rddata_valid(w_p2_rdv),

        .dfi_p3_address(w_p3_addr), .dfi_p3_bank(w_p3_bank),
        .dfi_p3_cas_n(w_p3_cas_n), .dfi_p3_cs_n(w_p3_cs_n),
        .dfi_p3_ras_n(w_p3_ras_n), .dfi_p3_we_n(w_p3_we_n),
        .dfi_p3_cke(w_p3_cke), .dfi_p3_odt(w_p3_odt),
        .dfi_p3_reset_n(w_p3_rst_n), .dfi_p3_act_n(w_p3_act_n),
        .dfi_p3_wrdata(w_p3_wrd), .dfi_p3_wrdata_en(w_p3_wren),
        .dfi_p3_wrdata_mask(w_p3_wrm), .dfi_p3_rddata_en(w_p3_rden),
        .dfi_p3_rddata(w_p3_rdd), .dfi_p3_rddata_valid(w_p3_rdv),

        .ddram_a(ddram_a), .ddram_ba(ddram_ba),
        .ddram_ras_n(ddram_ras_n), .ddram_cas_n(ddram_cas_n),
        .ddram_we_n(ddram_we_n), .ddram_dm(ddram_dm),
        .ddram_dq(ddram_dq), .ddram_dqs_p(ddram_dqs_p),
        .ddram_dqs_n(ddram_dqs_n), .ddram_clk_p(ddram_clk_p),
        .ddram_clk_n(ddram_clk_n), .ddram_cke(ddram_cke),
        .ddram_odt(ddram_odt), .ddram_cs_n(ddram_cs_n),

        .adr(w_phy_csr_adr), .we(w_phy_csr_we),
        .dat_w(w_phy_csr_dat_w), .dat_r(w_phy_csr_dat_r)
    );

    // DFI init-complete into the controller. The generated a7ddrphy has NO
    // hardware init-done output (LiteDRAM inits/levels the PHY in software),
    // so in our firmware-leveling model the PHY is "ready" to pass DFI
    // commands as soon as it's out of config: assert init-complete high so the
    // controller's init_sequencer leaves S_DFI_INIT and runs the DDR2 JEDEC
    // init (MRS/etc.) over the DFI. Firmware then levels DQ/DQS read capture
    // via the calib CSR window. (Was tied 1'b0 -- a stub leftover -- which held
    // init_sequencer in S_DFI_INIT so the DRAM was never initialised: writes
    // backpressured, reads errored.) aresetn already gates on MMCM lock, so
    // this only takes effect once the sys/sys4x clocks are stable.
    assign w_dfi_init_complete = 1'b1;

    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0,
        w_dfi_dram_clk_disable, w_dfi_init_start,
        w_dfi_ctrlupd_req, w_dfi_phyupd_ack,
        1'b0};
    /* verilator lint_on UNUSED */

endmodule : ddr2_char_top
