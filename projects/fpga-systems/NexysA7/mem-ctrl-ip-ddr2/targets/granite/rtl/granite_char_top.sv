// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: granite_char_top
// Purpose: FPGA pin-level top for the Granite DDR2/LPDDR2 characterization
//          harness. Sibling of build-perf/rtl/ddr2_char_top.sv; swaps the
//          controller instance to the Granite macro.
//
// Target board: Digilent Nexys A7-100T (xc7a100tcsg324-1)
//
// Pin mapping (from granite_char_top.xdc; keep port names in lockstep):
//   CLK100MHZ       100 MHz system clock (E3)
//   CPU_RESETN      center pushbutton (C12, active-low)
//   UART_TXD_IN     FTDI -> FPGA RX     (C4)
//   UART_RXD_OUT    FPGA -> FTDI TX     (D4)
//   LED[15:0]       harness status
//   AN[7:0], CA..CG, DP  4-digit 7-segment
//
//   DDR2 pads:  ddram_a[12:0], ddram_ba[2:0], ddram_ras_n, ddram_cas_n,
//   ddram_we_n, ddram_cs_n, ddram_cke, ddram_odt, ddram_dm[1:0],
//   ddram_dq[15:0], ddram_dqs_p[1:0], ddram_dqs_n[1:0], ddram_clk_p,
//   ddram_clk_n.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module granite_char_top #(
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

    // Reset synchronisation (async assert, sync deassert)
    (* ASYNC_REG = "TRUE" *) logic r_rst_meta;
    (* ASYNC_REG = "TRUE" *) logic r_rst_sync;
    `ALWAYS_FF_RST(CLK100MHZ, CPU_RESETN,
        if (`RST_ASSERTED(CPU_RESETN)) begin
            r_rst_meta <= 1'b0;
            r_rst_sync <= 1'b0;
        end else begin
            r_rst_meta <= 1'b1;
            r_rst_sync <= r_rst_meta;
        end
    )

    // Clock generation for the a7ddrphy (1:2 / nphases=2) at 300 MT/s.
    // Granite A7 plan: 75 MHz sys / 300 MT/s DDR2-300.
    // IDELAYCTRL needs a dedicated 200 MHz ref.
    //   * DDR2_CHAR_SYNTH: real MMCME2_BASE + BUFGs + IDELAYCTRL (Vivado).
    //   * else (verilator/cocotb): all clocks alias CLK100MHZ, locked=1.
    wire w_sys, w_sys2x, w_sys2x_dqs, w_idelay;
    wire w_clk_locked;
    (* mark_debug = "true" *) wire w_idelay_rdy;

`ifdef DDR2_CHAR_SYNTH
    wire w_sys_i, w_sys2x_i, w_sys2x_dqs_i, w_idelay_i, w_clkfb_i, w_clkfb;
`ifdef GRANITE_SYS_66
    // Optional 66.67 MHz known-good fallback (same as pumice default).
    localparam real MMCM_MULT = 8.0;   // VCO = 800 MHz
    localparam real MMCM_CO0  = 12.0;  // sys       = 66.67 MHz
    localparam int  MMCM_CO1  = 6;     // sys2x     = 133.3 MHz (DDR2-266)
    localparam int  MMCM_CO2  = 6;     // sys2x_dqs = 133.3 MHz
    localparam int  MMCM_CO3  = 4;     // idelay    = 200 MHz (/4)
`elsif GRANITE_SYS_100
    // 100 MHz sys / 150 MHz sys2x = DDR2-300 (granite timing-push build).
    localparam real MMCM_MULT = 6.0;   // VCO = 600 MHz
    localparam real MMCM_CO0  = 6.0;   // sys       = 100 MHz
    localparam int  MMCM_CO1  = 4;     // sys2x     = 150 MHz (DDR2-300)
    localparam int  MMCM_CO2  = 4;     // sys2x_dqs = 150 MHz
    localparam int  MMCM_CO3  = 3;     // idelay    = 200 MHz (/3)
`else
    // DEFAULT: 75 MHz sys / 150 MHz sys2x = DDR2-300 (Granite A7 plan).
    localparam real MMCM_MULT = 6.0;   // VCO = 600 MHz
    localparam real MMCM_CO0  = 8.0;   // sys       = 75 MHz
    localparam int  MMCM_CO1  = 4;     // sys2x     = 150 MHz (DDR2-300)
    localparam int  MMCM_CO2  = 4;     // sys2x_dqs = 150 MHz
    localparam int  MMCM_CO3  = 3;     // idelay    = 200 MHz (/3)
`endif
    MMCME2_BASE #(
        .CLKIN1_PERIOD   (10.0),
        .DIVCLK_DIVIDE   (1),
        .CLKFBOUT_MULT_F (MMCM_MULT),
        .CLKOUT0_DIVIDE_F(MMCM_CO0),
        .CLKOUT1_DIVIDE  (MMCM_CO1),
        .CLKOUT2_DIVIDE  (MMCM_CO2),
        .CLKOUT2_PHASE   (90.0),
        .CLKOUT3_DIVIDE  (MMCM_CO3)
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
    IDELAYCTRL u_idelayctrl (.REFCLK(w_idelay), .RST(~w_clk_locked), .RDY(w_idelay_rdy));
`else
    assign w_sys       = CLK100MHZ;
    assign w_sys2x     = CLK100MHZ;
    assign w_sys2x_dqs = CLK100MHZ;
    assign w_idelay    = CLK100MHZ;
    assign w_idelay_rdy = 1'b1;
    assign w_clk_locked = 1'b1;
`endif

    wire aclk    = w_sys;
    wire aresetn = r_rst_sync & w_clk_locked & w_idelay_rdy;

    // 7-segment glue
    logic [6:0] w_seg;
    assign CA = w_seg[0];
    assign CB = w_seg[1];
    assign CC = w_seg[2];
    assign CD = w_seg[3];
    assign CE = w_seg[4];
    assign CF = w_seg[5];
    assign CG = w_seg[6];

    // Flat DFI wires (harness <-> adapter <-> a7ddrphy)
    localparam int AXI_DATA_WIDTH  = 64;
    localparam int DRAM_BEAT_WIDTH = 32;
    localparam int DRAM_DEVICE_WIDTH = 16;
    localparam int DFI_RATE        = 2;
    localparam int DFI_DATA_WIDTH  = DFI_RATE * DRAM_BEAT_WIDTH;
    localparam int DFI_STRB_WIDTH  = DFI_DATA_WIDTH / 8;
    localparam int DRAM_BL         = 4;
    localparam int BURST_LEN_MULTIPLE = (DRAM_BL * DRAM_DEVICE_WIDTH) / AXI_DATA_WIDTH;
    localparam int DFI_ADDR_BUS_W  = ROW_WIDTH * DFI_RATE;
    localparam int DFI_BANK_BUS_W  = 3 * DFI_RATE;

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

    // a7ddrphy calibration CSR bus
    logic [9:0]  w_phy_csr_adr;
    logic        w_phy_csr_we;
    logic [31:0] w_phy_csr_dat_w;
    logic [31:0] w_phy_csr_dat_r;

    // Harness
    granite_char_harness #(
        .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
        .DRAM_BEAT_WIDTH    (DRAM_BEAT_WIDTH),
        .DRAM_DEVICE_WIDTH  (DRAM_DEVICE_WIDTH),
        .DFI_RATE           (DFI_RATE),
        .DRAM_BL            (DRAM_BL),
        .BURST_LEN_MULTIPLE (BURST_LEN_MULTIPLE),
        .HAS_LPDDR2         (1'b0),   // DDR2 board: LPDDR2 training plane compiled out (report 5.10)
`ifdef GRANITE_FIXED_TIMINGS
        .FIXED_TIMINGS      (1'b1),   // report 5.10 item 3: T_* constants, TIMINGS CSRs ignored
`endif
`ifdef GRANITE_NUM_ENTRIES
        .NUM_ENTRIES        (`GRANITE_NUM_ENTRIES),
`endif
`ifdef GRANITE_BANK_FIFO_DEPTH
        .BANK_FIFO_DEPTH    (`GRANITE_BANK_FIFO_DEPTH),
`endif
`ifdef GRANITE_RD_RET_DEPTH
        .RD_RET_DEPTH       (`GRANITE_RD_RET_DEPTH),
`else
        .RD_RET_DEPTH       (64),
`endif
`ifdef GRANITE_RD_DBG_FIFO
        .RD_DBG_FIFO_DEPTH  (`GRANITE_RD_DBG_FIFO),
`else
        .RD_DBG_FIFO_DEPTH  (0),
`endif
        .ROW_WIDTH          (ROW_WIDTH),
`ifdef GRANITE_SYS_66
        .FPGA_CLK_HZ        (66_666_667)
`elsif GRANITE_SYS_100
        .FPGA_CLK_HZ        (100_000_000)
`else
        .FPGA_CLK_HZ        (75_000_000)
`endif
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

        .o_phy_csr_adr          (w_phy_csr_adr),
        .o_phy_csr_we           (w_phy_csr_we),
        .o_phy_csr_dat_w        (w_phy_csr_dat_w),
        .i_phy_csr_dat_r        (w_phy_csr_dat_r)
    );

    // Flat DFI -> per-phase DFI (into a7ddrphy). 4 phases (p0..p3).
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
        .DFI_ADDR_W  (ROW_WIDTH),
        .DFI_BANK_W  (3),
        .PHASE_DATA  (DRAM_BEAT_WIDTH),
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

    wire sys2x_clk       = w_sys2x;
    wire sys2x_dqs_clk   = w_sys2x_dqs;
    wire sys_rst_p       = ~aresetn;
    wire sys2x_rst_p     = ~aresetn;
    wire sys2x_dqs_rst_p = ~aresetn;

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

    assign w_dfi_init_complete = 1'b1;

    /* verilator lint_off UNUSED */
    wire _unused_ok = &{1'b0,
        w_dfi_dram_clk_disable, w_dfi_init_start,
        w_dfi_ctrlupd_req, w_dfi_phyupd_ack,
        1'b0};
    /* verilator lint_on UNUSED */

endmodule : granite_char_top
