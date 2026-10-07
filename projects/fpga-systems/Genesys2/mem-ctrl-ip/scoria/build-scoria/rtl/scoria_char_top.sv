// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: scoria_char_top
// Purpose: The Genesys 2 board top for the scoria DDR3 characterization build.
//          Clocking, the IDELAYCTRL, the DFI adapter, the LiteDRAM K7DDRPHY,
//          and the pads. Everything else is in scoria_char_harness.
//
// The A-side of the A/B. build-litedram is the B-side and the board proof: it
// passes memtest on this hardware at WNS +1.588, with identical pins and an
// identical DRAM. One thing differs between the two builds -- the controller --
// which is what makes a bandwidth comparison mean anything.
//
// ---------------------------------------------------------------------------
// CLOCKING. Input is the Genesys 2's 200 MHz DIFFERENTIAL system clock.
//
//   VCO      = 200 x 4 / 1 = 800 MHz        (K7 -2 range is 600..1200)
//   CLKOUT0  = /2.5  -> 320 MHz  sys4x      (fractional: CLKOUT0 only)
//   CLKOUT1  = /10   ->  80 MHz  sys        (the controller clock)
//   CLKOUT2  = /4    -> 200 MHz  idelay ref (IDELAYCTRL REFCLK must be 200)
//
// 80 MHz, not 100. scoria_top misses 100 MHz by 1.26 ns even at high
// implementation effort (scoria BUG-003), and 80 MHz keeps DDR3 in spec:
// 4 phases x 80 = 320 MHz CK, tCK 3.125 ns, inside the tCK(AVG) max of 3.3 ns
// (JESD79-3F). 75 MHz would be 3.333 ns and out of spec -- LiteDRAM will
// generate for it anyway, which is why gen_k7ddrphy.py warns.
//
// CLKOUT0 CARRIES sys4x BECAUSE IT IS THE FRACTIONAL ONE. Only CLKOUT0 has a
// fractional divider on MMCME2, and 800/320 = 2.5. Putting sys on CLKOUT0 and
// sys4x elsewhere would need VCO 960 for an integer /3, and then the 200 MHz
// IDELAY reference is 960/4.8 -- not integer, and IDELAYCTRL REFCLK is not
// negotiable. This is the one assignment that satisfies all three.
//
// NO sys4x_dqs. The A7 needs a 90-degree-shifted DQS clock because it has no
// ODELAY; K7 does its DQS shift in ODELAYE2, and the generated PHY confirms it
// -- 67 ODELAYE2 instances and exactly two clock inputs, sys_clk and sys4x_clk.
// Measured from the netlist, not assumed from the family.
//
// ---------------------------------------------------------------------------
// THE IDELAYCTRL IS NOT OPTIONAL AND IS NOT IN THE PHY. The generated k7ddrphy
// contains 33 IDELAYE2 and 67 ODELAYE2 and ZERO IDELAYCTRL -- LiteX
// instantiates it at the SoC level, so it lands here. Without it every delay
// primitive is uncalibrated and its taps mean nothing.
//
// Vivado's DRC also requires the delays and the IDELAYCTRL to share an
// IODELAY_GROUP, and migen's Verilog conversion DROPS the attribute, so the
// XDC sets it. See fpga/constraints/idelay_group.xdc.

`timescale 1ns / 1ps

module scoria_char_top #(
    // 80 MHz / 115200 baud, rounded. The UART is the only host path, so a
    // wrong value here looks like dead hardware.
    parameter int CLKS_PER_BIT = 695,
    parameter int ROW_WIDTH    = 15,
    parameter int NUM_BANKS    = 8,
    parameter int COL_WIDTH    = 10,
    parameter int DFI_RATE     = 4,
    parameter int DRAM_BL      = 8,
    parameter int DRAM_BEAT_WIDTH   = 64,   // DFI data per phase (2 x DQ)
    parameter int DRAM_DEVICE_WIDTH = 32,   // the DQ bus
    parameter int CLK_HZ       = 80_000_000
) (
    // ---- board ------------------------------------------------------------
    input  wire        clk200_p,
    input  wire        clk200_n,
    input  wire        cpu_reset_n,
    input  wire        uart_rx,
    output wire        uart_tx,
    output wire [7:0]  led,

    // ---- DDR3 pads: names match the generated XDC and the LiteDRAM build ---
    output wire [14:0] ddram_a,
    output wire [2:0]  ddram_ba,
    output wire        ddram_ras_n,
    output wire        ddram_cas_n,
    output wire        ddram_we_n,
    output wire        ddram_cs_n,
    output wire [3:0]  ddram_dm,
    inout  wire [31:0] ddram_dq,
    inout  wire [3:0]  ddram_dqs_p,
    inout  wire [3:0]  ddram_dqs_n,
    output wire        ddram_clk_p,
    output wire        ddram_clk_n,
    output wire        ddram_cke,
    output wire        ddram_odt,
    output wire        ddram_reset_n
);

    localparam int DFI_DATA_WIDTH  = DRAM_BEAT_WIDTH * DFI_RATE;
    localparam int DFI_STRB_WIDTH  = DFI_DATA_WIDTH / 8;
    localparam int DFI_EN_WIDTH    = DFI_RATE;
    localparam int DFI_VALID_WIDTH = DFI_RATE;
    localparam int DFI_ADDR_BUS_W  = ROW_WIDTH * DFI_RATE;
    localparam int DFI_BANK_BUS_W  = $clog2(NUM_BANKS) * DFI_RATE;
    localparam int DFI_CTRL_BUS_W  = DFI_RATE;
    localparam int DFI_CS_BUS_W    = DFI_RATE;      // NUM_RANKS = 1

    // =====================================================================
    // Clocking
    // =====================================================================
    wire w_clk200;
    IBUFDS u_ibufds_clk200 (.I(clk200_p), .IB(clk200_n), .O(w_clk200));

    wire w_sys_i, w_sys4x_i, w_idelay_i, w_clkfb_i, w_clkfb, w_mmcm_locked;
    wire w_sys, w_sys4x, w_idelay_ref;

    MMCME2_BASE #(
        .BANDWIDTH        ("OPTIMIZED"),
        .CLKIN1_PERIOD    (5.000),        // 200 MHz
        .DIVCLK_DIVIDE    (1),
        .CLKFBOUT_MULT_F  (4.000),        // VCO = 800 MHz
        .CLKOUT0_DIVIDE_F (2.500),        // 320 MHz sys4x  (fractional)
        .CLKOUT1_DIVIDE   (10),           //  80 MHz sys
        .CLKOUT2_DIVIDE   (4),            // 200 MHz idelay ref
        .CLKOUT0_PHASE    (0.000),
        .CLKOUT1_PHASE    (0.000),
        .CLKOUT2_PHASE    (0.000),
        .STARTUP_WAIT     ("FALSE")
    ) u_mmcm (
        .CLKIN1   (w_clk200),
        .CLKFBIN  (w_clkfb),
        .CLKFBOUT (w_clkfb_i),
        .CLKOUT0  (w_sys4x_i),
        .CLKOUT1  (w_sys_i),
        .CLKOUT2  (w_idelay_i),
        .CLKOUT0B (), .CLKOUT1B (), .CLKOUT2B (),
        .CLKOUT3  (), .CLKOUT3B (), .CLKOUT4 (), .CLKOUT5 (), .CLKOUT6 (),
        .CLKFBOUTB(),
        .LOCKED   (w_mmcm_locked),
        .PWRDWN   (1'b0),
        .RST      (~cpu_reset_n)
    );

    // Every MMCM output through a BUFG. A clock that reaches logic without one
    // routes on general fabric, and on this family that has produced an
    // invalid auto-inferred generated clock and a PHANTOM -23.5 ns WNS that
    // cost a day of hunting (project_ddr2_char_wsysi_invalid_genclock).
    BUFG u_bufg_fb     (.I(w_clkfb_i),  .O(w_clkfb));
    BUFG u_bufg_sys    (.I(w_sys_i),    .O(w_sys));
    BUFG u_bufg_sys4x  (.I(w_sys4x_i),  .O(w_sys4x));
    BUFG u_bufg_idelay (.I(w_idelay_i), .O(w_idelay_ref));

    // =====================================================================
    // Resets. Held until the MMCM locks AND the IDELAYCTRL reports ready --
    // releasing before IDELAYCTRL_RDY means every delay tap is uncalibrated
    // and the first read window is meaningless.
    // =====================================================================
    wire w_idelay_rdy;
    (* ASYNC_REG = "TRUE" *) reg [7:0] r_rst_sync;
    always @(posedge w_sys) begin
        if (!cpu_reset_n || !w_mmcm_locked || !w_idelay_rdy) r_rst_sync <= '0;
        else                                                 r_rst_sync <= {r_rst_sync[6:0], 1'b1};
    end
    wire w_aresetn = r_rst_sync[7];

    // The PHY takes active-HIGH resets, one per clock domain, because migen
    // generates them that way.
    (* ASYNC_REG = "TRUE" *) reg [3:0] r_rst4x_sync;
    always @(posedge w_sys4x) begin
        if (!cpu_reset_n || !w_mmcm_locked || !w_idelay_rdy) r_rst4x_sync <= '0;
        else                                                 r_rst4x_sync <= {r_rst4x_sync[2:0], 1'b1};
    end
    wire w_sys_rst   = ~w_aresetn;
    wire w_sys4x_rst = ~r_rst4x_sync[3];

    // =====================================================================
    // IDELAYCTRL -- calibrates the PHY's IDELAYE2/ODELAYE2. REFCLK must be
    // 200 MHz. The PHY does not contain one (33 IDELAYE2 + 67 ODELAYE2, zero
    // IDELAYCTRL), so it lives here.
    // =====================================================================
    IDELAYCTRL u_idelayctrl (
        .REFCLK (w_idelay_ref),
        .RST    (~w_mmcm_locked),
        .RDY    (w_idelay_rdy)
    );

    // =====================================================================
    // The harness
    // =====================================================================
    wire [DFI_ADDR_BUS_W-1:0]  w_dfi_address;
    wire [DFI_BANK_BUS_W-1:0]  w_dfi_bank;
    wire [DFI_CTRL_BUS_W-1:0]  w_dfi_cas_n, w_dfi_ras_n, w_dfi_we_n;
    wire [DFI_CS_BUS_W-1:0]    w_dfi_cs_n, w_dfi_cke, w_dfi_odt;
    wire                       w_dfi_reset_n;
    wire [DFI_DATA_WIDTH-1:0]  w_dfi_wrdata, w_dfi_rddata;
    wire [DFI_EN_WIDTH-1:0]    w_dfi_wrdata_en, w_dfi_rddata_en;
    wire [DFI_STRB_WIDTH-1:0]  w_dfi_wrdata_mask;
    wire [DFI_VALID_WIDTH-1:0] w_dfi_rddata_valid;
    wire [9:0]  w_phy_csr_adr;
    wire        w_phy_csr_we;
    wire [31:0] w_phy_csr_dat_w, w_phy_csr_dat_r;

    scoria_char_harness #(
        .CLKS_PER_BIT      (CLKS_PER_BIT),
        .NUM_RANKS         (1),
        .NUM_BANKS         (NUM_BANKS),
        .ROW_WIDTH         (ROW_WIDTH),
        .COL_WIDTH         (COL_WIDTH),
        .DFI_RATE          (DFI_RATE),
        .DRAM_BL           (DRAM_BL),
        .DRAM_BEAT_WIDTH   (DRAM_BEAT_WIDTH),
        .DRAM_DEVICE_WIDTH (DRAM_DEVICE_WIDTH),
        .CLK_HZ            (CLK_HZ)
    ) u_harness (
        .aclk    (w_sys),
        .aresetn (w_aresetn),
        .i_uart_rx (uart_rx),
        .o_uart_tx (uart_tx),
        .o_led     (led),
        .o_dfi_address     (w_dfi_address),
        .o_dfi_bank        (w_dfi_bank),
        .o_dfi_cas_n       (w_dfi_cas_n),
        .o_dfi_ras_n       (w_dfi_ras_n),
        .o_dfi_we_n        (w_dfi_we_n),
        .o_dfi_cs_n        (w_dfi_cs_n),
        .o_dfi_cke         (w_dfi_cke),
        .o_dfi_odt         (w_dfi_odt),
        .o_dfi_reset_n     (w_dfi_reset_n),
        .o_dfi_wrdata      (w_dfi_wrdata),
        .o_dfi_wrdata_en   (w_dfi_wrdata_en),
        .o_dfi_wrdata_mask (w_dfi_wrdata_mask),
        .o_dfi_rddata_en   (w_dfi_rddata_en),
        .i_dfi_rddata      (w_dfi_rddata),
        .i_dfi_rddata_valid(w_dfi_rddata_valid),
        .o_phy_csr_adr   (w_phy_csr_adr),
        .o_phy_csr_we    (w_phy_csr_we),
        .o_phy_csr_dat_w (w_phy_csr_dat_w),
        .i_phy_csr_dat_r (w_phy_csr_dat_r)
    );

    // =====================================================================
    // Flat DFI -> per-phase DFI
    // =====================================================================
    wire [ROW_WIDTH-1:0] p0_address, p1_address, p2_address, p3_address;
    wire [2:0] p0_bank, p1_bank, p2_bank, p3_bank;
    wire p0_ras_n, p1_ras_n, p2_ras_n, p3_ras_n;
    wire p0_cas_n, p1_cas_n, p2_cas_n, p3_cas_n;
    wire p0_we_n,  p1_we_n,  p2_we_n,  p3_we_n;
    wire p0_cs_n,  p1_cs_n,  p2_cs_n,  p3_cs_n;
    wire p0_cke,   p1_cke,   p2_cke,   p3_cke;
    wire p0_odt,   p1_odt,   p2_odt,   p3_odt;
    wire p0_reset_n, p1_reset_n, p2_reset_n, p3_reset_n;
    wire p0_act_n, p1_act_n, p2_act_n, p3_act_n;
    wire p0_wrdata_en, p1_wrdata_en, p2_wrdata_en, p3_wrdata_en;
    wire [DRAM_BEAT_WIDTH-1:0] p0_wrdata, p1_wrdata, p2_wrdata, p3_wrdata;
    wire [DRAM_BEAT_WIDTH/8-1:0] p0_wrdata_mask, p1_wrdata_mask,
                                 p2_wrdata_mask, p3_wrdata_mask;
    wire p0_rddata_en, p1_rddata_en, p2_rddata_en, p3_rddata_en;
    wire [DRAM_BEAT_WIDTH-1:0] p0_rddata, p1_rddata, p2_rddata, p3_rddata;
    wire p0_rddata_valid, p1_rddata_valid, p2_rddata_valid, p3_rddata_valid;

    dfi_flat_to_k7ddrphy #(
        .DFI_ADDR_W (ROW_WIDTH),
        .DFI_BANK_W ($clog2(NUM_BANKS)),
        .NPHASES    (DFI_RATE),
        .PHASE_DATA (DRAM_BEAT_WIDTH)
    ) u_dfi_adapt (
        .dfi_address_flat     (w_dfi_address),
        .dfi_bank_flat        (w_dfi_bank),
        .dfi_cas_n_flat       (w_dfi_cas_n),
        .dfi_ras_n_flat       (w_dfi_ras_n),
        .dfi_we_n_flat        (w_dfi_we_n),
        .dfi_cs_n_flat        (w_dfi_cs_n),
        .dfi_cke_flat         (w_dfi_cke),
        .dfi_odt_flat         (w_dfi_odt),
        .dfi_reset_n          (w_dfi_reset_n),
        .dfi_wrdata_flat      (w_dfi_wrdata),
        .dfi_wrdata_mask_flat (w_dfi_wrdata_mask),
        .dfi_wrdata_en_flat   (w_dfi_wrdata_en),
        .dfi_rddata_en_flat   (w_dfi_rddata_en),
        .dfi_rddata_flat      (w_dfi_rddata),
        .dfi_rddata_valid_flat(w_dfi_rddata_valid),

        .dfi_p0_address(p0_address), .dfi_p1_address(p1_address),
        .dfi_p2_address(p2_address), .dfi_p3_address(p3_address),
        .dfi_p0_bank(p0_bank), .dfi_p1_bank(p1_bank),
        .dfi_p2_bank(p2_bank), .dfi_p3_bank(p3_bank),
        .dfi_p0_ras_n(p0_ras_n), .dfi_p1_ras_n(p1_ras_n),
        .dfi_p2_ras_n(p2_ras_n), .dfi_p3_ras_n(p3_ras_n),
        .dfi_p0_cas_n(p0_cas_n), .dfi_p1_cas_n(p1_cas_n),
        .dfi_p2_cas_n(p2_cas_n), .dfi_p3_cas_n(p3_cas_n),
        .dfi_p0_we_n(p0_we_n), .dfi_p1_we_n(p1_we_n),
        .dfi_p2_we_n(p2_we_n), .dfi_p3_we_n(p3_we_n),
        .dfi_p0_cs_n(p0_cs_n), .dfi_p1_cs_n(p1_cs_n),
        .dfi_p2_cs_n(p2_cs_n), .dfi_p3_cs_n(p3_cs_n),
        .dfi_p0_cke(p0_cke), .dfi_p1_cke(p1_cke),
        .dfi_p2_cke(p2_cke), .dfi_p3_cke(p3_cke),
        .dfi_p0_odt(p0_odt), .dfi_p1_odt(p1_odt),
        .dfi_p2_odt(p2_odt), .dfi_p3_odt(p3_odt),
        .dfi_p0_reset_n(p0_reset_n), .dfi_p1_reset_n(p1_reset_n),
        .dfi_p2_reset_n(p2_reset_n), .dfi_p3_reset_n(p3_reset_n),
        .dfi_p0_act_n(p0_act_n), .dfi_p1_act_n(p1_act_n),
        .dfi_p2_act_n(p2_act_n), .dfi_p3_act_n(p3_act_n),
        .dfi_p0_wrdata_en(p0_wrdata_en), .dfi_p1_wrdata_en(p1_wrdata_en),
        .dfi_p2_wrdata_en(p2_wrdata_en), .dfi_p3_wrdata_en(p3_wrdata_en),
        .dfi_p0_wrdata(p0_wrdata), .dfi_p1_wrdata(p1_wrdata),
        .dfi_p2_wrdata(p2_wrdata), .dfi_p3_wrdata(p3_wrdata),
        .dfi_p0_wrdata_mask(p0_wrdata_mask), .dfi_p1_wrdata_mask(p1_wrdata_mask),
        .dfi_p2_wrdata_mask(p2_wrdata_mask), .dfi_p3_wrdata_mask(p3_wrdata_mask),
        .dfi_p0_rddata_en(p0_rddata_en), .dfi_p1_rddata_en(p1_rddata_en),
        .dfi_p2_rddata_en(p2_rddata_en), .dfi_p3_rddata_en(p3_rddata_en),
        .dfi_p0_rddata(p0_rddata), .dfi_p1_rddata(p1_rddata),
        .dfi_p2_rddata(p2_rddata), .dfi_p3_rddata(p3_rddata),
        .dfi_p0_rddata_valid(p0_rddata_valid), .dfi_p1_rddata_valid(p1_rddata_valid),
        .dfi_p2_rddata_valid(p2_rddata_valid), .dfi_p3_rddata_valid(p3_rddata_valid)
    );

    // =====================================================================
    // The PHY. Generated by bin/gen_k7ddrphy.py from LiteDRAM -- the same
    // K7DDRPHY the board proof uses. Lint reads a blackbox stub derived FROM
    // the generated module, so the interface checked is the interface the PHY
    // has; Vivado reads the real 9110-line body.
    // =====================================================================
    k7ddrphy u_k7ddrphy (
        .sys_clk   (w_sys),
        .sys_rst   (w_sys_rst),
        .sys4x_clk (w_sys4x),
        .sys4x_rst (w_sys4x_rst),

        // Calibration CSRs: 32-bit data, 10-bit address, driven by
        // harness_csr's DFI_TUNING indirection. `re` is tied high because the
        // bank's read path is combinational here and the host only ever reads
        // after a write settles.
        .adr   (w_phy_csr_adr),
        .re    (1'b1),
        .we    (w_phy_csr_we),
        .dat_w (w_phy_csr_dat_w),
        .dat_r (w_phy_csr_dat_r),

        .dfi_p0_address(p0_address), .dfi_p0_bank(p0_bank),
        .dfi_p0_cas_n(p0_cas_n), .dfi_p0_cs_n(p0_cs_n),
        .dfi_p0_ras_n(p0_ras_n), .dfi_p0_we_n(p0_we_n),
        .dfi_p0_cke(p0_cke), .dfi_p0_odt(p0_odt),
        .dfi_p0_reset_n(p0_reset_n), .dfi_p0_act_n(p0_act_n),
        .dfi_p0_wrdata(p0_wrdata), .dfi_p0_wrdata_en(p0_wrdata_en),
        .dfi_p0_wrdata_mask(p0_wrdata_mask), .dfi_p0_rddata_en(p0_rddata_en),
        .dfi_p0_rddata(p0_rddata), .dfi_p0_rddata_valid(p0_rddata_valid),

        .dfi_p1_address(p1_address), .dfi_p1_bank(p1_bank),
        .dfi_p1_cas_n(p1_cas_n), .dfi_p1_cs_n(p1_cs_n),
        .dfi_p1_ras_n(p1_ras_n), .dfi_p1_we_n(p1_we_n),
        .dfi_p1_cke(p1_cke), .dfi_p1_odt(p1_odt),
        .dfi_p1_reset_n(p1_reset_n), .dfi_p1_act_n(p1_act_n),
        .dfi_p1_wrdata(p1_wrdata), .dfi_p1_wrdata_en(p1_wrdata_en),
        .dfi_p1_wrdata_mask(p1_wrdata_mask), .dfi_p1_rddata_en(p1_rddata_en),
        .dfi_p1_rddata(p1_rddata), .dfi_p1_rddata_valid(p1_rddata_valid),

        .dfi_p2_address(p2_address), .dfi_p2_bank(p2_bank),
        .dfi_p2_cas_n(p2_cas_n), .dfi_p2_cs_n(p2_cs_n),
        .dfi_p2_ras_n(p2_ras_n), .dfi_p2_we_n(p2_we_n),
        .dfi_p2_cke(p2_cke), .dfi_p2_odt(p2_odt),
        .dfi_p2_reset_n(p2_reset_n), .dfi_p2_act_n(p2_act_n),
        .dfi_p2_wrdata(p2_wrdata), .dfi_p2_wrdata_en(p2_wrdata_en),
        .dfi_p2_wrdata_mask(p2_wrdata_mask), .dfi_p2_rddata_en(p2_rddata_en),
        .dfi_p2_rddata(p2_rddata), .dfi_p2_rddata_valid(p2_rddata_valid),

        .dfi_p3_address(p3_address), .dfi_p3_bank(p3_bank),
        .dfi_p3_cas_n(p3_cas_n), .dfi_p3_cs_n(p3_cs_n),
        .dfi_p3_ras_n(p3_ras_n), .dfi_p3_we_n(p3_we_n),
        .dfi_p3_cke(p3_cke), .dfi_p3_odt(p3_odt),
        .dfi_p3_reset_n(p3_reset_n), .dfi_p3_act_n(p3_act_n),
        .dfi_p3_wrdata(p3_wrdata), .dfi_p3_wrdata_en(p3_wrdata_en),
        .dfi_p3_wrdata_mask(p3_wrdata_mask), .dfi_p3_rddata_en(p3_rddata_en),
        .dfi_p3_rddata(p3_rddata), .dfi_p3_rddata_valid(p3_rddata_valid),

        // Pads. ddram_reset_n is DRIVEN BY THE PHY, from the per-phase
        // dfi_reset_n the adapter fans out -- it is not a top-level tie.
        .ddram_a(ddram_a), .ddram_ba(ddram_ba),
        .ddram_ras_n(ddram_ras_n), .ddram_cas_n(ddram_cas_n),
        .ddram_we_n(ddram_we_n), .ddram_cs_n(ddram_cs_n),
        .ddram_dm(ddram_dm), .ddram_dq(ddram_dq),
        .ddram_dqs_p(ddram_dqs_p), .ddram_dqs_n(ddram_dqs_n),
        .ddram_clk_p(ddram_clk_p), .ddram_clk_n(ddram_clk_n),
        .ddram_cke(ddram_cke), .ddram_odt(ddram_odt),
        .ddram_reset_n(ddram_reset_n)
    );

endmodule
