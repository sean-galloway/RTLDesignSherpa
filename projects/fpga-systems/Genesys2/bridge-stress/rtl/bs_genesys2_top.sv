// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: bs_genesys2_top
// Purpose: Genesys 2 board top of the bridge stress model: the generated
//          stress harness on two MMCM clocks, UART to the host, status on
//          the LEDs.
// Documentation: projects/fpga-systems/Genesys2/bridge-stress/PRD.md
// Author: sean galloway
// Created: 2026-10-19
//==============================================================================
// Clocks
//   sys_clk_p/n  200 MHz LVDS (AD12/AD11) -> IBUFDS -> MMCM, VCO 900 MHz
//   aclk         100 MHz (VCO / 9): the DUT bridge, the configuration path and
//                every port the DUT TOML does not mark cdc
//   cclk          75 MHz (VCO / 12): every cdc port. The sim harness runs the
//                same 100 / 75 MHz pair.
// Reset
//   cpu_resetn (R19, active low) or MMCM unlocked holds both domains; each
//   leaves reset through its own reset_sync.
// LEDs
//   [0] heartbeat (aclk / 2^26)   [1] MMCM locked   [2] run busy
//   [3] all done                  [4] any error     [5] done and no error
//   [7:6] reserved (0)
// The harness module is chosen by the build: BS_HARNESS (default the AXI4
// build's), with its filelist from rtl/generated/filelists/.
//==============================================================================

`timescale 1ns / 1ps

`ifndef BS_HARNESS
`define BS_HARNESS bs_harness_bridge_bs_axi4
`endif

module bs_genesys2_top #(
    parameter int FPGA_CLK_HZ = 100_000_000,
    parameter int UART_BAUD   = 115_200
) (
    input  logic       sys_clk_p,
    input  logic       sys_clk_n,
    input  logic       cpu_resetn,

    input  logic       uart_tx_in,     // host -> FPGA (Y20)
    output logic       uart_rx_out,    // FPGA -> host (Y23)
    output logic [7:0] led
);

    // ---- clocks ----------------------------------------------------------------
    logic w_clk200, w_clkfb, w_clkfb_buf, w_aclk_unbuf, w_cclk_unbuf, w_locked;
    logic aclk, cclk;

    IBUFDS u_ibufds (.I(sys_clk_p), .IB(sys_clk_n), .O(w_clk200));

    MMCME2_BASE #(
        .CLKIN1_PERIOD    (5.000),
        .CLKFBOUT_MULT_F  (4.500),
        .DIVCLK_DIVIDE    (1),
        .CLKOUT0_DIVIDE_F (9.000),
        .CLKOUT1_DIVIDE   (12)
    ) u_mmcm (
        .CLKIN1   (w_clk200),
        .CLKFBIN  (w_clkfb_buf),
        .CLKFBOUT (w_clkfb),
        .CLKFBOUTB(),
        .CLKOUT0  (w_aclk_unbuf),
        .CLKOUT0B (),
        .CLKOUT1  (w_cclk_unbuf),
        .CLKOUT1B (), .CLKOUT2 (), .CLKOUT2B(), .CLKOUT3 (), .CLKOUT3B(),
        .CLKOUT4  (), .CLKOUT5 (), .CLKOUT6 (),
        .LOCKED   (w_locked),
        .PWRDWN   (1'b0),
        .RST      (1'b0)
    );

    BUFG u_bufg_fb (.I(w_clkfb),      .O(w_clkfb_buf));
    BUFG u_bufg_a  (.I(w_aclk_unbuf), .O(aclk));
    BUFG u_bufg_c  (.I(w_cclk_unbuf), .O(cclk));

    // ---- resets: async assert, sync release per domain -------------------------
    logic w_rst_n, aresetn, cresetn;
    assign w_rst_n = cpu_resetn && w_locked;

    reset_sync #(.N(3)) u_rst_a (.clk(aclk), .rst_n(w_rst_n), .sync_rst_n(aresetn));
    reset_sync #(.N(3)) u_rst_c (.clk(cclk), .rst_n(w_rst_n), .sync_rst_n(cresetn));

    // ---- the harness ---------------------------------------------------------------
    logic w_all_done, w_any_err, w_busy;

    `BS_HARNESS #(
        .CLKS_PER_BIT (FPGA_CLK_HZ / UART_BAUD)
    ) u_harness (
        .aclk, .aresetn, .cclk, .cresetn,
        .i_uart_rx  (uart_tx_in),
        .o_uart_tx  (uart_rx_out),
        .o_all_done (w_all_done),
        .o_any_err  (w_any_err),
        .o_busy     (w_busy)
    );

    // ---- LEDs ------------------------------------------------------------------------
    logic [25:0] r_beat;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) r_beat <= '0;
        else          r_beat <= r_beat + 26'd1;
    end

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) led <= '0;
        else led <= {2'b00, w_all_done && !w_any_err, w_any_err, w_all_done, w_busy,
                     1'b1, r_beat[25]};
    end

endmodule : bs_genesys2_top
