// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: litedram_ddr3_board_top
// Purpose: Pin-level top for the Genesys 2 LiteDRAM DDR3 board proof. Wraps the
//          generated litedram_genesys2_ddr3 core and brings nothing else.
//
// This build exists to answer ONE question before any scoria RTL is on the
// board: are the board, the pins, the PHY and the DRAM themselves sound? The
// generated core embeds a VexRiscv and a BIOS whose memtest reports over UART,
// so a pass here is a self-contained verdict with no controller of ours in it.
//
// That separation is the whole point. On the Nexys A7 the equivalent LiteDRAM
// memtest is the only reason the later DDR2 PHY-calibration hunt was tractable
// -- without a known-good reference, "reads return garbage" has no denominator.
//
// The AXI user port is deliberately TIED IDLE. The BIOS memtest runs through
// the CPU's own port, not this one; the user port is what the scoria harness
// will drive in the sibling build, and leaving it idle here keeps this build a
// pure board proof rather than a partial harness.
//
// Notes:
//   - The board clock is a 200 MHz LVDS pair; the core's internal PLL derives
//     the 100 MHz sys clock (1:4 -> 400 MHz CK -> DDR3-800).
//   - cpu_reset_n is active LOW (R19). The core's rst is active HIGH.
//   - ddram_reset_n is a real DRAM pin. DFI carries no reset signal, which is
//     why both LiteDRAM and scoria bring it out at the top rather than through
//     the DFI bus.

`timescale 1ns / 1ps

module litedram_ddr3_board_top (
    // ---- board clock: 200 MHz LVDS (AD12/AD11) ----
    input  logic        clk200_p,
    input  logic        clk200_n,
    // ---- reset button, active LOW (R19) ----
    input  logic        cpu_reset_n,

    // ---- BIOS console ----
    input  logic        uart_rx,
    output logic        uart_tx,

    // ---- bring-up visibility ----
    output logic [7:0]  led,

    // ---- DDR3 (2 x MT41J256M16, 32-bit) ----
    output logic [14:0] ddram_a,
    output logic [2:0]  ddram_ba,
    output logic        ddram_ras_n,
    output logic        ddram_cas_n,
    output logic        ddram_we_n,
    output logic        ddram_cs_n,
    output logic [3:0]  ddram_dm,
    inout  wire  [31:0] ddram_dq,
    inout  wire  [3:0]  ddram_dqs_p,
    inout  wire  [3:0]  ddram_dqs_n,
    output logic        ddram_clk_p,
    output logic        ddram_clk_n,
    output logic        ddram_cke,
    output logic        ddram_odt,
    output logic        ddram_reset_n
);

    // ---- differential board clock -> single-ended ----
    logic w_clk200;
    IBUFDS #(
        .DIFF_TERM    ("FALSE"),
        .IBUF_LOW_PWR ("TRUE"),
        .IOSTANDARD   ("LVDS")
    ) u_clk200_ibufds (
        .I  (clk200_p),
        .IB (clk200_n),
        .O  (w_clk200)
    );

    logic w_init_done, w_init_error, w_pll_locked;
    logic w_user_clk, w_user_rst;

    litedram_genesys2_ddr3 u_litedram (
        .clk            (w_clk200),
        .rst            (!cpu_reset_n),     // board button is active LOW
        .pll_locked     (w_pll_locked),
        .init_done      (w_init_done),
        .init_error     (w_init_error),
        .uart_rx        (uart_rx),
        .uart_tx        (uart_tx),

        // The core exports its user-side clock/reset. Unused here because the
        // AXI port is idle; the scoria-side build is where these matter.
        .user_clk       (w_user_clk),
        .user_rst       (w_user_rst),

        // ---- AXI user port: TIED IDLE (see the header) ----
        .user_port_axi_0_awvalid (1'b0),
        .user_port_axi_0_awaddr  (30'd0),
        .user_port_axi_0_awburst (2'd1),    // INCR, so an accidental issue is legal
        .user_port_axi_0_awlen   (8'd0),
        .user_port_axi_0_awsize  (3'd3),    // 8 bytes = the 64-bit port
        .user_port_axi_0_awid    (8'd0),
        .user_port_axi_0_awready (),
        .user_port_axi_0_wvalid  (1'b0),
        .user_port_axi_0_wdata   (64'd0),
        .user_port_axi_0_wstrb   (8'd0),
        .user_port_axi_0_wlast   (1'b0),
        .user_port_axi_0_wready  (),
        .user_port_axi_0_bready  (1'b1),    // never stall a response
        .user_port_axi_0_bvalid  (),
        .user_port_axi_0_bresp   (),
        .user_port_axi_0_bid     (),
        .user_port_axi_0_arvalid (1'b0),
        .user_port_axi_0_araddr  (30'd0),
        .user_port_axi_0_arburst (2'd1),
        .user_port_axi_0_arlen   (8'd0),
        .user_port_axi_0_arsize  (3'd3),
        .user_port_axi_0_arid    (8'd0),
        .user_port_axi_0_arready (),
        .user_port_axi_0_rready  (1'b1),
        .user_port_axi_0_rvalid  (),
        .user_port_axi_0_rdata   (),
        .user_port_axi_0_rresp   (),
        .user_port_axi_0_rlast   (),
        .user_port_axi_0_rid     (),

        // ---- DDR3 pins, straight through ----
        .ddram_a        (ddram_a),
        .ddram_ba       (ddram_ba),
        .ddram_ras_n    (ddram_ras_n),
        .ddram_cas_n    (ddram_cas_n),
        .ddram_we_n     (ddram_we_n),
        .ddram_cs_n     (ddram_cs_n),
        .ddram_dm       (ddram_dm),
        .ddram_dq       (ddram_dq),
        .ddram_dqs_p    (ddram_dqs_p),
        .ddram_dqs_n    (ddram_dqs_n),
        .ddram_clk_p    (ddram_clk_p),
        .ddram_clk_n    (ddram_clk_n),
        .ddram_cke      (ddram_cke),
        .ddram_odt      (ddram_odt),
        .ddram_reset_n  (ddram_reset_n)
    );

    // LED map, readable from across the desk during bring-up. init_error is
    // given its own bit rather than being folded into a "not done" state: the
    // two failures look identical on a single LED and are diagnosed
    // differently -- never-done is calibration hanging, error is calibration
    // completing and failing.
    always_comb begin
        led    = '0;
        led[0] = w_pll_locked;
        led[1] = w_init_done;
        led[2] = w_init_error;
        led[3] = w_user_rst;
        led[7] = cpu_reset_n;     // proves the button and the pin mapping
    end

endmodule : litedram_ddr3_board_top
