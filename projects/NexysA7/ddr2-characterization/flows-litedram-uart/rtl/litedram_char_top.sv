// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: litedram_char_top
// Purpose: FPGA pin-level top for the LiteDRAM apples-to-apples characterization
//          harness. litedram_core (own PLL + a7ddrphy + DDR2 init) drives the
//          board DDR2 pads and exposes a 64-bit AXI4 user port on user_clk; the
//          DUT-agnostic char_engine_harness (SAME engines + perf taps + timer +
//          harness_csr + UART bridge as the pumice flow) runs on user_clk and
//          drives that AXI port. This measures LiteDRAM with the identical host
//          program + metrics used for pumice -> a direct benchmark.
//
// Target: Digilent Nexys A7-100T (xc7a100tcsg324-1). Pins in
//         constraints/litedram_char.xdc (keep in lockstep with these ports).
//
// NOTE: litedram_core must be regenerated with a FUNCTIONAL BIOS so it self-inits
//       and asserts init_done:  ./regen.sh --bios   (see HARNESS_PLAN.md). Its
//       BIOS console uart_rx is tied idle; the board FTDI UART is the harness
//       console (UART_TXD_IN/RXD_OUT -> char_engine_harness).
`timescale 1ns / 1ps

module litedram_char_top (
    input  logic        CLK100MHZ,
    input  logic        CPU_RESETN,     // active-low pushbutton

    input  logic        UART_TXD_IN,    // FTDI -> FPGA RX (harness console)
    output logic        UART_RXD_OUT,   // FPGA -> FTDI TX

    output logic [15:0] LED,
    output logic [7:0]  AN,
    output logic        CA, CB, CC, CD, CE, CF, CG, DP,

    // DDR2 pads driven by litedram_core (13-bit row addr).
    output logic [12:0] ddram_a,
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

    // ---- clocks / init from litedram_core -----------------------------------
    logic        user_clk, user_rst;
    logic        init_done, init_error, pll_locked;

    // ---- AXI between the harness (master) and litedram user port ------------
    logic [7:0]  ax_awid, ax_arid, ax_bid, ax_rid;
    logic [31:0] ax_awaddr, ax_araddr;
    logic [7:0]  ax_awlen, ax_arlen;
    logic [2:0]  ax_awsize, ax_arsize;
    logic [1:0]  ax_awburst, ax_arburst, ax_bresp, ax_rresp;
    logic        ax_awvalid, ax_awready, ax_arvalid, ax_arready;
    logic [63:0] ax_wdata, ax_rdata;
    logic [7:0]  ax_wstrb;
    logic        ax_wlast, ax_wvalid, ax_wready;
    logic        ax_bvalid, ax_bready, ax_rlast, ax_rvalid, ax_rready;

    // =========================================================================
    // LiteDRAM core — self-inits DDR2, exposes user_clk + AXI user port.
    // BIOS console uart tied idle (auto-init); harness uses the board FTDI UART.
    // =========================================================================
    litedram_core u_core (
        .clk        (CLK100MHZ),
        .rst        (~CPU_RESETN),
        .ddram_a    (ddram_a),      .ddram_ba (ddram_ba),
        .ddram_ras_n(ddram_ras_n),  .ddram_cas_n(ddram_cas_n),
        .ddram_we_n (ddram_we_n),   .ddram_cs_n(ddram_cs_n),
        .ddram_cke  (ddram_cke),    .ddram_odt (ddram_odt),
        .ddram_reset_n(/* open — DDR2 has no reset pin */), .ddram_dm(ddram_dm),
        .ddram_dq   (ddram_dq),     .ddram_dqs_p(ddram_dqs_p),
        .ddram_dqs_n(ddram_dqs_n),  .ddram_clk_p(ddram_clk_p),
        .ddram_clk_n(ddram_clk_n),
        .init_done  (init_done),    .init_error(init_error),
        .pll_locked (pll_locked),
        .uart_rx    (1'b1),         .uart_tx (/* open */),
        .user_clk   (user_clk),     .user_rst(user_rst),
        // AXI user port (write half from the writer, read half from the reader)
        .user_port_axi_0_awid   (ax_awid),
        .user_port_axi_0_awaddr (ax_awaddr[26:0]),
        .user_port_axi_0_awlen  (ax_awlen),
        .user_port_axi_0_awsize ({1'b0, ax_awsize}),
        .user_port_axi_0_awburst(ax_awburst),
        .user_port_axi_0_awvalid(ax_awvalid),
        .user_port_axi_0_awready(ax_awready),
        .user_port_axi_0_wdata  (ax_wdata),
        .user_port_axi_0_wstrb  (ax_wstrb),
        .user_port_axi_0_wlast  (ax_wlast),
        .user_port_axi_0_wvalid (ax_wvalid),
        .user_port_axi_0_wready (ax_wready),
        .user_port_axi_0_bid    (ax_bid),
        .user_port_axi_0_bresp  (ax_bresp),
        .user_port_axi_0_bvalid (ax_bvalid),
        .user_port_axi_0_bready (ax_bready),
        .user_port_axi_0_arid   (ax_arid),
        .user_port_axi_0_araddr (ax_araddr[26:0]),
        .user_port_axi_0_arlen  (ax_arlen),
        .user_port_axi_0_arsize ({1'b0, ax_arsize}),
        .user_port_axi_0_arburst(ax_arburst),
        .user_port_axi_0_arvalid(ax_arvalid),
        .user_port_axi_0_arready(ax_arready),
        .user_port_axi_0_rid    (ax_rid),
        .user_port_axi_0_rdata  (ax_rdata),
        .user_port_axi_0_rresp  (ax_rresp),
        .user_port_axi_0_rlast  (ax_rlast),
        .user_port_axi_0_rvalid (ax_rvalid),
        .user_port_axi_0_rready (ax_rready)
    );

    // litedram awsize/arsize are 4-bit; harness drives 3-bit -> zero-extend.
    // (assigned via the [3:0] slice above with the upper bit implicitly 0 by the
    //  wire being sized 3-bit on the harness side; make it explicit here.)

    // =========================================================================
    // DUT-agnostic engine harness on user_clk (SAME as the pumice flow).
    // =========================================================================
    char_engine_harness #(
        .AXI_ADDR_WIDTH (32),
        .FPGA_CLK_HZ    (100_000_000),   // litedram user_clk (sys) freq
        .UART_BAUD      (115_200)
    ) u_harness (
        .aclk    (user_clk),
        .aresetn (~user_rst),
        .i_uart_rx(UART_TXD_IN),
        .o_uart_tx(UART_RXD_OUT),
        .o_led   (LED),
        .o_seven_seg_an (AN),
        .o_seven_seg_seg({CG, CF, CE, CD, CC, CB, CA}),
        .o_seven_seg_dp (DP),
        .i_init_done (init_done),
        .i_init_fail (init_error),
        .m_axi_awid   (ax_awid),   .m_axi_awaddr (ax_awaddr),
        .m_axi_awlen  (ax_awlen),  .m_axi_awsize (ax_awsize),
        .m_axi_awburst(ax_awburst),.m_axi_awuser (/* open */),
        .m_axi_awvalid(ax_awvalid),.m_axi_awready(ax_awready),
        .m_axi_wdata  (ax_wdata),  .m_axi_wstrb  (ax_wstrb),
        .m_axi_wlast  (ax_wlast),  .m_axi_wuser  (/* open */),
        .m_axi_wvalid (ax_wvalid), .m_axi_wready (ax_wready),
        .m_axi_bid    (ax_bid),    .m_axi_bresp  (ax_bresp),
        .m_axi_buser  (8'd0),      .m_axi_bvalid (ax_bvalid),
        .m_axi_bready (ax_bready),
        .m_axi_arid   (ax_arid),   .m_axi_araddr (ax_araddr),
        .m_axi_arlen  (ax_arlen),  .m_axi_arsize (ax_arsize),
        .m_axi_arburst(ax_arburst),.m_axi_aruser (/* open */),
        .m_axi_arvalid(ax_arvalid),.m_axi_arready(ax_arready),
        .m_axi_rid    (ax_rid),    .m_axi_rdata  (ax_rdata),
        .m_axi_rresp  (ax_rresp),  .m_axi_rlast  (ax_rlast),
        .m_axi_ruser  (8'd0),      .m_axi_rvalid (ax_rvalid),
        .m_axi_rready (ax_rready)
    );

endmodule : litedram_char_top
