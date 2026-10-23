// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Cocotb TB wrapper around the LiteDRAM A/B harness: the DUT-agnostic
// char_engine_harness (UART bridge + harness_csr + 1->6 AXIL bridge + the
// SAME char_engine_block the pumice and granite sim tops wrap) driving
// LiteX's simulation core litedram_core_sim (LiteDRAMCore + SDRAMPHYModel,
// VexRiscv BIOS baked into ROM so the core self-initialises and raises
// init_done, exactly as the board core does).
//
// This is the sim half of the three-way comparison: the identical UART byte
// stream, the identical injectors and observers, the identical host program
// -- only the controller behind the AXI port differs. Mirrors
// flows-litedram-uart/rtl/litedram_char_top.sv minus the pins: the sim core
// has no pads, no PLL (user_clk == clk) and no reset input (internal POR).
//
// Prerequisite: gen/sim/gateware/litedram_core_sim.v regenerated WITH the
// BIOS (flows-litedram-uart `./regen.sh --bios`, or litedram_gen --sim
// without --no-compile-software); a core generated without software has
// empty .init files and never asserts init_done.

`timescale 1ns / 1ps

module litedram_char_uart_tb_top #(
    // litedram_hp.yml sys_clk_freq: the sim core's clk IS user_clk
    parameter int FPGA_CLK_HZ       = 75_000_000,
    // Sim runs the UART as close to the system clock as it will go (see the
    // pumice TB top for the CLKS_PER_BIT=4 floor).
    parameter int UART_BAUD         = 18_750_000,   // -> CLKS_PER_BIT = 4
    parameter int UART_CLKS_PER_BIT = FPGA_CLK_HZ / UART_BAUD,
    // Generators per direction (the injectors); the perf proxy raises it with
    // TEST_NUM_GEN so eight per direction can run at once (owner, 2026-10-22).
    parameter int NUM_GEN           = 4
) (
    input  logic aclk,
    input  logic aresetn,

    input  logic i_uart_rx,
    output logic o_uart_tx
);

    // ---- clocks / init from the sim core -----------------------------------
    logic user_clk, user_rst, init_done, init_error;

    // ---- AXI between the harness (master) and the core's user port --------
    // 8-bit id: the generator index rides in the top bits (litedram_hp.yml
    // id_width 8), as on the board.
    localparam int CHAR_GEN_ID_W = 8;

    logic [CHAR_GEN_ID_W-1:0] ax_awid, ax_arid, ax_bid, ax_rid;
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
    // LiteDRAM sim core: self-inits the modelled DDR2, exposes user_clk + AXI.
    // BIOS console tied idle (auto-init). The SIM core declares awsize/arsize
    // [3:0] where the board core has [2:0]: zero-extend (awsize is load-
    // bearing: beat increment = 1 << awsize). 27 of 32 address bits reach
    // the core (128 MiB).
    // =========================================================================
    litedram_core_sim u_core (
        .clk        (aclk),
        .init_done  (init_done),
        .init_error (init_error),
        .sim_trace  (1'b0),
        .uart_rx    (1'b1),
        .uart_tx    (/* open */),
        .user_clk   (user_clk),
        .user_rst   (user_rst),
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

    /* verilator lint_off UNUSEDSIGNAL */
    wire _unused = &{1'b0, ax_awaddr[31:27], ax_araddr[31:27], user_clk};
    /* verilator lint_on UNUSEDSIGNAL */

    // =========================================================================
    // The engine harness, on the same clock, held in reset while the core's
    // internal POR is asserted.
    // =========================================================================
    char_engine_harness #(
        .AXI_ADDR_WIDTH     (32),
        .AXI_ID_WIDTH       (CHAR_GEN_ID_W),
        .NUM_GEN            (NUM_GEN),
        .FPGA_CLK_HZ        (FPGA_CLK_HZ),
        .UART_BAUD          (UART_BAUD),
        // x16 BL4 / host-64: one AXI beat per DRAM burst -> quantum 1.
        .BURST_LEN_MULTIPLE (1),
        .CFG_DFI_RATE       (2),
        .CFG_DRAM_BL        (4),
        .CFG_ROW_WIDTH      (13),
        .CFG_DRAM_BEAT_W    (32),
        .CFG_DRAM_DEVICE_W  (16)
    ) u_harness (
        .aclk    (aclk),
        .aresetn (aresetn & ~user_rst),
        .i_uart_rx(i_uart_rx),
        .o_uart_tx(o_uart_tx),
        .o_led   (/* open */),
        .o_seven_seg_an (/* open */),
        .o_seven_seg_seg(/* open */),
        .o_seven_seg_dp (/* open */),
        .i_init_done (init_done),
        .i_init_fail (init_error),
        .m_axi_awid   (ax_awid),   .m_axi_awaddr  (ax_awaddr),
        .m_axi_awlen  (ax_awlen),  .m_axi_awsize  (ax_awsize),
        .m_axi_awburst(ax_awburst),.m_axi_awlock  (/* open */),
        .m_axi_awcache(/* open */),.m_axi_awprot  (/* open */),
        .m_axi_awqos  (/* open */),.m_axi_awregion(/* open */),
        .m_axi_awuser (/* open */),
        .m_axi_awvalid(ax_awvalid),.m_axi_awready (ax_awready),
        .m_axi_wdata  (ax_wdata),  .m_axi_wstrb   (ax_wstrb),
        .m_axi_wlast  (ax_wlast),  .m_axi_wuser   (/* open */),
        .m_axi_wvalid (ax_wvalid), .m_axi_wready  (ax_wready),
        .m_axi_bid    (ax_bid),    .m_axi_bresp   (ax_bresp),
        .m_axi_buser  (8'd0),      .m_axi_bvalid  (ax_bvalid),
        .m_axi_bready (ax_bready),
        .m_axi_arid   (ax_arid),   .m_axi_araddr  (ax_araddr),
        .m_axi_arlen  (ax_arlen),  .m_axi_arsize  (ax_arsize),
        .m_axi_arburst(ax_arburst),.m_axi_arlock  (/* open */),
        .m_axi_arcache(/* open */),.m_axi_arprot  (/* open */),
        .m_axi_arqos  (/* open */),.m_axi_arregion(/* open */),
        .m_axi_aruser (/* open */),
        .m_axi_arvalid(ax_arvalid),.m_axi_arready (ax_arready),
        .m_axi_rid    (ax_rid),    .m_axi_rdata   (ax_rdata),
        .m_axi_rresp  (ax_rresp),  .m_axi_rlast   (ax_rlast),
        .m_axi_ruser  (8'd0),      .m_axi_rvalid  (ax_rvalid),
        .m_axi_rready (ax_rready)
    );

endmodule : litedram_char_uart_tb_top
