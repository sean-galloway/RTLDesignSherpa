// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Module: amber_pair_genesys2_top
// Purpose: Genesys 2 (Kintex-7 XC7K325T-2) board top for the amber pair-rig
//          bring-up harness. Differential 200 MHz oscillator -> IBUFDS ->
//          MMCME2_BASE 90MHz + BUFG, pushbutton reset two-flop sync, UART
//          rx/tx pins, and the amber_pair_harness instance.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module amber_pair_genesys2_top #(
    // Harness clock = VCO_MHZ / CLKOUT0_DIVIDE, VCO = 200 MHz sysclk * MULT_F.
    parameter int VCO_MHZ        = 1350,
    parameter int CLKOUT0_DIVIDE = 15,
    parameter int UART_BAUD      = 115_200,
    // amber geometry (pair-rig FULL)
    parameter int ADDR_WIDTH     = l1_pkg::AMBER_ADDR_WIDTH,
    parameter int SETS           = l1_pkg::AMBER_SETS,
    parameter int WAYS           = l1_pkg::AMBER_WAYS,
    parameter int LINE_BYTES     = l1_pkg::AMBER_LINE_BYTES,
    parameter int BUS_WIDTH      = l1_pkg::AMBER_BUS_WIDTH,
    parameter int REPL_POLICY    = int'(l1_pkg::AMBER_REPL_LRU),
    parameter bit USE_MONITOR    = 1'b1,
    parameter int MEM_DEPTH_KB   = 512,
    parameter int MON_N_PROFILE  = 32
) (
    input  logic       sysclk_p,      // 200 MHz LVDS (+)
    input  logic       sysclk_n,      // 200 MHz LVDS (-)
    input  logic       cpu_resetn,    // active-low pushbutton (R19)

    input  logic       uart_tx_in,    // host -> FPGA
    output logic       uart_rx_out,   // FPGA -> host

    output logic [7:0] led
);

    localparam int FPGA_CLK_HZ = (VCO_MHZ * 1_000_000) / CLKOUT0_DIVIDE;
    localparam real CLKFBOUT_MULT = real'(VCO_MHZ) / 200.0;
    localparam int MEM_DEPTH = (MEM_DEPTH_KB * 1024 * 8) / BUS_WIDTH;

    initial begin
        if (VCO_MHZ % 25 != 0)
            $error("VCO_MHZ=%0d is not a multiple of 25: MULT_F=%0f is off the MMCM 0.125 grid",
                   VCO_MHZ, real'(VCO_MHZ) / 200.0);
        if (VCO_MHZ < 600 || VCO_MHZ > 1440)
            $error("VCO_MHZ=%0d outside the -2 Kintex MMCM range 600..1440", VCO_MHZ);
        if ((VCO_MHZ * 1_000_000) % CLKOUT0_DIVIDE != 0)
            $error("VCO_MHZ=%0d / CLKOUT0_DIVIDE=%0d is not an integer Hz frequency",
                   VCO_MHZ, CLKOUT0_DIVIDE);
    end

    // =========================================================================
    // 200 MHz LVDS -> single-ended -> MMCM -> harness clock.
    // =========================================================================
    logic sysclk_ib, clk_unbuf, aclk, clkfb, clkfb_buf, mmcm_locked;

    IBUFDS u_ibufds (.I(sysclk_p), .IB(sysclk_n), .O(sysclk_ib));

    MMCME2_BASE #(
        .BANDWIDTH        ("OPTIMIZED"),
        .CLKIN1_PERIOD    (5.000),
        .DIVCLK_DIVIDE    (1),
        .CLKFBOUT_MULT_F  (CLKFBOUT_MULT),
        .CLKOUT0_DIVIDE_F (CLKOUT0_DIVIDE),
        .CLKOUT0_DUTY_CYCLE(0.500),
        .CLKOUT0_PHASE    (0.000),
        .STARTUP_WAIT     ("FALSE")
    ) u_mmcm (
        .CLKIN1   (sysclk_ib),
        .CLKFBIN  (clkfb_buf),
        .CLKFBOUT (clkfb),
        .CLKFBOUTB(),
        .CLKOUT0  (clk_unbuf),
        .CLKOUT0B (), .CLKOUT1 (), .CLKOUT1B(), .CLKOUT2 (), .CLKOUT2B(),
        .CLKOUT3  (), .CLKOUT3B(), .CLKOUT4 (), .CLKOUT5 (), .CLKOUT6 (),
        .LOCKED   (mmcm_locked),
        .RST      (1'b0),
        .PWRDWN   (1'b0)
    );
    BUFG u_bufg_fb (.I(clkfb),     .O(clkfb_buf));
    BUFG u_bufg_c0 (.I(clk_unbuf), .O(aclk));

    // =========================================================================
    // Reset synchronization -- async assert, sync deassert.
    // =========================================================================
    logic rst_n_raw;
    assign rst_n_raw = cpu_resetn & mmcm_locked;

    (* ASYNC_REG = "TRUE" *) logic r_rst_meta;
    (* ASYNC_REG = "TRUE" *) logic r_rst_sync;
    `ALWAYS_FF_RST(aclk, rst_n_raw,
        if (`RST_ASSERTED(rst_n_raw)) begin
            r_rst_meta <= 1'b0;
            r_rst_sync <= 1'b0;
        end else begin
            r_rst_meta <= 1'b1;
            r_rst_sync <= r_rst_meta;
        end
    )

    wire aresetn = r_rst_sync;

    // =========================================================================
    // Harness
    // =========================================================================
    logic w_done, w_busy, w_error;
    logic [3:0] w_heartbeat;

    amber_pair_harness #(
        .FPGA_CLK_HZ   (FPGA_CLK_HZ),
        .UART_BAUD     (UART_BAUD),
        .ADDR_WIDTH    (ADDR_WIDTH),
        .SETS          (SETS),
        .WAYS          (WAYS),
        .LINE_BYTES    (LINE_BYTES),
        .BUS_WIDTH     (BUS_WIDTH),
        .REPL_POLICY   (REPL_POLICY),
        .USE_MONITOR   (USE_MONITOR),
        .MEM_DEPTH     (MEM_DEPTH),
        .MON_N_PROFILE (MON_N_PROFILE)
    ) u_harness (
        .aclk      (aclk),
        .aresetn   (aresetn),
        .i_uart_rx (uart_tx_in),
        .o_uart_tx (uart_rx_out),
        // Direct-host AXIL is a sim/cocotb-only path (USE_DIRECT_HOST=1).
        // This board top always services the host over UART, so tie the
        // direct-host inputs off and leave its outputs open.
        .host_axi_awaddr  (32'b0),
        .host_axi_awprot  (3'b0),
        .host_axi_awvalid (1'b0),
        .host_axi_awready (),
        .host_axi_wdata   (32'b0),
        .host_axi_wstrb   (4'b0),
        .host_axi_wvalid  (1'b0),
        .host_axi_wready  (),
        .host_axi_bresp   (),
        .host_axi_bvalid  (),
        .host_axi_bready  (1'b0),
        .host_axi_araddr  (32'b0),
        .host_axi_arprot  (3'b0),
        .host_axi_arvalid (1'b0),
        .host_axi_arready (),
        .host_axi_rdata   (),
        .host_axi_rresp   (),
        .host_axi_rvalid  (),
        .host_axi_rready  (1'b0),
        .o_done    (w_done),
        .o_busy    (w_busy),
        .o_error   (w_error)
    );

    // =========================================================================
    // Heartbeat and LEDs
    // =========================================================================
    localparam int HEARTBEAT_DIV = FPGA_CLK_HZ / 2;  // ~0.5 Hz toggle -> 1 Hz blink
    logic [$clog2(HEARTBEAT_DIV+1)-1:0] r_heartbeat_div;

    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_heartbeat_div <= '0;
            w_heartbeat     <= '0;
        end else begin
            if (r_heartbeat_div >= HEARTBEAT_DIV[$clog2(HEARTBEAT_DIV+1)-1:0]) begin
                r_heartbeat_div <= '0;
                w_heartbeat[0]  <= ~w_heartbeat[0];
            end else begin
                r_heartbeat_div <= r_heartbeat_div + 1'b1;
            end
        end
    )

    assign led = {w_busy,
                  w_done,
                  w_error,
                  w_heartbeat[0],
                  4'b0};

endmodule : amber_pair_genesys2_top
