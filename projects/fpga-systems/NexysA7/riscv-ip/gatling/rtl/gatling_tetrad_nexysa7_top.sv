// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gatling_tetrad_nexysa7_top
// Purpose: gatling_tetrad (the barrel core, the Xcell unit and four cells)
//          on the Nexys A7-100T: 100 MHz -> MMCM -> 4.6875 MHz, reset, the
//          rig (UART -> AXI4-Lite -> program memory + cell harness ->
//          gatling_tetrad), LEDs
//
// Documentation: projects/fpga-systems/NexysA7/riscv-ip/gatling/README.md
// Subsystem: fpga-systems / riscv-ip
//
// Created: 2026-11-26
//
// Notes:
//   - 4.6875 MHz is a functional bring-up clock, the one alu-infer's own
//     Nexys A7 bring-up uses: alu-infer's bf16 rows and accumulate lanes are
//     combinational at their default latencies (a 211-level path, alu-infer
//     TASK-010).  The core and Xcell unit close at 100 MHz on their own.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gatling_tetrad_nexysa7_top (
    input  logic        sysclk,         // 100 MHz oscillator (E3)
    input  logic        cpu_resetn,     // active-low pushbutton (C12)
    input  logic        uart_tx_in,     // host -> FPGA
    output logic        uart_rx_out,    // FPGA -> host
    output logic [7:0]  led
);

    // VCO 600 MHz (the bottom of the Artix-7 -1 range) / 128 = 4.6875 MHz
    localparam int FPGA_CLK_HZ       = 4_687_500;
    localparam int UART_BAUD         = 115_200;
    localparam int UART_CLKS_PER_BIT = (FPGA_CLK_HZ + UART_BAUD / 2) / UART_BAUD;

    logic clk_unbuf, clk, clkfb, clkfb_buf, mmcm_locked;

    MMCME2_BASE #(
        .BANDWIDTH         ("OPTIMIZED"),
        .CLKIN1_PERIOD     (10.000),
        .DIVCLK_DIVIDE     (1),
        .CLKFBOUT_MULT_F   (6.000),
        .CLKOUT0_DIVIDE_F  (128.000),
        .CLKOUT0_DUTY_CYCLE(0.500),
        .CLKOUT0_PHASE     (0.000),
        .STARTUP_WAIT      ("FALSE")
    ) u_mmcm (
        .CLKIN1   (sysclk),
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
    BUFG u_bufg_c0 (.I(clk_unbuf), .O(clk));

    // Reset: held until the MMCM locks, OR the pushbutton; synchronized
    logic rst_n_raw, sys_rstn;
    assign rst_n_raw = cpu_resetn & mmcm_locked;

    (* ASYNC_REG = "TRUE" *) logic r_rstn_sync0, r_rstn_sync1;
    `ALWAYS_FF_RST(clk, rst_n_raw,
        if (`RST_ASSERTED(rst_n_raw)) begin
            r_rstn_sync0 <= 1'b0;
            r_rstn_sync1 <= 1'b0;
        end else begin
            r_rstn_sync0 <= 1'b1;
            r_rstn_sync1 <= r_rstn_sync0;
        end
    )
    assign sys_rstn = r_rstn_sync1;

    logic [3:0] w_run, w_halted, w_done;
    logic       w_req, w_rsp;

    gatling_tetrad_rig #(.CLKS_PER_BIT(UART_CLKS_PER_BIT)) u_rig (
        .aclk(clk), .aresetn(sys_rstn),
        .i_uart_rx(uart_tx_in), .o_uart_tx(uart_rx_out),
        .o_run(w_run), .o_halted(w_halted), .o_done(w_done),
        .o_axil_req(w_req), .o_axil_rsp(w_rsp));

    // LEDs: 0-3 a context running (on), done (blinking) or halted otherwise
    // (fast blink); 4 MMCM locked; 5/6 UART activity; 7 heartbeat
    logic [23:0] r_heartbeat;
    `ALWAYS_FF_RST(clk, sys_rstn,
        if (`RST_ASSERTED(sys_rstn)) r_heartbeat <= '0;
        else                         r_heartbeat <= r_heartbeat + 24'd1;
    )

    for (genvar h = 0; h < 4; h++) begin : g_ctx_led
        assign led[h] = (w_run[h] && !w_halted[h])
                     || (w_done[h] && r_heartbeat[21])
                     || (w_halted[h] && !w_done[h] && r_heartbeat[19]);
    end
    assign led[4] = mmcm_locked;
    assign led[5] = w_req;
    assign led[6] = w_rsp;
    assign led[7] = r_heartbeat[23];

endmodule : gatling_tetrad_nexysa7_top
