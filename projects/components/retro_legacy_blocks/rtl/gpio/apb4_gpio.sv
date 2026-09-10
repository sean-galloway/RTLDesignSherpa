// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb4_gpio
// Purpose: APB GPIO Controller Top Level
//
// Description:
//   Complete APB-accessible GPIO controller with:
//   - 32-bit GPIO port
//   - Per-bit direction control
//   - Edge and level interrupt support
//   - Atomic set/clear/toggle operations
//   - Optional CDC for async pin domains
//
// Architecture (RLB Standard Pattern):
//   APB -> apb4_slave[_cdc] -> CMD/RSP -> peakrdl_to_cmdrsp ->
//     -> gpio_regs (PeakRDL) -> hwif -> gpio_core
//
// FPGA Integration Notes:
//   The gpio_in/gpio_out/gpio_oe signals should be connected to
//   IOBUF primitives at the FPGA top level:
//
//   IOBUF u_iobuf[31:0] (
//       .IO    (gpio_pins),      // Bidirectional pad
//       .O     (gpio_in),        // Input path (to this module)
//       .I     (gpio_out),       // Output path (from this module)
//       .T     (~gpio_oe)        // Tristate control (active low for IOBUF)
//   );
//
// Interrupt Clock Domain (issue #44):
//   gpio_config_regs produces irq in the CORE clock domain, which is gpio_clk
//   when CDC_ENABLE=1. That output is consumed by an interrupt controller in
//   the pclk domain, so with CDC_ENABLE=1 it is passed through a 2-flop
//   synchronizer into pclk. With CDC_ENABLE=0 the two domains are the same
//   clock and the synchronizer is bypassed, so the zero-latency behaviour of
//   the single-clock configuration is unchanged.
//
//   The observability contract that follows from that synchronizer -- see the
//   comment at the instance below for the full statement -- is that EDGE-mode
//   pins are always observed on irq, while LEVEL-mode pins require the input
//   to be held long enough for the synchronizer to sample it.
//
// CHECK BY INSPECTION (this was a simulation-time parameter guard; contracts
// belong in the header, properties in external formal bindings):
//   - GPIO_WIDTH must be in [1,32]. Every GPIO register field is 32 bits wide,
//     so a wider port truncates silently and a zero/negative width has no
//     legal slice. Nothing in the RTL rejects an out-of-range override.
//
// Documentation: projects/components/retro_legacy_blocks/rtl/gpio/README.md
// Created: 2025-11-29
// Updated: 2025-11-30 - Changed to 32-bit APB and s_apb_* naming
// Updated: 2026-09-08 - issue #44: synchronize irq into pclk when CDC_ENABLE=1
// Updated: 2026-09-08 - issue #44 review: state the irq observability contract
//                       per interrupt mode, add the GPIO_WIDTH elaboration guard
// Updated: 2026-09-09 - simulation-time param guard removed; the width
//                       constraint is CHECK BY INSPECTION above

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb4_gpio #(
    // GPIO Parameters
    parameter int GPIO_WIDTH   = 32,            // GPIO port width
    parameter int SYNC_STAGES  = 2,             // Input synchronizer stages

    // CDC Parameters
    parameter int CDC_ENABLE   = 0,             // 1=async clocks, 0=same clock
    parameter int SKID_DEPTH   = 2, // CDC skid buffer depth
    // Async-FIFO pointer encoding, forwarded to the CDC block: 0 = Gray
    // (power-of-2 depth only), 1 = Johnson (any depth, DEPTH-bit pointers).
    // Gray by default -- Johnson is opt-in.
    parameter int USE_JOHNSON = 0
) (
    // APB Clock and Reset
    input  logic                        pclk,
    input  logic                        presetn,

    // Optional separate GPIO clock (when CDC_ENABLE=1)
    input  logic                        gpio_clk,
    input  logic                        gpio_rstn,

    // APB Slave Interface (consistent s_apb_* naming, 32-bit)
    input  logic                        s_apb_PSEL,
    input  logic                        s_apb_PENABLE,
    output logic                        s_apb_PREADY,
    input  logic [11:0]                 s_apb_PADDR,
    input  logic                        s_apb_PWRITE,
    input  logic [31:0]                 s_apb_PWDATA,
    input  logic [3:0]                  s_apb_PSTRB,
    input  logic [2:0]                  s_apb_PPROT,
    output logic [31:0]                 s_apb_PRDATA,
    output logic                        s_apb_PSLVERR,

    // GPIO Pins Interface
    input  logic [GPIO_WIDTH-1:0]       gpio_in,
    output logic [GPIO_WIDTH-1:0]       gpio_out,
    output logic [GPIO_WIDTH-1:0]       gpio_oe,

    // Interrupt Output
    output logic                        irq
);

    // ========================================================================
    // Internal Signals
    // ========================================================================

    // Fixed parameters for RLB standard
    localparam int APB_ADDR_WIDTH = 12;
    localparam int APB_DATA_WIDTH = 32;
    localparam int APB_STRB_WIDTH = APB_DATA_WIDTH / 8;
    localparam int APB_PROT_WIDTH = 3;

    // CMD/RSP interface (APB slave to peakrdl_to_cmdrsp)
    logic                       w_cmd_valid;
    logic                       w_cmd_ready;
    logic                       w_cmd_pwrite;
    logic [APB_ADDR_WIDTH-1:0]  w_cmd_paddr;
    logic [APB_DATA_WIDTH-1:0]  w_cmd_pwdata;
    logic [APB_STRB_WIDTH-1:0]  w_cmd_pstrb;
    logic [APB_PROT_WIDTH-1:0]  w_cmd_pprot;
    logic                       w_rsp_valid;
    logic                       w_rsp_ready;
    logic [APB_DATA_WIDTH-1:0]  w_rsp_prdata;
    logic                       w_rsp_pslverr;

    // PeakRDL regblock interface
    logic                       w_regblk_req;
    logic                       w_regblk_req_is_wr;
    logic [APB_ADDR_WIDTH-1:0]  w_regblk_addr;
    logic [APB_DATA_WIDTH-1:0]  w_regblk_wr_data;
    logic [APB_DATA_WIDTH-1:0]  w_regblk_wr_biten;
    logic                       w_regblk_req_stall_wr;
    logic                       w_regblk_req_stall_rd;
    logic                       w_regblk_rd_ack;
    logic                       w_regblk_rd_err;
    logic [APB_DATA_WIDTH-1:0]  w_regblk_rd_data;
    logic                       w_regblk_wr_ack;
    logic                       w_regblk_wr_err;

    // Clock selection
    logic w_core_clk;
    logic w_core_rstn;

    // Aggregate interrupt, in the CORE clock domain (gpio_clk when
    // CDC_ENABLE=1), before the synchronizer below.
    logic w_irq_core;

    assign w_core_clk  = (CDC_ENABLE != 0) ? gpio_clk  : pclk;
    assign w_core_rstn = (CDC_ENABLE != 0) ? gpio_rstn : presetn;

    // ========================================================================
    // APB Slave - CMD/RSP Conversion
    // ========================================================================
    generate
        if (CDC_ENABLE != 0) begin : gen_cdc
            apb4_slave_cdc #(
                .ADDR_WIDTH (APB_ADDR_WIDTH),
                .DATA_WIDTH (APB_DATA_WIDTH),
                .DEPTH      (SKID_DEPTH),
                .USE_JOHNSON (USE_JOHNSON)
            ) u_apb4_slave_cdc (
                // APB clock domain
                .pclk           (pclk),
                .presetn        (presetn),
                // Core clock domain
                .aclk           (w_core_clk),
                .aresetn        (w_core_rstn),
                // APB interface
                .s_apb_PSEL     (s_apb_PSEL),
                .s_apb_PENABLE  (s_apb_PENABLE),
                .s_apb_PREADY   (s_apb_PREADY),
                .s_apb_PADDR    (s_apb_PADDR),
                .s_apb_PWRITE   (s_apb_PWRITE),
                .s_apb_PWDATA   (s_apb_PWDATA),
                .s_apb_PSTRB    (s_apb_PSTRB),
                .s_apb_PPROT    (s_apb_PPROT),
                .s_apb_PRDATA   (s_apb_PRDATA),
                .s_apb_PSLVERR  (s_apb_PSLVERR),
                // CMD/RSP interface
                .cmd_valid      (w_cmd_valid),
                .cmd_ready      (w_cmd_ready),
                .cmd_pwrite     (w_cmd_pwrite),
                .cmd_paddr      (w_cmd_paddr),
                .cmd_pwdata     (w_cmd_pwdata),
                .cmd_pstrb      (w_cmd_pstrb),
                .cmd_pprot      (w_cmd_pprot),
                .rsp_valid      (w_rsp_valid),
                .rsp_ready      (w_rsp_ready),
                .rsp_prdata     (w_rsp_prdata),
                .rsp_pslverr    (w_rsp_pslverr)
            );
        end else begin : gen_no_cdc
            apb4_slave #(
                .ADDR_WIDTH (APB_ADDR_WIDTH),
                .DATA_WIDTH (APB_DATA_WIDTH)
            ) u_apb4_slave (
                .pclk           (pclk),
                .presetn        (presetn),
                // APB interface
                .s_apb_PSEL     (s_apb_PSEL),
                .s_apb_PENABLE  (s_apb_PENABLE),
                .s_apb_PREADY   (s_apb_PREADY),
                .s_apb_PADDR    (s_apb_PADDR),
                .s_apb_PWRITE   (s_apb_PWRITE),
                .s_apb_PWDATA   (s_apb_PWDATA),
                .s_apb_PSTRB    (s_apb_PSTRB),
                .s_apb_PPROT    (s_apb_PPROT),
                .s_apb_PRDATA   (s_apb_PRDATA),
                .s_apb_PSLVERR  (s_apb_PSLVERR),
                // CMD/RSP interface
                .cmd_valid      (w_cmd_valid),
                .cmd_ready      (w_cmd_ready),
                .cmd_pwrite     (w_cmd_pwrite),
                .cmd_paddr      (w_cmd_paddr),
                .cmd_pwdata     (w_cmd_pwdata),
                .cmd_pstrb      (w_cmd_pstrb),
                .cmd_pprot      (w_cmd_pprot),
                .rsp_valid      (w_rsp_valid),
                .rsp_ready      (w_rsp_ready),
                .rsp_prdata     (w_rsp_prdata),
                .rsp_pslverr    (w_rsp_pslverr)
            );
        end
    endgenerate

    // ========================================================================
    // PeakRDL to CMD/RSP Adapter
    // ========================================================================
    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH (APB_ADDR_WIDTH),
        .DATA_WIDTH (APB_DATA_WIDTH)
    ) u_peakrdl_adapter (
        .aclk               (w_core_clk),
        .aresetn            (w_core_rstn),

        // CMD/RSP input from APB slave
        .cmd_valid          (w_cmd_valid),
        .cmd_ready          (w_cmd_ready),
        .cmd_pwrite         (w_cmd_pwrite),
        .cmd_paddr          (w_cmd_paddr),
        .cmd_pwdata         (w_cmd_pwdata),
        .cmd_pstrb          (w_cmd_pstrb),
        .rsp_valid          (w_rsp_valid),
        .rsp_ready          (w_rsp_ready),
        .rsp_prdata         (w_rsp_prdata),
        .rsp_pslverr        (w_rsp_pslverr),

        // PeakRDL register block interface
        .regblk_req         (w_regblk_req),
        .regblk_req_is_wr   (w_regblk_req_is_wr),
        .regblk_addr        (w_regblk_addr),
        .regblk_wr_data     (w_regblk_wr_data),
        .regblk_wr_biten    (w_regblk_wr_biten),
        .regblk_req_stall_wr(w_regblk_req_stall_wr),
        .regblk_req_stall_rd(w_regblk_req_stall_rd),
        .regblk_rd_ack      (w_regblk_rd_ack),
        .regblk_rd_err      (w_regblk_rd_err),
        .regblk_rd_data     (w_regblk_rd_data),
        .regblk_wr_ack      (w_regblk_wr_ack),
        .regblk_wr_err      (w_regblk_wr_err)
    );

    // ========================================================================
    // GPIO Configuration Registers + Core
    // ========================================================================
    gpio_config_regs #(
        .GPIO_WIDTH     (GPIO_WIDTH),
        .SYNC_STAGES    (SYNC_STAGES),
        .ADDR_WIDTH     (APB_ADDR_WIDTH),
        .DATA_WIDTH     (APB_DATA_WIDTH)
    ) u_gpio_config_regs (
        .clk                (w_core_clk),
        .rst_n              (w_core_rstn),

        // PeakRDL regblock interface (from peakrdl_to_cmdrsp)
        .regblk_req         (w_regblk_req),
        .regblk_req_is_wr   (w_regblk_req_is_wr),
        .regblk_addr        (w_regblk_addr),
        .regblk_wr_data     (w_regblk_wr_data),
        .regblk_wr_biten    (w_regblk_wr_biten),
        .regblk_req_stall_wr(w_regblk_req_stall_wr),
        .regblk_req_stall_rd(w_regblk_req_stall_rd),
        .regblk_rd_ack      (w_regblk_rd_ack),
        .regblk_rd_err      (w_regblk_rd_err),
        .regblk_rd_data     (w_regblk_rd_data),
        .regblk_wr_ack      (w_regblk_wr_ack),
        .regblk_wr_err      (w_regblk_wr_err),

        // GPIO pins
        .gpio_in            (gpio_in),
        .gpio_out           (gpio_out),
        .gpio_oe            (gpio_oe),

        // Interrupt (core clock domain)
        .irq                (w_irq_core)
    );

    // ========================================================================
    // Interrupt Synchronization to pclk
    // ========================================================================
    // irq is a LEVEL, and a plain 2-flop synchronizer neither handshakes nor
    // stretches: it samples. What that costs is per interrupt mode, and this is
    // the contract, not an implementation note.
    //
    //   EDGE mode: the event is latched in GPIO_INT_STATUS (sticky, W1C), so
    //   the core-domain irq stays asserted until software clears the bit. It is
    //   always observed on the pclk-domain irq, whatever the pulse width was.
    //
    //   LEVEL mode: irq is exactly as wide as the SYNCHRONIZED input level, so
    //   with CDC_ENABLE=1 an assertion must hold for at least 2 pclk periods
    //   (this synchronizer) plus SYNC_STAGES gpio_clk periods (gpio_core's
    //   input synchronizer) to be guaranteed visible on irq. A level shorter
    //   than that may never be sampled here. Use EDGE mode for short pulses.
    //
    //   Either way software polling GPIO_INT_STATUS sees the event: the sticky
    //   bit is set from the core-domain status path and is not gated by this
    //   synchronizer.
    //
    // With CDC_ENABLE=0 there is no sampling loss at all -- the domains are the
    // same clock and the synchronizer is bypassed.
    generate
        if (CDC_ENABLE != 0) begin : gen_irq_sync
            glitch_free_n_dff_arn #(
                .FLOP_COUNT (2),
                .WIDTH      (1)
            ) u_irq_sync (
                .clk    (pclk),
                .rst_n  (presetn),
                .d      (w_irq_core),
                .q      (irq)
            );
        end else begin : gen_irq_direct
            // Same clock domain -- crossing would only add latency.
            assign irq = w_irq_core;
        end
    endgenerate


    // Elaboration-time parameter guard (sim only). Not an assertion in the
    // house sense: see vault/handbook/design/no-assertions-in-rtl.md.
`ifndef SYNTHESIS
    initial begin : param_check
        if (GPIO_WIDTH > APB_DATA_WIDTH || GPIO_WIDTH < 1) begin
            $error("apb4_gpio: GPIO_WIDTH=%0d out of range [1,%0d]",
                   GPIO_WIDTH, APB_DATA_WIDTH);
        end
    end
`endif

endmodule : apb4_gpio
