// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb4_pit_8254
// Purpose: APB wrapper for Intel 8254-compatible Programmable Interval Timer
//
// Top-level integration module providing:
// - APB4 slave interface
// - 3 independent 16-bit counters
// - Mode 0 (interrupt on terminal count); modes 1-5 not implemented
// - Binary or BCD counting
// - Interrupt outputs
// - Optional clock domain crossing
//
// Follows HPET 3-layer architecture:
//   Layer 1: apb4_pit_8254 (this module) - APB interface and CDC
//   Layer 2: pit_config_regs - Register wrapper, decode and command strobes
//   Layer 3: pit_core - Counter array, GATE synchronizer
//
// Parameters:
//   - NUM_COUNTERS: fixed at 3 (the register map is generated for 3 counters)
//   - CDC_ENABLE:   1 = counters run on pit_clk, the whole cmd/rsp stream
//                   crosses pclk <-> pit_clk in apb4_slave_cdc
//                   0 = everything runs on pclk
//   - USE_JOHNSON:  async-FIFO pointer encoding for the CDC block
//   - SYNC_STAGES:  gate_in input synchronizer depth, >= 2. Default 2.
//
// Register Map (32-bit aligned). NOTHING ELSE in the 4 KB window is decoded:
// every other address is dropped with PSLVERR (pit_config_regs.sv).
//   0x000: PIT_CONFIG      - Global configuration (enable, clock select)
//   0x004: PIT_CONTROL     - Control word (8254-compatible); RW = 00 is the
//                            counter-latch COMMAND, not a read/write mode
//   0x008: PIT_STATUS      - Read-back status (3x 8-bit status bytes)
//   0x00C: RESERVED        - Reserved, reads zero
//   0x010: COUNTER0_DATA   - Counter 0 value (16-bit); write loads, read
//                            returns the live (or latched) count
//   0x014: COUNTER1_DATA   - Counter 1 value (16-bit)
//   0x018: COUNTER2_DATA   - Counter 2 value (16-bit)
//
// gate_in is asynchronous in BOTH configurations and is synchronized in
// pit_core with SYNC_STAGES flops - see that file's header for why the
// synchronizer is not gated on CDC_ENABLE.
//
// Updated: 2026-09-09 - GitHub #52: GATE pause/resume, count 0 = 65536,
//                       latch-as-command, strict decode with PSLVERR, aligned
//                       one-cycle strobes, gate_in synchronizer

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb4_pit_8254 #(
    parameter int NUM_COUNTERS = 3,
    parameter bit CDC_ENABLE   = 0, // Enable clock domain crossing
    // Async-FIFO pointer encoding, forwarded to the CDC block: 0 = Gray
    // (power-of-2 depth only), 1 = Johnson (any depth, DEPTH-bit pointers).
    // Gray by default -- Johnson is opt-in.
    parameter int USE_JOHNSON  = 0,
    parameter int SYNC_STAGES  = 2   // gate_in input synchronizer depth, >= 2
) (
    //========================================================================
    // Clock and Reset - Dual Domain
    //========================================================================
    input  wire                    pclk,           // APB clock domain
    input  wire                    presetn,        // APB reset (active low)
    input  wire                    pit_clk,        // PIT clock domain (used for timer logic)
    input  wire                    pit_resetn,     // PIT reset (active low)

    //========================================================================
    // APB4 Slave Interface (Low Frequency Domain)
    //========================================================================
    input  wire                    s_apb_PSEL,
    input  wire                    s_apb_PENABLE,
    output wire                    s_apb_PREADY,
    input  wire [11:0]             s_apb_PADDR,    // Fixed 12-bit addressing
    input  wire                    s_apb_PWRITE,
    input  wire [31:0]             s_apb_PWDATA,
    input  wire [3:0]              s_apb_PSTRB,
    input  wire [2:0]              s_apb_PPROT,
    output wire [31:0]             s_apb_PRDATA,
    output wire                    s_apb_PSLVERR,

    //========================================================================
    // Timer Interface (High Frequency Domain)
    //========================================================================
    input  wire [NUM_COUNTERS-1:0] gate_in,        // GATE inputs for counters
    output wire [NUM_COUNTERS-1:0] timer_irq       // Interrupt outputs
);

    //========================================================================
    // CMD/RSP Interface Signals
    //========================================================================

    logic                    w_cmd_valid;
    logic                    w_cmd_ready;
    logic                    w_cmd_pwrite;
    logic [11:0]             w_cmd_paddr;
    logic [31:0]             w_cmd_pwdata;
    logic [3:0]              w_cmd_pstrb;

    logic                    w_rsp_valid;
    logic                    w_rsp_ready;
    logic [31:0]             w_rsp_prdata;
    logic                    w_rsp_pslverr;

    //========================================================================
    // APB Slave - Convert APB to CMD/RSP Interface
    //========================================================================

    generate
        if (CDC_ENABLE) begin : g_apb4_slave_cdc
            // Clock Domain Crossing version for async clocks
            apb4_slave_cdc #(
                .ADDR_WIDTH(12),
                .DATA_WIDTH(32),
                .STRB_WIDTH(4),
                .PROT_WIDTH(3),
                .DEPTH(2),
                .USE_JOHNSON (USE_JOHNSON)
            ) u_apb4_slave_cdc (
                // APB Clock Domain
                .pclk                 (pclk),
                .presetn              (presetn),

                // PIT Clock Domain
                .aclk                 (pit_clk),
                .aresetn              (pit_resetn),

                // APB Interface (pclk domain)
                .s_apb_PSEL           (s_apb_PSEL),
                .s_apb_PENABLE        (s_apb_PENABLE),
                .s_apb_PREADY         (s_apb_PREADY),
                .s_apb_PADDR          (s_apb_PADDR),
                .s_apb_PWRITE         (s_apb_PWRITE),
                .s_apb_PWDATA         (s_apb_PWDATA),
                .s_apb_PSTRB          (s_apb_PSTRB),
                .s_apb_PPROT          (s_apb_PPROT),
                .s_apb_PRDATA         (s_apb_PRDATA),
                .s_apb_PSLVERR        (s_apb_PSLVERR),

                // Command Interface (pit_clk domain)
                .cmd_valid            (w_cmd_valid),
                .cmd_ready            (w_cmd_ready),
                .cmd_pwrite           (w_cmd_pwrite),
                .cmd_paddr            (w_cmd_paddr),
                .cmd_pwdata           (w_cmd_pwdata),
                .cmd_pstrb            (w_cmd_pstrb),
                .cmd_pprot            (),  // Unused

                // Response Interface (pit_clk domain)
                .rsp_valid            (w_rsp_valid),
                .rsp_ready            (w_rsp_ready),
                .rsp_prdata           (w_rsp_prdata),
                .rsp_pslverr          (w_rsp_pslverr)
            );
        end else begin : g_apb4_slave_no_cdc
            // Non-CDC version for same clock domain (pclk == pit_clk)
            apb4_slave #(
                .ADDR_WIDTH(12),
                .DATA_WIDTH(32),
                .STRB_WIDTH(4),
                .PROT_WIDTH(3)
            ) u_apb4_slave (
                // Single clock domain (use pclk)
                .pclk                 (pclk),
                .presetn              (presetn),

                // APB Interface
                .s_apb_PSEL           (s_apb_PSEL),
                .s_apb_PENABLE        (s_apb_PENABLE),
                .s_apb_PREADY         (s_apb_PREADY),
                .s_apb_PADDR          (s_apb_PADDR),
                .s_apb_PWRITE         (s_apb_PWRITE),
                .s_apb_PWDATA         (s_apb_PWDATA),
                .s_apb_PSTRB          (s_apb_PSTRB),
                .s_apb_PPROT          (s_apb_PPROT),
                .s_apb_PRDATA         (s_apb_PRDATA),
                .s_apb_PSLVERR        (s_apb_PSLVERR),

                // Command Interface (same pclk domain)
                .cmd_valid            (w_cmd_valid),
                .cmd_ready            (w_cmd_ready),
                .cmd_pwrite           (w_cmd_pwrite),
                .cmd_paddr            (w_cmd_paddr),
                .cmd_pwdata           (w_cmd_pwdata),
                .cmd_pstrb            (w_cmd_pstrb),
                .cmd_pprot            (),  // Unused

                // Response Interface (same pclk domain)
                .rsp_valid            (w_rsp_valid),
                .rsp_ready            (w_rsp_ready),
                .rsp_prdata           (w_rsp_prdata),
                .rsp_pslverr          (w_rsp_pslverr)
            );
        end
    endgenerate

    //========================================================================
    // Clock and Reset Selection
    //========================================================================

    // CDC_ENABLE is a parameter, so this is a constant select the tools fold
    // away - not a runtime clock mux. Written as a ternary rather than a
    // generate so pit_clk/pit_resetn stay referenced in BOTH configurations
    // (a generate leaves them dangling at CDC_ENABLE = 0, which lint reports
    // as unused top-level inputs).
    wire w_timer_clk   = CDC_ENABLE ? pit_clk    : pclk;
    wire w_timer_rst_n = CDC_ENABLE ? pit_resetn : presetn;

    //========================================================================
    // Configuration Register Interface
    //========================================================================

    wire        w_pit_enable;
    wire        w_clock_select;
    wire        w_bcd;
    wire [2:0]  w_mode;
    wire [1:0]  w_rw_mode;
    wire [1:0]  w_counter_select;
    wire        w_control_wr;
    wire [7:0]  w_counter0_status;
    wire [7:0]  w_counter1_status;
    wire [7:0]  w_counter2_status;
    wire [15:0] w_counter0_reg_out;
    wire [15:0] w_counter1_reg_out;
    wire [15:0] w_counter2_reg_out;
    wire [15:0] w_counter0_reg_in;
    wire [15:0] w_counter1_reg_in;
    wire [15:0] w_counter2_reg_in;
    wire        w_counter0_reg_wr;
    wire        w_counter1_reg_wr;
    wire        w_counter2_reg_wr;
    wire        w_counter0_reg_rd;
    wire        w_counter1_reg_rd;
    wire        w_counter2_reg_rd;

    pit_config_regs u_config_regs (
        // Clock and Reset - the counting domain, same selection as the core
        .clk                   (w_timer_clk),
        .rst_n                 (w_timer_rst_n),

        // CMD/RSP interface
        .cmd_valid             (w_cmd_valid),
        .cmd_ready             (w_cmd_ready),
        .cmd_pwrite            (w_cmd_pwrite),
        .cmd_paddr             (w_cmd_paddr),
        .cmd_pwdata            (w_cmd_pwdata),
        .cmd_pstrb             (w_cmd_pstrb),

        .rsp_valid             (w_rsp_valid),
        .rsp_ready             (w_rsp_ready),
        .rsp_prdata            (w_rsp_prdata),
        .rsp_pslverr           (w_rsp_pslverr),

        // PIT Core Interface
        .pit_enable            (w_pit_enable),
        .clock_select          (w_clock_select),

        .control_wr            (w_control_wr),
        .bcd                   (w_bcd),
        .mode                  (w_mode),
        .rw_mode               (w_rw_mode),
        .counter_select        (w_counter_select),

        .counter0_data_wr      (w_counter0_reg_wr),
        .counter0_data_rd      (w_counter0_reg_rd),
        .counter0_data         (w_counter0_reg_in),
        .counter0_readback     (w_counter0_reg_out),
        .counter1_data_wr      (w_counter1_reg_wr),
        .counter1_data_rd      (w_counter1_reg_rd),
        .counter1_data         (w_counter1_reg_in),
        .counter1_readback     (w_counter1_reg_out),
        .counter2_data_wr      (w_counter2_reg_wr),
        .counter2_data_rd      (w_counter2_reg_rd),
        .counter2_data         (w_counter2_reg_in),
        .counter2_readback     (w_counter2_reg_out),

        .counter0_status       (w_counter0_status),
        .counter1_status       (w_counter1_status),
        .counter2_status       (w_counter2_status)
    );

    //========================================================================
    // PIT Core (Counter Array)
    //========================================================================

    pit_core #(
        .NUM_COUNTERS(NUM_COUNTERS),
        .SYNC_STAGES (SYNC_STAGES)
    ) u_pit_core (
        .clk                 (w_timer_clk),
        .rst_n               (w_timer_rst_n),
        // Configuration
        .cfg_pit_enable      (w_pit_enable),
        .cfg_clock_select    (w_clock_select),
        .cfg_bcd             (w_bcd),
        .cfg_mode            (w_mode),
        .cfg_rw_mode         (w_rw_mode),
        .cfg_counter_select  (w_counter_select),
        .cfg_control_wr      (w_control_wr),
        // Counter data
        .counter0_reg_in     (w_counter0_reg_in),
        .counter1_reg_in     (w_counter1_reg_in),
        .counter2_reg_in     (w_counter2_reg_in),
        .counter0_reg_wr     (w_counter0_reg_wr),
        .counter1_reg_wr     (w_counter1_reg_wr),
        .counter2_reg_wr     (w_counter2_reg_wr),
        .counter0_reg_rd     (w_counter0_reg_rd),
        .counter1_reg_rd     (w_counter1_reg_rd),
        .counter2_reg_rd     (w_counter2_reg_rd),
        .counter0_reg_out    (w_counter0_reg_out),
        .counter1_reg_out    (w_counter1_reg_out),
        .counter2_reg_out    (w_counter2_reg_out),
        // Status
        .counter0_status     (w_counter0_status),
        .counter1_status     (w_counter1_status),
        .counter2_status     (w_counter2_status),
        // Hardware interface
        .i_gate              (gate_in),
        .o_out               (timer_irq)
    );

    //========================================================================
    // CDC note
    //========================================================================

    // CDC_ENABLE=1 is implemented above: apb4_slave_cdc carries the whole
    // cmd/rsp stream across pclk <-> pit_clk, and the config regs + core run
    // entirely on pit_clk, so the bus needs no per-signal crossings here.
    // CDC_ENABLE=0 (default) runs everything on pclk via apb4_slave.
    //
    // gate_in is the ONE signal that is not covered by that argument: it is a
    // pin, asynchronous to whichever clock the counters end up on. It crosses
    // in pit_core's SYNC_STAGES-deep synchronizer, unconditionally.

endmodule
