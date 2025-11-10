// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_hpet
// Purpose: Apb Hpet module
//
// Documentation: projects/components/apb_hpet.sv/PRD.md
// Subsystem: apb_hpet.sv
//
// Author: sean galloway
// Created: 2025-10-18

/**
 * ============================================================================
 * APB HPET Top Level Integration
 * ============================================================================
 *
 * DESCRIPTION:
 *   Top-level module that integrates APB slave with CDC, configuration
 *   registers, and HPET timer core. Provides complete HPET functionality
 *   with dual clock domain support.
 *
 * ARCHITECTURE:
 *   - APB Slave CDC: Handles low-frequency APB interface with clock crossing
 *   - Config Registers: High-speed register bank for HPET configuration
 *   - HPET Core: High-speed timer logic with precise timing
 *
 * CLOCK DOMAINS:
 *   - pclk: Low frequency APB interface clock
 *   - hpet_clk: High frequency timer clock
 *
 * REGISTER MAP AND BIT FIELDS:
 *
 *   Global Registers:
 *   ----------------
 *   0x000: HPET_ID - Capabilities and ID (Read-Only)
 *          [31:24] Vendor ID (parameterized, default 0x01)
 *          [23:16] Revision ID (parameterized, default 0x01)
 *          [15:13] Reserved
 *          [12:8]  Number of Timers - 1 (e.g., 0x01 for 2 timers)
 *          [7]     64-bit Counter Capable (1=yes, 0=no)
 *          [6]     Reserved
 *          [5]     Legacy Replacement Capable (1=yes, 0=no)
 *          [4:0]   Reserved
 *
 *   0x004: HPET_CONFIG - Global Configuration (Read/Write)
 *          [31:2]  Reserved
 *          [1]     Legacy Replacement Enable (1=enable, 0=disable)
 *          [0]     HPET Enable (1=enable counter, 0=disable counter)
 *
 *   0x008: HPET_STATUS - Interrupt Status (Read/Write-to-Clear)
 *          [31:NUM_TIMERS] Reserved
 *          [NUM_TIMERS-1:0] Timer Interrupt Status (1=interrupt pending, write 1 to clear)
 *                           Bit n corresponds to Timer n
 *
 *   0x00C: RESERVED - Reserved register (Read-Only)
 *          [31:0]  Reserved, returns 0x00000000
 *
 *   0x010: HPET_COUNTER_LO - Main Counter Low 32 bits (Read/Write)
 *          [31:0]  Lower 32 bits of 64-bit main counter
 *
 *   0x014: HPET_COUNTER_HI - Main Counter High 32 bits (Read/Write)
 *          [31:0]  Upper 32 bits of 64-bit main counter
 *
 *   Timer Registers (32-byte blocks starting at 0x100):
 *   ---------------------------------------------------------------
 *   Each timer occupies 32 bytes (0x20) of address space:
 *
 *   Timer 0: 0x100-0x11F
 *      0x100: TIMER0_CONFIG  - Timer 0 Configuration (Read/Write)
 *      0x104: TIMER0_COMP_LO - Timer 0 Comparator Low 32 bits (Read/Write)
 *      0x108: TIMER0_COMP_HI - Timer 0 Comparator High 32 bits (Read/Write)
 *      0x10C-0x11F: Reserved for Timer 0 expansion
 *
 *   Timer 1: 0x120-0x13F
 *      0x120: TIMER1_CONFIG  - Timer 1 Configuration (Read/Write)
 *      0x124: TIMER1_COMP_LO - Timer 1 Comparator Low 32 bits (Read/Write)
 *      0x128: TIMER1_COMP_HI - Timer 1 Comparator High 32 bits (Read/Write)
 *      0x12C-0x13F: Reserved for Timer 1 expansion
 *
 *   Timer 2: 0x140-0x15F (if NUM_TIMERS >= 3)
 *      0x140: TIMER2_CONFIG
 *      0x144: TIMER2_COMP_LO
 *      0x148: TIMER2_COMP_HI
 *      0x14C-0x15F: Reserved
 *
 *   Timer 3: 0x160-0x17F (if NUM_TIMERS >= 4)
 *   Timer 4: 0x180-0x19F (if NUM_TIMERS >= 5)
 *   Timer 5: 0x1A0-0x1BF (if NUM_TIMERS >= 6)
 *   Timer 6: 0x1C0-0x1DF (if NUM_TIMERS >= 7)
 *   Timer 7: 0x1E0-0x1FF (if NUM_TIMERS = 8)
 *
 *   Timer Register Bit Fields:
 *   ---------------------------
 *   TIMER_CONFIG Register:
 *          [31:7]  Reserved
 *          [6]     Value Set Mode (1=comparator acts as accumulator, 0=normal)
 *          [5]     Size (1=64-bit comparison, 0=32-bit comparison)
 *          [4]     Type (1=periodic mode, 0=one-shot mode)
 *          [3]     Interrupt Enable (1=enable interrupt, 0=disable interrupt)
 *          [2]     Timer Enable (1=enable timer, 0=disable timer)
 *          [1:0]   Reserved
 *
 *   TIMER_COMP_LO Register:
 *          [31:0]  Lower 32 bits of timer comparator value
 *                  In one-shot mode: fires when counter >= comparator
 *                  In periodic mode: initial compare value and period
 *
 *   TIMER_COMP_HI Register:
 *          [31:0]  Upper 32 bits of timer comparator value
 *                  Only used when Size bit is set for 64-bit comparison
 *
 * ADDRESS SPACE LAYOUT (Fixed 12-bit addressing for all configurations):
 *
 *   Address Range    | Description
 *   -----------------|--------------------------------------------------
 *   0x000-0x0FF      | Global registers (ID, Config, Status, Counter)
 *   0x100-0x11F      | Timer 0 registers
 *   0x120-0x13F      | Timer 1 registers
 *   0x140-0x15F      | Timer 2 registers (if NUM_TIMERS >= 3)
 *   0x160-0x17F      | Timer 3 registers (if NUM_TIMERS >= 4)
 *   0x180-0x19F      | Timer 4 registers (if NUM_TIMERS >= 5)
 *   0x1A0-0x1BF      | Timer 5 registers (if NUM_TIMERS >= 6)
 *   0x1C0-0x1DF      | Timer 6 registers (if NUM_TIMERS >= 7)
 *   0x1E0-0x1FF      | Timer 7 registers (if NUM_TIMERS = 8)
 *   0x200-0xFFF      | Reserved for future expansion
 *
 * NOTES:
 *   - Fixed 12-bit address width supports up to 4KB address space
 *   - Timer spacing of 32 bytes allows for future expansion
 *   - All configurations (2-8 timers) use the same address map
 *   - Unused timer addresses return 0 on reads, writes are ignored
 * ============================================================================
 */

`timescale 1ns / 1ps

/* verilator lint_off SYNCASYNCNET */
// Note: presetn and hpet_resetn connect to modules with different reset styles.
// hpet_config_regs uses async reset, peakrdl_to_cmdrsp uses sync reset.
// This is intentional - both modules are in same clock domain.
module apb_hpet #(
    parameter int VENDOR_ID = 1,
    parameter int REVISION_ID = 1,
    parameter int NUM_TIMERS = 2,
    parameter int CDC_ENABLE = 0  // 0=same clock (apb_slave), 1=different clocks (apb_slave_cdc)
)(
    // ========================================================================
    // Clock and Reset - Dual Domain
    // ========================================================================
    input  logic                    pclk,          // APB clock domain (always used for APB interface)
    input  logic                    presetn,       // APB reset (active low)
    input  logic                    hpet_clk,      // HPET clock domain (used for timer logic)
    input  logic                    hpet_resetn,   // HPET reset (active low)

    // ========================================================================
    // APB4 Slave Interface (Low Frequency Domain)
    // ========================================================================
    input  logic                    s_apb_PSEL,
    input  logic                    s_apb_PENABLE,
    output logic                    s_apb_PREADY,
    input  logic [11:0]             s_apb_PADDR,   // Fixed 12-bit addressing
    input  logic                    s_apb_PWRITE,
    input  logic [31:0]             s_apb_PWDATA,
    input  logic [3:0]              s_apb_PSTRB,
    input  logic [2:0]              s_apb_PPROT,
    output logic [31:0]             s_apb_PRDATA,
    output logic                    s_apb_PSLVERR,

    // ========================================================================
    // Timer Interrupt Outputs (High Frequency Domain)
    // ========================================================================
    output logic [NUM_TIMERS-1:0]   timer_irq
);

// ============================================================================
// CDC Command/Response Interface Signals
// ============================================================================
logic                    w_cmd_valid;
logic                    w_cmd_ready;
logic                    w_cmd_pwrite;
logic [11:0]             w_cmd_paddr;     // Fixed 12-bit addressing
logic [31:0]             w_cmd_pwdata;    // Fixed 32-bit data
logic [3:0]              w_cmd_pstrb;
logic [2:0]              w_cmd_pprot;

logic                    w_rsp_valid;
logic                    w_rsp_ready;
logic [31:0]             w_rsp_prdata;    // Fixed 32-bit data
logic                    w_rsp_pslverr;

// ============================================================================
// Configuration Register Interface Signals
// ============================================================================
logic                    w_hpet_enable;
logic                    w_legacy_replacement;
logic                    w_counter_write;
logic [63:0]             w_counter_wdata;
logic [63:0]             w_counter_rdata;
logic [NUM_TIMERS-1:0]   w_timer_enable;
logic [NUM_TIMERS-1:0]   w_timer_int_enable;
logic [NUM_TIMERS-1:0]   w_timer_type;
logic [NUM_TIMERS-1:0]   w_timer_size;
logic [NUM_TIMERS-1:0]   w_timer_value_set;
logic [NUM_TIMERS-1:0]   w_timer_comp_write;
logic [63:0]             w_timer_comp_wdata [NUM_TIMERS];  // Per-timer data bus
logic                    w_timer_comp_write_high;
logic [63:0]             w_timer_comp_rdata [NUM_TIMERS];
logic [NUM_TIMERS-1:0]   w_timer_int_status;
logic [NUM_TIMERS-1:0]   w_timer_int_clear;

// ============================================================================
// APB Slave - CDC or Non-CDC based on parameter
// ============================================================================
generate
    if (CDC_ENABLE != 0) begin : g_apb_slave_cdc
        // Clock Domain Crossing version for async clocks
        apb_slave_cdc #(
            .ADDR_WIDTH(12),
            .DATA_WIDTH(32),
            .STRB_WIDTH(4),
            .PROT_WIDTH(3),
            .DEPTH     (2)
        ) u_apb_slave_cdc (
            // APB Clock Domain
            .pclk                 (pclk),
            .presetn              (presetn),

            // HPET Clock Domain
            .aclk                 (hpet_clk),
            .aresetn              (hpet_resetn),

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

            // Command Interface (hpet_clk domain)
            .cmd_valid            (w_cmd_valid),
            .cmd_ready            (w_cmd_ready),
            .cmd_pwrite           (w_cmd_pwrite),
            .cmd_paddr            (w_cmd_paddr),
            .cmd_pwdata           (w_cmd_pwdata),
            .cmd_pstrb            (w_cmd_pstrb),
            .cmd_pprot            (w_cmd_pprot),

            // Response Interface (hpet_clk domain)
            .rsp_valid            (w_rsp_valid),
            .rsp_ready            (w_rsp_ready),
            .rsp_prdata           (w_rsp_prdata),
            .rsp_pslverr          (w_rsp_pslverr)
        );
    end else begin : g_apb_slave_no_cdc
        // Non-CDC version for same clock domain (pclk == hpet_clk)
        apb_slave #(
            .ADDR_WIDTH(12),
            .DATA_WIDTH(32),
            .STRB_WIDTH(4),
            .PROT_WIDTH(3)
        ) u_apb_slave (
            // Single clock domain (use pclk for both APB and cmd/rsp)
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
            .cmd_pprot            (w_cmd_pprot),

            // Response Interface (same pclk domain)
            .rsp_valid            (w_rsp_valid),
            .rsp_ready            (w_rsp_ready),
            .rsp_prdata           (w_rsp_prdata),
            .rsp_pslverr          (w_rsp_pslverr)
        );
    end
endgenerate

// ============================================================================
// HPET Configuration Registers
// CDC_ENABLE=0: Uses pclk (same clock as APB)
// CDC_ENABLE=1: Uses hpet_clk (async clock)
// ============================================================================
hpet_config_regs #(
    .VENDOR_ID        (VENDOR_ID),
    .REVISION_ID      (REVISION_ID),
    .NUM_TIMERS       (NUM_TIMERS)
) u_hpet_config_regs (
    // Clock and Reset - conditional based on CDC_ENABLE
    .clk               (CDC_ENABLE[0] ? hpet_clk : pclk),
    .rst_n             (CDC_ENABLE[0] ? hpet_resetn : presetn),

    // Command/Response Interface
    .cmd_valid         (w_cmd_valid),
    .cmd_ready         (w_cmd_ready),
    .cmd_pwrite        (w_cmd_pwrite),
    .cmd_paddr         (w_cmd_paddr),
    .cmd_pwdata        (w_cmd_pwdata),
    .cmd_pstrb         (w_cmd_pstrb),

    .rsp_valid         (w_rsp_valid),
    .rsp_ready         (w_rsp_ready),
    .rsp_prdata        (w_rsp_prdata),
    .rsp_pslverr       (w_rsp_pslverr),

    // HPET Core Interface
    .hpet_enable          (w_hpet_enable),
    .legacy_replacement   (w_legacy_replacement),
    .counter_write        (w_counter_write),
    .counter_wdata        (w_counter_wdata),
    .counter_rdata        (w_counter_rdata),
    .timer_enable         (w_timer_enable),
    .timer_int_enable     (w_timer_int_enable),
    .timer_type           (w_timer_type),
    .timer_size           (w_timer_size),
    .timer_value_set      (w_timer_value_set),
    .timer_comp_write     (w_timer_comp_write),
    .timer_comp_wdata     (w_timer_comp_wdata),
    .timer_comp_write_high(w_timer_comp_write_high),
    .timer_comp_rdata     (w_timer_comp_rdata),
    .timer_int_status     (w_timer_int_status),
    .timer_int_clear      (w_timer_int_clear)
);

// ============================================================================
// HPET Timer Core
// CDC_ENABLE=0: Uses pclk (same clock as APB)
// CDC_ENABLE=1: Uses hpet_clk (async clock, high speed for precise timing)
// ============================================================================
hpet_core #(
    .NUM_TIMERS(NUM_TIMERS)
) u_hpet_core (
    // Clock and Reset - conditional based on CDC_ENABLE
    .clk                  (CDC_ENABLE[0] ? hpet_clk : pclk),
    .rst_n                (CDC_ENABLE[0] ? hpet_resetn : presetn),

    // Configuration Interface
    .hpet_enable          (w_hpet_enable),
    .counter_write        (w_counter_write),
    .counter_wdata        (w_counter_wdata),
    .counter_rdata        (w_counter_rdata),
    .timer_enable         (w_timer_enable),
    .timer_int_enable     (w_timer_int_enable),
    .timer_type           (w_timer_type),
    .timer_size           (w_timer_size),
    .timer_comp_write     (w_timer_comp_write),
    .timer_comp_wdata     (w_timer_comp_wdata),
    .timer_comp_write_high(w_timer_comp_write_high),
    .timer_comp_rdata     (w_timer_comp_rdata),

    // Interrupt Interface
    .timer_int_status     (w_timer_int_status),
    .timer_int_clear      (w_timer_int_clear),
    .timer_irq            (timer_irq)
);

/* verilator lint_on SYNCASYNCNET */
endmodule : apb_hpet
