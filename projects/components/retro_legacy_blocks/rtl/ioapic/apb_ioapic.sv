// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_ioapic
// Purpose: APB IOAPIC Top Level Integration
//
// Documentation: projects/components/retro_legacy_blocks/rtl/ioapic/README.md
// Subsystem: ioapic
//
// Author: sean galloway
// Created: 2025-11-16

/**
 * ============================================================================
 * APB IOAPIC Top Level Integration  
 * ============================================================================
 *
 * DESCRIPTION:
 *   Top-level module that integrates APB slave with CDC, configuration
 *   registers, and IOAPIC core. Provides complete I/O APIC functionality
 *   with Intel 82093AA compatibility.
 *
 * ARCHITECTURE:
 *   - APB Slave CDC: Handles APB interface with optional clock crossing
 *   - Config Registers: Implements indirect register access (IOREGSEL/IOWIN)
 *   - IOAPIC Core: Interrupt routing and arbitration logic
 *
 * CLOCK DOMAINS:
 *   - pclk: APB interface clock
 *   - ioapic_clk: IOAPIC controller clock
 *   - CDC_ENABLE=0: Single clock (pclk == ioapic_clk, no CDC)
 *   - CDC_ENABLE=1: Dual clock (pclk != ioapic_clk, CDC enabled)
 *
 * REGISTER ACCESS METHOD (Intel IOAPIC Indirect Access):
 *   1. Write register offset to IOREGSEL (APB address 0x00)
 *   2. Read/write data via IOWIN (APB address 0x04)
 *
 * REGISTER MAP:
 *   APB Direct Access:
 *     0x00: IOREGSEL - Register select for indirect access
 *     0x04: IOWIN    - Data window for selected register
 *
 *   Internal Registers (via IOREGSEL/IOWIN):
 *     0x00: IOAPICID  - IOAPIC identification
 *     0x01: IOAPICVER - Version and capabilities
 *     0x02: IOAPICARB - Arbitration priority
 *     0x10-0x3F: IOREDTBL - Redirection table (24 IRQs × 2 regs)
 *
 * INTERRUPT FEATURES:
 *   - 24 IRQ inputs with programmable redirection
 *   - Edge and level trigger modes
 *   - Active high/low polarity
 *   - Interrupt masking per IRQ
 *   - Delivery mode support (Fixed for MVP)
 *   - Remote IRR for level-triggered interrupts
 *   - Priority-based arbitration
 *
 * ============================================================================
 */

`timescale 1ns / 1ps

/* verilator lint_off SYNCASYNCNET */
// Note: presetn and ioapic_resetn connect to modules with different reset styles.
// ioapic_config_regs uses async reset, peakrdl_to_cmdrsp uses sync reset.
// This is intentional - both modules are in same clock domain.
module apb_ioapic #(
    parameter int NUM_IRQS = 24,       // Number of IRQ inputs (typically 24)
    parameter int CDC_ENABLE = 0       // 0=same clock (apb_slave), 1=different clocks (apb_slave_cdc)
)(
    // ========================================================================
    // Clock and Reset - Dual Domain
    // ========================================================================
    input  logic                    pclk,          // APB clock domain
    input  logic                    presetn,       // APB reset (active low)
    input  logic                    ioapic_clk,    // IOAPIC clock domain
    input  logic                    ioapic_resetn, // IOAPIC reset (active low)

    // ========================================================================
    // APB4 Slave Interface (APB Clock Domain)
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
    // External Interrupt Interfaces (IOAPIC Clock Domain)
    // ========================================================================
    
    // IRQ inputs from system (24 interrupt sources)
    input  logic [NUM_IRQS-1:0]     irq_in,
    
    // Interrupt output to CPU/LAPIC
    output logic                    irq_out_valid,      // Interrupt delivery request
    output logic [7:0]              irq_out_vector,     // Vector to deliver
    output logic [7:0]              irq_out_dest,       // Destination APIC ID
    output logic [2:0]              irq_out_deliv_mode, // Delivery mode
    input  logic                    irq_out_ready,      // CPU acknowledge
    
    // EOI (End of Interrupt) from CPU
    input  logic                    eoi_in,             // EOI strobe
    input  logic [7:0]              eoi_vector          // Vector being EOI'd
);

    // ========================================================================
    // CDC Command/Response Interface Signals
    // ========================================================================
    logic                    w_cmd_valid;
    logic                    w_cmd_ready;
    logic                    w_cmd_pwrite;
    logic [11:0]             w_cmd_paddr;
    logic [31:0]             w_cmd_pwdata;
    logic [3:0]              w_cmd_pstrb;
    logic [2:0]              w_cmd_pprot;

    logic                    w_rsp_valid;
    logic                    w_rsp_ready;
    logic [31:0]             w_rsp_prdata;
    logic                    w_rsp_pslverr;

    // ========================================================================
    // Configuration Interface Signals (per IRQ arrays)
    // ========================================================================
    logic [7:0]  w_cfg_vector       [NUM_IRQS];
    logic [2:0]  w_cfg_deliv_mode   [NUM_IRQS];
    logic        w_cfg_dest_mode    [NUM_IRQS];
    logic        w_cfg_polarity     [NUM_IRQS];
    logic        w_cfg_trigger_mode [NUM_IRQS];
    logic        w_cfg_mask         [NUM_IRQS];
    logic [7:0]  w_cfg_destination  [NUM_IRQS];
    logic [3:0]  w_cfg_ioapic_id;

    // Status signals from core
    logic        w_status_deliv_status [NUM_IRQS];
    logic        w_status_remote_irr   [NUM_IRQS];
    logic [3:0]  w_status_arb_id;

    // EOI signals
    logic        w_eoi_out;
    logic [7:0]  w_eoi_vector_out;

    // ========================================================================
    // APB Slave - CDC or Non-CDC based on parameter
    // ========================================================================
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

                // IOAPIC Clock Domain
                .aclk                 (ioapic_clk),
                .aresetn              (ioapic_resetn),

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

                // Command Interface (ioapic_clk domain)
                .cmd_valid            (w_cmd_valid),
                .cmd_ready            (w_cmd_ready),
                .cmd_pwrite           (w_cmd_pwrite),
                .cmd_paddr            (w_cmd_paddr),
                .cmd_pwdata           (w_cmd_pwdata),
                .cmd_pstrb            (w_cmd_pstrb),
                .cmd_pprot            (w_cmd_pprot),

                // Response Interface (ioapic_clk domain)
                .rsp_valid            (w_rsp_valid),
                .rsp_ready            (w_rsp_ready),
                .rsp_prdata           (w_rsp_prdata),
                .rsp_pslverr          (w_rsp_pslverr)
            );
        end else begin : g_apb_slave_no_cdc
            // Non-CDC version for same clock domain (pclk == ioapic_clk)
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

    // ========================================================================
    // IOAPIC Configuration Registers
    // CDC_ENABLE=0: Uses pclk (same clock as APB)
    // CDC_ENABLE=1: Uses ioapic_clk (async clock)
    // ========================================================================
    ioapic_config_regs #(
        .NUM_IRQS        (NUM_IRQS)
    ) u_ioapic_config_regs (
        // Clock and Reset - conditional based on CDC_ENABLE
        .clk               (CDC_ENABLE[0] ? ioapic_clk : pclk),
        .rst_n             (CDC_ENABLE[0] ? ioapic_resetn : presetn),

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

        // Configuration outputs to core (per IRQ)
        .cfg_vector        (w_cfg_vector),
        .cfg_deliv_mode    (w_cfg_deliv_mode),
        .cfg_dest_mode     (w_cfg_dest_mode),
        .cfg_polarity      (w_cfg_polarity),
        .cfg_trigger_mode  (w_cfg_trigger_mode),
        .cfg_mask          (w_cfg_mask),
        .cfg_destination   (w_cfg_destination),
        .cfg_ioapic_id     (w_cfg_ioapic_id),

        // Status inputs from core
        .status_deliv_status(w_status_deliv_status),
        .status_remote_irr  (w_status_remote_irr),
        .status_arb_id      (w_status_arb_id),

        // EOI interface
        .eoi_out           (w_eoi_out),
        .eoi_vector_out    (w_eoi_vector_out),
        .eoi_in            (eoi_in),
        .eoi_vector_in     (eoi_vector)
    );

    // ========================================================================
    // IOAPIC Core Logic
    // CDC_ENABLE=0: Uses pclk (same clock as APB)
    // CDC_ENABLE=1: Uses ioapic_clk (async clock)
    // ========================================================================
    ioapic_core #(
        .NUM_IRQS(NUM_IRQS)
    ) u_ioapic_core (
        // Clock and Reset - conditional based on CDC_ENABLE
        .clk                  (CDC_ENABLE[0] ? ioapic_clk : pclk),
        .rst_n                (CDC_ENABLE[0] ? ioapic_resetn : presetn),

        // Configuration inputs (per IRQ)
        .cfg_vector           (w_cfg_vector),
        .cfg_deliv_mode       (w_cfg_deliv_mode),
        .cfg_dest_mode        (w_cfg_dest_mode),
        .cfg_polarity         (w_cfg_polarity),
        .cfg_trigger_mode     (w_cfg_trigger_mode),
        .cfg_mask             (w_cfg_mask),
        .cfg_destination      (w_cfg_destination),
        .cfg_ioapic_id        (w_cfg_ioapic_id),

        // Status outputs
        .status_deliv_status  (w_status_deliv_status),
        .status_remote_irr    (w_status_remote_irr),
        .status_arb_id        (w_status_arb_id),

        // External IRQ inputs
        .irq_in               (irq_in),

        // Interrupt output to CPU
        .irq_out_valid        (irq_out_valid),
        .irq_out_vector       (irq_out_vector),
        .irq_out_dest         (irq_out_dest),
        .irq_out_deliv_mode   (irq_out_deliv_mode),
        .irq_out_ready        (irq_out_ready),

        // EOI input from CPU
        .eoi_in               (w_eoi_out),
        .eoi_vector           (w_eoi_vector_out)
    );

/* verilator lint_on SYNCASYNCNET */
endmodule : apb_ioapic
