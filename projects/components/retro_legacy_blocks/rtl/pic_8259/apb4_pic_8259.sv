// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb4_pic_8259
// Purpose: APB wrapper for Intel 8259A-compatible Programmable Interrupt Controller
//
// Top-level integration module providing:
// - APB4 slave interface
// - 8 prioritized interrupt inputs (IRQ0-7)
// - Edge and level triggered modes
// - Fixed and rotating priority modes
// - Interrupt masking
// - End-of-Interrupt (EOI) handling
// - Cascade support (master/slave configuration)
// - Auto-EOI mode
//
// Follows HPET 3-layer architecture:
//   Layer 1: apb4_pic_8259 (this module) - APB interface
//   Layer 2: pic_8259_config_regs - Register wrapper with edge detection
//   Layer 3: pic_8259_core - Interrupt controller logic
//
// Parameters:
//   - SYNC_STAGES: irq_in input synchronizer depth, >= 2. Default 2.
//
// Register Map (32-bit aligned). NOTHING ELSE in the 4 KB window is decoded:
// every other address is dropped with PSLVERR (pic_8259_config_regs.sv).
//   0x000: PIC_CONFIG      - Global configuration and control
//   0x004: PIC_ICW1        - Initialization Command Word 1
//   0x008: PIC_ICW2        - Initialization Command Word 2
//   0x00C: PIC_ICW3        - Initialization Command Word 3
//   0x010: PIC_ICW4        - Initialization Command Word 4
//   0x014: PIC_OCW1        - Operation Command Word 1 (IMR)
//   0x018: PIC_OCW2        - Operation Command Word 2 (EOI, priority)
//   0x01C: PIC_OCW3        - Operation Command Word 3 (special modes)
//   0x020: PIC_IRR         - Interrupt Request Register (read-only)
//   0x024: PIC_ISR         - In-Service Register (read-only)
//   0x028: PIC_STATUS      - Status register (read-only)
//   0x02C: PIC_INTA        - Interrupt acknowledge BY READ (read-only, and
//                            reading it has side effects - see pic_8259_core.sv)
//
// Updated: 2026-09-09 - GitHub #50: PIC_INTA acknowledge-by-read, strict
//                       address decode with PSLVERR, irq_in synchronizer

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb4_pic_8259 #(
    parameter int SYNC_STAGES = 2   // irq_in input synchronizer depth, >= 2
) (
    //========================================================================
    // Clock and Reset
    //========================================================================
    input  wire                    pclk,           // APB clock
    input  wire                    presetn,        // APB reset (active low)

    //========================================================================
    // APB4 Slave Interface
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
    // Interrupt Interface
    //========================================================================
    input  wire [7:0]              irq_in,         // IRQ inputs (IRQ0-7, async)
    output wire                    int_out         // Interrupt output (INT pin)
);

    //========================================================================
    // CMD/RSP Interface Signals
    //========================================================================

    logic        w_cmd_valid;
    logic        w_cmd_ready;
    logic        w_cmd_pwrite;
    logic [11:0] w_cmd_paddr;
    logic [31:0] w_cmd_pwdata;
    logic [3:0]  w_cmd_pstrb;

    logic        w_rsp_valid;
    logic        w_rsp_ready;
    logic [31:0] w_rsp_prdata;
    logic        w_rsp_pslverr;

    //========================================================================
    // APB Slave - Convert APB to CMD/RSP Interface
    //========================================================================

    apb4_slave #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32),
        .STRB_WIDTH(4),
        .PROT_WIDTH(3)
    ) u_apb4_slave (
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

        // Command Interface
        .cmd_valid            (w_cmd_valid),
        .cmd_ready            (w_cmd_ready),
        .cmd_pwrite           (w_cmd_pwrite),
        .cmd_paddr            (w_cmd_paddr),
        .cmd_pwdata           (w_cmd_pwdata),
        .cmd_pstrb            (w_cmd_pstrb),
        .cmd_pprot            (),  // Unused

        // Response Interface
        .rsp_valid            (w_rsp_valid),
        .rsp_ready            (w_rsp_ready),
        .rsp_prdata           (w_rsp_prdata),
        .rsp_pslverr          (w_rsp_pslverr)
    );

    //========================================================================
    // Configuration Register Interface Signals
    //========================================================================

    logic        w_pic_enable;
    logic        w_init_mode;
    logic        w_ic4;
    logic        w_sngl;
    logic        w_ltim;
    logic [7:0]  w_vector_base;
    logic        w_aeoi;
    logic [7:0]  w_imr;
    logic        w_icw1_wr;
    logic        w_icw2_wr;
    logic        w_icw3_wr;
    logic        w_icw4_wr;
    logic        w_ocw2_wr;
    logic        w_ocw3_wr;
    logic [2:0]  w_ocw2_irq_level;
    logic [2:0]  w_ocw2_eoi_cmd;
    logic [1:0]  w_ocw3_smm_cmd;
    logic        w_inta_ack;
    logic [7:0]  w_inta_vector;
    logic        w_inta_valid;
    logic [7:0]  w_irr;
    logic [7:0]  w_isr;
    logic        w_init_complete;
    logic [2:0]  w_icw_step;
    logic        w_int_output;
    logic [2:0]  w_highest_priority;

    //========================================================================
    // Configuration Registers
    //========================================================================

    pic_8259_config_regs u_config_regs (
        .clk                   (pclk),
        .rst_n                 (presetn),

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

        // Configuration to the core
        .pic_enable            (w_pic_enable),
        .init_mode             (w_init_mode),
        .ic4                   (w_ic4),
        .sngl                  (w_sngl),
        .ltim                  (w_ltim),
        .vector_base           (w_vector_base),
        .aeoi                  (w_aeoi),
        .imr                   (w_imr),

        // Write strobes and command values
        .icw1_wr               (w_icw1_wr),
        .icw2_wr               (w_icw2_wr),
        .icw3_wr               (w_icw3_wr),
        .icw4_wr               (w_icw4_wr),
        .ocw2_wr               (w_ocw2_wr),
        .ocw3_wr               (w_ocw3_wr),
        .ocw2_irq_level        (w_ocw2_irq_level),
        .ocw2_eoi_cmd          (w_ocw2_eoi_cmd),
        .ocw3_smm_cmd          (w_ocw3_smm_cmd),

        // Acknowledge by read
        .inta_ack              (w_inta_ack),
        .inta_vector           (w_inta_vector),
        .inta_valid            (w_inta_valid),

        // Status from the core
        .irr_in                (w_irr),
        .isr_in                (w_isr),
        .init_complete         (w_init_complete),
        .icw_step              (w_icw_step),
        .int_output            (w_int_output),
        .highest_priority      (w_highest_priority)
    );

    //========================================================================
    // PIC Core (Interrupt Controller Logic)
    //========================================================================

    pic_8259_core #(
        .SYNC_STAGES         (SYNC_STAGES)
    ) u_pic_core (
        .clk                 (pclk),
        .rst_n               (presetn),

        // Configuration
        .cfg_pic_enable      (w_pic_enable),
        .cfg_init_mode       (w_init_mode),
        .cfg_ic4             (w_ic4),
        .cfg_sngl            (w_sngl),
        .cfg_ltim            (w_ltim),
        .cfg_vector_base     (w_vector_base),
        .cfg_aeoi            (w_aeoi),
        .cfg_imr             (w_imr),

        // ICW/OCW write strobes
        .icw1_wr             (w_icw1_wr),
        .icw2_wr             (w_icw2_wr),
        .icw3_wr             (w_icw3_wr),
        .icw4_wr             (w_icw4_wr),
        .ocw2_wr             (w_ocw2_wr),
        .ocw3_wr             (w_ocw3_wr),
        .ocw2_irq_level      (w_ocw2_irq_level),
        .ocw2_eoi_cmd        (w_ocw2_eoi_cmd),
        .ocw3_smm_cmd        (w_ocw3_smm_cmd),

        // Acknowledge by read
        .inta_ack            (w_inta_ack),
        .inta_vector         (w_inta_vector),
        .inta_valid          (w_inta_valid),

        // Status outputs
        .irr_out             (w_irr),
        .isr_out             (w_isr),
        .init_complete       (w_init_complete),
        .icw_step            (w_icw_step),
        .int_output          (w_int_output),
        .highest_priority    (w_highest_priority),

        // Hardware interface
        .irq_in              (irq_in)
    );

    //========================================================================
    // Output Assignment
    //========================================================================

    assign int_out = w_int_output;

endmodule
