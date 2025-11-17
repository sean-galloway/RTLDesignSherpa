// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_pic_8259
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
//   Layer 1: apb_pic_8259 (this module) - APB interface
//   Layer 2: pic_8259_config_regs - Register wrapper with edge detection
//   Layer 3: pic_8259_core - Interrupt controller logic
//
// Register Map (32-bit aligned):
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

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb_pic_8259 (
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
    input  wire [7:0]              irq_in,         // IRQ inputs (IRQ0-7)
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

    apb_slave #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32),
        .STRB_WIDTH(4),
        .PROT_WIDTH(3)
    ) u_apb_slave (
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

    wire        w_pic_enable;
    wire        w_init_mode;
    wire        w_auto_reset_init;
    wire        w_ic4;
    wire        w_sngl;
    wire        w_ltim;
    wire [7:0]  w_vector_base;
    wire [7:0]  w_cascade;
    wire        w_aeoi;
    wire [1:0]  w_buf_mode;
    wire        w_sfnm;
    wire        w_icw1_wr;
    wire        w_icw2_wr;
    wire        w_icw3_wr;
    wire        w_icw4_wr;
    wire        w_ocw2_wr;
    wire        w_ocw3_wr;
    wire [2:0]  w_ocw2_irq_level;
    wire [2:0]  w_ocw2_eoi_cmd;
    wire [1:0]  w_ocw3_read_reg_cmd;
    wire        w_ocw3_poll_cmd;
    wire [1:0]  w_ocw3_smm_cmd;
    wire        w_imr_reg_wr;
    wire [7:0]  w_imr_reg_out;
    wire [7:0]  w_imr_reg_in;
    wire [7:0]  w_irr;
    wire [7:0]  w_isr;
    wire        w_init_complete;
    wire [2:0]  w_icw_step;
    wire        w_int_output;
    wire [2:0]  w_highest_priority;

    //========================================================================
    // Configuration Registers Module
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

        // PIC Core Interface
        .pic_enable            (w_pic_enable),
        .init_mode             (w_init_mode),
        .auto_reset_init       (w_auto_reset_init),
        .ic4                   (w_ic4),
        .sngl                  (w_sngl),
        .ltim                  (w_ltim),
        .vector_base           (w_vector_base),
        .cascade               (w_cascade),
        .aeoi                  (w_aeoi),
        .buf_mode              (w_buf_mode),
        .sfnm                  (w_sfnm),
        .icw1_wr               (w_icw1_wr),
        .icw2_wr               (w_icw2_wr),
        .icw3_wr               (w_icw3_wr),
        .icw4_wr               (w_icw4_wr),
        .ocw2_wr               (w_ocw2_wr),
        .ocw3_wr               (w_ocw3_wr),
        .ocw2_irq_level        (w_ocw2_irq_level),
        .ocw2_eoi_cmd          (w_ocw2_eoi_cmd),
        .ocw3_read_reg_cmd     (w_ocw3_read_reg_cmd),
        .ocw3_poll_cmd         (w_ocw3_poll_cmd),
        .ocw3_smm_cmd          (w_ocw3_smm_cmd),
        .imr_reg_wr            (w_imr_reg_wr),
        .imr_reg_out           (w_imr_reg_out),
        .imr_reg_in            (w_imr_reg_in),
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

    wire [7:0] w_int_vector;  // For future INTA cycle support

    pic_8259_core u_pic_core (
        .clk                 (pclk),
        .rst                 (~presetn),  // Convert active-low to active-high
        
        // Configuration
        .cfg_pic_enable      (w_pic_enable),
        .cfg_init_mode       (w_init_mode),
        .cfg_auto_reset_init (w_auto_reset_init),
        .cfg_ic4             (w_ic4),
        .cfg_sngl            (w_sngl),
        .cfg_ltim            (w_ltim),
        .cfg_vector_base     (w_vector_base),
        .cfg_cascade         (w_cascade),
        .cfg_aeoi            (w_aeoi),
        .cfg_buf_mode        (w_buf_mode),
        .cfg_sfnm            (w_sfnm),
        
        // ICW/OCW write strobes
        .icw1_wr             (w_icw1_wr),
        .icw2_wr             (w_icw2_wr),
        .icw3_wr             (w_icw3_wr),
        .icw4_wr             (w_icw4_wr),
        .ocw2_wr             (w_ocw2_wr),
        .ocw3_wr             (w_ocw3_wr),
        
        // OCW2/OCW3 commands
        .ocw2_irq_level      (w_ocw2_irq_level),
        .ocw2_eoi_cmd        (w_ocw2_eoi_cmd),
        .ocw3_read_reg_cmd   (w_ocw3_read_reg_cmd),
        .ocw3_poll_cmd       (w_ocw3_poll_cmd),
        .ocw3_smm_cmd        (w_ocw3_smm_cmd),
        
        // IMR bidirectional
        .imr_reg_in          (w_imr_reg_out),
        .imr_reg_wr          (w_imr_reg_wr),
        .imr_reg_out         (w_imr_reg_in),
        
        // Status outputs
        .irr_out             (w_irr),
        .isr_out             (w_isr),
        .init_complete       (w_init_complete),
        .icw_step            (w_icw_step),
        .int_output          (w_int_output),
        .highest_priority    (w_highest_priority),
        
        // Hardware interface
        .irq_in              (irq_in),
        .int_vector          (w_int_vector)
    );

    //========================================================================
    // Output Assignment
    //========================================================================

    assign int_out = w_int_output;

endmodule
