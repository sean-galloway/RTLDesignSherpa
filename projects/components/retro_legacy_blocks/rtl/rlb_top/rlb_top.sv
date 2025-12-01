// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rlb_top
// Purpose: Top-level integration for Retro Legacy Block peripherals
//
// Description:
//   Integrates all RLB peripherals with a 1-to-10 APB crossbar providing
//   a single master connection to the external fabric.
//
// Address Map (4KB windows from BASE_ADDR 0xFEC00000):
//   0x0000 - 0x0FFF: HPET
//   0x1000 - 0x1FFF: 8259 PIC
//   0x2000 - 0x2FFF: 8254 PIT
//   0x3000 - 0x3FFF: RTC
//   0x4000 - 0x4FFF: SMBus
//   0x5000 - 0x5FFF: PM/ACPI
//   0x6000 - 0x6FFF: IOAPIC
//   0x7000 - 0x7FFF: GPIO
//   0x8000 - 0x8FFF: UART 16550
//   0x9000 - 0x9FFF: Reserved
//
// Documentation: projects/components/retro_legacy_blocks/docs/
// Created: 2025-11-30

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rlb_top #(
    // Global APB parameters
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH / 8,
    parameter logic [ADDR_WIDTH-1:0] BASE_ADDR = 32'hFEC00000,

    // HPET parameters
    parameter int HPET_VENDOR_ID  = 1,
    parameter int HPET_REVISION   = 1,
    parameter int HPET_NUM_TIMERS = 2,

    // PIT parameters
    parameter int PIT_NUM_COUNTERS = 3,

    // IOAPIC parameters
    parameter int IOAPIC_NUM_IRQS = 24,

    // GPIO parameters
    parameter int GPIO_WIDTH = 32,
    parameter int GPIO_SYNC_STAGES = 2,

    // UART parameters
    parameter int UART_FIFO_DEPTH = 16,
    parameter int UART_SYNC_STAGES = 2,

    // SMBus parameters
    parameter int SMBUS_FIFO_DEPTH = 32
) (
    // ========================================================================
    // Clock and Reset
    // ========================================================================
    input  logic                  pclk,           // APB clock (primary)
    input  logic                  presetn,        // APB reset (active low)

    // Optional peripheral-specific clocks (tie to pclk if same domain)
    input  logic                  hpet_clk,
    input  logic                  hpet_resetn,
    input  logic                  pit_clk,
    input  logic                  pit_resetn,
    input  logic                  rtc_clk,
    input  logic                  rtc_resetn,
    input  logic                  smbus_clk,
    input  logic                  smbus_resetn,
    input  logic                  pm_clk,
    input  logic                  pm_resetn,
    input  logic                  ioapic_clk,
    input  logic                  ioapic_resetn,
    input  logic                  gpio_clk,
    input  logic                  gpio_rstn,
    input  logic                  uart_clk,
    input  logic                  uart_rstn,

    // ========================================================================
    // Master APB Interface (from external master/fabric)
    // ========================================================================
    input  logic                  s_apb_PSEL,
    input  logic                  s_apb_PENABLE,
    input  logic [ADDR_WIDTH-1:0] s_apb_PADDR,
    input  logic                  s_apb_PWRITE,
    input  logic [DATA_WIDTH-1:0] s_apb_PWDATA,
    input  logic [STRB_WIDTH-1:0] s_apb_PSTRB,
    input  logic [2:0]            s_apb_PPROT,
    output logic [DATA_WIDTH-1:0] s_apb_PRDATA,
    output logic                  s_apb_PSLVERR,
    output logic                  s_apb_PREADY,

    // ========================================================================
    // HPET External Interface
    // ========================================================================
    output logic [HPET_NUM_TIMERS-1:0] hpet_timer_irq,

    // ========================================================================
    // 8259 PIC External Interface
    // ========================================================================
    input  logic [7:0]            pic_irq_in,       // IRQ inputs (IRQ0-7)
    output logic                  pic_int_out,      // Interrupt output

    // ========================================================================
    // 8254 PIT External Interface
    // ========================================================================
    input  logic [PIT_NUM_COUNTERS-1:0] pit_gate_in,
    output logic [PIT_NUM_COUNTERS-1:0] pit_timer_irq,

    // ========================================================================
    // RTC External Interface
    // ========================================================================
    output logic                  rtc_alarm_irq,
    output logic                  rtc_second_irq,

    // ========================================================================
    // SMBus External Interface
    // ========================================================================
    input  logic                  smb_scl_i,
    output logic                  smb_scl_o,
    output logic                  smb_scl_t,
    input  logic                  smb_sda_i,
    output logic                  smb_sda_o,
    output logic                  smb_sda_t,
    output logic                  smb_interrupt,

    // ========================================================================
    // PM/ACPI External Interface
    // ========================================================================
    input  logic [31:0]           pm_gpe_events,
    input  logic                  pm_power_button_n,
    input  logic                  pm_sleep_button_n,
    input  logic                  pm_rtc_alarm,
    input  logic                  pm_ext_wake_n,
    output logic [31:0]           pm_clock_gate_en,
    output logic [7:0]            pm_power_domain_en,
    output logic                  pm_sys_reset_req,
    output logic                  pm_periph_reset_req,
    output logic                  pm_interrupt,

    // ========================================================================
    // IOAPIC External Interface
    // ========================================================================
    input  logic [IOAPIC_NUM_IRQS-1:0] ioapic_irq_in,
    output logic                  ioapic_irq_out_valid,
    output logic [7:0]            ioapic_irq_out_vector,
    output logic [7:0]            ioapic_irq_out_dest,
    output logic [2:0]            ioapic_irq_out_deliv_mode,
    input  logic                  ioapic_irq_out_ready,
    input  logic                  ioapic_eoi_in,
    input  logic [7:0]            ioapic_eoi_vector,

    // ========================================================================
    // GPIO External Interface
    // ========================================================================
    input  logic [GPIO_WIDTH-1:0] gpio_in,
    output logic [GPIO_WIDTH-1:0] gpio_out,
    output logic [GPIO_WIDTH-1:0] gpio_oe,
    output logic                  gpio_irq,

    // ========================================================================
    // UART 16550 External Interface
    // ========================================================================
    input  logic                  uart_rx,
    output logic                  uart_tx,
    input  logic                  uart_cts_n,
    input  logic                  uart_dsr_n,
    input  logic                  uart_ri_n,
    input  logic                  uart_dcd_n,
    output logic                  uart_dtr_n,
    output logic                  uart_rts_n,
    output logic                  uart_out1_n,
    output logic                  uart_out2_n,
    output logic                  uart_irq
);

    // ========================================================================
    // Internal APB Connections (crossbar to peripherals)
    // ========================================================================

    // HPET APB
    logic        hpet_apb_PSEL;
    logic        hpet_apb_PENABLE;
    logic [11:0] hpet_apb_PADDR;
    logic        hpet_apb_PWRITE;
    logic [31:0] hpet_apb_PWDATA;
    logic [3:0]  hpet_apb_PSTRB;
    logic [2:0]  hpet_apb_PPROT;
    logic [31:0] hpet_apb_PRDATA;
    logic        hpet_apb_PSLVERR;
    logic        hpet_apb_PREADY;

    // PIC APB
    logic        pic_apb_PSEL;
    logic        pic_apb_PENABLE;
    logic [11:0] pic_apb_PADDR;
    logic        pic_apb_PWRITE;
    logic [31:0] pic_apb_PWDATA;
    logic [3:0]  pic_apb_PSTRB;
    logic [2:0]  pic_apb_PPROT;
    logic [31:0] pic_apb_PRDATA;
    logic        pic_apb_PSLVERR;
    logic        pic_apb_PREADY;

    // PIT APB
    logic        pit_apb_PSEL;
    logic        pit_apb_PENABLE;
    logic [11:0] pit_apb_PADDR;
    logic        pit_apb_PWRITE;
    logic [31:0] pit_apb_PWDATA;
    logic [3:0]  pit_apb_PSTRB;
    logic [2:0]  pit_apb_PPROT;
    logic [31:0] pit_apb_PRDATA;
    logic        pit_apb_PSLVERR;
    logic        pit_apb_PREADY;

    // RTC APB
    logic        rtc_apb_PSEL;
    logic        rtc_apb_PENABLE;
    logic [11:0] rtc_apb_PADDR;
    logic        rtc_apb_PWRITE;
    logic [31:0] rtc_apb_PWDATA;
    logic [3:0]  rtc_apb_PSTRB;
    logic [2:0]  rtc_apb_PPROT;
    logic [31:0] rtc_apb_PRDATA;
    logic        rtc_apb_PSLVERR;
    logic        rtc_apb_PREADY;

    // SMBus APB
    logic        smbus_apb_PSEL;
    logic        smbus_apb_PENABLE;
    logic [11:0] smbus_apb_PADDR;
    logic        smbus_apb_PWRITE;
    logic [31:0] smbus_apb_PWDATA;
    logic [3:0]  smbus_apb_PSTRB;
    logic [2:0]  smbus_apb_PPROT;
    logic [31:0] smbus_apb_PRDATA;
    logic        smbus_apb_PSLVERR;
    logic        smbus_apb_PREADY;

    // PM/ACPI APB
    logic        pm_apb_PSEL;
    logic        pm_apb_PENABLE;
    logic [11:0] pm_apb_PADDR;
    logic        pm_apb_PWRITE;
    logic [31:0] pm_apb_PWDATA;
    logic [3:0]  pm_apb_PSTRB;
    logic [2:0]  pm_apb_PPROT;
    logic [31:0] pm_apb_PRDATA;
    logic        pm_apb_PSLVERR;
    logic        pm_apb_PREADY;

    // IOAPIC APB
    logic        ioapic_apb_PSEL;
    logic        ioapic_apb_PENABLE;
    logic [11:0] ioapic_apb_PADDR;
    logic        ioapic_apb_PWRITE;
    logic [31:0] ioapic_apb_PWDATA;
    logic [3:0]  ioapic_apb_PSTRB;
    logic [2:0]  ioapic_apb_PPROT;
    logic [31:0] ioapic_apb_PRDATA;
    logic        ioapic_apb_PSLVERR;
    logic        ioapic_apb_PREADY;

    // GPIO APB
    logic        gpio_apb_PSEL;
    logic        gpio_apb_PENABLE;
    logic [11:0] gpio_apb_PADDR;
    logic        gpio_apb_PWRITE;
    logic [31:0] gpio_apb_PWDATA;
    logic [3:0]  gpio_apb_PSTRB;
    logic [2:0]  gpio_apb_PPROT;
    logic [31:0] gpio_apb_PRDATA;
    logic        gpio_apb_PSLVERR;
    logic        gpio_apb_PREADY;

    // UART APB
    logic        uart_apb_PSEL;
    logic        uart_apb_PENABLE;
    logic [11:0] uart_apb_PADDR;
    logic        uart_apb_PWRITE;
    logic [31:0] uart_apb_PWDATA;
    logic [3:0]  uart_apb_PSTRB;
    logic [2:0]  uart_apb_PPROT;
    logic [31:0] uart_apb_PRDATA;
    logic        uart_apb_PSLVERR;
    logic        uart_apb_PREADY;

    // Reserved slot APB (tie off)
    logic        rsvd_apb_PSEL;
    logic        rsvd_apb_PENABLE;
    logic [11:0] rsvd_apb_PADDR;
    logic        rsvd_apb_PWRITE;
    logic [31:0] rsvd_apb_PWDATA;
    logic [3:0]  rsvd_apb_PSTRB;
    logic [2:0]  rsvd_apb_PPROT;
    logic [31:0] rsvd_apb_PRDATA;
    logic        rsvd_apb_PSLVERR;
    logic        rsvd_apb_PREADY;

    // Reserved slot tie-off
    assign rsvd_apb_PRDATA  = 32'hDEADBEEF;
    assign rsvd_apb_PSLVERR = 1'b1;  // Error for reserved access
    assign rsvd_apb_PREADY  = 1'b1;

    // ========================================================================
    // APB Crossbar
    // ========================================================================
    apb_xbar_rlb_1to10 #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .BASE_ADDR  (BASE_ADDR)
    ) u_apb_xbar (
        .pclk           (pclk),
        .presetn        (presetn),

        // Master APB (from external)
        .s_apb_PSEL     (s_apb_PSEL),
        .s_apb_PENABLE  (s_apb_PENABLE),
        .s_apb_PADDR    (s_apb_PADDR),
        .s_apb_PWRITE   (s_apb_PWRITE),
        .s_apb_PWDATA   (s_apb_PWDATA),
        .s_apb_PSTRB    (s_apb_PSTRB),
        .s_apb_PPROT    (s_apb_PPROT),
        .s_apb_PRDATA   (s_apb_PRDATA),
        .s_apb_PSLVERR  (s_apb_PSLVERR),
        .s_apb_PREADY   (s_apb_PREADY),

        // Slave 0: HPET
        .hpet_apb_PSEL    (hpet_apb_PSEL),
        .hpet_apb_PENABLE (hpet_apb_PENABLE),
        .hpet_apb_PADDR   (hpet_apb_PADDR),
        .hpet_apb_PWRITE  (hpet_apb_PWRITE),
        .hpet_apb_PWDATA  (hpet_apb_PWDATA),
        .hpet_apb_PSTRB   (hpet_apb_PSTRB),
        .hpet_apb_PPROT   (hpet_apb_PPROT),
        .hpet_apb_PRDATA  (hpet_apb_PRDATA),
        .hpet_apb_PSLVERR (hpet_apb_PSLVERR),
        .hpet_apb_PREADY  (hpet_apb_PREADY),

        // Slave 1: 8259 PIC
        .pic_apb_PSEL    (pic_apb_PSEL),
        .pic_apb_PENABLE (pic_apb_PENABLE),
        .pic_apb_PADDR   (pic_apb_PADDR),
        .pic_apb_PWRITE  (pic_apb_PWRITE),
        .pic_apb_PWDATA  (pic_apb_PWDATA),
        .pic_apb_PSTRB   (pic_apb_PSTRB),
        .pic_apb_PPROT   (pic_apb_PPROT),
        .pic_apb_PRDATA  (pic_apb_PRDATA),
        .pic_apb_PSLVERR (pic_apb_PSLVERR),
        .pic_apb_PREADY  (pic_apb_PREADY),

        // Slave 2: 8254 PIT
        .pit_apb_PSEL    (pit_apb_PSEL),
        .pit_apb_PENABLE (pit_apb_PENABLE),
        .pit_apb_PADDR   (pit_apb_PADDR),
        .pit_apb_PWRITE  (pit_apb_PWRITE),
        .pit_apb_PWDATA  (pit_apb_PWDATA),
        .pit_apb_PSTRB   (pit_apb_PSTRB),
        .pit_apb_PPROT   (pit_apb_PPROT),
        .pit_apb_PRDATA  (pit_apb_PRDATA),
        .pit_apb_PSLVERR (pit_apb_PSLVERR),
        .pit_apb_PREADY  (pit_apb_PREADY),

        // Slave 3: RTC
        .rtc_apb_PSEL    (rtc_apb_PSEL),
        .rtc_apb_PENABLE (rtc_apb_PENABLE),
        .rtc_apb_PADDR   (rtc_apb_PADDR),
        .rtc_apb_PWRITE  (rtc_apb_PWRITE),
        .rtc_apb_PWDATA  (rtc_apb_PWDATA),
        .rtc_apb_PSTRB   (rtc_apb_PSTRB),
        .rtc_apb_PPROT   (rtc_apb_PPROT),
        .rtc_apb_PRDATA  (rtc_apb_PRDATA),
        .rtc_apb_PSLVERR (rtc_apb_PSLVERR),
        .rtc_apb_PREADY  (rtc_apb_PREADY),

        // Slave 4: SMBus
        .smbus_apb_PSEL    (smbus_apb_PSEL),
        .smbus_apb_PENABLE (smbus_apb_PENABLE),
        .smbus_apb_PADDR   (smbus_apb_PADDR),
        .smbus_apb_PWRITE  (smbus_apb_PWRITE),
        .smbus_apb_PWDATA  (smbus_apb_PWDATA),
        .smbus_apb_PSTRB   (smbus_apb_PSTRB),
        .smbus_apb_PPROT   (smbus_apb_PPROT),
        .smbus_apb_PRDATA  (smbus_apb_PRDATA),
        .smbus_apb_PSLVERR (smbus_apb_PSLVERR),
        .smbus_apb_PREADY  (smbus_apb_PREADY),

        // Slave 5: PM/ACPI
        .pm_apb_PSEL    (pm_apb_PSEL),
        .pm_apb_PENABLE (pm_apb_PENABLE),
        .pm_apb_PADDR   (pm_apb_PADDR),
        .pm_apb_PWRITE  (pm_apb_PWRITE),
        .pm_apb_PWDATA  (pm_apb_PWDATA),
        .pm_apb_PSTRB   (pm_apb_PSTRB),
        .pm_apb_PPROT   (pm_apb_PPROT),
        .pm_apb_PRDATA  (pm_apb_PRDATA),
        .pm_apb_PSLVERR (pm_apb_PSLVERR),
        .pm_apb_PREADY  (pm_apb_PREADY),

        // Slave 6: IOAPIC
        .ioapic_apb_PSEL    (ioapic_apb_PSEL),
        .ioapic_apb_PENABLE (ioapic_apb_PENABLE),
        .ioapic_apb_PADDR   (ioapic_apb_PADDR),
        .ioapic_apb_PWRITE  (ioapic_apb_PWRITE),
        .ioapic_apb_PWDATA  (ioapic_apb_PWDATA),
        .ioapic_apb_PSTRB   (ioapic_apb_PSTRB),
        .ioapic_apb_PPROT   (ioapic_apb_PPROT),
        .ioapic_apb_PRDATA  (ioapic_apb_PRDATA),
        .ioapic_apb_PSLVERR (ioapic_apb_PSLVERR),
        .ioapic_apb_PREADY  (ioapic_apb_PREADY),

        // Slave 7: GPIO
        .gpio_apb_PSEL    (gpio_apb_PSEL),
        .gpio_apb_PENABLE (gpio_apb_PENABLE),
        .gpio_apb_PADDR   (gpio_apb_PADDR),
        .gpio_apb_PWRITE  (gpio_apb_PWRITE),
        .gpio_apb_PWDATA  (gpio_apb_PWDATA),
        .gpio_apb_PSTRB   (gpio_apb_PSTRB),
        .gpio_apb_PPROT   (gpio_apb_PPROT),
        .gpio_apb_PRDATA  (gpio_apb_PRDATA),
        .gpio_apb_PSLVERR (gpio_apb_PSLVERR),
        .gpio_apb_PREADY  (gpio_apb_PREADY),

        // Slave 8: UART 16550
        .uart_apb_PSEL    (uart_apb_PSEL),
        .uart_apb_PENABLE (uart_apb_PENABLE),
        .uart_apb_PADDR   (uart_apb_PADDR),
        .uart_apb_PWRITE  (uart_apb_PWRITE),
        .uart_apb_PWDATA  (uart_apb_PWDATA),
        .uart_apb_PSTRB   (uart_apb_PSTRB),
        .uart_apb_PPROT   (uart_apb_PPROT),
        .uart_apb_PRDATA  (uart_apb_PRDATA),
        .uart_apb_PSLVERR (uart_apb_PSLVERR),
        .uart_apb_PREADY  (uart_apb_PREADY),

        // Slave 9: Reserved
        .rsvd_apb_PSEL    (rsvd_apb_PSEL),
        .rsvd_apb_PENABLE (rsvd_apb_PENABLE),
        .rsvd_apb_PADDR   (rsvd_apb_PADDR),
        .rsvd_apb_PWRITE  (rsvd_apb_PWRITE),
        .rsvd_apb_PWDATA  (rsvd_apb_PWDATA),
        .rsvd_apb_PSTRB   (rsvd_apb_PSTRB),
        .rsvd_apb_PPROT   (rsvd_apb_PPROT),
        .rsvd_apb_PRDATA  (rsvd_apb_PRDATA),
        .rsvd_apb_PSLVERR (rsvd_apb_PSLVERR),
        .rsvd_apb_PREADY  (rsvd_apb_PREADY)
    );

    // ========================================================================
    // Peripheral Instances
    // ========================================================================

    // HPET (High Precision Event Timer)
    apb_hpet #(
        .VENDOR_ID   (HPET_VENDOR_ID),
        .REVISION_ID (HPET_REVISION),
        .NUM_TIMERS  (HPET_NUM_TIMERS),
        .CDC_ENABLE  (0)
    ) u_hpet (
        .pclk          (pclk),
        .presetn       (presetn),
        .hpet_clk      (hpet_clk),
        .hpet_resetn   (hpet_resetn),
        .s_apb_PSEL    (hpet_apb_PSEL),
        .s_apb_PENABLE (hpet_apb_PENABLE),
        .s_apb_PREADY  (hpet_apb_PREADY),
        .s_apb_PADDR   (hpet_apb_PADDR),
        .s_apb_PWRITE  (hpet_apb_PWRITE),
        .s_apb_PWDATA  (hpet_apb_PWDATA),
        .s_apb_PSTRB   (hpet_apb_PSTRB),
        .s_apb_PPROT   (hpet_apb_PPROT),
        .s_apb_PRDATA  (hpet_apb_PRDATA),
        .s_apb_PSLVERR (hpet_apb_PSLVERR),
        .timer_irq     (hpet_timer_irq)
    );

    // 8259 PIC (Programmable Interrupt Controller)
    apb_pic_8259 u_pic (
        .pclk          (pclk),
        .presetn       (presetn),
        .s_apb_PSEL    (pic_apb_PSEL),
        .s_apb_PENABLE (pic_apb_PENABLE),
        .s_apb_PREADY  (pic_apb_PREADY),
        .s_apb_PADDR   (pic_apb_PADDR),
        .s_apb_PWRITE  (pic_apb_PWRITE),
        .s_apb_PWDATA  (pic_apb_PWDATA),
        .s_apb_PSTRB   (pic_apb_PSTRB),
        .s_apb_PPROT   (pic_apb_PPROT),
        .s_apb_PRDATA  (pic_apb_PRDATA),
        .s_apb_PSLVERR (pic_apb_PSLVERR),
        .irq_in        (pic_irq_in),
        .int_out       (pic_int_out)
    );

    // 8254 PIT (Programmable Interval Timer)
    apb_pit_8254 #(
        .NUM_COUNTERS (PIT_NUM_COUNTERS),
        .CDC_ENABLE   (0)
    ) u_pit (
        .pclk          (pclk),
        .presetn       (presetn),
        .pit_clk       (pit_clk),
        .pit_resetn    (pit_resetn),
        .s_apb_PSEL    (pit_apb_PSEL),
        .s_apb_PENABLE (pit_apb_PENABLE),
        .s_apb_PREADY  (pit_apb_PREADY),
        .s_apb_PADDR   (pit_apb_PADDR),
        .s_apb_PWRITE  (pit_apb_PWRITE),
        .s_apb_PWDATA  (pit_apb_PWDATA),
        .s_apb_PSTRB   (pit_apb_PSTRB),
        .s_apb_PPROT   (pit_apb_PPROT),
        .s_apb_PRDATA  (pit_apb_PRDATA),
        .s_apb_PSLVERR (pit_apb_PSLVERR),
        .gate_in       (pit_gate_in),
        .timer_irq     (pit_timer_irq)
    );

    // RTC (Real-Time Clock)
    apb_rtc u_rtc (
        .pclk          (pclk),
        .presetn       (presetn),
        .rtc_clk       (rtc_clk),
        .rtc_resetn    (rtc_resetn),
        .s_apb_PSEL    (rtc_apb_PSEL),
        .s_apb_PENABLE (rtc_apb_PENABLE),
        .s_apb_PREADY  (rtc_apb_PREADY),
        .s_apb_PADDR   (rtc_apb_PADDR),
        .s_apb_PWRITE  (rtc_apb_PWRITE),
        .s_apb_PWDATA  (rtc_apb_PWDATA),
        .s_apb_PSTRB   (rtc_apb_PSTRB),
        .s_apb_PPROT   (rtc_apb_PPROT),
        .s_apb_PRDATA  (rtc_apb_PRDATA),
        .s_apb_PSLVERR (rtc_apb_PSLVERR),
        .rtc_alarm_irq (rtc_alarm_irq),
        .rtc_second_irq(rtc_second_irq)
    );

    // SMBus Controller
    apb_smbus #(
        .FIFO_DEPTH (SMBUS_FIFO_DEPTH),
        .CDC_ENABLE (0)
    ) u_smbus (
        .pclk          (pclk),
        .presetn       (presetn),
        .smbus_clk     (smbus_clk),
        .smbus_resetn  (smbus_resetn),
        .s_apb_PSEL    (smbus_apb_PSEL),
        .s_apb_PENABLE (smbus_apb_PENABLE),
        .s_apb_PREADY  (smbus_apb_PREADY),
        .s_apb_PADDR   (smbus_apb_PADDR),
        .s_apb_PWRITE  (smbus_apb_PWRITE),
        .s_apb_PWDATA  (smbus_apb_PWDATA),
        .s_apb_PSTRB   (smbus_apb_PSTRB),
        .s_apb_PPROT   (smbus_apb_PPROT),
        .s_apb_PRDATA  (smbus_apb_PRDATA),
        .s_apb_PSLVERR (smbus_apb_PSLVERR),
        .smb_scl_i     (smb_scl_i),
        .smb_scl_o     (smb_scl_o),
        .smb_scl_t     (smb_scl_t),
        .smb_sda_i     (smb_sda_i),
        .smb_sda_o     (smb_sda_o),
        .smb_sda_t     (smb_sda_t),
        .smb_interrupt (smb_interrupt)
    );

    // PM/ACPI Controller
    apb_pm_acpi #(
        .CDC_ENABLE (0)
    ) u_pm_acpi (
        .pclk             (pclk),
        .presetn          (presetn),
        .pm_clk           (pm_clk),
        .pm_resetn        (pm_resetn),
        .s_apb_PSEL       (pm_apb_PSEL),
        .s_apb_PENABLE    (pm_apb_PENABLE),
        .s_apb_PREADY     (pm_apb_PREADY),
        .s_apb_PADDR      (pm_apb_PADDR),
        .s_apb_PWRITE     (pm_apb_PWRITE),
        .s_apb_PWDATA     (pm_apb_PWDATA),
        .s_apb_PSTRB      (pm_apb_PSTRB),
        .s_apb_PPROT      (pm_apb_PPROT),
        .s_apb_PRDATA     (pm_apb_PRDATA),
        .s_apb_PSLVERR    (pm_apb_PSLVERR),
        .gpe_events       (pm_gpe_events),
        .power_button_n   (pm_power_button_n),
        .sleep_button_n   (pm_sleep_button_n),
        .rtc_alarm        (pm_rtc_alarm),
        .ext_wake_n       (pm_ext_wake_n),
        .clock_gate_en    (pm_clock_gate_en),
        .power_domain_en  (pm_power_domain_en),
        .sys_reset_req    (pm_sys_reset_req),
        .periph_reset_req (pm_periph_reset_req),
        .pm_interrupt     (pm_interrupt)
    );

    // IOAPIC (I/O Advanced Programmable Interrupt Controller)
    apb_ioapic #(
        .NUM_IRQS   (IOAPIC_NUM_IRQS),
        .CDC_ENABLE (0)
    ) u_ioapic (
        .pclk             (pclk),
        .presetn          (presetn),
        .ioapic_clk       (ioapic_clk),
        .ioapic_resetn    (ioapic_resetn),
        .s_apb_PSEL       (ioapic_apb_PSEL),
        .s_apb_PENABLE    (ioapic_apb_PENABLE),
        .s_apb_PREADY     (ioapic_apb_PREADY),
        .s_apb_PADDR      (ioapic_apb_PADDR),
        .s_apb_PWRITE     (ioapic_apb_PWRITE),
        .s_apb_PWDATA     (ioapic_apb_PWDATA),
        .s_apb_PSTRB      (ioapic_apb_PSTRB),
        .s_apb_PPROT      (ioapic_apb_PPROT),
        .s_apb_PRDATA     (ioapic_apb_PRDATA),
        .s_apb_PSLVERR    (ioapic_apb_PSLVERR),
        .irq_in           (ioapic_irq_in),
        .irq_out_valid    (ioapic_irq_out_valid),
        .irq_out_vector   (ioapic_irq_out_vector),
        .irq_out_dest     (ioapic_irq_out_dest),
        .irq_out_deliv_mode (ioapic_irq_out_deliv_mode),
        .irq_out_ready    (ioapic_irq_out_ready),
        .eoi_in           (ioapic_eoi_in),
        .eoi_vector       (ioapic_eoi_vector)
    );

    // GPIO Controller
    apb_gpio #(
        .GPIO_WIDTH  (GPIO_WIDTH),
        .SYNC_STAGES (GPIO_SYNC_STAGES),
        .CDC_ENABLE  (0),
        .SKID_DEPTH  (2)
    ) u_gpio (
        .pclk          (pclk),
        .presetn       (presetn),
        .gpio_clk      (gpio_clk),
        .gpio_rstn     (gpio_rstn),
        .s_apb_PSEL    (gpio_apb_PSEL),
        .s_apb_PENABLE (gpio_apb_PENABLE),
        .s_apb_PREADY  (gpio_apb_PREADY),
        .s_apb_PADDR   (gpio_apb_PADDR),
        .s_apb_PWRITE  (gpio_apb_PWRITE),
        .s_apb_PWDATA  (gpio_apb_PWDATA),
        .s_apb_PSTRB   (gpio_apb_PSTRB),
        .s_apb_PPROT   (gpio_apb_PPROT),
        .s_apb_PRDATA  (gpio_apb_PRDATA),
        .s_apb_PSLVERR (gpio_apb_PSLVERR),
        .gpio_in       (gpio_in),
        .gpio_out      (gpio_out),
        .gpio_oe       (gpio_oe),
        .irq           (gpio_irq)
    );

    // UART 16550
    apb_uart_16550 #(
        .FIFO_DEPTH  (UART_FIFO_DEPTH),
        .SYNC_STAGES (UART_SYNC_STAGES),
        .CDC_ENABLE  (0),
        .SKID_DEPTH  (2)
    ) u_uart (
        .pclk          (pclk),
        .presetn       (presetn),
        .uart_clk      (uart_clk),
        .uart_rstn     (uart_rstn),
        .s_apb_PSEL    (uart_apb_PSEL),
        .s_apb_PENABLE (uart_apb_PENABLE),
        .s_apb_PREADY  (uart_apb_PREADY),
        .s_apb_PADDR   (uart_apb_PADDR),
        .s_apb_PWRITE  (uart_apb_PWRITE),
        .s_apb_PWDATA  (uart_apb_PWDATA),
        .s_apb_PSTRB   (uart_apb_PSTRB),
        .s_apb_PPROT   (uart_apb_PPROT),
        .s_apb_PRDATA  (uart_apb_PRDATA),
        .s_apb_PSLVERR (uart_apb_PSLVERR),
        .uart_rx       (uart_rx),
        .uart_tx       (uart_tx),
        .cts_n         (uart_cts_n),
        .dsr_n         (uart_dsr_n),
        .ri_n          (uart_ri_n),
        .dcd_n         (uart_dcd_n),
        .dtr_n         (uart_dtr_n),
        .rts_n         (uart_rts_n),
        .out1_n        (uart_out1_n),
        .out2_n        (uart_out2_n),
        .irq           (uart_irq)
    );

endmodule : rlb_top
