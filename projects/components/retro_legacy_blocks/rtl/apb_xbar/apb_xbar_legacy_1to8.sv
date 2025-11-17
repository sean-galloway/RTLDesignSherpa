// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_xbar_legacy_1to8
// Purpose: Named-Port Wrapper for APB Crossbar (Retro Legacy Blocks)
//
// Description:
//   Wrapper around the generated apb_xbar_1to8 module that provides
//   descriptive named ports for legacy PC peripheral blocks.
//
//   This wrapper instantiates the full apb_xbar_1to8 (with apb_slave/apb_master
//   protocol converters and registered response routing) and maps the numbered
//   slave ports (s0-s7) to meaningful names for each legacy block.
//
// Address Map - Two Separate Regions for Standard Compatibility:
//
// Region 1 (IOAPIC at standard address):
//   BASE_ADDR = 0xFEC0_0000
//   Slave 0 - IOAPIC:      0xFEC0_0000 - 0xFEC0_0FFF (4KB) - Standard @ 0xFEC00000 ✓
//
// Region 2 (HPET at standard address):
//   Note: HPET should use BASE_ADDR = 0xFED0_0000 for standard placement
//   Slave 1 - HPET:        Use separate instance @ 0xFED0_0000 (4KB) - Standard ✓
//
// Remaining Legacy I/O Blocks (memory-mapped, any BASE_ADDR):
//   Slave 2 - PIT 8254:    BASE + 0x2000 - 0x2FFF (4KB) - Standard I/O 0x40-0x5F
//   Slave 3 - RTC:         BASE + 0x3000 - 0x3FFF (4KB) - Standard I/O 0x70-0x7F
//   Slave 4 - PIC 8259:    BASE + 0x4000 - 0x4FFF (4KB) - Standard I/O 0x20-0xA1
//   Slave 5 - PM ACPI:     BASE + 0x5000 - 0x5FFF (4KB) - Varies by chipset
//   Slave 6 - SMBUS:       BASE + 0x6000 - 0x6FFF (4KB) - Varies by chipset
//   Slave 7 - Subtractive: BASE + 0x7000 - 0x7FFF (4KB) - Catch-all unmapped
//
// IMPORTANT: IOAPIC and HPET should be instantiated separately in top-level design:
//   - This crossbar at BASE_ADDR=0xFEC00000 provides IOAPIC + Legacy I/O blocks
//   - Separate HPET instance at 0xFED00000 for standard compliance
//   Address decode uses bits[14:12] for 8×4KB slaves
//
// Documentation: projects/components/retro_legacy_blocks/PRD.md
// Subsystem: retro_legacy_blocks
//
// Author: Claude (AI Assistant)
// Created: 2025-11-15

`timescale 1ns / 1ps

module apb_xbar_legacy_1to8 #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH / 8,
    parameter logic [ADDR_WIDTH-1:0] BASE_ADDR = 32'hFEC0_0000
) (
    // Clock and Reset
    input  logic                  pclk,
    input  logic                  presetn,

    // Master APB interface (from CPU/interconnect)
    input  logic                  m_apb_PSEL,
    input  logic                  m_apb_PENABLE,
    input  logic [ADDR_WIDTH-1:0] m_apb_PADDR,
    input  logic                  m_apb_PWRITE,
    input  logic [DATA_WIDTH-1:0] m_apb_PWDATA,
    input  logic [STRB_WIDTH-1:0] m_apb_PSTRB,
    input  logic [2:0]            m_apb_PPROT,
    output logic [DATA_WIDTH-1:0] m_apb_PRDATA,
    output logic                  m_apb_PSLVERR,
    output logic                  m_apb_PREADY,

    // Slave 0 - IOAPIC (0xFEC0_0000)
    output logic                  ioapic_apb_PSEL,
    output logic                  ioapic_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] ioapic_apb_PADDR,
    output logic                  ioapic_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] ioapic_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] ioapic_apb_PSTRB,
    output logic [2:0]            ioapic_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] ioapic_apb_PRDATA,
    input  logic                  ioapic_apb_PSLVERR,
    input  logic                  ioapic_apb_PREADY,

    // Slave 1 - HPET (0xFEC0_1000)
    output logic                  hpet_apb_PSEL,
    output logic                  hpet_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] hpet_apb_PADDR,
    output logic                  hpet_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] hpet_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] hpet_apb_PSTRB,
    output logic [2:0]            hpet_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] hpet_apb_PRDATA,
    input  logic                  hpet_apb_PSLVERR,
    input  logic                  hpet_apb_PREADY,

    // Slave 2 - PIT 8254 (0xFEC0_2000)
    output logic                  pit_8254_apb_PSEL,
    output logic                  pit_8254_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] pit_8254_apb_PADDR,
    output logic                  pit_8254_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] pit_8254_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] pit_8254_apb_PSTRB,
    output logic [2:0]            pit_8254_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] pit_8254_apb_PRDATA,
    input  logic                  pit_8254_apb_PSLVERR,
    input  logic                  pit_8254_apb_PREADY,

    // Slave 3 - RTC (0xFEC0_3000)
    output logic                  rtc_apb_PSEL,
    output logic                  rtc_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] rtc_apb_PADDR,
    output logic                  rtc_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] rtc_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] rtc_apb_PSTRB,
    output logic [2:0]            rtc_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] rtc_apb_PRDATA,
    input  logic                  rtc_apb_PSLVERR,
    input  logic                  rtc_apb_PREADY,

    // Slave 4 - PIC 8259 (0xFEC0_4000)
    output logic                  pic_8259_apb_PSEL,
    output logic                  pic_8259_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] pic_8259_apb_PADDR,
    output logic                  pic_8259_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] pic_8259_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] pic_8259_apb_PSTRB,
    output logic [2:0]            pic_8259_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] pic_8259_apb_PRDATA,
    input  logic                  pic_8259_apb_PSLVERR,
    input  logic                  pic_8259_apb_PREADY,

    // Slave 5 - PM ACPI (0xFEC0_5000)
    output logic                  pm_acpi_apb_PSEL,
    output logic                  pm_acpi_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] pm_acpi_apb_PADDR,
    output logic                  pm_acpi_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] pm_acpi_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] pm_acpi_apb_PSTRB,
    output logic [2:0]            pm_acpi_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] pm_acpi_apb_PRDATA,
    input  logic                  pm_acpi_apb_PSLVERR,
    input  logic                  pm_acpi_apb_PREADY,

    // Slave 6 - SMBUS (0xFEC0_6000)
    output logic                  smbus_apb_PSEL,
    output logic                  smbus_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] smbus_apb_PADDR,
    output logic                  smbus_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] smbus_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] smbus_apb_PSTRB,
    output logic [2:0]            smbus_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] smbus_apb_PRDATA,
    input  logic                  smbus_apb_PSLVERR,
    input  logic                  smbus_apb_PREADY,

    // Slave 7 - Subtractive Agent (0xFEC0_7000)
    output logic                  subtractive_apb_PSEL,
    output logic                  subtractive_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0] subtractive_apb_PADDR,
    output logic                  subtractive_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] subtractive_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] subtractive_apb_PSTRB,
    output logic [2:0]            subtractive_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] subtractive_apb_PRDATA,
    input  logic                  subtractive_apb_PSLVERR,
    input  logic                  subtractive_apb_PREADY
);

    // Instantiate the generated 1-to-8 crossbar
    apb_xbar_1to8 #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .STRB_WIDTH(STRB_WIDTH),
        .BASE_ADDR(BASE_ADDR)
    ) u_xbar (
        .pclk(pclk),
        .presetn(presetn),

        // Master interface
        .m0_apb_PSEL(m_apb_PSEL),
        .m0_apb_PENABLE(m_apb_PENABLE),
        .m0_apb_PADDR(m_apb_PADDR),
        .m0_apb_PWRITE(m_apb_PWRITE),
        .m0_apb_PWDATA(m_apb_PWDATA),
        .m0_apb_PSTRB(m_apb_PSTRB),
        .m0_apb_PPROT(m_apb_PPROT),
        .m0_apb_PRDATA(m_apb_PRDATA),
        .m0_apb_PSLVERR(m_apb_PSLVERR),
        .m0_apb_PREADY(m_apb_PREADY),

        // Slave 0 - IOAPIC
        .s0_apb_PSEL(ioapic_apb_PSEL),
        .s0_apb_PENABLE(ioapic_apb_PENABLE),
        .s0_apb_PADDR(ioapic_apb_PADDR),
        .s0_apb_PWRITE(ioapic_apb_PWRITE),
        .s0_apb_PWDATA(ioapic_apb_PWDATA),
        .s0_apb_PSTRB(ioapic_apb_PSTRB),
        .s0_apb_PPROT(ioapic_apb_PPROT),
        .s0_apb_PRDATA(ioapic_apb_PRDATA),
        .s0_apb_PSLVERR(ioapic_apb_PSLVERR),
        .s0_apb_PREADY(ioapic_apb_PREADY),

        // Slave 1 - HPET
        .s1_apb_PSEL(hpet_apb_PSEL),
        .s1_apb_PENABLE(hpet_apb_PENABLE),
        .s1_apb_PADDR(hpet_apb_PADDR),
        .s1_apb_PWRITE(hpet_apb_PWRITE),
        .s1_apb_PWDATA(hpet_apb_PWDATA),
        .s1_apb_PSTRB(hpet_apb_PSTRB),
        .s1_apb_PPROT(hpet_apb_PPROT),
        .s1_apb_PRDATA(hpet_apb_PRDATA),
        .s1_apb_PSLVERR(hpet_apb_PSLVERR),
        .s1_apb_PREADY(hpet_apb_PREADY),

        // Slave 2 - PIT 8254
        .s2_apb_PSEL(pit_8254_apb_PSEL),
        .s2_apb_PENABLE(pit_8254_apb_PENABLE),
        .s2_apb_PADDR(pit_8254_apb_PADDR),
        .s2_apb_PWRITE(pit_8254_apb_PWRITE),
        .s2_apb_PWDATA(pit_8254_apb_PWDATA),
        .s2_apb_PSTRB(pit_8254_apb_PSTRB),
        .s2_apb_PPROT(pit_8254_apb_PPROT),
        .s2_apb_PRDATA(pit_8254_apb_PRDATA),
        .s2_apb_PSLVERR(pit_8254_apb_PSLVERR),
        .s2_apb_PREADY(pit_8254_apb_PREADY),

        // Slave 3 - RTC
        .s3_apb_PSEL(rtc_apb_PSEL),
        .s3_apb_PENABLE(rtc_apb_PENABLE),
        .s3_apb_PADDR(rtc_apb_PADDR),
        .s3_apb_PWRITE(rtc_apb_PWRITE),
        .s3_apb_PWDATA(rtc_apb_PWDATA),
        .s3_apb_PSTRB(rtc_apb_PSTRB),
        .s3_apb_PPROT(rtc_apb_PPROT),
        .s3_apb_PRDATA(rtc_apb_PRDATA),
        .s3_apb_PSLVERR(rtc_apb_PSLVERR),
        .s3_apb_PREADY(rtc_apb_PREADY),

        // Slave 4 - PIC 8259
        .s4_apb_PSEL(pic_8259_apb_PSEL),
        .s4_apb_PENABLE(pic_8259_apb_PENABLE),
        .s4_apb_PADDR(pic_8259_apb_PADDR),
        .s4_apb_PWRITE(pic_8259_apb_PWRITE),
        .s4_apb_PWDATA(pic_8259_apb_PWDATA),
        .s4_apb_PSTRB(pic_8259_apb_PSTRB),
        .s4_apb_PPROT(pic_8259_apb_PPROT),
        .s4_apb_PRDATA(pic_8259_apb_PRDATA),
        .s4_apb_PSLVERR(pic_8259_apb_PSLVERR),
        .s4_apb_PREADY(pic_8259_apb_PREADY),

        // Slave 5 - PM ACPI
        .s5_apb_PSEL(pm_acpi_apb_PSEL),
        .s5_apb_PENABLE(pm_acpi_apb_PENABLE),
        .s5_apb_PADDR(pm_acpi_apb_PADDR),
        .s5_apb_PWRITE(pm_acpi_apb_PWRITE),
        .s5_apb_PWDATA(pm_acpi_apb_PWDATA),
        .s5_apb_PSTRB(pm_acpi_apb_PSTRB),
        .s5_apb_PPROT(pm_acpi_apb_PPROT),
        .s5_apb_PRDATA(pm_acpi_apb_PRDATA),
        .s5_apb_PSLVERR(pm_acpi_apb_PSLVERR),
        .s5_apb_PREADY(pm_acpi_apb_PREADY),

        // Slave 6 - SMBUS
        .s6_apb_PSEL(smbus_apb_PSEL),
        .s6_apb_PENABLE(smbus_apb_PENABLE),
        .s6_apb_PADDR(smbus_apb_PADDR),
        .s6_apb_PWRITE(smbus_apb_PWRITE),
        .s6_apb_PWDATA(smbus_apb_PWDATA),
        .s6_apb_PSTRB(smbus_apb_PSTRB),
        .s6_apb_PPROT(smbus_apb_PPROT),
        .s6_apb_PRDATA(smbus_apb_PRDATA),
        .s6_apb_PSLVERR(smbus_apb_PSLVERR),
        .s6_apb_PREADY(smbus_apb_PREADY),

        // Slave 7 - Subtractive
        .s7_apb_PSEL(subtractive_apb_PSEL),
        .s7_apb_PENABLE(subtractive_apb_PENABLE),
        .s7_apb_PADDR(subtractive_apb_PADDR),
        .s7_apb_PWRITE(subtractive_apb_PWRITE),
        .s7_apb_PWDATA(subtractive_apb_PWDATA),
        .s7_apb_PSTRB(subtractive_apb_PSTRB),
        .s7_apb_PPROT(subtractive_apb_PPROT),
        .s7_apb_PRDATA(subtractive_apb_PRDATA),
        .s7_apb_PSLVERR(subtractive_apb_PSLVERR),
        .s7_apb_PREADY(subtractive_apb_PREADY)
    );

endmodule : apb_xbar_legacy_1to8
