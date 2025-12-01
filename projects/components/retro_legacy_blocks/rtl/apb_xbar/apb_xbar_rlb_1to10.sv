// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb_xbar_rlb_1to10
// Purpose: APB Crossbar for Retro Legacy Blocks (1 master, 10 slaves)
//
// Description:
//   1-to-10 APB crossbar connecting external APB master to RLB peripherals.
//   Uses 4KB windows with 4-bit address decode on bits [15:12].
//
// Address Map (4KB windows):
//   Slave 0: HPET         [BASE + 0x0000, BASE + 0x0FFF]
//   Slave 1: 8259 PIC     [BASE + 0x1000, BASE + 0x1FFF]
//   Slave 2: 8254 PIT     [BASE + 0x2000, BASE + 0x2FFF]
//   Slave 3: RTC          [BASE + 0x3000, BASE + 0x3FFF]
//   Slave 4: SMBus        [BASE + 0x4000, BASE + 0x4FFF]
//   Slave 5: PM/ACPI      [BASE + 0x5000, BASE + 0x5FFF]
//   Slave 6: IOAPIC       [BASE + 0x6000, BASE + 0x6FFF]
//   Slave 7: GPIO         [BASE + 0x7000, BASE + 0x7FFF]
//   Slave 8: UART 16550   [BASE + 0x8000, BASE + 0x8FFF]
//   Slave 9: Reserved     [BASE + 0x9000, BASE + 0x9FFF]
//
// Documentation: projects/components/retro_legacy_blocks/docs/
// Created: 2025-11-30

`timescale 1ns / 1ps

`include "reset_defs.svh"

module apb_xbar_rlb_1to10 #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH / 8,
    parameter logic [ADDR_WIDTH-1:0] BASE_ADDR = 32'hFEC00000
) (
    // Clock and Reset
    input  logic                  pclk,
    input  logic                  presetn,

    // Master APB interface (from external master)
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

    // Slave 0: HPET APB interface
    output logic                  hpet_apb_PSEL,
    output logic                  hpet_apb_PENABLE,
    output logic [11:0]           hpet_apb_PADDR,
    output logic                  hpet_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] hpet_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] hpet_apb_PSTRB,
    output logic [2:0]            hpet_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] hpet_apb_PRDATA,
    input  logic                  hpet_apb_PSLVERR,
    input  logic                  hpet_apb_PREADY,

    // Slave 1: 8259 PIC APB interface
    output logic                  pic_apb_PSEL,
    output logic                  pic_apb_PENABLE,
    output logic [11:0]           pic_apb_PADDR,
    output logic                  pic_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] pic_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] pic_apb_PSTRB,
    output logic [2:0]            pic_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] pic_apb_PRDATA,
    input  logic                  pic_apb_PSLVERR,
    input  logic                  pic_apb_PREADY,

    // Slave 2: 8254 PIT APB interface
    output logic                  pit_apb_PSEL,
    output logic                  pit_apb_PENABLE,
    output logic [11:0]           pit_apb_PADDR,
    output logic                  pit_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] pit_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] pit_apb_PSTRB,
    output logic [2:0]            pit_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] pit_apb_PRDATA,
    input  logic                  pit_apb_PSLVERR,
    input  logic                  pit_apb_PREADY,

    // Slave 3: RTC APB interface
    output logic                  rtc_apb_PSEL,
    output logic                  rtc_apb_PENABLE,
    output logic [11:0]           rtc_apb_PADDR,
    output logic                  rtc_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] rtc_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] rtc_apb_PSTRB,
    output logic [2:0]            rtc_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] rtc_apb_PRDATA,
    input  logic                  rtc_apb_PSLVERR,
    input  logic                  rtc_apb_PREADY,

    // Slave 4: SMBus APB interface
    output logic                  smbus_apb_PSEL,
    output logic                  smbus_apb_PENABLE,
    output logic [11:0]           smbus_apb_PADDR,
    output logic                  smbus_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] smbus_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] smbus_apb_PSTRB,
    output logic [2:0]            smbus_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] smbus_apb_PRDATA,
    input  logic                  smbus_apb_PSLVERR,
    input  logic                  smbus_apb_PREADY,

    // Slave 5: PM/ACPI APB interface
    output logic                  pm_apb_PSEL,
    output logic                  pm_apb_PENABLE,
    output logic [11:0]           pm_apb_PADDR,
    output logic                  pm_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] pm_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] pm_apb_PSTRB,
    output logic [2:0]            pm_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] pm_apb_PRDATA,
    input  logic                  pm_apb_PSLVERR,
    input  logic                  pm_apb_PREADY,

    // Slave 6: IOAPIC APB interface
    output logic                  ioapic_apb_PSEL,
    output logic                  ioapic_apb_PENABLE,
    output logic [11:0]           ioapic_apb_PADDR,
    output logic                  ioapic_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] ioapic_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] ioapic_apb_PSTRB,
    output logic [2:0]            ioapic_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] ioapic_apb_PRDATA,
    input  logic                  ioapic_apb_PSLVERR,
    input  logic                  ioapic_apb_PREADY,

    // Slave 7: GPIO APB interface
    output logic                  gpio_apb_PSEL,
    output logic                  gpio_apb_PENABLE,
    output logic [11:0]           gpio_apb_PADDR,
    output logic                  gpio_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] gpio_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] gpio_apb_PSTRB,
    output logic [2:0]            gpio_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] gpio_apb_PRDATA,
    input  logic                  gpio_apb_PSLVERR,
    input  logic                  gpio_apb_PREADY,

    // Slave 8: UART 16550 APB interface
    output logic                  uart_apb_PSEL,
    output logic                  uart_apb_PENABLE,
    output logic [11:0]           uart_apb_PADDR,
    output logic                  uart_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] uart_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] uart_apb_PSTRB,
    output logic [2:0]            uart_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] uart_apb_PRDATA,
    input  logic                  uart_apb_PSLVERR,
    input  logic                  uart_apb_PREADY,

    // Slave 9: Reserved APB interface
    output logic                  rsvd_apb_PSEL,
    output logic                  rsvd_apb_PENABLE,
    output logic [11:0]           rsvd_apb_PADDR,
    output logic                  rsvd_apb_PWRITE,
    output logic [DATA_WIDTH-1:0] rsvd_apb_PWDATA,
    output logic [STRB_WIDTH-1:0] rsvd_apb_PSTRB,
    output logic [2:0]            rsvd_apb_PPROT,
    input  logic [DATA_WIDTH-1:0] rsvd_apb_PRDATA,
    input  logic                  rsvd_apb_PSLVERR,
    input  logic                  rsvd_apb_PREADY
);

    // ========================================================================
    // Command/Response Interface Signals
    // ========================================================================

    // Master cmd/rsp signals
    logic                  m_cmd_valid;
    logic                  m_cmd_ready;
    logic                  m_cmd_pwrite;
    logic [ADDR_WIDTH-1:0] m_cmd_paddr;
    logic [DATA_WIDTH-1:0] m_cmd_pwdata;
    logic [STRB_WIDTH-1:0] m_cmd_pstrb;
    logic [2:0]            m_cmd_pprot;
    logic                  m_rsp_valid;
    logic                  m_rsp_ready;
    logic [DATA_WIDTH-1:0] m_rsp_prdata;
    logic                  m_rsp_pslverr;

    // Slave cmd/rsp signals (10 slaves)
    logic        s_cmd_valid  [0:9];
    logic        s_cmd_ready  [0:9];
    logic        s_cmd_pwrite [0:9];
    logic [11:0] s_cmd_paddr  [0:9];
    logic [DATA_WIDTH-1:0] s_cmd_pwdata [0:9];
    logic [STRB_WIDTH-1:0] s_cmd_pstrb  [0:9];
    logic [2:0]  s_cmd_pprot  [0:9];
    logic        s_rsp_valid  [0:9];
    logic        s_rsp_ready  [0:9];
    logic [DATA_WIDTH-1:0] s_rsp_prdata [0:9];
    logic        s_rsp_pslverr[0:9];

    // ========================================================================
    // APB Slave - Convert master APB to cmd/rsp
    // ========================================================================
    apb_slave #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_slave (
        .pclk           (pclk),
        .presetn        (presetn),
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
        .cmd_valid      (m_cmd_valid),
        .cmd_ready      (m_cmd_ready),
        .cmd_pwrite     (m_cmd_pwrite),
        .cmd_paddr      (m_cmd_paddr),
        .cmd_pwdata     (m_cmd_pwdata),
        .cmd_pstrb      (m_cmd_pstrb),
        .cmd_pprot      (m_cmd_pprot),
        .rsp_valid      (m_rsp_valid),
        .rsp_ready      (m_rsp_ready),
        .rsp_prdata     (m_rsp_prdata),
        .rsp_pslverr    (m_rsp_pslverr)
    );

    // ========================================================================
    // Address Decode Logic
    // ========================================================================
    logic [3:0] slave_sel;
    logic       addr_in_range;
    logic [3:0] r_slave_sel;  // Registered for response routing

    // Decode 4KB windows using address bits [15:12]
    always_comb begin
        addr_in_range = (m_cmd_paddr >= BASE_ADDR) &&
                        (m_cmd_paddr < (BASE_ADDR + 32'h0000A000));  // 10 x 4KB = 40KB
        slave_sel = m_cmd_paddr[15:12];
    end

    // Register slave selection when command accepted
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            r_slave_sel <= 4'd0;
        end else begin
            if (m_cmd_valid && m_cmd_ready) begin
                r_slave_sel <= slave_sel;
            end
        end
    end

    // ========================================================================
    // Command Routing to Slaves
    // ========================================================================
    genvar i;
    generate
        for (i = 0; i < 10; i++) begin : gen_cmd_route
            assign s_cmd_valid[i]  = m_cmd_valid && addr_in_range && (slave_sel == i[3:0]);
            assign s_cmd_pwrite[i] = m_cmd_pwrite;
            assign s_cmd_paddr[i]  = m_cmd_paddr[11:0];  // 4KB offset
            assign s_cmd_pwdata[i] = m_cmd_pwdata;
            assign s_cmd_pstrb[i]  = m_cmd_pstrb;
            assign s_cmd_pprot[i]  = m_cmd_pprot;
        end
    endgenerate

    // Master ready when selected slave is ready
    always_comb begin
        m_cmd_ready = 1'b0;
        if (m_cmd_valid && addr_in_range) begin
            case (slave_sel)
                4'd0: m_cmd_ready = s_cmd_ready[0];
                4'd1: m_cmd_ready = s_cmd_ready[1];
                4'd2: m_cmd_ready = s_cmd_ready[2];
                4'd3: m_cmd_ready = s_cmd_ready[3];
                4'd4: m_cmd_ready = s_cmd_ready[4];
                4'd5: m_cmd_ready = s_cmd_ready[5];
                4'd6: m_cmd_ready = s_cmd_ready[6];
                4'd7: m_cmd_ready = s_cmd_ready[7];
                4'd8: m_cmd_ready = s_cmd_ready[8];
                4'd9: m_cmd_ready = s_cmd_ready[9];
                default: m_cmd_ready = 1'b0;
            endcase
        end
    end

    // ========================================================================
    // Response Routing from Slaves
    // ========================================================================
    always_comb begin
        m_rsp_valid   = 1'b0;
        m_rsp_prdata  = '0;
        m_rsp_pslverr = 1'b0;
        case (r_slave_sel)
            4'd0: begin
                m_rsp_valid   = s_rsp_valid[0];
                m_rsp_prdata  = s_rsp_prdata[0];
                m_rsp_pslverr = s_rsp_pslverr[0];
            end
            4'd1: begin
                m_rsp_valid   = s_rsp_valid[1];
                m_rsp_prdata  = s_rsp_prdata[1];
                m_rsp_pslverr = s_rsp_pslverr[1];
            end
            4'd2: begin
                m_rsp_valid   = s_rsp_valid[2];
                m_rsp_prdata  = s_rsp_prdata[2];
                m_rsp_pslverr = s_rsp_pslverr[2];
            end
            4'd3: begin
                m_rsp_valid   = s_rsp_valid[3];
                m_rsp_prdata  = s_rsp_prdata[3];
                m_rsp_pslverr = s_rsp_pslverr[3];
            end
            4'd4: begin
                m_rsp_valid   = s_rsp_valid[4];
                m_rsp_prdata  = s_rsp_prdata[4];
                m_rsp_pslverr = s_rsp_pslverr[4];
            end
            4'd5: begin
                m_rsp_valid   = s_rsp_valid[5];
                m_rsp_prdata  = s_rsp_prdata[5];
                m_rsp_pslverr = s_rsp_pslverr[5];
            end
            4'd6: begin
                m_rsp_valid   = s_rsp_valid[6];
                m_rsp_prdata  = s_rsp_prdata[6];
                m_rsp_pslverr = s_rsp_pslverr[6];
            end
            4'd7: begin
                m_rsp_valid   = s_rsp_valid[7];
                m_rsp_prdata  = s_rsp_prdata[7];
                m_rsp_pslverr = s_rsp_pslverr[7];
            end
            4'd8: begin
                m_rsp_valid   = s_rsp_valid[8];
                m_rsp_prdata  = s_rsp_prdata[8];
                m_rsp_pslverr = s_rsp_pslverr[8];
            end
            4'd9: begin
                m_rsp_valid   = s_rsp_valid[9];
                m_rsp_prdata  = s_rsp_prdata[9];
                m_rsp_pslverr = s_rsp_pslverr[9];
            end
            default: begin
                m_rsp_valid   = 1'b0;
                m_rsp_prdata  = '0;
                m_rsp_pslverr = 1'b1;  // Error for invalid address
            end
        endcase
    end

    // Response ready routing
    generate
        for (i = 0; i < 10; i++) begin : gen_rsp_ready
            assign s_rsp_ready[i] = (r_slave_sel == i[3:0]) ? m_rsp_ready : 1'b0;
        end
    endgenerate

    // ========================================================================
    // APB Masters - Convert cmd/rsp to slave APB interfaces
    // ========================================================================

    // Slave 0: HPET
    apb_master #(
        .ADDR_WIDTH (12),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_hpet (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (hpet_apb_PSEL),
        .m_apb_PENABLE  (hpet_apb_PENABLE),
        .m_apb_PREADY   (hpet_apb_PREADY),
        .m_apb_PADDR    (hpet_apb_PADDR),
        .m_apb_PWRITE   (hpet_apb_PWRITE),
        .m_apb_PWDATA   (hpet_apb_PWDATA),
        .m_apb_PSTRB    (hpet_apb_PSTRB),
        .m_apb_PPROT    (hpet_apb_PPROT),
        .m_apb_PRDATA   (hpet_apb_PRDATA),
        .m_apb_PSLVERR  (hpet_apb_PSLVERR),
        .cmd_valid      (s_cmd_valid[0]),
        .cmd_ready      (s_cmd_ready[0]),
        .cmd_pwrite     (s_cmd_pwrite[0]),
        .cmd_paddr      (s_cmd_paddr[0]),
        .cmd_pwdata     (s_cmd_pwdata[0]),
        .cmd_pstrb      (s_cmd_pstrb[0]),
        .cmd_pprot      (s_cmd_pprot[0]),
        .rsp_valid      (s_rsp_valid[0]),
        .rsp_ready      (s_rsp_ready[0]),
        .rsp_prdata     (s_rsp_prdata[0]),
        .rsp_pslverr    (s_rsp_pslverr[0])
    );

    // Slave 1: 8259 PIC
    apb_master #(
        .ADDR_WIDTH (12),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_pic (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (pic_apb_PSEL),
        .m_apb_PENABLE  (pic_apb_PENABLE),
        .m_apb_PREADY   (pic_apb_PREADY),
        .m_apb_PADDR    (pic_apb_PADDR),
        .m_apb_PWRITE   (pic_apb_PWRITE),
        .m_apb_PWDATA   (pic_apb_PWDATA),
        .m_apb_PSTRB    (pic_apb_PSTRB),
        .m_apb_PPROT    (pic_apb_PPROT),
        .m_apb_PRDATA   (pic_apb_PRDATA),
        .m_apb_PSLVERR  (pic_apb_PSLVERR),
        .cmd_valid      (s_cmd_valid[1]),
        .cmd_ready      (s_cmd_ready[1]),
        .cmd_pwrite     (s_cmd_pwrite[1]),
        .cmd_paddr      (s_cmd_paddr[1]),
        .cmd_pwdata     (s_cmd_pwdata[1]),
        .cmd_pstrb      (s_cmd_pstrb[1]),
        .cmd_pprot      (s_cmd_pprot[1]),
        .rsp_valid      (s_rsp_valid[1]),
        .rsp_ready      (s_rsp_ready[1]),
        .rsp_prdata     (s_rsp_prdata[1]),
        .rsp_pslverr    (s_rsp_pslverr[1])
    );

    // Slave 2: 8254 PIT
    apb_master #(
        .ADDR_WIDTH (12),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_pit (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (pit_apb_PSEL),
        .m_apb_PENABLE  (pit_apb_PENABLE),
        .m_apb_PREADY   (pit_apb_PREADY),
        .m_apb_PADDR    (pit_apb_PADDR),
        .m_apb_PWRITE   (pit_apb_PWRITE),
        .m_apb_PWDATA   (pit_apb_PWDATA),
        .m_apb_PSTRB    (pit_apb_PSTRB),
        .m_apb_PPROT    (pit_apb_PPROT),
        .m_apb_PRDATA   (pit_apb_PRDATA),
        .m_apb_PSLVERR  (pit_apb_PSLVERR),
        .cmd_valid      (s_cmd_valid[2]),
        .cmd_ready      (s_cmd_ready[2]),
        .cmd_pwrite     (s_cmd_pwrite[2]),
        .cmd_paddr      (s_cmd_paddr[2]),
        .cmd_pwdata     (s_cmd_pwdata[2]),
        .cmd_pstrb      (s_cmd_pstrb[2]),
        .cmd_pprot      (s_cmd_pprot[2]),
        .rsp_valid      (s_rsp_valid[2]),
        .rsp_ready      (s_rsp_ready[2]),
        .rsp_prdata     (s_rsp_prdata[2]),
        .rsp_pslverr    (s_rsp_pslverr[2])
    );

    // Slave 3: RTC
    apb_master #(
        .ADDR_WIDTH (12),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_rtc (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (rtc_apb_PSEL),
        .m_apb_PENABLE  (rtc_apb_PENABLE),
        .m_apb_PREADY   (rtc_apb_PREADY),
        .m_apb_PADDR    (rtc_apb_PADDR),
        .m_apb_PWRITE   (rtc_apb_PWRITE),
        .m_apb_PWDATA   (rtc_apb_PWDATA),
        .m_apb_PSTRB    (rtc_apb_PSTRB),
        .m_apb_PPROT    (rtc_apb_PPROT),
        .m_apb_PRDATA   (rtc_apb_PRDATA),
        .m_apb_PSLVERR  (rtc_apb_PSLVERR),
        .cmd_valid      (s_cmd_valid[3]),
        .cmd_ready      (s_cmd_ready[3]),
        .cmd_pwrite     (s_cmd_pwrite[3]),
        .cmd_paddr      (s_cmd_paddr[3]),
        .cmd_pwdata     (s_cmd_pwdata[3]),
        .cmd_pstrb      (s_cmd_pstrb[3]),
        .cmd_pprot      (s_cmd_pprot[3]),
        .rsp_valid      (s_rsp_valid[3]),
        .rsp_ready      (s_rsp_ready[3]),
        .rsp_prdata     (s_rsp_prdata[3]),
        .rsp_pslverr    (s_rsp_pslverr[3])
    );

    // Slave 4: SMBus
    apb_master #(
        .ADDR_WIDTH (12),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_smbus (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (smbus_apb_PSEL),
        .m_apb_PENABLE  (smbus_apb_PENABLE),
        .m_apb_PREADY   (smbus_apb_PREADY),
        .m_apb_PADDR    (smbus_apb_PADDR),
        .m_apb_PWRITE   (smbus_apb_PWRITE),
        .m_apb_PWDATA   (smbus_apb_PWDATA),
        .m_apb_PSTRB    (smbus_apb_PSTRB),
        .m_apb_PPROT    (smbus_apb_PPROT),
        .m_apb_PRDATA   (smbus_apb_PRDATA),
        .m_apb_PSLVERR  (smbus_apb_PSLVERR),
        .cmd_valid      (s_cmd_valid[4]),
        .cmd_ready      (s_cmd_ready[4]),
        .cmd_pwrite     (s_cmd_pwrite[4]),
        .cmd_paddr      (s_cmd_paddr[4]),
        .cmd_pwdata     (s_cmd_pwdata[4]),
        .cmd_pstrb      (s_cmd_pstrb[4]),
        .cmd_pprot      (s_cmd_pprot[4]),
        .rsp_valid      (s_rsp_valid[4]),
        .rsp_ready      (s_rsp_ready[4]),
        .rsp_prdata     (s_rsp_prdata[4]),
        .rsp_pslverr    (s_rsp_pslverr[4])
    );

    // Slave 5: PM/ACPI
    apb_master #(
        .ADDR_WIDTH (12),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_pm (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (pm_apb_PSEL),
        .m_apb_PENABLE  (pm_apb_PENABLE),
        .m_apb_PREADY   (pm_apb_PREADY),
        .m_apb_PADDR    (pm_apb_PADDR),
        .m_apb_PWRITE   (pm_apb_PWRITE),
        .m_apb_PWDATA   (pm_apb_PWDATA),
        .m_apb_PSTRB    (pm_apb_PSTRB),
        .m_apb_PPROT    (pm_apb_PPROT),
        .m_apb_PRDATA   (pm_apb_PRDATA),
        .m_apb_PSLVERR  (pm_apb_PSLVERR),
        .cmd_valid      (s_cmd_valid[5]),
        .cmd_ready      (s_cmd_ready[5]),
        .cmd_pwrite     (s_cmd_pwrite[5]),
        .cmd_paddr      (s_cmd_paddr[5]),
        .cmd_pwdata     (s_cmd_pwdata[5]),
        .cmd_pstrb      (s_cmd_pstrb[5]),
        .cmd_pprot      (s_cmd_pprot[5]),
        .rsp_valid      (s_rsp_valid[5]),
        .rsp_ready      (s_rsp_ready[5]),
        .rsp_prdata     (s_rsp_prdata[5]),
        .rsp_pslverr    (s_rsp_pslverr[5])
    );

    // Slave 6: IOAPIC
    apb_master #(
        .ADDR_WIDTH (12),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_ioapic (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (ioapic_apb_PSEL),
        .m_apb_PENABLE  (ioapic_apb_PENABLE),
        .m_apb_PREADY   (ioapic_apb_PREADY),
        .m_apb_PADDR    (ioapic_apb_PADDR),
        .m_apb_PWRITE   (ioapic_apb_PWRITE),
        .m_apb_PWDATA   (ioapic_apb_PWDATA),
        .m_apb_PSTRB    (ioapic_apb_PSTRB),
        .m_apb_PPROT    (ioapic_apb_PPROT),
        .m_apb_PRDATA   (ioapic_apb_PRDATA),
        .m_apb_PSLVERR  (ioapic_apb_PSLVERR),
        .cmd_valid      (s_cmd_valid[6]),
        .cmd_ready      (s_cmd_ready[6]),
        .cmd_pwrite     (s_cmd_pwrite[6]),
        .cmd_paddr      (s_cmd_paddr[6]),
        .cmd_pwdata     (s_cmd_pwdata[6]),
        .cmd_pstrb      (s_cmd_pstrb[6]),
        .cmd_pprot      (s_cmd_pprot[6]),
        .rsp_valid      (s_rsp_valid[6]),
        .rsp_ready      (s_rsp_ready[6]),
        .rsp_prdata     (s_rsp_prdata[6]),
        .rsp_pslverr    (s_rsp_pslverr[6])
    );

    // Slave 7: GPIO
    apb_master #(
        .ADDR_WIDTH (12),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_gpio (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (gpio_apb_PSEL),
        .m_apb_PENABLE  (gpio_apb_PENABLE),
        .m_apb_PREADY   (gpio_apb_PREADY),
        .m_apb_PADDR    (gpio_apb_PADDR),
        .m_apb_PWRITE   (gpio_apb_PWRITE),
        .m_apb_PWDATA   (gpio_apb_PWDATA),
        .m_apb_PSTRB    (gpio_apb_PSTRB),
        .m_apb_PPROT    (gpio_apb_PPROT),
        .m_apb_PRDATA   (gpio_apb_PRDATA),
        .m_apb_PSLVERR  (gpio_apb_PSLVERR),
        .cmd_valid      (s_cmd_valid[7]),
        .cmd_ready      (s_cmd_ready[7]),
        .cmd_pwrite     (s_cmd_pwrite[7]),
        .cmd_paddr      (s_cmd_paddr[7]),
        .cmd_pwdata     (s_cmd_pwdata[7]),
        .cmd_pstrb      (s_cmd_pstrb[7]),
        .cmd_pprot      (s_cmd_pprot[7]),
        .rsp_valid      (s_rsp_valid[7]),
        .rsp_ready      (s_rsp_ready[7]),
        .rsp_prdata     (s_rsp_prdata[7]),
        .rsp_pslverr    (s_rsp_pslverr[7])
    );

    // Slave 8: UART 16550
    apb_master #(
        .ADDR_WIDTH (12),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_uart (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (uart_apb_PSEL),
        .m_apb_PENABLE  (uart_apb_PENABLE),
        .m_apb_PREADY   (uart_apb_PREADY),
        .m_apb_PADDR    (uart_apb_PADDR),
        .m_apb_PWRITE   (uart_apb_PWRITE),
        .m_apb_PWDATA   (uart_apb_PWDATA),
        .m_apb_PSTRB    (uart_apb_PSTRB),
        .m_apb_PPROT    (uart_apb_PPROT),
        .m_apb_PRDATA   (uart_apb_PRDATA),
        .m_apb_PSLVERR  (uart_apb_PSLVERR),
        .cmd_valid      (s_cmd_valid[8]),
        .cmd_ready      (s_cmd_ready[8]),
        .cmd_pwrite     (s_cmd_pwrite[8]),
        .cmd_paddr      (s_cmd_paddr[8]),
        .cmd_pwdata     (s_cmd_pwdata[8]),
        .cmd_pstrb      (s_cmd_pstrb[8]),
        .cmd_pprot      (s_cmd_pprot[8]),
        .rsp_valid      (s_rsp_valid[8]),
        .rsp_ready      (s_rsp_ready[8]),
        .rsp_prdata     (s_rsp_prdata[8]),
        .rsp_pslverr    (s_rsp_pslverr[8])
    );

    // Slave 9: Reserved
    apb_master #(
        .ADDR_WIDTH (12),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH),
        .PROT_WIDTH (3)
    ) u_apb_master_rsvd (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (rsvd_apb_PSEL),
        .m_apb_PENABLE  (rsvd_apb_PENABLE),
        .m_apb_PREADY   (rsvd_apb_PREADY),
        .m_apb_PADDR    (rsvd_apb_PADDR),
        .m_apb_PWRITE   (rsvd_apb_PWRITE),
        .m_apb_PWDATA   (rsvd_apb_PWDATA),
        .m_apb_PSTRB    (rsvd_apb_PSTRB),
        .m_apb_PPROT    (rsvd_apb_PPROT),
        .m_apb_PRDATA   (rsvd_apb_PRDATA),
        .m_apb_PSLVERR  (rsvd_apb_PSLVERR),
        .cmd_valid      (s_cmd_valid[9]),
        .cmd_ready      (s_cmd_ready[9]),
        .cmd_pwrite     (s_cmd_pwrite[9]),
        .cmd_paddr      (s_cmd_paddr[9]),
        .cmd_pwdata     (s_cmd_pwdata[9]),
        .cmd_pstrb      (s_cmd_pstrb[9]),
        .cmd_pprot      (s_cmd_pprot[9]),
        .rsp_valid      (s_rsp_valid[9]),
        .rsp_ready      (s_rsp_ready[9]),
        .rsp_prdata     (s_rsp_prdata[9]),
        .rsp_pslverr    (s_rsp_pslverr[9])
    );

endmodule : apb_xbar_rlb_1to10
