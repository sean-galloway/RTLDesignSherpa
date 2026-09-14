// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ioapic_msi_emit_tb_top
// Purpose: DV wrapper that puts ioapic_msi_emit where it actually goes --
//          on the far side of a real apb4_ioapic delivery channel, driving
//          a real apb4_master_stub (RLB-008).
//
// The formal proof covers the emitter's mapping at its own ports, with
// msi_addr_base and msi_data_template as FREE variables and rsp_data as
// anyseq. It deliberately does not instantiate the master:
// "apb4_master_stub's closure would prove the MASTER, not the emitter".
//
// That leaves one thing nothing has checked, and it is the whole point of
// making the address and data REGISTERS rather than parameters: that a value
// SOFTWARE writes through IOREGSEL/IOWIN is the value that appears on the
// bus. The path is IOWIN -> regblock -> cfg_msi_addr -> msi_addr_base ->
// cmd_data -> PADDR, and every hop of it is outside the formal harness.
//
// The IOAPIC's own ports are re-exported under their EXACT original names so
// IOAPICTB binds unchanged (it reads flat dut.pclk / dut.s_apb_* /
// dut.irq_in / dut.eoi_*).
//
// irq_out_ready and irq_out_retry are OUTPUTS here. The emitter drives them,
// so the testbench must not: a TB write would fight the RTL. That is why the
// paired TB class reimplements setup_components() and reset_dut(), and
// disables the three inherited helpers that drive those pins.
//
// The m_apb_* names are not cosmetic: APBSlave/APBMonitor bind by composing
// prefix + "_" + signal, and their required set is PSEL, PWRITE, PENABLE,
// PADDR, PWDATA, PRDATA, PREADY. Rename these and the BFM raises at bind
// time.
`timescale 1ns / 1ps

module ioapic_msi_emit_tb_top #(
    parameter int NUM_IRQS   = 24,
    parameter int CDC_ENABLE = 0,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH / 8
) (
    // --- apb4_ioapic ports, names preserved for IOAPICTB ---
    input  logic                    pclk,
    input  logic                    presetn,
    input  logic                    ioapic_clk,
    input  logic                    ioapic_resetn,
    input  logic                    s_apb_PSEL,
    input  logic                    s_apb_PENABLE,
    output logic                    s_apb_PREADY,
    input  logic [11:0]             s_apb_PADDR,
    input  logic                    s_apb_PWRITE,
    input  logic [31:0]             s_apb_PWDATA,
    input  logic [3:0]              s_apb_PSTRB,
    input  logic [2:0]              s_apb_PPROT,
    output logic [31:0]             s_apb_PRDATA,
    output logic                    s_apb_PSLVERR,
    input  logic [NUM_IRQS-1:0]     irq_in,
    input  logic                    eoi_in,
    input  logic [7:0]              eoi_vector,

    // --- the delivery channel, OBSERVED (the emitter drives ready/retry) ---
    output logic                    irq_out_valid,
    output logic [7:0]              irq_out_vector,
    output logic [7:0]              irq_out_dest,
    output logic                    irq_out_dest_mode,
    output logic [2:0]              irq_out_deliv_mode,
    output logic                    irq_out_ready,
    output logic                    irq_out_retry,

    // --- the MSI config the IOAPIC surfaces, observed so a test can
    //     prove the register path independently of the bus ---
    output logic [31:0]             cfg_msi_addr,
    output logic [31:0]             cfg_msi_data,

    // --- the MSI write itself, on a real APB master ---
    output logic                    m_apb_PSEL,
    output logic                    m_apb_PENABLE,
    output logic [ADDR_WIDTH-1:0]   m_apb_PADDR,
    output logic                    m_apb_PWRITE,
    output logic [DATA_WIDTH-1:0]   m_apb_PWDATA,
    output logic [STRB_WIDTH-1:0]   m_apb_PSTRB,
    output logic [2:0]              m_apb_PPROT,
    input  logic [DATA_WIDTH-1:0]   m_apb_PRDATA,
    input  logic                    m_apb_PSLVERR,
    input  logic                    m_apb_PREADY
);

    localparam int CPW = ADDR_WIDTH + DATA_WIDTH + STRB_WIDTH + 3 + 1 + 1 + 1;
    localparam int RPW = DATA_WIDTH + 1 + 1 + 1;

    logic           w_cmd_valid, w_cmd_ready;
    logic [CPW-1:0] w_cmd_data;
    logic           w_rsp_valid, w_rsp_ready;
    logic [RPW-1:0] w_rsp_data;

    apb4_ioapic #(
        .NUM_IRQS   (NUM_IRQS),
        .CDC_ENABLE (CDC_ENABLE)
    ) u_ioapic (
        .pclk               (pclk),
        .presetn            (presetn),
        .ioapic_clk         (ioapic_clk),
        .ioapic_resetn      (ioapic_resetn),
        .s_apb_PSEL         (s_apb_PSEL),
        .s_apb_PENABLE      (s_apb_PENABLE),
        .s_apb_PREADY       (s_apb_PREADY),
        .s_apb_PADDR        (s_apb_PADDR),
        .s_apb_PWRITE       (s_apb_PWRITE),
        .s_apb_PWDATA       (s_apb_PWDATA),
        .s_apb_PSTRB        (s_apb_PSTRB),
        .s_apb_PPROT        (s_apb_PPROT),
        .s_apb_PRDATA       (s_apb_PRDATA),
        .s_apb_PSLVERR      (s_apb_PSLVERR),
        .irq_in             (irq_in),
        .irq_out_valid      (irq_out_valid),
        .irq_out_vector     (irq_out_vector),
        .irq_out_dest       (irq_out_dest),
        .irq_out_dest_mode  (irq_out_dest_mode),
        .irq_out_deliv_mode (irq_out_deliv_mode),
        .irq_out_ready      (irq_out_ready),
        .irq_out_retry      (irq_out_retry),
        .eoi_in             (eoi_in),
        .eoi_vector         (eoi_vector),
        .cfg_msi_addr       (cfg_msi_addr),
        .cfg_msi_data       (cfg_msi_data),
        // Boot-interrupt support (RLB-008): this harness does not
        // exercise it. Explicit and open -- omitting them is
        // PINMISSING, which is an ERROR under cocotb's flags.
        .cfg_mask_vec       (),
        .cfg_boot_intx_en   ()
    );

    // The emitter. Combinational: the handshake closes in the same cycle the
    // master accepts, so deliv_ready is cmd_ready.
    ioapic_msi_emit #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .STRB_WIDTH (STRB_WIDTH)
    ) u_msi (
        .deliv_valid        (irq_out_valid),
        .deliv_vector       (irq_out_vector),
        .deliv_dest         (irq_out_dest),
        .deliv_dest_mode    (irq_out_dest_mode),
        .deliv_deliv_mode   (irq_out_deliv_mode),
        .deliv_ready        (irq_out_ready),
        .deliv_retry        (irq_out_retry),
        .msi_addr_base      (cfg_msi_addr),
        .msi_data_template  (cfg_msi_data),
        .cmd_valid          (w_cmd_valid),
        .cmd_ready          (w_cmd_ready),
        .cmd_data           (w_cmd_data),
        .rsp_valid          (w_rsp_valid),
        .rsp_ready          (w_rsp_ready),
        .rsp_data           (w_rsp_data)
    );

    // The real master. This turns the packed command into PSEL/PENABLE and
    // returns PSLVERR as a response, which is the only way the retry path
    // can be exercised end to end.
    apb4_master_stub #(
        .DATA_WIDTH (DATA_WIDTH),
        .ADDR_WIDTH (ADDR_WIDTH),
        .STRB_WIDTH (STRB_WIDTH)
    ) u_master (
        .pclk           (pclk),
        .presetn        (presetn),
        .m_apb_PSEL     (m_apb_PSEL),
        .m_apb_PENABLE  (m_apb_PENABLE),
        .m_apb_PADDR    (m_apb_PADDR),
        .m_apb_PWRITE   (m_apb_PWRITE),
        .m_apb_PWDATA   (m_apb_PWDATA),
        .m_apb_PSTRB    (m_apb_PSTRB),
        .m_apb_PPROT    (m_apb_PPROT),
        .m_apb_PRDATA   (m_apb_PRDATA),
        .m_apb_PSLVERR  (m_apb_PSLVERR),
        .m_apb_PREADY   (m_apb_PREADY),
        .cmd_valid      (w_cmd_valid),
        .cmd_ready      (w_cmd_ready),
        .cmd_data       (w_cmd_data),
        .rsp_valid      (w_rsp_valid),
        .rsp_ready      (w_rsp_ready),
        .rsp_data       (w_rsp_data)
    );

endmodule : ioapic_msi_emit_tb_top
