// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ioapic_boot_intx_tb_top
// Purpose: DV wrapper that puts ioapic_boot_intx where it actually goes --
//          beside a real apb4_ioapic, fed by that block's own mask export
//          and its own enable register (RLB-008).
//
// The formal proof covers the companion's contract at its own ports, with
// irq_in, cfg_mask and boot_intx_en as free variables. What it cannot show is
// that those three come from where they are supposed to: that cfg_mask really
// tracks the IOREDTBL mask bits software writes, and that boot_intx_en really
// is IOAPICBOOTINTX.enable reached through IOREGSEL/IOWIN. Both of those are
// register paths through the real block, and they are the whole point of this
// harness.
//
// UNLIKE the arb / merge / msi_emit wrappers, this one does NOT take the
// delivery handshake away from the testbench. ioapic_boot_intx never touches
// irq_out_ready or irq_out_retry -- it reads the mask, not the channel -- so
// IOAPICTB binds and behaves exactly as it does against the bare block, with
// no subclass and no disabled helpers.
//
// The IOAPIC's own ports are re-exported under their EXACT original names so
// IOAPICTB binds unchanged.

`timescale 1ns / 1ps

module ioapic_boot_intx_tb_top #(
    parameter int NUM_IRQS   = 24,
    parameter int CDC_ENABLE = 0,
    parameter int NUM_PIC    = 8
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
    output logic                    irq_out_valid,
    output logic [7:0]              irq_out_vector,
    output logic [7:0]              irq_out_dest,
    output logic                    irq_out_dest_mode,
    output logic [2:0]              irq_out_deliv_mode,
    input  logic                    irq_out_ready,
    input  logic                    irq_out_retry,
    input  logic                    eoi_in,
    input  logic [7:0]              eoi_vector,

    // --- what the block exports, observed so a test can separate a broken
    //     register path from a broken companion ---
    output logic [NUM_IRQS-1:0]     cfg_mask_vec,
    output logic                    cfg_boot_intx_en,

    // --- what the companion decided ---
    output logic [NUM_IRQS-1:0]     reroute,
    output logic [NUM_PIC-1:0]      pic_irq
);

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
        .cfg_msi_addr       (),
        .cfg_msi_data       (),
        .cfg_mask_vec       (cfg_mask_vec),
        .cfg_boot_intx_en   (cfg_boot_intx_en)
    );

    // Identity map for the low 8 pins: IOAPIC pin n -> legacy input n. Pins
    // 8 and above carry the no-reroute code (NUM_PIC), so the test can show
    // a masked, asserted, enabled pin that still reaches nothing -- which is
    // what proves the map is consulted rather than ignored.
    //
    // Field 0 is the LSB, so the identity fields are written last here.
    localparam logic [NUM_IRQS*4-1:0] PIC_MAP_ID = {
        {(NUM_IRQS-8){4'h8}},
        4'h7, 4'h6, 4'h5, 4'h4, 4'h3, 4'h2, 4'h1, 4'h0
    };

    ioapic_boot_intx #(
        .NUM_IRQS  (NUM_IRQS),
        .NUM_PIC   (NUM_PIC),
        .PIC_IDX_W (4),
        .PIC_MAP   (PIC_MAP_ID)
    ) u_boot_intx (
        .irq_in       (irq_in),
        .cfg_mask     (cfg_mask_vec),
        .boot_intx_en (cfg_boot_intx_en),
        .reroute      (reroute),
        .pic_irq      (pic_irq)
    );

endmodule : ioapic_boot_intx_tb_top
