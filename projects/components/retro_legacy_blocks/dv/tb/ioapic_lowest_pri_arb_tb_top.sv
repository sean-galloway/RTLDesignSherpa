// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ioapic_lowest_pri_arb_tb_top
// Purpose: DV wrapper that puts ioapic_lowest_pri_arb where it actually goes --
//          on the far side of a real apb4_ioapic delivery channel (RLB-008).
//
// The formal proof covers the arbiter's contract at its own ports. What it
// CANNOT show is that the two halves fit: that the arbiter's deliv_ready and
// deliv_retry drive ioapic_core's handshake the way the core expects, and that
// a refusal actually causes the interrupt to be offered again. That needs the
// real block, so this wrapper wires them together and exports both sides.
//
// The IOAPIC's own ports are re-exported under their EXACT original names so
// IOAPICTB binds unchanged (it reads flat dut.pclk / dut.s_apb_* / dut.irq_in /
// dut.eoi_* and expects nothing hierarchical).
//
// irq_out_ready and irq_out_retry are OUTPUTS here, not inputs. The arbiter
// drives them now, so the testbench must not: a TB write would fight the RTL.
// That is why the paired TB class overrides setup_components() and
// wait_for_interrupt(), both of which drive those pins in IOAPICTB.
`timescale 1ns / 1ps

module ioapic_lowest_pri_arb_tb_top #(
    parameter int NUM_IRQS   = 24,
    parameter int CDC_ENABLE = 0,
    parameter int NUM_CPUS   = 4
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

    // --- the delivery channel, OBSERVED (the arbiter drives ready/retry) ---
    output logic                    irq_out_valid,
    output logic [7:0]              irq_out_vector,
    output logic [7:0]              irq_out_dest,
    output logic                    irq_out_dest_mode,
    output logic [2:0]              irq_out_deliv_mode,
    output logic                    irq_out_ready,
    output logic                    irq_out_retry,

    // --- the consumer's own state, driven by the testbench ---
    input  logic [7:0]              cpu_apic_id      [NUM_CPUS],
    input  logic [7:0]              cpu_logical_dest [NUM_CPUS],
    input  logic [7:0]              cpu_priority     [NUM_CPUS],
    input  logic [NUM_CPUS-1:0]     cpu_can_accept,

    // --- what the arbiter decided ---
    output logic [NUM_CPUS-1:0]     cpu_irq_valid,
    output logic [7:0]              cpu_irq_vector,
    output logic [2:0]              cpu_irq_deliv_mode
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
        // MSI config outputs (RLB-008): this harness exercises the
        // delivery channel, not MSI. Explicit and open -- omitting them
        // entirely is PINMISSING.
        .cfg_msi_addr       (),
        .cfg_msi_data       (),
        // Boot-interrupt support (RLB-008): this harness does not
        // exercise it. Explicit and open -- omitting them is
        // PINMISSING, which is an ERROR under cocotb's flags.
        .cfg_mask_vec       (),
        .cfg_boot_intx_en   ()
    );

    // The consumer half. Combinational, so the handshake closes in the same
    // cycle the core presents a message -- deliv_ready is deliv_valid.
    ioapic_lowest_pri_arb #(
        .NUM_CPUS (NUM_CPUS)
    ) u_arb (
        .deliv_valid        (irq_out_valid),
        .deliv_vector       (irq_out_vector),
        .deliv_dest         (irq_out_dest),
        .deliv_dest_mode    (irq_out_dest_mode),
        .deliv_deliv_mode   (irq_out_deliv_mode),
        .deliv_ready        (irq_out_ready),
        .deliv_retry        (irq_out_retry),
        .cpu_apic_id        (cpu_apic_id),
        .cpu_logical_dest   (cpu_logical_dest),
        .cpu_priority       (cpu_priority),
        .cpu_can_accept     (cpu_can_accept),
        .cpu_irq_valid      (cpu_irq_valid),
        .cpu_irq_vector     (cpu_irq_vector),
        .cpu_irq_deliv_mode (cpu_irq_deliv_mode)
    );

endmodule : ioapic_lowest_pri_arb_tb_top
