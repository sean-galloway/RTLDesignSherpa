// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: ioapic_boot_intx
// Description: Chipset boot-interrupt rerouting -- a masked IOAPIC pin also
//              drives its mapped legacy 8259 input (RLB-008).
//
// WHAT THIS IS, AND WHAT IT IS NOT. Boot interrupt is the CHIPSET behaviour
// where a device's INTx is rerouted to the legacy PIC while the IOAPIC is
// not delivering it, so an interrupt raised before the OS programs the
// IOAPIC is not lost. It is NOT INIT-SIPI-SIPI: that is a local APIC's
// AP-startup IPI and was never this block's business. RLB-008 carried that
// confusion for a while; this module is the corrected requirement.
//
// WHY A COMPANION. Same reason as ioapic_lowest_pri_arb, ioapic_deliv_merge
// and ioapic_msi_emit: apb4_ioapic's port list does not grow to hold system
// glue, and apb4_ioapic.f does not reference this file. The block exports
// the per-pin mask it already has; the rerouting, and the choice of which
// legacy input a pin lands on, live out here. An integrator that does not
// want boot interrupts simply does not instantiate it.
//
// COMBINATIONAL, so no clk/rst_n. The reroute is a function of three things
// that are all already stable: the pin, its mask bit and the enable. A clock
// port would exist only for symmetry, which is not a reason a port should
// exist -- the same call made in ioapic_msi_emit.
//
// THE GATE IS enable AND mask, and both terms matter (Sean, 2026-09-14):
//   - without the mask term a pin the IOAPIC is actively delivering would
//     ALSO reach the PIC, and the interrupt would be taken twice;
//   - without the enable term the only way to stop a deliberately masked pin
//     leaking to the PIC would be to unmask it, and an OS that has finished
//     programming the IOAPIC generally wants the crutch switched off.
//
// THE MAPPING is a packed parameter, PIC_IDX_W bits per pin, rather than an
// unpacked parameter array: unpacked parameter arrays are the kind of thing
// that survives simulation and then surprises a downstream tool. A field
// value of NUM_PIC or above means that pin does not reroute, and that is the
// DEFAULT for every pin -- rerouting is opt-in, so an integrator who
// instantiates this module without setting PIC_MAP gets no behaviour change.

`timescale 1ns / 1ps

module ioapic_boot_intx #(
    parameter int NUM_IRQS  = 24,   // IOAPIC pins
    parameter int NUM_PIC   = 8,    // legacy PIC inputs (IRQ0-7)
    // Bits per map field. 4 holds 0..7 plus a no-reroute code, which is what
    // NUM_PIC = 8 needs; widen it only if NUM_PIC grows past 15.
    parameter int PIC_IDX_W = 4,
    // Field i (PIC_IDX_W bits) is the legacy input that IOAPIC pin i
    // reroutes to. Default: every field = NUM_PIC, i.e. nothing reroutes.
    parameter logic [NUM_IRQS*PIC_IDX_W-1:0] PIC_MAP =
        {NUM_IRQS{PIC_IDX_W'(NUM_PIC)}}
) (
    // The INTx lines themselves. These are the SAME signals the IOAPIC takes
    // on irq_in -- the pin is shared, which is the whole point: one source,
    // two possible destinations depending on whether the IOAPIC is
    // delivering it. Deliberately NOT taken from inside apb4_ioapic.
    input  logic [NUM_IRQS-1:0]  irq_in,

    // Per-pin IOREDTBL mask, exported by apb4_ioapic. 1 = masked, i.e. the
    // IOAPIC is NOT delivering this pin.
    input  logic [NUM_IRQS-1:0]  cfg_mask,

    // IOAPICBOOTINTX.enable, IOWIN selector 0x07.
    input  logic                 boot_intx_en,

    // Per-pin: this pin is rerouting right now. Exposed because it is the
    // crisp property -- reroute[i] == en && mask[i] && irq_in[i] -- and it
    // lets an integrator supply its own mapping instead of PIC_MAP.
    output logic [NUM_IRQS-1:0]  reroute,

    // The 8259-bound term: bit m is the OR of every rerouting pin mapped to
    // legacy input m.
    output logic [NUM_PIC-1:0]   pic_irq
);

    // ------------------------------------------------------------------
    // Per-pin reroute decision
    // ------------------------------------------------------------------
    assign reroute = irq_in & cfg_mask & {NUM_IRQS{boot_intx_en}};

    // ------------------------------------------------------------------
    // Map onto the legacy inputs
    // ------------------------------------------------------------------
    // A pin whose field is >= NUM_PIC matches no m and so contributes
    // nothing, which is how the no-reroute code works without a separate
    // test.
    always_comb begin
        pic_irq = '0;
        for (int m = 0; m < NUM_PIC; m++) begin
            for (int i = 0; i < NUM_IRQS; i++) begin
                if (PIC_MAP[i*PIC_IDX_W +: PIC_IDX_W] == PIC_IDX_W'(m)) begin
                    pic_irq[m] = pic_irq[m] | reroute[i];
                end
            end
        end
    end

`ifndef SYNTHESIS
    initial begin : param_check
        if (NUM_IRQS < 1)
            $error("ioapic_boot_intx: NUM_IRQS must be >= 1, got %0d",
                   NUM_IRQS);
        if (NUM_PIC < 1)
            $error("ioapic_boot_intx: NUM_PIC must be >= 1, got %0d",
                   NUM_PIC);
        if ((1 << PIC_IDX_W) <= NUM_PIC)
            $error("ioapic_boot_intx: PIC_IDX_W=%0d cannot hold NUM_PIC=%0d plus a no-reroute code",
                   PIC_IDX_W, NUM_PIC);
    end
`endif

endmodule : ioapic_boot_intx
