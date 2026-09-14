// SPDX-License-Identifier: MIT
// Formal properties for ioapic_boot_intx (RLB-008).
//
// The module is combinational and dependency-free, so this harness pulls in
// nothing but the DUT -- same shape as ioapic_lowest_pri_arb and
// ioapic_msi_emit.
//
// A CONCRETE PIC_MAP is used rather than the default, because the default is
// "nothing reroutes" and pic_irq would be provably zero -- a proof that holds
// for the wrong reason. The map below is deliberately asymmetric so the OR
// and the no-reroute code are both exercised:
//
//   pin0 -> legacy 0      pin2 -> legacy 0   (so pic_irq[0] is an OR of two)
//   pin1 -> legacy 1      pin3 -> 2 == NUM_PIC, i.e. never reroutes
//
// Packed field i sits at [i*W +: W], so field0 is the LSB nibble:
//   {pin3, pin2, pin1, pin0} = {4'd2, 4'd0, 4'd1, 4'd0} = 16'h2010

`timescale 1ns / 1ps

module formal_ioapic_boot_intx;

    localparam int N = 4;   // NUM_IRQS
    localparam int P = 2;   // NUM_PIC
    localparam int W = 4;   // PIC_IDX_W

    (* anyseq *) reg [N-1:0] irq_in;
    (* anyseq *) reg [N-1:0] cfg_mask;
    (* anyseq *) reg         boot_intx_en;

    wire [N-1:0] reroute;
    wire [P-1:0] pic_irq;

    ioapic_boot_intx #(
        .NUM_IRQS  (N),
        .NUM_PIC   (P),
        .PIC_IDX_W (W),
        .PIC_MAP   (16'h2010)
    ) u_dut (
        .irq_in       (irq_in),
        .cfg_mask     (cfg_mask),
        .boot_intx_en (boot_intx_en),
        .reroute      (reroute),
        .pic_irq      (pic_irq)
    );

    always @(*) begin
        // P1: the reroute decision, per pin, exactly.
        ap_reroute_eq: assert (reroute ==
            (irq_in & cfg_mask & {N{boot_intx_en}}));

        // P2: disabled means nothing reroutes, whatever the masks say. This
        // is the half that lets an OS switch the crutch off.
        if (!boot_intx_en)
            ap_disabled_silent: assert (reroute == '0 && pic_irq == '0);

        // P3: an UNMASKED pin never reroutes. Without this term a pin the
        // IOAPIC is actively delivering would also reach the PIC and the
        // interrupt would be taken twice.
        ap_unmasked_never: assert ((reroute & ~cfg_mask) == '0);

        // P4: the map. pic_irq[0] is the OR of the two pins that land on it,
        // pic_irq[1] is the single pin that lands on it, and pin3 -- whose
        // field is the no-reroute code -- contributes to neither.
        ap_map_0: assert (pic_irq[0] == (reroute[0] | reroute[2]));
        ap_map_1: assert (pic_irq[1] ==  reroute[1]);
    end

    // Reachability: without these the asserts can pass vacuously.
    always @(*) begin
        cp_reroute:     cover (|reroute);
        cp_or_both:     cover (reroute[0] && reroute[2] && pic_irq[0]);
        cp_only_one:    cover (reroute[0] && !reroute[2] && pic_irq[0]);
        cp_pin1:        cover (pic_irq[1]);
        cp_no_reroute:  cover (irq_in[3] && cfg_mask[3] && boot_intx_en
                               && pic_irq == '0);
        cp_disabled:    cover (!boot_intx_en && |(irq_in & cfg_mask));
    end

endmodule
