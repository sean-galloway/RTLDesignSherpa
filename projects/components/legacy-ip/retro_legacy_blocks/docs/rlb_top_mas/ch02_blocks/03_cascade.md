<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# RLB Top - The 8259 Cascade Cross-Connect

## Overview

The subsystem carries a PC/AT interrupt pair: `u_pic` is the master
(window 1), `u_pic_slave` is the slave (window 9), and the two are wired
together inside `rlb_top` exactly as the cascaded configuration the
8259 was designed for. The cross-connect between them is three named
signals — the only internal state path `rlb_top` owns besides the
interrupt fabric. This page is the wiring in detail; the software
sequences that bring the pair up are in
[Chapter 4.1](../ch04_programming/01_initialization.md).

## Why the Pair Exists At All

Sixteen interrupt inputs need two 8259s: the master covers IRQ0-7, the
slave covers IRQ8-15. The slave's window at 0xFEC09000 is what makes
IRQ8-15 exist — and IRQ8 in particular is the line HPET timer 1 replaces
when legacy-replacement mode is on (RLB/hpet TASK-003).

## The Three-Wire Cross-Connect

| Signal | From | To | Carries |
| --- | --- | --- | --- |
| `w_spic_int` | slave `int_out` | master IR2 (forced) | The slave's interrupt request |
| `w_pic_cas_ack` | master `cas_ack` | slave `cas_ack_in` | The cascade acknowledge |
| `w_spic_vector` | slave `inta_vector_o` | master `cas_vector` | The slave's vector, returned by the master in place of its own |

The remaining cascade pins are tied or left open by role: the master is
`cas_ack_in = 1'b0` because nothing above it acknowledges its INT, and
its `inta_vector_o` is unconnected because nobody above consumes the
vector. The slave's `cas_vector` input is `8'h00` — it never forwards a
deeper cascade — and its `cas_ack` output is unconnected.

## The Master: IR2 Is Forced, Not OR-ed

The master's interrupt input is:

```systemverilog
assign w_master_pic_irq = ((pic_irq_in[7:0] | w_boot_intx_pic_irq
                            | w_fabric_irq[7:0]) & 8'hFB)
                        | {5'b0, w_spic_int, 2'b0};
```

Reading it inside out: the external inputs, the boot-interrupt reroute,
and the fabric's low half are OR-ed together, then **bit 2 is masked
off** (`& 8'hFB`), and then the slave's `INT` is forced onto that bit.
In a PC/AT pair, master IR2 belongs to the cascade — it carries the
slave's `INT`, not an external device — so an external IRQ2, or a
boot-interrupt reroute onto pin 2, would otherwise impersonate the
slave. Mask-then-force makes that impossible: every other master level
is unchanged, and IR2 is exactly the slave's request.

This is also why **IRQ2 reaches nothing from the outside**. The address
map and the interrupt map both still show the line; it is consumed
internally by construction.

## The Slave: An Inline Input Worth Naming

The slave's interrupt input is an inline expression, not a named signal:

```systemverilog
.irq_in (pic_irq_in[15:8] | w_fabric_irq[15:8]),
```

There is nothing to probe by name. With `pic_irq_in` held at zero, the
slave's IR line for a given IRQ is exactly `w_fabric_irq[irq]` — which is
how the `full` suite verifies the slave-routed sources per line: drive
the block, watch `w_fabric_irq[15:8]`, and the slave's view is known by
construction.

On the cascade side the slave exports its vector upward
(`inta_vector_o` → `w_spic_vector` → master's `cas_vector`), so when the
master acknowledges a slave-sourced interrupt, the vector the CPU
eventually reads is the slave's — the master returns it in place of its
own. That vector path is the entire reason `w_spic_vector` exists as a
named wire rather than a port-to-port connection.

## The Boot-Interrupt Side Effect

`u_ioapic_boot_intx` can reroute IOAPIC pins onto legacy PIC inputs, and
its identity map still names legacy input 2 for pin 2. That entry has
been **dead since the cascade took IR2**: a reroute onto pin 2 is masked
off the master's input before the slave's INT is forced on, so it
reaches nothing. The map keeps the entry so it still reads as the
published 82093AA identity mapping; an integrator who genuinely needs pin
2 rerouted must choose a different legacy input via `PIC_MAP`.

## Verification Heritage

The cross-connect is the subject of RLB/pic_8259 TASK-001. The `func`
suite proves the slave answers on window 9 and that the aggregated IRQ
reaches `rlb_irq_out`; the `full` suite adds the cascade invariant — a
slave-routed source delivered end to end through the master's `int_out` —
and coincident asserts spanning both controllers. The bring-up sequences
(single controller, cascaded pair) transcribed into Chapter 4.1 come from
the cocotb helpers `init_pic` and `init_pic_cascade`, which are known to
work because this suite passes.

## Related Documents

- [Block Hierarchy Overview](00_overview.md) - the two-instance wiring table
- [The Interrupt Fabric](02_interrupt_fabric.md) - what reaches the slave's IR lines
- [Initialization](../ch04_programming/01_initialization.md) - programming the pair (ICW3 master/slave values)
- [Window Map](../ch05_registers/01_register_map.md) - window 9 decode
