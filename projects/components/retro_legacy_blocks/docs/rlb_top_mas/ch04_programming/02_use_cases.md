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

# RLB Top - Use Cases

Six worked paths through the subsystem. Each one is exercised by the integration
test suite, so each is known to work as described.

## Use Case 1: A UART Interrupt Through the Master Controller

The simplest routing path: a source on a master line.

| Stage | Signal |
| --- | --- |
| Source | `uart_irq` from `u_uart` |
| Fabric line | IRQ4 (`IRQ_UART`, convention: COM1) |
| Master input | `w_master_pic_irq[4]` |
| Output | `pic_int_out` |

```c
pic_init_cascade(0x20, 0x28);       /* or pic_init_single(0x20) -- IRQ4 is a master line */
uart_enable_interrupts();           /* see uart_16550_mas */
/* uart_irq -> w_fabric_irq[4] -> master IR4 -> pic_int_out */
```

The vector the CPU sees is `master_base + 4`, so `0x24` with a base of `0x20`.

## Use Case 2: A GPIO Interrupt Through the Cascade

A source on a slave line. This is the common case, not the exception - four of
the six sourcing blocks land on the slave controller.

| Stage | Signal |
| --- | --- |
| Source | `gpio_irq` from `u_gpio` |
| Fabric line | IRQ11 (`IRQ_GPIO`, a **choice**, parameterised) |
| Slave input | slave IR3, because 11 - 8 = 3 |
| Slave output | `w_spic_int` |
| Master input | `w_master_pic_irq[2]`, forced from the slave |
| Output | `pic_int_out`, returning the **slave's** vector |

```c
pic_init_cascade(0x20, 0x28);       /* mandatory: IRQ11 is a slave line */
gpio_enable_interrupt(pin);         /* see gpio_mas */
```

The vector is `slave_base + 3`, so `0x2B` with a slave base of `0x28`. The master
returns the slave's vector in place of its own - that is what the cascade
acknowledge path is for.

Master IR2 rising here is **correct behaviour**, not a spurious cascade
interrupt. The invariant to check is that IR2 equals the slave's `INT`, never
that IR2 stays low.

## Use Case 3: The Same Source Through the IOAPIC

The fabric feeds the IOAPIC in parallel with the controllers. No source change is
needed - only IOAPIC configuration.

```c
ioapic_arm(11, 0x40 + 11, /* masked = */ 0);   /* unmask IRQ11's entry */
gpio_enable_interrupt(pin);
/* Delivery appears on ioapic_irq_out_valid with vector 0x4B. */
```

Both paths are live at once: the same GPIO assertion reaches the cascade *and*
produces an IOAPIC delivery. If you want only one, mask the other - mask the
IOAPIC entry, or mask the line in the controller's `OCW1`.

Remember the mask default. An entry you never programmed is masked, and a masked
entry delivers nothing while looking perfectly correct from the source side.

## Use Case 4: HPET Legacy Replacement

Replacing the 8254 tick and the RTC periodic interrupt with HPET timers.

| HPET output | Line | Replaces |
| --- | --- | --- |
| `hpet_legacy_irq0` | IRQ0 | 8254 channel 0 tick |
| `hpet_legacy_irq8` | IRQ8 | RTC periodic interrupt |

```c
hpet_set_legacy_replacement(1);     /* see hpet_mas */
pit_disable_counter(0);             /* avoid two sources on IRQ0 */
rtc_disable_periodic();             /* avoid two sources on IRQ8 */
```

The HPET core suppresses timers 0 and 1 on `hpet_timer_irq` while this mode is
active, so a single event cannot arrive twice from the HPET itself. Silencing the
8254 and the RTC is still your job: the fabric ORs all three onto those lines, so
leaving them enabled is legal and produces interrupts from sources you thought
you had replaced.

The general HPET timers are unaffected, and remain unrouted - they reach
`rlb_irq_out` and their own pins only.

## Use Case 5: Boot-Interrupt Rerouting

Catching a source whose IOAPIC entry is masked, so it is not lost during boot
before the IOAPIC is configured.

```c
ioapic_arm(irq, vector, /* masked = */ 1);     /* IOAPIC will NOT deliver */
ioapic_write(IOAPIC_BOOTINTX, 1);              /* reroute masked pins to the PIC */
/* The source now reaches the legacy controller instead. */
```

The map is the identity mapping for IOAPIC pins 0-7 onto legacy inputs 0-7, and
no reroute above pin 7.

**Pin 2 cannot be rerouted.** The map still names legacy input 2, but master IR2
is masked off every external source and driven from the slave controller, so a
reroute onto pin 2 reaches nothing. If you need pin 2's source on the legacy
path, pick a different legacy input.

Rerouting is disabled at reset, so the master's interrupt input is exactly
`pic_irq_in` until you perform the second write above.

## Use Case 6: One Interrupt Line for the Whole Subsystem

For a system that would rather not model ten interrupt sources.

```c
/* Wire rlb_irq_out to your controller. On assertion, poll to find the source. */
if (rlb_irq_out_asserted()) {
    /* Check each block's status register to identify the source. */
}
```

`rlb_irq_out` asserts while **any** block interrupt is asserted, including
`pic_int_out` itself. It carries no vector and no priority - it is a pure OR, and
identifying the source means polling. It drives nothing inside the subsystem,
which is precisely why including the controller's own output in it is safe.

This is also the path that sees the general HPET timers, which no other path
does.

## Coincident Sources

The fabric is combinational and per-line, so simultaneous sources are handled by
construction: each lands on its own line, and lines that share a source are OR-ed.
The integration suite exercises two, three and four coincident sources, spanning
both controllers - for example the UART on master IR4 while SMBus, ACPI and GPIO
assert together under the cascade.

Two practical notes from that testing:

- **Some sources are slow to assert.** ACPI takes tens of clocks from
  `pm_gpe_events` to `pm_interrupt`, and SMBus considerably longer. Code that
  expects a source to be asserted a few cycles after its stimulus will sample
  too early.
- **Priority is the controller's job, not the fabric's.** The fabric presents
  every asserted line at once; which one the CPU services is decided by the 8259
  priority logic, or by the IOAPIC's delivery configuration.

## Related Documents

- [Initialization](01_initialization.md) - the bring-up sequences these use cases assume
- [Architecture](../ch01_overview/02_architecture.md) - the fabric, cascade and aggregate
- [Window Map](../ch05_registers/01_register_map.md)
