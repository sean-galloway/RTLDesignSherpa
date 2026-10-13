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

# RLB Top - Interrupt Pin Reference

## Overview

This page answers the pin-level question: **which line does each block's
interrupt land on, and where does each external interrupt pin go?** The
routing intent — convention versus choice, OR-ed rather than
substituted, IRQ2 never driven — is documented in
[The Interrupt Fabric](../ch02_blocks/02_interrupt_fabric.md). This page
is the table a firmware or board engineer looks up a single pin in.
Nothing here invents behaviour: every row is a signal on `rlb_top`'s
port list, and the port list is in
[Top-Level Interface](01_top_level.md).

## Block Interrupt Outputs, Pin by Pin

| RTL pin | Fabric line | Master 8259 | Slave 8259 | IOAPIC pin | `rlb_irq_out` | Notes |
| --- | --- | --- | --- | --- | --- | --- |
| `pit_timer_irq[0]` | IRQ0 | IR0 | — | 0 | yes | 8254 channel-0 tick |
| `pit_timer_irq[2:1]` | none | — | — | — | yes | Channels 1-2 leave on their pins and the aggregate only |
| `hpet_legacy_irq0` | IRQ0 | IR0 | — | 0 | yes | Only while `HPET_CONFIG.legacy_replacement` is set; suppresses `hpet_timer_irq[0]` while set |
| `hpet_legacy_irq8` | IRQ8 | — | IR0 | 8 | yes | Only while legacy replacement is set; suppresses `hpet_timer_irq[1]` while set |
| `hpet_timer_irq[1:0]` | none | — | — | — | yes | **Deliberately not routed** — no conventional legacy line; `TIMER_INT_ROUTE_CAP` reads 0 for the same reason |
| `uart_irq` | IRQ4 | IR4 | — | 4 | yes | COM1 by convention |
| `rtc_alarm_irq` | IRQ8 | — | IR0 | 8 | yes | Shares IRQ8 with `rtc_second_irq` and `hpet_legacy_irq8` |
| `rtc_second_irq` | IRQ8 | — | IR0 | 8 | yes | Periodic interrupt |
| `smb_interrupt` | IRQ10 | — | IR2 | 10 | yes | **Choice** — parameter `IRQ_SMBUS` |
| `pm_interrupt` | IRQ9 | — | IR1 | 9 | yes | ACPI by convention; PM wake inputs (`pm_rtc_alarm`, `pm_ext_wake_n`, GPE banks) feed the PM block, not the fabric |
| `gpio_irq` | IRQ11 | — | IR3 | 11 | yes | **Choice** — parameter `IRQ_GPIO` |
| `pic_int_out` | none | — | — | — | yes | The master's delivered output. Fed back to nothing internally — a loop — it appears **only** in the aggregate |
| `ioapic_irq_out_*` | n/a | — | — | — | no | A message interface (`valid`, `vector`, `dest`, `deliv_mode`, `dest_mode`), not a level line; consumed by the receiver above the subsystem |

Rows saying "IR0" for the slave mean the slave's interrupt input bit 0,
which **is** IRQ8 in system numbering — the slave covers IRQ8-15. Rows
saying "none" under Fabric reach the aggregate and their own pins only.

## The Sixteen Legacy Lines As the Controllers See Them

| IRQ | Master IR | Slave IR | IOAPIC pin | Source(s) on the fabric | Fixed or parameter |
| --- | --- | --- | --- | --- | --- |
| 0 | IR0 | — | 0 | `pit_timer_irq[0]`, `hpet_legacy_irq0` | convention |
| 1 | IR1 | — | 1 | none | — |
| 2 | — | — | — | **never driven** — cascade input, forced from the slave's `INT` | — |
| 3 | IR3 | — | 3 | none | — |
| 4 | IR4 | — | 4 | `uart_irq` | convention |
| 5 | IR5 | — | 5 | none | — |
| 6 | IR6 | — | 6 | none | — |
| 7 | IR7 | — | 7 | none | — |
| 8 | — | IR0 | 8 | `rtc_alarm_irq`, `rtc_second_irq`, `hpet_legacy_irq8` | convention |
| 9 | — | IR1 | 9 | `pm_interrupt` | convention |
| 10 | — | IR2 | 10 | `smb_interrupt` | parameter `IRQ_SMBUS` |
| 11 | — | IR3 | 11 | `gpio_irq` | parameter `IRQ_GPIO` |
| 12 | — | IR4 | 12 | none | — |
| 13 | — | IR5 | 13 | none | — |
| 14 | — | IR6 | 14 | none | — |
| 15 | — | IR7 | 15 | none | — |

IOAPIC pins 16-23 exist on the boundary (`IOAPIC_NUM_IRQS` = 24) and
are sourced only by the board, through `ioapic_irq_in` — the subsystem
drives no fabric line above 15.

## External Interrupt Input Pins

| Pin | Feeds | Notes |
| --- | --- | --- |
| `pic_irq_in[7:0]` | Master, OR-ed with boot-interrupt reroute and fabric lines 0-7 | Bit 2 is **ignored**: masked off before the slave's `INT` is forced onto IR2, so driving it reaches nothing |
| `pic_irq_in[15:8]` | Slave, OR-ed with fabric lines 8-15 | System IRQ8-15 |
| `ioapic_irq_in[23:0]` | IOAPIC pins, OR-ed with the zero-extended fabric; also feeds `u_ioapic_boot_intx` | Pins 0-7 can be rerouted onto legacy inputs when the IOAPIC is not delivering them (see below); a reroute onto pin 2 is a dead entry |
| `ioapic_eoi_in`, `ioapic_eoi_vector[7:0]` | IOAPIC EOI input | End-of-interrupt from the local APIC side |
| `ioapic_irq_out_ready`, `ioapic_irq_out_retry` | Delivery handshake inputs | Tie `retry` low if the receiver always accepts |

## The Aggregate

`rlb_irq_out` is a pure OR of: `hpet_timer_irq`, `hpet_legacy_irq0`,
`hpet_legacy_irq8`, `pic_int_out`, `pit_timer_irq`, `rtc_alarm_irq`,
`rtc_second_irq`, `smb_interrupt`, `pm_interrupt`, `gpio_irq`,
`uart_irq`. It exists for a SoC that wants one interrupt input rather
than ten pins; it drives nothing inside the subsystem, which is why
including `pic_int_out` in it is safe. The IOAPIC's message-style
delivery output is **not** part of it.

## Scope Boundaries Restated

Three integration decisions live at this boundary and are choices, not
defects:

- `hpet_timer_irq` is not routed into the fabric (first table, third row).
- The two MSI configuration outputs (`cfg_msi_addr`, `cfg_msi_data`) are
  connected and left open — `ioapic_msi_emit` is not instantiated.
- Boot-interrupt rerouting exists (`u_ioapic_boot_intx`) but its
  pin-to-legacy map defaults to the identity mapping for pins 0-7 and no
  reroute above that; the pin-2 entry is dead because IRQ2 is the
  cascade input.

## Related Documents

- [The Interrupt Fabric](../ch02_blocks/02_interrupt_fabric.md) - why the table above looks the way it does
- [The Cascade Cross-Connect](../ch02_blocks/03_cascade.md) - why IRQ2 is never driven
- [Initialization](../ch04_programming/01_initialization.md) - programming the controllers to receive these lines
- [Use Cases](../ch04_programming/02_use_cases.md) - one interrupt routed end to end
