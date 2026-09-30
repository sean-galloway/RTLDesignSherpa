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

# RLB Top - Address Map

## rlb_top Has No Registers

`rlb_top` implements no registers of its own. Every address it answers belongs to
a block it instantiates. This chapter is therefore the **window map** - how an
address is decoded, and which specification documents the registers inside each
window.

## Decode

| Property | Value |
| --- | --- |
| Base | `BASE_ADDR`, default `0xFEC0_0000` |
| Window size | `0x1000` (4KB) |
| Windows | 10, indices 0-9 |
| Slave index | `PADDR[15:12]` |
| Offset within a block | `PADDR[11:0]` |
| Reserved | none - all ten windows are assigned |
| Unmapped | completes with `PSLVERR`; does not hang |

The decode is a clean power of two: the window number *is* `PADDR[15:12]`, and
the address a block sees is the low twelve bits. A block's own register map is
therefore documented in offsets from `0x000`, and the subsystem address is
`BASE_ADDR + window * 0x1000 + offset`.

## Window Map

| Window | Address range | Block | Register map |
| --- | --- | --- | --- |
| 0 | `0xFEC0_0000` - `0xFEC0_0FFF` | HPET | [hpet_mas ch05_registers/01_register_map.md](../../hpet_mas/ch05_registers/01_register_map.md) |
| 1 | `0xFEC0_1000` - `0xFEC0_1FFF` | 8259 PIC (master) | [pic_8259_mas ch05_registers/01_register_map.md](../../pic_8259_mas/ch05_registers/01_register_map.md) |
| 2 | `0xFEC0_2000` - `0xFEC0_2FFF` | 8254 PIT | [pit_8254_mas ch05_registers/01_register_map.md](../../pit_8254_mas/ch05_registers/01_register_map.md) |
| 3 | `0xFEC0_3000` - `0xFEC0_3FFF` | RTC | [rtc_mas ch05_registers/01_register_map.md](../../rtc_mas/ch05_registers/01_register_map.md) |
| 4 | `0xFEC0_4000` - `0xFEC0_4FFF` | SMBus | [smbus_mas ch05_registers/01_register_map.md](../../smbus_mas/ch05_registers/01_register_map.md) |
| 5 | `0xFEC0_5000` - `0xFEC0_5FFF` | PM/ACPI | [pm_acpi_mas ch05_registers/01_register_map.md](../../pm_acpi_mas/ch05_registers/01_register_map.md) |
| 6 | `0xFEC0_6000` - `0xFEC0_6FFF` | IOAPIC | [ioapic_mas ch05_registers/01_register_map.md](../../ioapic_mas/ch05_registers/01_register_map.md) |
| 7 | `0xFEC0_7000` - `0xFEC0_7FFF` | GPIO | [gpio_mas ch05_registers/01_register_map.md](../../gpio_mas/ch05_registers/01_register_map.md) |
| 8 | `0xFEC0_8000` - `0xFEC0_8FFF` | UART 16550 | [uart_16550_mas ch05_registers/01_register_map.md](../../uart_16550_mas/ch05_registers/01_register_map.md) |
| 9 | `0xFEC0_9000` - `0xFEC0_9FFF` | 8259 PIC (cascade slave) | [pic_8259_mas ch05_registers/01_register_map.md](../../pic_8259_mas/ch05_registers/01_register_map.md) |

Windows 1 and 9 are the same block with the same register map, wired as a master
and slave pair. The registers are identical; what differs is the cascade
configuration written into them. See
[Initialization](../ch04_programming/01_initialization.md).

## Read-Safe Probe Registers

For confirming a window is alive without disturbing it.

| Window | Block | Probe offset | Register |
| --- | --- | --- | --- |
| 0 | HPET | `0x000` | `HPET_ID`, read-only identity |
| 1 | PIC (master) | `0x000` | `PIC_CONFIG` |
| 2 | PIT | `0x000` | `PIT_CONFIG` |
| 3 | RTC | `0x000` | `RTC_CONFIG` |
| 4 | SMBus | `0x000` | `SMBUS_CONTROL` |
| 5 | PM/ACPI | `0x000` | `ACPI_CONTROL` |
| 6 | IOAPIC | `0x000` | `IOREGSEL` |
| 7 | GPIO | `0x000` | `GPIO_CONTROL` |
| 8 | UART 16550 | **`0x020`** | `UART_SCR` scratch - **not** `0x000` |
| 9 | PIC (slave) | `0x000` | `PIC_CONFIG` |

**The UART is the exception and it matters.** Offset `0x000` in the UART window
is the receive buffer; reading it pops a byte off the RX FIFO. Probe the scratch
register at `0x020` instead. An identity read that quietly consumes received data
is a genuinely difficult bug to find.

## The IOAPIC Is Indirect

The IOAPIC occupies a 4KB window but exposes only two directly addressed
registers. Everything else is reached by writing an index to `IOREGSEL` and then
the data to `IOWIN`. The redirection table in particular is two 32-bit halves per
pin, reached through that indirection - so an IOAPIC "register offset" in the
IOAPIC specification is a selector value, not a window offset.

## Interrupt Line Assignments

Not registers, but the other half of the programming surface. The line numbers
are fixed in hardware for convention assignments and parameterised for choices.

| Line | Source | Basis | Controller input |
| --- | --- | --- | --- |
| IRQ0 | `pit_timer_irq[0]` OR `hpet_legacy_irq0` | convention | master IR0 |
| IRQ2 | cascade only - never driven by the fabric | convention | master IR2, from the slave's `INT` |
| IRQ4 | `uart_irq` | convention | master IR4 |
| IRQ8 | `rtc_alarm_irq` OR `rtc_second_irq` OR `hpet_legacy_irq8` | convention | slave IR0 |
| IRQ9 | `pm_interrupt` | convention | slave IR1 |
| IRQ10 | `smb_interrupt` | **choice**, parameter `IRQ_SMBUS` | slave IR2 |
| IRQ11 | `gpio_irq` | **choice**, parameter `IRQ_GPIO` | slave IR3 |

Each line also reaches the IOAPIC pin of the same number. The IOAPIC's vector for
a pin is whatever software programs into that pin's redirection entry; there is no
hardware-fixed vector.

## Related Documents

- [Top-Level Interface](../ch03_interfaces/01_top_level.md) - the decode contract and port list
- [Initialization](../ch04_programming/01_initialization.md) - the address helper and bring-up order
- [Architecture](../ch01_overview/02_architecture.md) - how a line reaches its destinations
