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

# RLB Top - Overview

## What This Block Is

`rlb_top` is the integration level of the Retro Legacy Blocks subsystem. It
takes one APB4 slave port and presents, behind it, a complete set of
PC-compatible legacy peripherals: two interrupt controllers, an IOAPIC, two
timers, a real-time clock, an SMBus controller, a GPIO controller, a UART, and
a power-management block.

It is not a peripheral. It contains no registers of its own, implements no
protocol, and every address it answers belongs to something it instantiates.
What it does contribute is three things that exist nowhere else in the
subsystem:

1. **An address map.** A 1-to-10 APB crossbar splits one slave port into ten
   4KB windows from `BASE_ADDR`, and answers an unmapped address with
   `PSLVERR` rather than hanging.
2. **An interrupt fabric.** Each block's interrupt output is routed internally
   onto its conventional legacy line and delivered to both 8259s and to the
   IOAPIC, so a board does not have to wire ten interrupt pins back in.
3. **A cascade.** The two 8259 instances are cross-connected as a PC/AT
   master and slave pair, with the vector and acknowledge path between them.

## Why It Is a Separate Specification

Each of the nine other books in this directory specifies one block. None of
them can specify the above, because none of them can see it: a block knows its
own interrupt output pin, not which controller that pin reaches, and certainly
not what happens when two blocks assert at once.

Before this book existed, the routing table and the bring-up order lived only
in the testbench under `dv/tbclasses/rlb_top/`. That is a workable place to
verify behaviour and a poor place to look it up.

## Block Inventory

Ten windows, all assigned. There is no reserved window.

| Window | Address range | Block | Instance | Specification |
| --- | --- | --- | --- | --- |
| 0 | `0xFEC0_0000` - `0xFEC0_0FFF` | HPET | `u_hpet` | [hpet_mas](../../hpet_mas/hpet_mas_index.md) |
| 1 | `0xFEC0_1000` - `0xFEC0_1FFF` | 8259 PIC (master) | `u_pic` | [pic_8259_mas](../../pic_8259_mas/pic_8259_mas_index.md) |
| 2 | `0xFEC0_2000` - `0xFEC0_2FFF` | 8254 PIT | `u_pit` | [pit_8254_mas](../../pit_8254_mas/pit_8254_mas_index.md) |
| 3 | `0xFEC0_3000` - `0xFEC0_3FFF` | RTC | `u_rtc` | [rtc_mas](../../rtc_mas/rtc_mas_index.md) |
| 4 | `0xFEC0_4000` - `0xFEC0_4FFF` | SMBus | `u_smbus` | [smbus_mas](../../smbus_mas/smbus_mas_index.md) |
| 5 | `0xFEC0_5000` - `0xFEC0_5FFF` | PM/ACPI | `u_pm_acpi` | [pm_acpi_mas](../../pm_acpi_mas/pm_acpi_mas_index.md) |
| 6 | `0xFEC0_6000` - `0xFEC0_6FFF` | IOAPIC | `u_ioapic` | [ioapic_mas](../../ioapic_mas/ioapic_mas_index.md) |
| 7 | `0xFEC0_7000` - `0xFEC0_7FFF` | GPIO | `u_gpio` | [gpio_mas](../../gpio_mas/gpio_mas_index.md) |
| 8 | `0xFEC0_8000` - `0xFEC0_8FFF` | UART 16550 | `u_uart` | [uart_16550_mas](../../uart_16550_mas/uart_16550_mas_index.md) |
| 9 | `0xFEC0_9000` - `0xFEC0_9FFF` | 8259 PIC (cascade slave) | `u_pic_slave` | [pic_8259_mas](../../pic_8259_mas/pic_8259_mas_index.md) |

Two further instances carry no address window:

| Instance | Module | Contribution |
| --- | --- | --- |
| `u_apbx_xbar` | `apbx_xbar_1to10` | The address decode. Generated, not hand-written. |
| `u_ioapic_boot_intx` | `ioapic_boot_intx` | Turns "the IOAPIC is not delivering this pin" into a legacy PIC input. |

Twelve instances in total.

## Features

- Single APB4 slave entry point, 32-bit address and data, with `PSTRB` and
  `PPROT` carried through to every block
- Ten 4KB windows on a clean power-of-two decode: the slave index is
  `PADDR[15:12]`
- Unmapped addresses complete with `PSLVERR` instead of stalling the bus
- Interrupt fabric covering six sourcing blocks, presented on the conventional
  legacy IRQ lines
- Both 8259s cross-connected as a cascaded pair, with master IR2 protected
- A single aggregated `rlb_irq_out` for a system that wants one interrupt input
  rather than ten
- Boot-interrupt rerouting available and disabled by default
- External `pic_irq_in` and `ioapic_irq_in` retained as inputs and OR-ed with
  the internal fabric, so an existing board keeps its interrupt path

## Deliberate Scope Boundaries

These are decisions, not defects. Each is recorded here because each one looks
like a bug to somebody reading the RTL for the first time.

**IRQ2 is never driven by the fabric.** In a PC/AT pair, master IR2 belongs to
the cascade: it carries the slave controller's `INT`, not a device. `rlb_top`
masks IR2 off every other source and forces it from the slave, so an interrupt
routed to IRQ2 reaches nothing. This is also why IRQ8 exists as a line at all.

**The general HPET timers are not routed.** `hpet_timer_irq` has no
conventional legacy line, which is the same reason the HPET's
`TIMER_INT_ROUTE_CAP` field reads 0. Those timers reach `rlb_irq_out` and their
own output pins. Only the two legacy-replacement outputs, `hpet_legacy_irq0`
and `hpet_legacy_irq8`, enter the fabric.

**`ioapic_msi_emit` is not instantiated.** Software can program `cfg_msi_addr`
and `cfg_msi_data` through the IOAPIC's `IOWIN`, but nothing in this subsystem
consumes them. The pins are connected and deliberately left open rather than
omitted, because an omitted pin is a `PINMISSING` warning that hides the gap.

**Boot-interrupt rerouting has a default map, not a board map.** The pin to
legacy-input mapping is a board and chipset decision. The default is the
published identity mapping for pins 0-7 with no reroute above that, and
rerouting is disabled at reset.

**Every block is instantiated with `CDC_ENABLE(0)`.** The per-block clock and
reset ports are present on `rlb_top`'s boundary but unused in this
configuration. See [Clocks and Reset](03_clocks_and_reset.md).

## Applications

- A drop-in legacy peripheral subsystem for a soft-core SoC on FPGA
- A target for firmware and driver development against PC-compatible
  peripherals without the hardware
- A worked example of an integration level: generated address decode, an
  interrupt fabric with convention-versus-choice documented, and a cascade

## Related Documents

- [Architecture](02_architecture.md) - how the pieces fit together
- [Top-Level Interface](../ch03_interfaces/01_top_level.md) - the integration contract
- [Initialization](../ch04_programming/01_initialization.md) - bring-up order
- [Window Map](../ch05_registers/01_register_map.md) - the address map in detail
