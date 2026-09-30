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

# RLB Top - Architecture

## Hierarchy

```
rlb_top
├── u_apbx_xbar         apbx_xbar_1to10     one master, ten slaves (GENERATED)
├── u_hpet              apb4_hpet           window 0
├── u_pic               apb4_pic_8259       window 1   master of the pair
├── u_pic_slave         apb4_pic_8259       window 9   slave of the pair
├── u_pit               apb4_pit_8254       window 2
├── u_rtc               apb4_rtc            window 3
├── u_smbus             apb4_smbus          window 4
├── u_pm_acpi           apb4_pm_acpi        window 5
├── u_ioapic            apb4_ioapic         window 6
├── u_gpio              apb4_gpio           window 7
├── u_uart              apb4_uart_16550     window 8
└── u_ioapic_boot_intx  ioapic_boot_intx    no window; combinational companion
```

Everything else in the module is wiring and two pieces of combinational logic:
the interrupt fabric and the cascade cross-connect.

## The Address Path

One APB4 slave port enters the crossbar. The crossbar decodes `PADDR[15:12]`
into a slave index and forwards the transaction, including `PSTRB` and `PPROT`,
to that slave's port.

**The crossbar is generated.** It comes from the shared crossbar generator,
configured as one master, ten slaves, base `0xFEC00000`, 32-bit address and
data, 4KB per slave. Do not hand-edit `apbx_xbar_1to10.sv`. The generator owns
the decode-miss path, where an unmapped address completes with `PSLVERR`
instead of hanging, and a hand-rolled copy is exactly how that behaviour gets
lost - it already happened once to the crossbar this one replaced.

**The crossbar routes the full address; each block takes the low 12 bits.**
Every peripheral instantiation slices `PADDR[11:0]` off its window's channel.
A block therefore sees offsets from `0x000` within its own window and needs no
knowledge of `BASE_ADDR`. This is the one detail most likely to trip up a reader
comparing the top-level port width (32 bits) against a block's (12 bits).

| Property | Value |
| --- | --- |
| Base address | `BASE_ADDR`, default `0xFEC0_0000` |
| Window size | 4KB (`0x1000`) |
| Windows | 10, indices 0-9, none reserved |
| Slave index | `PADDR[15:12]` |
| Address seen by a block | `PADDR[11:0]` of its own window |
| Unmapped address | completes with `PSLVERR` |

## The Interrupt Fabric

Each block emits its interrupt on its own output pin, and those pins remain on
the boundary. The fabric additionally collects them into an internal 16-bit
vector, `w_fabric_irq`, on the conventional legacy line numbers, and feeds that
vector to three destinations.

### Source to line

| Source signal | Line | Basis | Reaches |
| --- | --- | --- | --- |
| `pit_timer_irq[0]` OR `hpet_legacy_irq0` | IRQ0 | convention (system timer) | master 8259 IR0, IOAPIC pin 0 |
| `uart_irq` | IRQ4 | convention (COM1) | master 8259 IR4, IOAPIC pin 4 |
| `rtc_alarm_irq` OR `rtc_second_irq` OR `hpet_legacy_irq8` | IRQ8 | convention (RTC alarm) | slave 8259 IR0, IOAPIC pin 8 |
| `pm_interrupt` | IRQ9 | convention (ACPI) | slave 8259 IR1, IOAPIC pin 9 |
| `smb_interrupt` | IRQ10 | **choice**, parameter `IRQ_SMBUS` | slave 8259 IR2, IOAPIC pin 10 |
| `gpio_irq` | IRQ11 | **choice**, parameter `IRQ_GPIO` | slave 8259 IR3, IOAPIC pin 11 |
| `hpet_timer_irq[*]` | none | no conventional line exists | `rlb_irq_out` and its own pins only |
| - | IRQ2 | reserved for the cascade | never driven by the fabric |

Convention versus choice is a real distinction here, and it is reflected in the
RTL. IRQ0, IRQ4, IRQ8 and IRQ9 come from the published typical-assignment table
reproduced in the IOAPIC specification, so they are fixed as `localparam` inside
the module: making them overridable would invite silently diverging from what
every driver already assumes. SMBus and GPIO have no traditional assignment -
the table offers only "Available" - so those two are this subsystem's choice and
are exposed as module parameters an integrator can move.

Two sources share IRQ0 and three share IRQ8. That is intentional and safe: HPET
legacy-replacement mode exists precisely to replace the 8254 tick and the RTC
periodic interrupt, and the HPET core suppresses timers 0 and 1 on
`hpet_timer_irq` while that mode is active, so the same event cannot arrive
twice.

### The three destinations

**Master 8259.** The master sees

```
w_master_pic_irq = ((pic_irq_in[7:0] | w_boot_intx_pic_irq | w_fabric_irq[7:0]) & 8'hFB)
                 | {5'b0, w_spic_int, 2'b0}
```

Note the order: the external input, the boot-interrupt reroute and the fabric
are OR-ed together first, then `& 8'hFB` clears bit 2, and only then is bit 2
driven from the slave's `INT`. The mask is what makes the cascade trustworthy -
without it an external IRQ2, or a boot-interrupt reroute onto pin 2, could
impersonate the slave controller. Every other master level passes through
unchanged.

**Slave 8259.** The slave's `irq_in` is the inline expression
`pic_irq_in[15:8] | w_fabric_irq[15:8]`. It is not a named signal, which is
worth knowing when probing: with `pic_irq_in` held at zero, the slave's IR line
for a given IRQ *is* `w_fabric_irq[irq]`.

**IOAPIC.** `w_ioapic_irq = ioapic_irq_in | w_fabric_irq`, zero-extended to the
IOAPIC's pin count. The fabric defines 16 legacy lines; the IOAPIC has
`IOAPIC_NUM_IRQS` pins, default 24, and the upper pins are for additional
devices this subsystem does not source.

### OR-ed in, never substituted

`pic_irq_in` and `ioapic_irq_in` remain inputs and are OR-ed with the fabric.
This is deliberate: an integrator keeps the external interrupt path, and every
test that drove those pins directly still works. Replacing them would have been
a silent change to the port contract.

`pic_int_out` is **not** a fabric source. Feeding the controller's own output
back into its inputs is a combinational loop. It appears only in the aggregate
below, which drives nothing internally.

## The Cascade Cross-Connect

The two 8259 instances are wired as a PC/AT pair.

| Direction | Signal | Purpose |
| --- | --- | --- |
| slave to master | `w_spic_int` | the slave's `INT`, forced onto master IR2 |
| master to slave | `w_pic_cas_ack` | the master's cascade acknowledge |
| slave to master | `w_spic_vector` | the slave's vector, returned by the master in place of its own |

The master's `cas_ack_in` ties low, because nothing acknowledges the master from
above. The invariant this creates is that master IR2 always equals
`w_spic_int` - not that IR2 never moves. For any IRQ8-15 source, IR2 *should*
rise; that is the cascade working.

## The Aggregated Output

`rlb_irq_out` is a single line asserted while any block interrupt is asserted:

```
rlb_irq_out = |{hpet_timer_irq, hpet_legacy_irq0, hpet_legacy_irq8,
                pic_int_out, pit_timer_irq,
                rtc_alarm_irq, rtc_second_irq, smb_interrupt,
                pm_interrupt, gpio_irq, uart_irq}
```

It exists for a system that wants one interrupt input rather than ten pins. It
is a pure OR, it includes `pic_int_out` because that is what a single-line
consumer wants to see, and it takes no part in the routing above - which is
precisely why including the controller's own output is safe here.

## Boot-Interrupt Rerouting

The IOAPIC exports which pins it is *not* delivering. `u_ioapic_boot_intx`
turns that into legacy PIC inputs, so a masked IOAPIC pin can still reach the
8259.

The map is the published identity mapping - IOAPIC pin *n* to legacy input *n*
for *n* in 0 to 7 - narrowed to the eight inputs the master controller has, with
a no-reroute code for pins 8 and above. Pin 2 is a dead entry in that table: it
still names legacy input 2, but master IR2 is masked off the external inputs and
driven from the slave, so a reroute onto pin 2 reaches nothing. It is left in the
map so the table still reads as the identity mapping; an integrator who needs pin
2 rerouted picks a different legacy input.

Rerouting is **safe by default**: the enable bit resets to 0, so
`w_boot_intx_pic_irq` is all zeros and the master's OR is exactly `pic_irq_in`
until software opts in.

## Related Documents

- [Overview](01_overview.md)
- [Clocks and Reset](03_clocks_and_reset.md)
- [Top-Level Interface](../ch03_interfaces/01_top_level.md)
- [Initialization](../ch04_programming/01_initialization.md)
