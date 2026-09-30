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

# RLB Top - Acronyms and Terminology

## Acronyms

| Term | Expansion | In this subsystem |
| --- | --- | --- |
| ACPI | Advanced Configuration and Power Interface | The power-management block on window 5 |
| APB | Advanced Peripheral Bus | The bus every block speaks; APB4 here |
| APB4 | AMBA 4 APB | The revision in use, with `PSTRB` and `PPROT` |
| CDC | Clock Domain Crossing | Parameter `CDC_ENABLE`, 0 in this configuration |
| EOI | End Of Interrupt | Acknowledge written back to a controller |
| GPE | General Purpose Event | ACPI wake and status events, `pm_gpe_events` |
| GPIO | General Purpose Input/Output | The controller on window 7 |
| HPET | High Precision Event Timer | The timer on window 0 |
| ICW | Initialization Command Word | 8259 configuration writes, ICW1-ICW4 |
| IOAPIC | I/O Advanced Programmable Interrupt Controller | The controller on window 6 |
| IR | Interrupt Request line | An individual input of an 8259, IR0-IR7 |
| IRQ | Interrupt Request | A legacy line number, IRQ0-IRQ15 |
| MSI | Message Signalled Interrupt | Configurable in the IOAPIC, not emitted here |
| OCW | Operation Command Word | 8259 runtime writes, OCW1-OCW3 |
| PIC | Programmable Interrupt Controller | The 8259 pair, windows 1 and 9 |
| PIT | Programmable Interval Timer | The 8254 on window 2 |
| PM | Power Management | Used interchangeably with ACPI here |
| RLB | Retro Legacy Blocks | This subsystem |
| RTC | Real-Time Clock | The block on window 3 |
| RTE | Redirection Table Entry | An IOAPIC per-pin configuration entry |
| SMBus | System Management Bus | The controller on window 4 |
| UART | Universal Asynchronous Receiver/Transmitter | The 16550 on window 8 |

## Terminology

**Window.** One of the ten 4KB address regions behind the crossbar. Window *n*
starts at `BASE_ADDR + n * 0x1000`. The window number equals the crossbar's
slave index, which equals `PADDR[15:12]`.

**Fabric.** The internal interrupt routing in `rlb_top`: the `w_fabric_irq`
vector and the logic that builds it and distributes it. Not a bus.

**Line.** A legacy IRQ number, 0 to 15. A line is a position in the fabric
vector, and separately an input on one of the two controllers.

**Convention versus choice.** A line assignment is *convention* if it comes
from the published typical-assignment table, and a *choice* if this subsystem
picked it because no traditional assignment exists. Convention assignments are
fixed in the RTL; choices are module parameters.

**Master and slave.** The two 8259 instances. The master is on window 1 and
drives `pic_int_out`; the slave is on window 9 and reaches the CPU only through
the master's IR2. Unrelated to the APB sense of master and slave.

**Cascade.** The connection between the two controllers. Master IR2 carries the
slave's `INT`, the master's acknowledge reaches the slave, and the slave's
vector is returned in place of the master's.

**Boot interrupt.** A source whose IOAPIC pin is masked, rerouted to the legacy
controller so it is not lost during boot before the IOAPIC is configured.

**Legacy replacement.** An HPET mode in which HPET timers 0 and 1 take over the
8254 tick and the RTC periodic interrupt, appearing on `hpet_legacy_irq0` and
`hpet_legacy_irq8` while being suppressed on `hpet_timer_irq`.

## Related Documents

- [Overview](01_overview.md)
- [References](05_references.md)
