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

# RLB Top - References

## External Specifications

Every peripheral in this subsystem implements a published specification. Copies
of the specifications used are kept in the component's `References/` directory.

| Block | Specification |
| --- | --- |
| HPET | High Precision Event Timer specification, revision 1.0a |
| 8259 PIC | 8259A programmable interrupt controller datasheet |
| 8254 PIT | 82C54 interval timer datasheet |
| RTC | MC146818 real-time clock plus RAM datasheet |
| SMBus | System Management Bus specification, version 3.3 |
| PM/ACPI | Advanced Configuration and Power Interface specification |
| IOAPIC | I/O advanced programmable interrupt controller datasheet |
| UART 16550 | 16550 asynchronous communications element datasheet |
| Bus | AMBA APB protocol specification, APB4 |

The interrupt line assignments this subsystem treats as convention - IRQ0 for
the system timer, IRQ4 for COM1, IRQ8 for the RTC alarm and IRQ9 for ACPI -
come from the typical-assignment table reproduced in
[ioapic_mas ch05](../../ioapic_mas/ch05_registers/01_register_map.md). That
table is the authority cited in the RTL, and it is also the evidence that IRQ10
and IRQ11 have no traditional assignment, which is why SMBus and GPIO are
parameters rather than fixed.

## In-Repository References

### This subsystem

| Item | Location |
| --- | --- |
| Integration RTL | [rtl/rlb_top/rlb_top.sv](../../../rtl/rlb_top/rlb_top.sv) |
| Integration filelist | [rtl/rlb_top/filelists/rlb_top.f](../../../rtl/rlb_top/filelists/rlb_top.f) |
| Generated crossbar | [rtl/apbx_xbar/apbx_xbar_1to10.sv](../../../rtl/apbx_xbar/apbx_xbar_1to10.sv) |
| Test runner | [dv/tests/test_rlb_top.py](../../../dv/tests/test_rlb_top.py) |
| Testbench classes | [dv/tbclasses/rlb_top/](../../../dv/tbclasses/rlb_top/) |
| Subsystem requirements | [PRD.md](../../../PRD.md) |
| Subsystem overview | [README.md](../../../README.md) |
| Area facts and traps | [CLAUDE.md](../../../CLAUDE.md) |
| FPGA integration guide | [docs/RLB_FPGA_IMPLEMENTATION_GUIDE.md](../../RLB_FPGA_IMPLEMENTATION_GUIDE.md) |
| Implementation status | [docs/IMPLEMENTATION_STATUS.md](../../IMPLEMENTATION_STATUS.md) |
| Driver development reading list | [docs/LegacyBlocksAndDriverGuide.md](../../LegacyBlocksAndDriverGuide.md) |

### Per-block specifications

| Block | Specification |
| --- | --- |
| HPET | [hpet_mas](../../hpet_mas/hpet_mas_index.md) |
| 8259 PIC | [pic_8259_mas](../../pic_8259_mas/pic_8259_mas_index.md) |
| 8254 PIT | [pit_8254_mas](../../pit_8254_mas/pit_8254_mas_index.md) |
| RTC | [rtc_mas](../../rtc_mas/rtc_mas_index.md) |
| SMBus | [smbus_mas](../../smbus_mas/smbus_mas_index.md) |
| PM/ACPI | [pm_acpi_mas](../../pm_acpi_mas/pm_acpi_mas_index.md) |
| IOAPIC | [ioapic_mas](../../ioapic_mas/ioapic_mas_index.md) |
| GPIO | [gpio_mas](../../gpio_mas/gpio_mas_index.md) |
| UART 16550 | [uart_16550_mas](../../uart_16550_mas/uart_16550_mas_index.md) |

### Repository practice

The methods this subsystem follows are recorded in the handbook rather than
restated here:

| Topic | Note |
| --- | --- |
| Generated RTL discipline | `vault/handbook/design/generated-rtl-discipline.md` |
| Reset and clocking | `vault/handbook/design/reset-and-clocking.md` |
| Filelists | `vault/handbook/design/filelists.md` |
| Running regressions | `vault/handbook/dv/running-regressions.md` |
| Register map links | `vault/handbook/authoring/register-map-links.md` |

## Related Documents

- [Overview](01_overview.md)
- [Acronyms](04_acronyms.md)
