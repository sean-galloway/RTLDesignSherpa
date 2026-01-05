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

### APB IOAPIC - Acronyms and Terminology

#### Acronyms

| Acronym | Full Name | Description |
|---------|-----------|-------------|
| **IOAPIC** | I/O Advanced Programmable Interrupt Controller | Intel's advanced interrupt routing controller |
| **APB** | Advanced Peripheral Bus | AMBA low-power peripheral bus |
| **AMBA** | Advanced Microcontroller Bus Architecture | ARM bus specification |
| **APIC** | Advanced Programmable Interrupt Controller | Generic term for advanced interrupt controllers |
| **LAPIC** | Local Advanced Programmable Interrupt Controller | Per-CPU interrupt controller |
| **IRQ** | Interrupt Request | Hardware interrupt signal |
| **EOI** | End of Interrupt | Signal that interrupt service is complete |
| **PIC** | Programmable Interrupt Controller | Legacy 8259-style interrupt controller |
| **ISA** | Industry Standard Architecture | Legacy PC bus |
| **PCI** | Peripheral Component Interconnect | Standard expansion bus |
| **RLB** | Retro Legacy Blocks | Project name for classic peripheral IP cores |
| **CDC** | Clock Domain Crossing | Synchronization between clock domains |
| **IRR** | Interrupt Request Register | Intel term for interrupt pending state |
| **ISR** | Interrupt Service Routine | Software interrupt handler |
| **SMI** | System Management Interrupt | Special interrupt for system management mode |
| **NMI** | Non-Maskable Interrupt | High-priority interrupt that can't be masked |
| **INIT** | Initialization | Processor initialization sequence |
| **ExtINT** | External Interrupt | 8259-compatible interrupt delivery |

#### Register Names

| Name | Full Name | Description |
|------|-----------|-------------|
| **IOREGSEL** | I/O Register Select | Indirect access register selector |
| **IOWIN** | I/O Window | Indirect access data window |
| **IOAPICID** | I/O APIC Identification | IOAPIC ID register |
| **IOAPICVER** | I/O APIC Version | Version and capabilities register |
| **IOAPICARB** | I/O APIC Arbitration | Bus arbitration priority register |
| **IOREDTBL** | I/O Redirection Table | Interrupt redirection configuration |

#### Key Terms

**Redirection Table:**
Array of 64-bit entries (one per IRQ) that configure how each interrupt is routed to CPUs. Contains vector, delivery mode, destination, trigger type, polarity, and mask.

**Indirect Access:**
Intel's register access method where software writes an offset to IOREGSEL, then accesses the selected register via IOWIN. Reduces address space requirements.

**Remote IRR (Interrupt Request Register):**
Status bit for level-triggered interrupts. Set when interrupt is accepted by CPU, cleared when EOI is received. Prevents interrupt re-triggering while being serviced.

**Delivery Status:**
Read-only bit indicating if an interrupt delivery is in progress for a specific IRQ. Used to monitor interrupt flow.

**Trigger Mode:**
- **Edge:** Interrupt on signal edge (rising after polarity adjustment)
- **Level:** Interrupt on signal level (requires EOI to clear)

**Polarity:**
- **Active High:** Interrupt when signal is logic 1
- **Active Low:** Interrupt when signal is logic 0 (inverted internally)

**Delivery Mode:**
Determines how interrupt is delivered to CPU:
- **Fixed:** To specific CPU
- **Lowest Priority:** To least-busy CPU
- **SMI/NMI/INIT/ExtINT:** Special modes

**Destination Mode:**
- **Physical:** Destination field is physical APIC ID
- **Logical:** Destination field is logical grouping (multi-cast)

**Priority Arbitration:**
When multiple IRQs are pending, hardware selects which to deliver first. Current implementation uses static priority (lowest IRQ number wins).

**End-of-Interrupt (EOI):**
Signal from CPU indicating interrupt service is complete. For level-triggered interrupts, clears Remote IRR and allows re-triggering if signal still asserted.

---

**See Also:**
- [References](05_references.md) - External standards and specifications
- [Overview](01_overview.md) - Component introduction
- [Architecture](02_architecture.md) - System architecture
