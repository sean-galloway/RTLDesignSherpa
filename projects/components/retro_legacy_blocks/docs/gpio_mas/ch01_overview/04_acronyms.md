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

# APB GPIO - Acronyms and Terminology

## Protocol Acronyms

| Acronym | Full Name | Description |
|---------|-----------|-------------|
| APB | Advanced Peripheral Bus | Low-power AMBA bus protocol |
| AMBA | Advanced Microcontroller Bus Architecture | ARM standard bus protocols |
| CDC | Clock Domain Crossing | Synchronization between clock domains |

## Signal Acronyms

| Acronym | Full Name | Description |
|---------|-----------|-------------|
| CLK | Clock | Timing reference signal |
| RST | Reset | System initialization signal |
| OE | Output Enable | Tri-state buffer control |
| IRQ | Interrupt Request | Hardware interrupt signal |

## GPIO-Specific Terms

| Term | Description |
|------|-------------|
| GPIO | General Purpose Input/Output - Configurable digital I/O pins |
| Pin | Individual GPIO signal (input or output) |
| Port | Group of 32 GPIO pins managed together |
| Direction | Input (0) or Output (1) configuration per pin |
| Polarity | Active-high or active-low signal interpretation |

## Interrupt Terms

| Term | Description |
|------|-------------|
| Edge-triggered | Interrupt on signal transition |
| Level-sensitive | Interrupt while signal is at specified level |
| Rising edge | Low-to-high transition |
| Falling edge | High-to-low transition |
| Both edges | Either transition direction |

## Register Terms

| Term | Description |
|------|-------------|
| RW | Read-Write register |
| RO | Read-Only register |
| W1C | Write-1-to-Clear register |
| HWIF | Hardware Interface (PeakRDL generated) |

---

**Next:** [05_references.md](05_references.md) - Reference documents
