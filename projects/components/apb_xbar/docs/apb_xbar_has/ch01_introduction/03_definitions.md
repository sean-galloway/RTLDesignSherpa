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

# Definitions and Acronyms

## Acronyms

| Acronym | Definition |
|---------|------------|
| AMBA | Advanced Microcontroller Bus Architecture |
| APB | Advanced Peripheral Bus |
| CPU | Central Processing Unit |
| DMA | Direct Memory Access |
| FSM | Finite State Machine |
| GPIO | General Purpose Input/Output |
| HAS | Hardware Architecture Specification |
| I2C | Inter-Integrated Circuit |
| LOC | Lines of Code |
| LUT | Lookup Table (FPGA resource) |
| MAS | Micro-Architecture Specification |
| PRD | Product Requirements Document |
| RTL | Register Transfer Level |
| SoC | System on Chip |
| SPI | Serial Peripheral Interface |
| UART | Universal Asynchronous Receiver/Transmitter |

: Acronym Definitions

## Terms

| Term | Definition |
|------|------------|
| Address Decode | Logic that determines which slave should receive a transaction based on address |
| Arbitration | Process of selecting one request when multiple masters compete for the same slave |
| Back-to-back | Consecutive transactions with no idle cycles between them |
| Crossbar | Interconnect topology allowing any master to communicate with any slave |
| Grant Persistence | Maintaining arbitration grant through entire transaction duration |
| Master | Device that initiates APB transactions (CPU, DMA, etc.) |
| Round-Robin | Arbitration scheme that rotates priority among requesters |
| Slave | Device that responds to APB transactions (peripherals) |
| Starvation | Condition where a requester is indefinitely denied access |
| Transaction | Complete APB read or write operation including setup and data phases |
| Zero-Bubble | No idle cycles inserted between consecutive transactions |

: Term Definitions

## APB Protocol Signals

| Signal | Direction | Description |
|--------|-----------|-------------|
| PCLK | Input | APB clock (all signals synchronous to rising edge) |
| PRESETn | Input | Active-low asynchronous reset |
| PADDR | Master to Slave | Address bus |
| PSEL | Master to Slave | Peripheral select (one per slave) |
| PENABLE | Master to Slave | Enable signal (high during data phase) |
| PWRITE | Master to Slave | Write/read direction (1=write, 0=read) |
| PWDATA | Master to Slave | Write data bus |
| PSTRB | Master to Slave | Write strobes (byte enables) |
| PPROT | Master to Slave | Protection attributes |
| PRDATA | Slave to Master | Read data bus |
| PREADY | Slave to Master | Ready signal (can extend transaction) |
| PSLVERR | Slave to Master | Slave error response |

: APB Protocol Signal Definitions

---

**Next:** [Chapter 2: System Overview](../ch02_system_overview/01_use_cases.md)
