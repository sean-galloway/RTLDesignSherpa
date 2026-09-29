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

# Acronyms and Definitions

## Acronyms

| Acronym | Definition |
|---------|------------|
| AXI | Advanced eXtensible Interface |
| AXIS | AXI-Stream |
| APB | Advanced Peripheral Bus |
| DMA | Direct Memory Access |
| FIFO | First-In First-Out |
| FSM | Finite State Machine |
| HAS | Hardware Architecture Specification |
| MAS | Module Architecture Specification |
| MonBus | Monitor Bus |
| RAPIDS | Rapid AXI Programmable In-band Descriptor System |
| SRAM | Static Random Access Memory |

: Acronym Definitions

## Definitions

| Term | Definition |
|------|------------|
| **Beat** | Single data transfer unit (512 bits = 64 bytes in default configuration) |
| **Channel** | Independent DMA context with dedicated descriptor processing |
| **Descriptor** | 256-bit control structure defining a single DMA transfer |
| **Descriptor Chain** | Linked list of descriptors for multi-transfer operations |
| **Sink Path** | Data flow from network (AXIS slave) to memory (AXI write) |
| **Source Path** | Data flow from memory (AXI read) to network (AXIS master) |
| **Fill** | Operation writing data into SRAM buffer (sink path input) |
| **Drain** | Operation reading data from SRAM buffer (source path output) |

: Term Definitions

## Signal Naming Conventions

| Prefix/Suffix | Meaning |
|---------------|---------|
| `m_axi_*` | AXI Master signals |
| `s_axis_*` | AXIS Slave signals |
| `m_axis_*` | AXIS Master signals |
| `cfg_*` | Configuration signals |
| `*_valid` | Handshake valid signal |
| `*_ready` | Handshake ready signal |
| `*_n` | Active-low signal |

: Signal Naming Conventions
