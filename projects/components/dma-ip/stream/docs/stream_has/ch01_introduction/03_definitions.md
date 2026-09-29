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
| APB | Advanced Peripheral Bus |
| AXI | Advanced eXtensible Interface |
| AMBA | Advanced Microcontroller Bus Architecture |
| BFM | Bus Functional Model |
| CDC | Clock Domain Crossing |
| DMA | Direct Memory Access |
| FIFO | First-In First-Out buffer |
| FSM | Finite State Machine |
| HAS | Hardware Architecture Specification |
| MAS | Micro-Architecture Specification |
| MonBus | Monitor Bus (internal debug/trace interface) |
| PRD | Product Requirements Document |
| RTL | Register Transfer Level |
| SG | Scatter-Gather |
| SRAM | Static Random Access Memory |
| STREAM | Scatter-gather Transfer Rapid Engine for AXI Memory |

---

## Definitions

### Architectural Terms

| Term | Definition |
|------|------------|
| **Beat** | A single data transfer on an AXI bus, corresponding to one clock cycle where valid data is transferred. For a 512-bit data bus, one beat transfers 64 bytes. |
| **Burst** | A sequence of consecutive beats forming a single AXI transaction. STREAM supports burst lengths up to 256 beats (AXI4 maximum). |
| **Channel** | An independent DMA transfer context. STREAM supports 8 channels, each capable of processing its own descriptor chain. |
| **Descriptor** | A 256-bit data structure in memory that defines a single DMA transfer operation, including source address, destination address, length, and chaining information. |
| **Descriptor Chain** | A linked list of descriptors where each descriptor points to the next, enabling complex scatter-gather transfer patterns. |
| **Scatter-Gather** | A DMA technique where data is transferred to/from non-contiguous memory locations using a list of descriptors. |

### Interface Terms

| Term | Definition |
|------|------------|
| **APB Slave** | STREAM's configuration interface, receiving programming commands from the system processor. |
| **AXI Master** | STREAM's memory interfaces for descriptor fetches and data transfers. Three masters: descriptor fetch, data read, data write. |
| **MonBus** | Monitor Bus - a 64-bit streaming interface for debug and performance monitoring packets. |
| **Backpressure** | Flow control mechanism where a receiver signals inability to accept data, causing the sender to pause. |

### Transfer Terms

| Term | Definition |
|------|------------|
| **Aligned Address** | An address that is a multiple of the data width in bytes. For 512-bit (64-byte) data width, aligned addresses are multiples of 64. |
| **Kick-off** | Initiating a DMA transfer by writing the first descriptor address to a channel's control register. |
| **Completion** | The successful end of a descriptor chain, optionally generating an interrupt. |
| **Chaining** | Following the `next_descriptor_ptr` to fetch and process subsequent descriptors. |

---

## Units and Measurements

| Term | Definition |
|------|------------|
| **Clock Cycle** | One period of the primary system clock (aclk). |
| **Latency** | Time from initiating an operation to its completion, typically measured in clock cycles. |
| **Throughput** | Data transfer rate, typically measured in bytes per second or beats per cycle. |
| **Utilization** | Percentage of available bandwidth actually used for data transfer. |

---

## Document-Specific Terms

| Term | Definition |
|------|------------|
| **External Interface** | A signal or bus that crosses the STREAM subsystem boundary. |
| **Internal Interface** | A signal or bus between blocks within STREAM, not visible externally. |
| **Configuration Register** | An APB-accessible register for controlling STREAM behavior. |
| **Status Register** | An APB-readable register reporting STREAM operational state. |

---

**Last Updated:** 2026-01-03
