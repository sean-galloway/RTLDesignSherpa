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

# System Requirements

## Interface Requirements

### APB Interface

| Requirement | Specification |
|-------------|---------------|
| **Protocol** | APB3 or APB4 |
| **Data Width** | 32 bits |
| **Address Width** | 12 bits minimum |
| **Timing** | Synchronous to `aclk` |

### AXI Interfaces

| Requirement | Descriptor | Read Data | Write Data |
|-------------|------------|-----------|------------|
| **Protocol** | AXI4 | AXI4 | AXI4 |
| **Data Width** | 256 bits | Parameterizable | Parameterizable |
| **Address Width** | 64 bits | 64 bits | 64 bits |
| **ID Width** | 4 bits min | 4 bits min | 4 bits min |
| **Outstanding** | 2 | Configurable | Configurable |

### MonBus Interface

| Requirement | Specification |
|-------------|---------------|
| **Data Width** | 64 bits |
| **Protocol** | Valid/Ready streaming |
| **Backpressure** | Required (must handle ready deassertion) |

---

## Memory Requirements

### Descriptor Memory

| Requirement | Specification |
|-------------|---------------|
| **Alignment** | 32-byte aligned |
| **Access** | Read access via descriptor AXI master |
| **Coherency** | Software responsibility |
| **Latency** | <100 cycles recommended |

### Data Memory

| Requirement | Specification |
|-------------|---------------|
| **Alignment** | Per data width (64-byte for 512-bit) |
| **Access** | Read via read master, Write via write master |
| **Bandwidth** | Sufficient for target throughput |

---

## System Bandwidth Allocation

### AXI Interconnect Requirements

To achieve maximum STREAM throughput:

| AXI Master | Required Bandwidth | Priority |
|------------|-------------------|----------|
| Descriptor Fetch | 0.1 GB/s | Medium |
| Data Read | 12.8 GB/s | High |
| Data Write | 12.8 GB/s | High |

### Interconnect Recommendations

- Configure STREAM AXI masters with high priority
- Ensure sufficient outstanding transaction support
- Consider dedicated paths for high-bandwidth DMA

---

## Interrupt Requirements

### Interrupt Controller

| Requirement | Specification |
|-------------|---------------|
| **Interrupt Lines** | 8 (per-channel) or 1 (combined) |
| **Type** | Level-sensitive, active-high |
| **Latency** | <10 cycles from assertion to controller |

### Interrupt Handling

- Software must read `IRQ_STATUS` to identify source
- Write-1-to-clear to acknowledge interrupts
- Channel remains blocked until error cleared (if applicable)

---

## Address Space Requirements

### STREAM Register Space

| Requirement | Specification |
|-------------|---------------|
| **Base Address** | System-defined |
| **Size** | 4 KB (0x1000) |
| **Alignment** | 4 KB aligned |

### Memory Map Constraints

- Descriptor addresses must be accessible via descriptor AXI master
- Source addresses must be accessible via read AXI master
- Destination addresses must be accessible via write AXI master
- All addresses must respect configured address range limits

---

## Software Requirements

### Driver Requirements

| Requirement | Description |
|-------------|-------------|
| **Descriptor Preparation** | Build descriptors in coherent memory |
| **Cache Management** | Flush descriptor cache before kick-off |
| **Interrupt Handling** | Service interrupts promptly |
| **Error Recovery** | Clear error status, optionally retry |

### Programming Sequence

1. Verify STREAM is enabled (`CTRL.ENABLE = 1`)
2. Check target channel is idle (`CHn_STATUS.IDLE = 1`)
3. Prepare descriptor chain in memory
4. Flush cache (if applicable)
5. Write first descriptor address to `CHn_CTRL`
6. Wait for interrupt or poll `CHn_STATUS`

---

**Last Updated:** 2026-01-03
